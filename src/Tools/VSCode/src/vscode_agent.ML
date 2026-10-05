(*  Title:      Tools/VSCode/src/vscode_agent.ML

Proof candidates for AI agents, tried on the state before a command without editing the
text: the operations behind the extension's MCP tools (vscode_agent.scala).

Each candidate is Isar text -- a terminal proof, apply steps, a whole proof block, or a
diagnostic command like thm or find_theorems -- run on the state with a timeout of its own.
The goal is the state's own, or one the agent states: "have" in a proof, "lemma" outside one.

A candidate runs in a thread of its own rather than in the query's worker: outside a worker
task Future.proofs_enabled is false, so "by" does not fork its proof and an error surfaces
within the candidate, which can then be given a timeout and its own output. That output --
of thm, find_theorems, warnings, the simplifier's trace -- is captured per thread, so it
reaches the agent rather than the messages of the command in the editor.

The simplifier's trace is not passed on but summarised: how often each rewrite rule was
applied, the cycle of rules that repeats at the end of a run that timed out, and the steps of
rules or terms the agent watches. The trace hooks (Raw_Simplifier.set_trace_ops) are theory
data that Simplifier_Trace owns, so this reads the text of the classic simp_trace.

Sledgehammer is a second operation, compiled only in a logic that contains it, as in
vscode_sledgehammer.ML; its proofs are tried as candidates afterwards.

Loaded as a prelude of the prover process, like vscode_completion.ML: plain ML over Pure,
without antiquotations, and declaring nothing at the toplevel.
*)

local

(** output, captured per thread **)

(*the sink of the current thread: true for a tracing message*)
val sink_var = Thread_Data.var () : (bool * string -> unit) Thread_Data.var;

fun capture tracing old ss =
  (case Thread_Data.get sink_var of
    SOME sink => sink (tracing, implode ss)
  | NONE => old ss);

val installed = Synchronized.var "vscode_agent_capture" ([]: (string list -> unit) list);

(*the channels are global references, and a setmp elsewhere puts back what it found: wrapped
  again whenever ours is not the one there*)
fun ensure_capture () =
  Synchronized.change installed (fn ours =>
    fold (fn (tracing, r) => fn ours =>
      if exists (fn f => pointer_eq (f, ! r)) ours then ours
      else
        let val f = capture tracing (! r)
        in r := f; f :: ours end)
      [(false, Private_Output.writeln_fn), (false, Private_Output.writeln_urgent_fn),
       (false, Private_Output.state_fn), (false, Private_Output.information_fn),
       (true, Private_Output.tracing_fn), (false, Private_Output.warning_fn),
       (false, Private_Output.legacy_fn)] ours);

val max_output = 12000;

fun bounded_buffer () =
  let
    val buf = Unsynchronized.ref ([]: string list);
    val used = Unsynchronized.ref 0;
    fun add s =
      if ! used >= max_output then ()
      else
        let val s' = if ! used + size s > max_output
          then String.substring (s, 0, max_output - ! used) ^ "\n..." else s
        in buf := s' :: ! buf; used := ! used + size s' end;
  in (add, fn () => cat_lines (rev (! buf))) end;


(** simplifier trace **)

type watch = {rules: string list, patterns: string list, limit: int};

type step =
  {depth: int, rule: string, instance: string,
   premises: string list Unsynchronized.ref, inner: string list Unsynchronized.ref,
   outcome: string Unsynchronized.ref};

val max_recent = 600;
val max_premises = 4;
val max_inner = 12;

(*"[2]Trying to rewrite:\n..." -> (2, "Trying to rewrite:", "...")*)
fun parse_message s =
  let
    val (head, body) =
      (case first_field "\n" s of
        SOME (h, b) => (h, b)
      | NONE => (s, ""));
  in
    if String.isPrefix "[" head then
      (case first_field "]" (unprefix "[" head) of
        SOME (d, rest) => Option.map (fn d => (d, rest, body)) (Int.fromString d)
      | NONE => NONE)
    else NONE
  end;

(*Applying instance of rewrite rule "List.rev_rev_ident":*)
fun rule_name rest body =
  (case space_explode "\"" rest of
    _ :: name :: _ => name
  | _ =>
    let val line = the_default body (Option.map #1 (first_field "\n" body))
    in "(unnamed: " ^ (if size line > 60 then String.substring (line, 0, 60) ^ "...)" else line ^ ")") end);

(*foo(2) and Theory.foo match the watched name foo*)
fun rule_matches names name =
  let
    val bare = (case first_field "(" name of SOME (n, _) => n | NONE => name);
    fun eq w = bare = w orelse name = w orelse Long_Name.base_name bare = w orelse
      String.isSuffix ("." ^ w) bare;
  in exists eq names end;

(*best effort: the pattern against the redex of an instance read back from its text, and only
  when the text spells the pattern's constants*)
fun pattern_matcher ctxt patterns =
  let
    val ctxt_pat = Proof_Context.set_mode Proof_Context.mode_pattern ctxt;
    val thy = Proof_Context.theory_of ctxt;
    val pats =
      map_filter (fn s =>
        Option.map (fn t => (t, map Long_Name.base_name (Term.add_const_names t [])))
          (try (Proof_Context.read_term_pattern ctxt) s)) patterns;
    fun redex text =
      try (fn () =>
        Syntax.read_prop ctxt_pat text
        |> Logic.strip_imp_concl |> Logic.dest_equals |> #1) ();
  in
    fn text =>
      let val candidates = filter (fn (_, cs) => forall (fn c => String.isSubstring c text) cs) pats
      in
        not (null candidates) andalso
          (case redex text of
            SOME t => exists (fn (p, _) => Pattern.matches thy (p, t)) candidates
          | NONE => false)
      end
  end;

fun make_trace ctxt (watch: watch option) =
  let
    val counts = Unsynchronized.ref (Symtab.empty: (int * int) Symtab.table);
    val recent = Unsynchronized.ref ([]: string list);
    val n_recent = Unsynchronized.ref 0;
    val pending = Unsynchronized.ref (Inttab.empty: string Inttab.table);
    val open_steps = Unsynchronized.ref (Inttab.empty: step Inttab.table);
    val steps = Unsynchronized.ref ([]: step list);
    val n_steps = Unsynchronized.ref 0;
    val more = Unsynchronized.ref 0;

    val limit = (case watch of SOME {limit, ...} => limit | NONE => 0);
    val by_name = (case watch of SOME {rules, ...} => rule_matches rules | NONE => K false);
    val by_pattern =
      (case watch of
        SOME {patterns = ps as _ :: _, ...} => pattern_matcher ctxt ps
      | _ => K false);
    fun watched name text = by_name name orelse by_pattern text;

    fun count name f = counts := Symtab.map_default (name, (0, 0)) f (! counts);
    fun record (step: step) =
      if ! n_steps < limit then (steps := step :: ! steps; n_steps := ! n_steps + 1)
      else more := ! more + 1;
    fun new_step depth rule instance outcome : step =
      {depth = depth, rule = rule, instance = instance, premises = Unsynchronized.ref [],
        inner = Unsynchronized.ref [], outcome = Unsynchronized.ref outcome};
    fun add_bounded n r x = if length (! r) < n then r := x :: ! r else ();

    fun message (depth, rest, body) =
      if String.isPrefix "Applying instance of rewrite rule" rest then
        let val name = rule_name rest body in
          pending := Inttab.update (depth, name) (! pending);
          count name (fn (a, f) => (a + 1, f));
          if ! n_recent < max_recent then
            (recent := name :: ! recent; n_recent := ! n_recent + 1)
          else recent := name :: take (max_recent - 1) (! recent);
          (case Inttab.lookup (! open_steps) (depth - 1) of
            SOME (step: step) => add_bounded max_inner (#inner step) name
          | NONE => ())
        end
      else if rest = "Rewriting:" then
        (case Inttab.lookup (! pending) depth of
          SOME name =>
            if limit > 0 andalso watched name body
            then record (new_step depth name body "rewrote") else ()
        | NONE => ())
      else if rest = "Trying to rewrite:" then
        (case Inttab.lookup (! pending) depth of
          SOME name =>
            if limit > 0 andalso watched name body then
              let val step = new_step depth name body "condition not decided"
              in record step; open_steps := Inttab.update (depth, step) (! open_steps) end
            else ()
        | NONE => ())
      else if rest = "SIMPLIFIER INVOKED ON THE FOLLOWING TERM:" then
        (case Inttab.lookup (! open_steps) (depth - 1) of
          SOME (step: step) => add_bounded max_premises (#premises step) body
        | NONE => ())
      else if rest = "FAILED" then
        ((case Inttab.lookup (! pending) depth of
            SOME name => count name (fn (a, f) => (a, f + 1))
          | NONE => ());
         (case Inttab.lookup (! open_steps) depth of
            SOME (step: step) =>
              (#outcome step := "condition failed";
               open_steps := Inttab.delete_safe depth (! open_steps))
          | NONE => ()))
      else if rest = "SUCCEEDED" then
        (case Inttab.lookup (! open_steps) depth of
          SOME (step: step) =>
            (#outcome step := "condition proved";
             open_steps := Inttab.delete_safe depth (! open_steps))
        | NONE => ())
      else ();

    fun sink text = (case parse_message text of SOME m => message m | NONE => ());

    (*the shortest period with which the latest rules repeat, at least three times*)
    fun cycle () =
      let
        val xs = ! recent;
        val n = length xs;
        fun periodic p = forall (fn i => nth xs i = nth xs (i + p)) (0 upto 2 * p - 1);
        fun find p = if 3 * p > n orelse p > 60 then [] else if periodic p then rev (take p xs) else find (p + 1);
      in find 1 end;

    fun result () =
      let
        val stats =
          Symtab.dest (! counts)
          |> sort (fn ((_, (a, _)), (_, (b, _))) => int_ord (b, a))
          |> take 10;
        val steps' =
          rev (! steps) |> map (fn {depth, rule, instance, premises, inner, outcome} =>
            [("depth", string_of_int depth), ("rule", rule), ("instance", instance),
             ("outcome", ! outcome),
             ("premises", space_implode "\n\n" (rev (! premises))),
             ("inner", commas (rev (! inner)))]);
      in (stats, cycle (), steps', ! more) end;
  in (sink, result) end;

fun trace_on st =
  Toplevel.command_exception false
    (Toplevel.make "vscode_agent" Position.none |> Toplevel.proof
      (Proof.map_contexts
        (Config.put Raw_Simplifier.simp_trace true #>
         Config.put Raw_Simplifier.simp_trace_depth_limit 100))) st;


(** candidates **)

fun content s = XML.content_of (YXML.parse_body s);

fun pretty_state st = Pretty.pure_string_of (Pretty.chunks (Toplevel.pretty_state st));

exception CANDIDATE of string;

(*the state after the text, and the names of its commands*)
fun run_text st text =
  let
    val thy = Toplevel.theory_of st;
    val trs = Outer_Syntax.parse_text thy (K thy) Position.none text;
    val names = map Toplevel.name_of trs;
    val _ = if null trs then raise CANDIDATE "empty text" else ();
    val _ =
      if exists (member (op =) ["sorry", "oops", "\092<proof>"]) names
      then raise CANDIDATE "skips the proof (sorry or oops)" else ();
    fun step tr st =
      Toplevel.command_exception false tr st
        handle Runtime.EXCURSION_FAIL (exn, _) =>
          raise CANDIDATE (cat_lines (map (content o #2 o #1) (Runtime.exn_messages exn)));
  in (fold step trs st, names) end;

(*Opens the agent's goal: "have" in a proof, "lemma" outside one; the statement is passed
  ready to follow the keyword*)
fun open_goal st "" = st
  | open_goal st stmt =
      #1 (run_text st ((if Toplevel.is_proof st then "have " else "lemma ") ^ stmt));

fun no_subgoals st =
  (case try (Thm.nprems_of o #goal o Proof.goal o Toplevel.proof_of) st of
    SOME 0 => true
  | _ => false);

fun outcome keywords st_goal (st', names) =
  if forall (Keyword.is_diag keywords) names then ("output", "")
  else if not (Toplevel.is_proof st_goal) then ("ok", "")
  else if not (Toplevel.is_proof st') orelse Toplevel.level st' < Toplevel.level st_goal
  then ("proved", "")
  else if no_subgoals st' then ("no_subgoals", pretty_state st')
  else ("goals_left", pretty_state st');

fun ms t = string_of_int (Time.toMilliseconds t);

(*one candidate, in the current thread, with its output going to the agent*)
fun run_candidate st_goal timeout traced watch text =
  let
    val ctxt = Toplevel.context_of st_goal;
    val keywords = Thy_Header.get_keywords' ctxt;
    val (add_output, get_output) = bounded_buffer ();
    val trace = if traced then SOME (make_trace ctxt watch) else NONE;
    fun sink (true, s) = (case trace of SOME (f, _) => f (content s) | NONE => ())
      | sink (false, s) = add_output (content s);
    val start = Timing.start ();
    val st0 = if traced andalso Toplevel.is_proof st_goal then trace_on st_goal else st_goal;
    val res =
      Thread_Data.setmp sink_var (SOME sink) (fn () =>
        Exn.capture_body (fn () =>
          Timeout.apply timeout (fn () => outcome keywords st_goal (run_text st0 text)) ())) ();
    val elapsed = #elapsed (Timing.result start);
    val (kind, text') =
      (case res of
        Exn.Res r => r
      | Exn.Exn (CANDIDATE msg) => ("error", msg)
      | Exn.Exn (Timeout.TIMEOUT _) => ("timeout", "")
      | Exn.Exn exn =>
          if Exn.is_interrupt exn then Exn.reraise exn
          else ("error", content (Runtime.exn_message exn)));
    val (stats, cycle, steps, more) =
      (case trace of SOME (_, result) => result () | NONE => ([], [], [], 0));
  in
    ([("text", text), ("outcome", kind), ("time_ms", ms elapsed), ("state", text'),
      ("output", get_output ()), ("traced", if traced then "true" else ""),
      ("more_steps", string_of_int more)], (stats, (cycle, steps)))
  end;

(*a candidate that timed out untraced runs once more with the trace on, for its statistics*)
fun try_candidate st_goal timeout stats watch text =
  let
    val traced = stats orelse is_some watch;
    val res as (props, _) = run_candidate st_goal timeout traced watch text;
  in
    if not traced andalso Properties.get props "outcome" = SOME "timeout" andalso
      Toplevel.is_proof st_goal
    then
      let
        val timeout' = if Time.< (timeout, seconds 5.0) then timeout else seconds 5.0;
        val (_, rest) = run_candidate st_goal timeout' true NONE text;
      in (Properties.put ("traced", "rerun") props, rest) end
    else res
  end;

(*each in a thread of its own, a few at a time; interrupted with the query*)
fun parallel n fs =
  let
    fun batch [] = []
      | batch fs =
          let
            val (now, later) = chop n fs;
            val vars = map (fn _ => Single_Assignment.var "vscode_agent") now;
            val threads =
              map2 (fn f => fn v =>
                Isabelle_Thread.fork
                  (Isabelle_Thread.params "vscode_agent" |> Isabelle_Thread.interrupts)
                  (fn () => Single_Assignment.assign v (Exn.capture_body f))) now vars;
            val results =
              (case Exn.capture_body (fn () => map Single_Assignment.await vars) of
                Exn.Res results => results
              | Exn.Exn exn =>
                  (List.app Isabelle_Thread.interrupt_thread threads; Exn.reraise exn));
          in map Exn.release results @ batch later end;
  in batch fs end;


(** arguments and result **)

(*plain strings, as overlays pass them on: goal, timeout in ms, "true" for statistics,
  watch limit, then three counted lists -- candidates, watched rules, watched patterns*)
fun decode_args (goal :: timeout_ms :: stats :: watch_limit :: rest) =
      let
        fun counted (n :: xs) =
              (case Int.fromString n of
                SOME k => if k <= length xs then chop k xs else error "Bad arguments"
              | NONE => error "Bad arguments")
          | counted [] = error "Bad arguments";
        val (candidates, rest1) = counted rest;
        val (rules, rest2) = counted rest1;
        val (patterns, _) = counted rest2;
        val limit = the_default 0 (Int.fromString watch_limit);
      in
        {goal = goal,
         timeout = Time.fromMilliseconds (the_default 10000 (Int.fromString timeout_ms)),
         stats = stats = "true",
         watch =
          if null rules andalso null patterns then NONE
          else SOME {rules = rules, patterns = patterns, limit = if limit <= 0 then 20 else limit},
         candidates = candidates}
      end
  | decode_args _ = error "Bad arguments";

fun encode_result (header, candidates) =
  let open XML.Encode in
    YXML.string_of_body
      (pair properties
        (list (pair properties (pair (list (pair string (pair int int)))
          (pair (list string) (list properties))))) (header, candidates))
  end;

fun try_all state {goal, timeout, stats, watch, candidates} =
  (case Exn.capture_body (fn () => open_goal state goal) of
    Exn.Res st_goal =>
      let
        val _ = ensure_capture ();
        val results =
          parallel 4 (map (fn text => fn () => try_candidate st_goal timeout stats watch text)
            candidates);
        val header =
          [("state", if Toplevel.is_proof st_goal then pretty_state st_goal else ""),
           ("proof", if Toplevel.is_proof st_goal then "true" else "")];
      in (header, results) end
  | Exn.Exn (CANDIDATE msg) => ([("error", "The goal could not be stated: " ^ msg)], [])
  | Exn.Exn exn =>
      if Exn.is_interrupt exn then Exn.reraise exn
      else ([("error", content (Runtime.exn_message exn))], []));


(** Sledgehammer: compiled in a logic that contains it **)

(*the goal is opened as above; the found proofs are tried as candidates afterwards*)
val sledgehammer_operation = "\
\Command.no_print_function \"vscode_agent_sledgehammer_query\";\n\
\Query_Operation.register {name = \"vscode_agent_sledgehammer\", pri = Task_Queue.urgent_pri}\n\
\  (fn {state = st, args, output_result, ...} =>\n\
\    let\n\
\      val (goal, timeout) =\n\
\        (case args of [g, t] => (g, t) | _ => error \"Bad arguments\");\n\
\      val st' =\n\
\        if goal = \"\" then st\n\
\        else\n\
\          let\n\
\            val thy = Toplevel.theory_of st;\n\
\            val text = (if Toplevel.is_proof st then \"have \" else \"lemma \") ^ goal;\n\
\          in\n\
\            fold (Toplevel.command_exception false)\n\
\              (Outer_Syntax.parse_text thy (K thy) Position.none text) st\n\
\          end;\n\
\      val state0 = Toplevel.proof_of st';\n\
\      val state =\n\
\        Proof.map_contexts\n\
\          (Try0_HOL.silence_methods #> Config.put SMT_Config.verbose false) state0;\n\
\      val params =\n\
\        Sledgehammer_Commands.default_params (Proof.theory_of state)\n\
\          [(\"timeout\", timeout), (\"isar_proofs\", \"false\"), (\"try0\", \"true\"),\n\
\           (\"debug\", \"false\"), (\"verbose\", \"false\"), (\"overlord\", \"false\")];\n\
\      val messages = Synchronized.var \"vscode_agent_sledgehammer\" ([]: string list);\n\
\      fun output s = Synchronized.change messages (cons s);\n\
\      fun run () =\n\
\        ignore (Sledgehammer.run_sledgehammer params Sledgehammer_Prover.Normal\n\
\          (SOME output) 1 Sledgehammer_Fact.no_fact_override state);\n\
\      val _ =\n\
\        Future.join ((singleton o Future.forks)\n\
\          {name = \"vscode_agent_sledgehammer\", group = NONE, deps = [], pri = ~2,\n\
\            interrupts = true} run);\n\
\    in\n\
\      output_result [YXML.string_of_body (XML.Encode.list XML.Encode.string\n\
\        (map (XML.content_of o YXML.parse_body) (rev (Synchronized.value messages))))]\n\
\    end);\n";

in

val _ =
  Query_Operation.register {name = "vscode_agent_try", pri = Task_Queue.urgent_pri}
    (fn {state, args, output_result, ...} =>
      output_result [encode_result (try_all state (decode_args args))]);

(*replaced below in a logic that contains Sledgehammer*)
val _ =
  Query_Operation.register {name = "vscode_agent_sledgehammer", pri = Task_Queue.urgent_pri}
    (fn _ => error "Sledgehammer needs a session that contains it, like HOL");

val _ =
  (case Thy_Info.lookup_theory "HOL.Sledgehammer" of
    SOME thy =>
      ML_Context.eval_source_in (SOME (Proof_Context.init_global thy)) ML_Compiler.flags
        (Input.string sledgehammer_operation)
  | NONE => ());

end;
