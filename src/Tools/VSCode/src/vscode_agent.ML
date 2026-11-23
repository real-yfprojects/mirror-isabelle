(*  Title:      Tools/VSCode/src/vscode_agent.ML

Proof candidates for AI agents, tried on the state before a command without editing the
text: the operations behind the extension's MCP tools (vscode_agent.scala).

Each candidate is Isar text -- a terminal proof, apply steps, a whole proof block, or a
diagnostic command like thm or find_theorems -- run on the state with a timeout of its own.
The goal is the state's own, or one the agent states: "have" in a proof, "lemma" outside one.

A candidate may outline a proof with sorry: it then comes back with the goals each sorry
skips, the holes the agent fills in next. Each step of a candidate is timed, and the slowest
steps of a candidate of several are reported, so that slow proofs show before they are written.

A candidate runs in a thread of its own rather than in the query's worker: outside a worker
task Future.proofs_enabled is false, so "by" does not fork its proof and an error surfaces
within the candidate, which can then be given a timeout and its own output. That output --
of thm, find_theorems, warnings, the simplifier's trace -- is captured per thread, so it
reaches the agent rather than the messages of the command in the editor.

The simplifier's trace is not passed on but summarised: how often each rewrite rule was
applied, the cycle of rules that repeats at the end of a run that timed out, and the steps of
rules or terms the agent watches. The trace hooks (Raw_Simplifier.set_trace_ops) are theory
data that Simplifier_Trace owns, so this reads the text of the classic simp_trace.

Sledgehammer for agents is a job of vscode_sledgehammer.ML, which goes on while the theory
is edited; the client tries its proofs as candidates afterwards.

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

fun is_sorry name = name = "sorry" orelse name = "\092<proof>";

(*a sorry outlines a proof that the agent fills in later; the cheating it does needs
  interactive mode, which a candidate's thread is not in*)
fun run_command tr st =
  Toplevel.command_exception (is_sorry (Toplevel.name_of tr)) tr st;

(*the source of a step: from its command to the next one, as far as its first line*)
fun step_source syms offsets i =
  let
    val start = nth offsets i;
    val stop = if i + 1 < length offsets then nth offsets (i + 1) else length syms + 1;
    val text = implode (take (stop - start) (drop (start - 1) syms));
    val line = the_default text (Option.map #1 (first_field "\n" text));
    val line' = Symbol.trim_blanks line;
  in if size line' > 80 then String.substring (line', 0, 77) ^ "..." else line' end;

type run =
  {state: Toplevel.state, names: string list,
   holes: (Properties.T * Toplevel.state) list, steps: (Properties.T * Time.time) list};

(*the state after the text, the names of its commands, the holes that its sorrys leave
  (their line in the text, the goals they skip, the text before them, and the state at
  them), and the time of each step*)
fun run_text st text : run =
  let
    val thy = Toplevel.theory_of st;
    val trs =
      Outer_Syntax.parse_text thy (K thy) Position.start text
      |> filter_out Toplevel.is_ignored;
    val names = map Toplevel.name_of trs;
    val _ = if null trs then raise CANDIDATE "empty text" else ();
    val _ =
      if member (op =) names "oops"
      then raise CANDIDATE "gives the proof up (oops)" else ();
    val syms = Symbol.explode text;
    val offsets =
      map_index (fn (i, tr) =>
        the_default (if i = 0 then 1 else size text) (Position.offset_of (Toplevel.pos_of tr)))
        trs;
    fun line_of tr = string_of_int (the_default 1 (Position.line_of (Toplevel.pos_of tr)));
    fun step (i, tr) (st, holes, steps) =
      let
        val holes' =
          if is_sorry (Toplevel.name_of tr)
          then
            ([("line", line_of tr), ("goals", pretty_state st),
              ("prefix", Symbol.trim_blanks (implode (take (nth offsets i - 1) syms)))], st)
            :: holes
          else holes;
        val start = Timing.start ();
        val st' =
          run_command tr st
            handle Runtime.EXCURSION_FAIL (exn, _) =>
              raise CANDIDATE (cat_lines (map (content o #2 o #1) (Runtime.exn_messages exn)));
        val props =
          [("line", line_of tr), ("command", Toplevel.name_of tr),
           ("source", step_source syms offsets i)];
      in (st', holes', (props, #elapsed (Timing.result start)) :: steps) end;
    val (st', holes, steps) = fold step (map_index I trs) (st, [], []);
  in {state = st', names = names, holes = rev holes, steps = rev steps} end;

(*how a goal of one's own is stated: "have" in a proof, after "proof -" where the proof goes on
  by apply, which takes no "have"; "lemma" outside a proof*)
fun goal_keyword st =
  if not (Toplevel.is_proof st) then "lemma "
  else if can (Proof.assert_backward o Toplevel.proof_of) st then "proof - have "
  else "have ";

(*Opens the agent's goal: "have" in a proof, "lemma" outside one; the statement is passed
  ready to follow the keyword*)
fun open_goal st "" = st
  | open_goal st stmt =
      #state (run_text st (goal_keyword st ^ stmt));

fun no_subgoals st =
  (case try (Thm.nprems_of o #goal o Proof.goal o Toplevel.proof_of) st of
    SOME 0 => true
  | _ => false);

fun outcome keywords st_goal ({state = st', names, holes, ...}: run) =
  if forall (Keyword.is_diag keywords) names then ("output", "")
  else if not (Toplevel.is_proof st_goal) then ("ok", "")
  else if not (Toplevel.is_proof st') orelse Toplevel.level st' < Toplevel.level st_goal
  then (if null holes then "proved" else "proved_with_sorry", "")
  else if no_subgoals st' then ("no_subgoals", pretty_state st')
  else ("goals_left", pretty_state st');

(*the outcomes after which there is a state to go on from*)
fun has_state kind =
  member (op =) ["proved", "proved_with_sorry", "goals_left", "no_subgoals", "ok"] kind;

fun ms t = string_of_int (Time.toMilliseconds t);

(*the steps of a text of several that took longest, slowest first*)
val slow_step = Time.fromMilliseconds 100;
fun slow_steps (steps: (Properties.T * Time.time) list) =
  if length steps < 2 then []
  else
    steps
    |> filter (fn (_, t) => Time.>= (t, slow_step))
    |> sort (fn ((_, a), (_, b)) => Time.compare (b, a))
    |> take 3
    |> map (fn (props, t) => props @ [("time_ms", ms t)]);

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
          Timeout.apply timeout (fn () =>
            let val run = run_text st0 text
            in (outcome keywords st_goal run, run) end) ())) ();
    val elapsed = #elapsed (Timing.result start);
    val ((kind, text'), holes, slow, reached) =
      (case res of
        Exn.Res (r, run: run) => (r, #holes run, slow_steps (#steps run), SOME (#state run))
      | Exn.Exn (CANDIDATE msg) => (("error", msg), [], [], NONE)
      | Exn.Exn (Timeout.TIMEOUT _) => (("timeout", ""), [], [], NONE)
      | Exn.Exn exn =>
          if Exn.is_interrupt exn then Exn.reraise exn
          else (("error", content (Runtime.exn_message exn)), [], [], NONE));
    val (stats, cycle, steps, more) =
      (case trace of SOME (_, result) => result () | NONE => ([], [], [], 0));
  in
    (([("text", text), ("outcome", kind), ("time_ms", ms elapsed), ("state", text'),
       ("output", get_output ()), ("traced", if traced then "true" else ""),
       ("more_steps", string_of_int more)], (stats, (cycle, (steps, (holes, slow))))),
     if has_state kind then reached else NONE)
  end;

(*a candidate that timed out untraced runs once more with the trace on, for its statistics*)
fun try_candidate st_goal timeout stats watch text =
  let
    val traced = stats orelse is_some watch;
    val res as ((props, _), reached) = run_candidate st_goal timeout traced watch text;
  in
    if not traced andalso Properties.get props "outcome" = SOME "timeout" andalso
      Toplevel.is_proof st_goal
    then
      let
        val timeout' = if Time.< (timeout, seconds 5.0) then timeout else seconds 5.0;
        val ((_, rest), _) = run_candidate st_goal timeout' true NONE text;
      in ((Properties.put ("traced", "rerun") props, rest), reached) end
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


(** handles: the states that candidates reached, to go on from **)

(*a state, and the root of its chain -- the state the agent's first call started from, at a
  line of the theory -- at which a goal left in the state is stated again*)
type stored = {state: Toplevel.state, root: Toplevel.state};

val max_handles = 256;

(*by number, the oldest dropped first*)
val handles = Synchronized.var "vscode_agent_handles" (Inttab.empty: stored Inttab.table, 0);

fun store_handle (h: stored) =
  Synchronized.change_result handles (fn (tab, n) =>
    let val n' = n + 1
    in ("h" ^ string_of_int n',
      (tab |> Inttab.update (n', h) |> Inttab.delete_safe (n' - max_handles), n'))
    end);

fun lookup_handle id =
  (case (if String.isPrefix "h" id then Int.fromString (unprefix "h" id) else NONE) of
    SOME n => Inttab.lookup (#1 (Synchronized.value handles)) n
  | NONE => NONE);


(* goals stated again at the root *)

fun print_term ctxt t = Pretty.pure_string_of (Syntax.pretty_term ctxt t);

(*the text that reads back as the term, with types shown if it takes them; or as a more
  general term, where reading gives a type nothing in the text fixes -- the second [] of
  "length ([] @ ys) = length ys + length []" -- a type variable of its own. That is as
  good for a statement, but not for a literal fact, which must match a fact*)
fun reparsable {general} ctxt t =
  let
    val thy = Proof_Context.theory_of ctxt;
    val tfrees = Term.add_tfrees t [];
    fun generalize t' =
      t' |> Term.map_types (Term.map_type_tfree (fn v as (a, S) =>
        if member (op =) tfrees v then raise Same.SAME else TVar ((a, 0), S)));
    fun reads s =
      (case try (Syntax.read_prop ctxt) s of
        SOME t' => t' aconv t orelse general andalso Pattern.matches thy (generalize t', t)
      | NONE => false);
    val plain = print_term ctxt t;
    val typed = print_term (Config.put show_types true ctxt) t;
  in
    if reads plain then SOME plain
    else if reads typed then SOME typed
    else NONE
  end;

(*the facts and assumptions of a context that the root did not have: what the chain added, by
  obtain, assume, case, have*)
fun new_premises ctxt0 ctxt =
  let
    val assms0 = map Thm.term_of (Assumption.all_assms_of ctxt0);
    val assms = map Thm.term_of (Assumption.all_assms_of ctxt);
    val facts0 = Proof_Context.facts_of ctxt0;
    val facts = Proof_Context.facts_of ctxt;
    val named = Facts.dest_static false [facts0] facts |> maps (map Thm.prop_of o #2);
    fun this_of c = map Thm.prop_of (the_default [] (try (Proof_Context.get_fact c) (Facts.named "this")));
    val this0 = this_of ctxt0;
    val this = filter_out (member (op aconv) this0) (this_of ctxt);
  in
    distinct (op aconv) (filter_out (member (op aconv) assms0) assms @ named @ this)
    |> filter_out (fn t => t aconv Logic.true_prop)
  end;

val max_statements = 8;

(*each subgoal of the state as a statement at the root: the variables fixed since the root
  bound by \<And>, the facts added since then as premises -- and how to use those facts when
  a proof of the statement is tried in the state*)
fun closed_statements root st =
  (case try (#goal o Proof.goal o Toplevel.proof_of) st of
    NONE => ([], "")
  | SOME goal =>
      let
        val ctxt0 = Toplevel.context_of root;
        val ctxt = Toplevel.context_of st;
        (*a fact with schematic variables -- the hypothesis of an induction on a goal under
          \<And> -- is a premise for all their values; the case has it as an assumption too,
          which comes first*)
        fun close_vars t =
          fold (fn (xi as (x, _), T) => fn p => Logic.all_const T $ Term.lambda_name (x, Var (xi, T)) p)
            (Term.add_vars t []) t;
        val pairs =
          map (fn t => (t, close_vars t)) (new_premises ctxt0 ctxt)
          |> distinct (fn ((_, a), (_, b)) => a aconv b);
        val prems = map #1 pairs;
        fun close t =
          let
            val prop = Logic.list_implies (map #2 pairs, t);
            val frees = rev (filter_out (Variable.is_fixed ctxt0 o #1) (Term.add_frees prop []));
            val prop' =
              fold_rev (fn (x, T) => fn p =>
                Logic.all_const T $ Term.lambda_name (Variable.revert_fixed ctxt x, Free (x, T)) p)
              frees prop;
          in
            (case reparsable {general = true} ctxt0 prop' of
              SOME s => [("statement", s)]
            | NONE => [("error", "it does not print so that it reads back the same")])
          end;
        (*each fact as a literal; one with schematic variables, which no literal is, by its name*)
        val named = Facts.dest_static false [Proof_Context.facts_of ctxt0] (Proof_Context.facts_of ctxt);
        fun by_name t =
          get_first (fn (a, ths) =>
            (case find_index (fn th => Thm.prop_of th aconv t) ths of
              ~1 => NONE
            | i =>
                SOME (#2 (Proof_Context.markup_extern_fact ctxt a) ^
                  (if length ths = 1 then "" else "(" ^ string_of_int (i + 1) ^ ")")))) named;
        fun literal t =
          Option.map (fn s => "\092<open>" ^ s ^ "\092<close>") (reparsable {general = false} ctxt t);
        fun fact_ref t =
          if Term.exists_subterm is_Var t then (case by_name t of NONE => literal t | some => some)
          else (case literal t of NONE => by_name t | some => some);
        val refs = map fact_ref prems;
        val using =
          if null prems orelse exists is_none refs then ""
          else "using " ^ space_implode " " (map the refs);
      in (map close (take max_statements (Thm.prems_of goal)), using) end);


(** arguments and result **)

(*plain strings, as overlays pass them on: the handle to start from (or ""), goal, timeout in
  ms, "true" for statistics, watch limit, then three counted lists -- candidates, watched
  rules, watched patterns*)
fun decode_args (from :: goal :: timeout_ms :: stats :: watch_limit :: rest) =
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
        {from = from, goal = goal,
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
          (pair (list string) (pair (list properties)
            (pair (list properties) (pair (list properties) (list properties))))))))
        (header, candidates))
  end;

(*how a proof goes on from a state: by "apply" in prove mode, by "show" in an Isar proof body;
  at the theory level, after a closed proof, only by stating more*)
fun mode st =
  if not (Toplevel.is_proof st) then "theory"
  else if can (Proof.assert_backward o Toplevel.proof_of) st then "prove" else "state";

(*a hole of an outline as a handle: the state at its sorry, where a proof for it is tried in
  place of the sorry, with its goals stated again at the root (numbered: statement_1, ...)*)
fun hole_handle root (props, st) =
  let
    val id = store_handle {state = st, root = root};
    val (statements, using) = the_default ([], "") (try (closed_statements root) st);
    val numbered =
      flat (map_index (fn (i, p) => map (fn (k, s) => (k ^ "_" ^ string_of_int (i + 1), s)) p)
        statements);
  in props @ [("handle", id), ("using", using), ("mode", mode st)] @ numbered end;

(*a candidate's result with the handle of the state it reached, and for goals left there each
  stated again at the root*)
fun with_handle root ((props, (stats, (cycle, (steps, (holes0, slow))))), reached) =
  let val holes = map (hole_handle root) holes0 in
  (case reached of
    NONE => (props, (stats, (cycle, (steps, (holes, (slow, []))))))
  | SOME st =>
      let
        val id = store_handle {state = st, root = root};
        val (statements, using) =
          if Properties.get props "outcome" = SOME "goals_left"
          then the_default ([], "") (try (closed_statements root) st)
          else ([], "");
      in
        (props @ [("handle", id), ("using", using), ("mode", mode st)],
          (stats, (cycle, (steps, (holes, (slow, statements))))))
      end)
  end;

fun try_all state {from, goal, timeout, stats, watch, candidates} =
  let
    val start =
      if from = "" then Exn.Res {state = state, root = state}
      else
        (case lookup_handle from of
          SOME h => Exn.Res h
        | NONE =>
            Exn.Exn (CANDIDATE ("There is no handle " ^ from ^
              " (any more): handles last until 256 newer ones are made, or the prover " ^
              "restarts. Start again from a line.")));
  in
    (case start of
      Exn.Exn (CANDIDATE msg) => ([("error", msg)], [])
    | Exn.Exn exn => Exn.reraise exn
    | Exn.Res {state = st0, root} =>
        (case Exn.capture_body (fn () => open_goal st0 goal) of
          Exn.Res st_goal =>
            let
              val _ = ensure_capture ();
              val results =
                parallel 4 (map (fn text => fn () => try_candidate st_goal timeout stats watch text)
                  candidates);
              val goal_handle = if goal = "" then "" else store_handle {state = st_goal, root = root};
              val header =
                [("state", if Toplevel.is_proof st_goal then pretty_state st_goal else ""),
                 ("proof", if Toplevel.is_proof st0 then "true" else ""),
                 ("goal_handle", goal_handle), ("goal_keyword", goal_keyword st0),
                 ("from_mode", if from = "" then "" else mode st0)];
            in (header, map (with_handle root) results) end
        | Exn.Exn (CANDIDATE msg) => ([("error", "The goal could not be stated: " ^ msg)], [])
        | Exn.Exn exn =>
            if Exn.is_interrupt exn then Exn.reraise exn
            else ([("error", content (Runtime.exn_message exn))], [])))
  end;


(** context: what the agent needs to know about a goal **)

val max_section = 8000;
val max_consts = 12;
val max_rules = 8;

fun bounded s =
  if size s > max_section then String.substring (s, 0, max_section) ^ "\n..." else s;

fun print_typ ctxt T = Pretty.pure_string_of (Syntax.pretty_typ ctxt T);

(*the fact a specification's rules go by, if there is one by that name: its name for a
  definition, NAME.simps for a fun or primrec, NAME.intros for an inductive predicate. A fun's
  rules come without a name (the function package registers none): then by the constant's*)
fun spec_fact_name ctxt c ({name, rough_classification, ...}: Spec_Rules.spec_rule) =
  let
    val name = if name = "" then c else name;
    val short =
      (case Long_Name.explode name of
        _ :: (rest as _ :: _) => Long_Name.implode rest
      | _ => name);
    val candidates =
      if name = "" then []
      else if String.isSuffix "_def" name then [short]
      else if Spec_Rules.is_equational rough_classification then [short ^ ".simps"]
      else if Spec_Rules.is_inductive rough_classification orelse
        Spec_Rules.is_co_inductive rough_classification then [short ^ ".intros"]
      else [];
    fun resolves n = is_some (try (Proof_Context.get_fact ctxt) (Facts.named n));
  in find_first resolves candidates end;

(*the constants of the terms that have a specification -- this theory's first, then in the
  order they occur -- each with its rules, taken at the type it has there*)
fun definitions ctxt ts =
  let
    val thy_name = Context.theory_base_name (Proof_Context.theory_of ctxt);
    val consts =
      fold Term.add_consts ts [] |> rev |> distinct (fn ((a, _), (b, _)) => a = b);
    val (own, other) = List.partition (fn (c, _) => Long_Name.qualifier c = thy_name) consts;
    (*an overloaded constant has a specification per instance: those of this type; a type
      class operation's are the instances' definitions, which do not help with a goal*)
    fun of_type T (spec: Spec_Rules.spec_rule) =
      not (null (#rules spec)) andalso
      exists (fn Const (_, T') => Type.could_unify (T', T) | _ => false) (#terms spec);
    fun entry (c, T) =
      if String.isSubstring "_class." c then NONE
      else
      (case filter (of_type T) (Spec_Rules.retrieve ctxt (Const (c, T))) of
        [] => NONE
      | specs => SOME (c, T, specs));
    fun spec_text c (spec: Spec_Rules.spec_rule) =
      let
        val rules = #rules spec;
        val shown = map (print_term ctxt o Thm.prop_of) (take max_rules rules);
        val more = length rules - max_rules;
      in
        (case spec_fact_name ctxt c spec of
          SOME n => "  by " ^ n ^ ":\n"
        | NONE => "") ^
        cat_lines (map (prefix "    ") (maps split_lines shown)) ^
        (if more > 0 then "\n    ... and " ^ string_of_int more ^ " more" else "")
      end;
    fun text (c, T, specs) =
      Long_Name.base_name c ^ " :: " ^ print_typ ctxt T ^ "\n" ^ cat_lines (map (spec_text c) specs);
  in
    map_filter entry (own @ other) |> take max_consts |> map text |> space_implode "\n\n"
  end;

(*the variables of the terms with their types, and the facts of the proof*)
fun local_facts ctxt ts =
  let
    val frees = fold Term.add_frees ts [] |> rev |> distinct (op =);
    fun name x = if Variable.is_fixed ctxt x then Variable.revert_fixed ctxt x else x;
    val vars =
      if null frees then ""
      else "variables: " ^ commas (map (fn (x, T) => name x ^ " :: " ^ print_typ ctxt T) frees);
    (*the named ones that hold something: not the unnamed facts (this, again), nor an empty
      prems of a case*)
    val named =
      Facts.dest_static false [Global_Theory.facts_of (Proof_Context.theory_of ctxt)]
        (Proof_Context.facts_of ctxt)
      |> filter_out (null o #2);
    val facts =
      if null named then ""
      else
        Pretty.pure_string_of
          (Pretty.big_list "local facts:" (map (Proof_Context.pretty_fact ctxt) named));
  in space_implode "\n" (filter (fn s => s <> "") [vars, facts]) end;

(*plain strings: the handle to start from (or ""), and a goal of the agent's own*)
fun context_of state [from, goal] =
      let
        val (st0, root) =
          if from = "" then (state, state)
          else
            (case lookup_handle from of
              SOME {state, root} => (state, root)
            | NONE =>
                error ("There is no handle " ^ from ^
                  " (any more): handles last until 256 newer ones are made, or the prover " ^
                  "restarts. Start again from a line."));
        val st =
          open_goal st0 goal
            handle CANDIDATE msg => error ("The goal could not be stated: " ^ msg);
        val ctxt = Toplevel.context_of st;
        val subgoals =
          (case try (#goal o Proof.goal o Toplevel.proof_of) st of
            SOME goal => Thm.prems_of goal
          | NONE => []);
        val statement =
          if from = "" then ""
          else
            (case closed_statements root st of
              ([("statement", s)] :: _, _) => s
            | _ => "");
      in
        [("goal", if Toplevel.is_proof st then pretty_state st else ""),
         ("definitions", bounded (definitions ctxt subgoals)),
         ("facts", bounded (local_facts ctxt subgoals)),
         ("statement", statement)]
      end
  | context_of _ _ = error "Bad arguments";

(*the facts that Sledgehammer's relevance filter MePo ranks highest for the first subgoal, as
  pairs of name and statement; arguments: a goal of the agent's own (or ""), and how many*)
val relevant_operation = "\
\Command.no_print_function \"vscode_agent_relevant_query\";\n\
\Query_Operation.register {name = \"vscode_agent_relevant\", pri = Task_Queue.urgent_pri}\n\
\  (fn {state = st, args, output_result, ...} =>\n\
\    let\n\
\      val (goal, limit) =\n\
\        (case args of\n\
\          [g, l] => (g, the_default 20 (Int.fromString l))\n\
\        | _ => error \"Bad arguments\");\n\
\      val st' =\n\
\        if goal = \"\" then st\n\
\        else\n\
\          let\n\
\            val thy = Toplevel.theory_of st;\n\
\            val text =\n\
\              (if not (Toplevel.is_proof st) then \"lemma \"\n\
\               else if can (Proof.assert_backward o Toplevel.proof_of) st then \"proof - have \"\n\
\               else \"have \") ^ goal;\n\
\          in\n\
\            fold (Toplevel.command_exception false)\n\
\              (Outer_Syntax.parse_text thy (K thy) Position.none text) st\n\
\          end;\n\
\      val prf =\n\
\        (case try Toplevel.proof_of st' of\n\
\          SOME prf => prf\n\
\        | NONE => error \"There is no goal here\");\n\
\      val {context = ctxt, facts = chained, goal = goal_thm} = Proof.goal prf;\n\
\      val _ = if Thm.nprems_of goal_thm = 0 then error \"There is no goal left here\" else ();\n\
\      val (_, hyps, concl) = ATP_Util.strip_subgoal goal_thm 1 ctxt;\n\
\      val facts =\n\
\        Sledgehammer_Fact.nearly_all_facts_of_context ctxt false\n\
\          Sledgehammer_Fact.no_fact_override chained hyps concl;\n\
\      val params = Sledgehammer_Commands.default_params (Proof_Context.theory_of ctxt) [];\n\
\      val found = Sledgehammer_MePo.mepo_suggested_facts ctxt params limit NONE hyps concl facts;\n\
\      fun statement th = Pretty.pure_string_of (Syntax.pretty_term ctxt (Thm.prop_of th));\n\
\    in\n\
\      output_result [YXML.string_of_body\n\
\        (XML.Encode.list (XML.Encode.pair XML.Encode.string XML.Encode.string)\n\
\          (map (fn ((name, _), th) => (name, statement th)) found))]\n\
\    end);\n";

in

val _ =
  Query_Operation.register {name = "vscode_agent_try", pri = Task_Queue.urgent_pri}
    (fn {state, args, output_result, ...} =>
      output_result [encode_result (try_all state (decode_args args))]);

val _ =
  Query_Operation.register {name = "vscode_agent_context", pri = Task_Queue.urgent_pri}
    (fn {state, args, output_result, ...} =>
      output_result [YXML.string_of_body (XML.Encode.properties (context_of state args))]);

(*replaced below in a logic that contains Sledgehammer*)
val _ =
  Query_Operation.register {name = "vscode_agent_relevant", pri = Task_Queue.urgent_pri}
    (fn _ => error "Relevant facts need a session that contains Sledgehammer, like HOL");

val _ =
  (case Thy_Info.lookup_theory "HOL.Sledgehammer" of
    SOME thy =>
      ML_Context.eval_source_in (SOME (Proof_Context.init_global thy)) ML_Compiler.flags
        (Input.string relevant_operation)
  | NONE => ());

end;
