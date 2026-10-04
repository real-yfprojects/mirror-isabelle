(*  Title:      Tools/VSCode/src/vscode_hover.ML

What a name stands for in the context of a command, for the hover of Isabelle/VSCode: the
statement of a fact, the type of a fixed variable or a constant, the term that a term
abbreviation (?thesis, ?case, let ?x) is bound to, and what a case provides. The PIDE markup
of the text only names these things.

Loaded as a prelude of the prover process, like vscode_completion.ML: plain ML over Pure,
without antiquotations, and declaring nothing at the toplevel.
*)

local

val max_thms = 8;

fun pretty_typing ctxt t T =
  Pretty.block [Syntax.pretty_term ctxt t, Pretty.str " ::", Pretty.brk 1,
    Syntax.pretty_typ ctxt T];

fun pretty_bind ctxt xi =
  (case Vartab.lookup (Variable.binds_of ctxt) xi of
    SOME (T, t) =>
      SOME (Pretty.block [Syntax.pretty_term ctxt (Var (xi, T)), Pretty.str " \092<equiv>",
        Pretty.brk 1, Syntax.pretty_term ctxt t])
  | NONE => NONE);

fun take_thms thms =
  let val n = length thms in
    if n <= max_thms then (thms, [])
    else (take max_thms thms,
      [Pretty.str ("\092<dots> " ^ string_of_int (n - max_thms) ^ " more")])
  end;


(* fact selection: "2", "1-3", "2-", "1,3" *)

fun read_interval s =
  let val int = the o Int.fromString in
    (case space_explode "-" s of
      [i] => Facts.Single (int i)
    | [i, ""] => Facts.From (int i)
    | [i, j] => Facts.FromTo (int i, int j)
    | _ => raise Option.Option)
  end;

fun select_thms "" thms = SOME thms
  | select_thms sel thms =
      try (fn () =>
        Facts.select (Facts.Named (("", Position.none),
          SOME (map read_interval (space_explode "," sel)))) thms) ();


(* infos by kind of entity *)

fun fact_info ctxt name sel =
  (case Proof_Context.lookup_fact ctxt name of
    SOME {thms, ...} =>
      (case select_thms sel thms of
        SOME (selected as _ :: _) =>
          let
            val (shown, rest) = take_thms selected;
            val a = if sel = "" then name else "";
          in SOME (Pretty.chunks (Proof_Context.pretty_fact ctxt (a, shown) :: rest)) end
      | _ => NONE)
  | NONE => NONE);

fun fixed_info ctxt x =
  (case Variable.default_type ctxt x of
    SOME T => SOME (pretty_typing ctxt (Free (x, T)) T)
  | NONE => NONE);

(*a declared type is schematic, 'a as ?'a: printed as it is written*)
fun unvarifyT T = the_default T (try Logic.unvarifyT_global T);
fun unvarify t = the_default t (try Logic.unvarify_global t);

fun strip_abs t =
  (case t of
    Abs _ =>
      let
        val (x, t') = Term.dest_abs_global t;
        val (xs, body) = strip_abs t';
      in (x :: xs, body) end
  | _ => ([], t));

(*the declared type of a constant, and for an abbreviation what it stands for, as an
  equation over its arguments: printed in abbreviation mode, which would otherwise fold
  the right-hand side back into the abbreviation (x \<noteq> y \<equiv> x \<noteq> y), and
  without the fixed variables of the context, which an argument may be named like*)
fun constant_info ctxt c =
  let
    val consts = Proof_Context.consts_of ctxt;
    val ctxt_abbrev =
      Proof_Context.init_global (Proof_Context.theory_of ctxt)
      |> Proof_Context.set_mode Proof_Context.mode_abbrev;
    val typing =
      (case try (Consts.type_scheme consts) c of
        SOME T => let val T' = unvarifyT T in [pretty_typing ctxt (Const (c, T')) T'] end
      | NONE => []);
    val abbrev =
      (case try (Consts.the_abbreviation consts) c of
        SOME (T, rhs) =>
          let
            val (xs, body) = strip_abs (unvarify rhs);
            val lhs = Term.list_comb (Const (c, unvarifyT T), map Free xs);
          in
            [Pretty.block [Syntax.pretty_term ctxt_abbrev lhs, Pretty.str " \092<equiv>",
              Pretty.brk 1, Syntax.pretty_term ctxt_abbrev body]]
          end
      | NONE => []);
  in if null typing then NONE else SOME (Pretty.chunks (typing @ abbrev)) end;

(*after the command that opens it: the goal of a case, and its assumptions, which are the
  local fact named like the case*)
fun case_info ctxt name =
  let
    val goal = the_list (pretty_bind ctxt (Rule_Cases.case_conclN, 0));
    val facts = Proof_Context.facts_of ctxt;
    val assms =
      (case Proof_Context.lookup_fact ctxt (Facts.intern facts name) of
        SOME {thms = thms as _ :: _, ...} =>
          let val (shown, rest) = take_thms thms
          in Pretty.block0 (Pretty.fbreaks (map (Thm.pretty_thm_item ctxt) shown)) :: rest end
      | _ => []);
    val prts =
      goal @ (if null assms then [] else Pretty.str "assumes:" :: assms);
  in if null prts then NONE else SOME (Pretty.chunks prts) end;

fun var_info ctxt s =
  (case try Lexicon.read_indexname (unprefix "?" s) of
    SOME xi => pretty_bind ctxt xi
  | NONE => NONE);

fun info ctxt kind name sel =
  if kind = Markup.factN then fact_info ctxt name sel
  else if kind = Markup.fixedN then fixed_info ctxt name
  else if kind = Markup.constantN then constant_info ctxt name
  else if kind = Markup.caseN then case_info ctxt name
  else if kind = Markup.varN then var_info ctxt name
  else NONE;

in


(* query operation: one info, as one result, or none *)

val _ =
  Query_Operation.register {name = "vscode_hover_info", pri = Task_Queue.urgent_pri}
    (fn {state, args, output_result, ...} =>
      (case (args, try Toplevel.context_of state) of
        ([kind, name, sel], SOME ctxt) =>
          (case info ctxt kind name sel of
            SOME prt => output_result [Pretty.string_of prt]
          | NONE => ())
      | _ => ()));

end;
