(*  Title:      Tools/VSCode/src/vscode_skeletons.ML

Code skeletons for the state after a command, offered by the editor as code actions: an Isar
sketch of a pending goal, subgoal blocks for a proof script, and the definitions and
instance proof an instantiation still lacks. The printing follows
HOL/ex/Sketch_and_Explore.thy, without its dependencies on HOL.

Loaded as a prelude of the prover process (Isabelle_Process.start, use_prelude), so that it
needs no heap of its own: plain ML over Pure, without antiquotations, and declaring nothing
at the toplevel (which would be printed on the process output).
*)

local

(* printing *)

fun simplify_spaces s = space_implode " " (String.tokens Char.isSpace s);

fun maybe_quote s =
  if Symbol.is_ascii_identifier s orelse
    (String.isPrefix "'" s andalso Symbol.is_ascii_identifier (unprefix "'" s))
  then s
  else if exists_string (fn c => c = "\"") s then cartouche s
  else quote s;

fun print_ctxt ctxt =
  fold (fn opt => Config.put opt false)
    [show_markup, Printer.show_type_emphasis, show_types, show_sorts, show_consts] ctxt;

fun print_typ ctxt T =
  Syntax.pretty_typ (print_ctxt ctxt) T |> Pretty.pure_string_of |> simplify_spaces |> maybe_quote;

fun print_term ctxt t =
  let val ctxt' = print_ctxt ctxt in
    singleton (Syntax.uncheck_terms ctxt') t
    |> Syntax.unparse_term ctxt'
    |> Pretty.pure_string_of
    |> simplify_spaces
    |> maybe_quote
  end;


(* clauses of a goal *)

fun split_clause t =
  let
    val (fixes, horn) = funpow_yield (length (Term.strip_all_vars t)) Logic.dest_all_global t;
  in (fixes, Logic.strip_imp_prems horn, Logic.strip_imp_concl horn) end;

fun goal_clauses goal = map split_clause (Logic.strip_imp_prems (Thm.prop_of goal));

fun eigen_context fixes ctxt =
  let val bindings = map (fn (s, T) => (Binding.name s, SOME T, NoSyn)) fixes in
    ctxt |> Variable.set_body false |> Proof_Context.add_fixes bindings |> snd
    handle ERROR _ =>
      ctxt |> Variable.set_body true |> Proof_Context.add_fixes bindings |> snd
  end;

fun print_clause ctxt indent (fixes, assms, concl) =
  let
    val ctxt' = eigen_context fixes ctxt;
    val prefix = Symbol.spaces indent;
    val sep = "\n" ^ prefix ^ "  and ";
    val fixes_s =
      if null fixes then []
      else
        [prefix ^ "fix " ^
          space_implode sep (map (fn (v, T) => v ^ " :: " ^ print_typ ctxt T) fixes)];
    val assumes_s =
      if null assms then []
      else [prefix ^ "assume " ^ space_implode sep (map (print_term ctxt') assms)];
  in fixes_s @ assumes_s @ [prefix ^ "show " ^ print_term ctxt' concl, prefix ^ "  sorry"] end;

fun print_sketch ctxt head clauses =
  head :: flat (separate ["next"] (map (print_clause ctxt 2) clauses)) @ ["qed"];

fun print_subgoal ctxt (fixes, _, _) =
  let
    val ctxt' = eigen_context fixes ctxt;
    val for_s =
      if null fixes then ""
      else " for " ^ implode_space (map (Thy_Header.print_name' ctxt' o fst) fixes);
  in ["subgoal" ^ for_s, "  sorry"] end;


(* skeletons: title, kind, text *)

(*determined by the text already written, so the editor may offer it as ghost text*)
val skeletonN = "skeleton";
(*one choice among others: offered only on request*)
val suggestionN = "suggestion";

(*a single pending goal: what the default rule leaves of it, as Isar*)
fun sketch state =
  (case try (Seq.the_result "" o Proof.proof NONE) state of
    NONE => []
  | SOME state' =>
      let val {context = ctxt, goal, ...} = Proof.goal state' in
        (case goal_clauses goal of
          [] => []
        | clauses =>
            [("Insert Isar sketch", suggestionN, cat_lines (print_sketch ctxt "proof" clauses))])
      end);

(*several subgoals of a proof script: a subgoal block for each*)
fun subgoals ctxt clauses =
  [("Insert subgoal skeleton (" ^ string_of_int (length clauses) ^ " subgoals)", suggestionN,
    cat_lines (maps (print_subgoal ctxt) clauses @ ["done"]))];

fun proof_skeletons state =
  if can Proof.assert_backward state then
    let val {context = ctxt, goal, ...} = Proof.goal state in
      (case goal_clauses goal of
        [] => []
      | [_] => sketch state
      | clauses => subgoals ctxt clauses)
    end
  else [];

(*an instantiation target: the parameters it has yet to define, then its instance proof*)
fun instantiation_skeletons lthy =
  (case try (Class.instantiation_instance I) lthy of
    NONE => []
  | SOME state =>
      let
        val thy = Proof_Context.theory_of lthy;
        val {context = ctxt, goal, ...} = Proof.goal state;
        val arities = map Logic.dest_of_class (Logic.strip_imp_prems (Thm.prop_of goal));
        val types = distinct (op =) (map fst arities);
        val sort = distinct (op =) (map snd arities);
        val class_params = Class.these_params thy (filter (can (Axclass.get_info thy)) sort);

        (*as Class.instantiation names them*)
        fun definition (T as Type (tyco, _)) (param, (_, (c, ty))) =
              if can (Axclass.param_of_inst thy) (c, tyco) then NONE
              else
                let val v = param ^ "_" ^ Long_Name.base_name tyco in
                  SOME ("definition " ^ v ^ " :: " ^ print_typ ctxt (map_atyps (K T) ty) ^
                    " where\n  " ^ quote (v ^ " = undefined") ^ "\n")
                end
          | definition _ _ = NONE;
        val definitions = map_filter I (map_product definition types class_params);

        (*as Class.conclude checks it*)
        val proven = forall (fn T => Sign.of_sort thy (T, sort)) types;
        val instance =
          if proven then []
          else
            (case Seq.pull (Class.standard_intro_classes_tac ctxt [] goal) of
              NONE => ["instance sorry"]
            | SOME (goal', _) =>
                (case goal_clauses goal' of
                  [] => ["instance .."]
                | clauses => print_sketch ctxt "instance proof" clauses));
      in
        if null definitions andalso null instance then []
        else [("Insert instantiation skeleton", skeletonN, cat_lines (definitions @ instance))]
      end);

fun skeletons st =
  (case try Toplevel.proof_of st of
    SOME state => proof_skeletons state
  | NONE =>
      (case try Toplevel.context_of st of
        SOME lthy => instantiation_skeletons lthy
      | NONE => []));

val timeout = Time.fromSeconds 2;

fun encode skeletons =
  let open XML.Encode
  in list (pair string (pair string string)) (map (fn (a, b, c) => (a, (b, c))) skeletons) end;

in

(* query operation: the skeletons for the state after a command, as one result *)

val _ =
  Query_Operation.register {name = "vscode_skeletons", pri = Task_Queue.urgent_pri}
    (fn {state, output_result, ...} =>
      let
        (*a failure only means no skeletons: it must not end up as an error of the command*)
        val result =
          (case Exn.result (Timeout.apply timeout skeletons) state of
            Exn.Res res => res
          | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else []);
      in output_result [YXML.string_of_body (encode result)] end);

end;
