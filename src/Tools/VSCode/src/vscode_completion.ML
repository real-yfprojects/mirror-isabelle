(*  Title:      Tools/VSCode/src/vscode_completion.ML

The names of a formal context, for completion within inner syntax: there the prover
reports names only for a name that it rejects, and a word being typed is merely a free
variable.

Loaded as a prelude of the prover process (Isabelle_Process.start, use_prelude), so that it
needs no heap of its own: plain ML over Pure, without antiquotations, and declaring nothing
at the toplevel (which would be printed on the process output).
*)

local

(* names: external name, kind, internal name *)

(*every form that refers to a name, the shortest first: a qualified one is what a user
  types to pick a name whose base name is ambiguous, e.g. PosReal.ppos*)
fun accesses ctxt space name =
  let
    val xname = Name_Space.extern_shortest ctxt space name;
    val chunks = Long_Name.explode name;
    val n = length chunks;
    val suffixes = map_range (fn i => Long_Name.implode (drop (n - 1 - i) chunks)) n;
  in
    if xname = "" orelse Long_Name.is_hidden xname orelse
      Name.is_internal (Long_Name.base_name xname)
    then []
    else distinct (op =) (xname :: filter (fn a => Name_Space.intern space a = name) suffixes)
  end;

fun space_names ctxt kind space pred =
  Name_Space.get_names space |> maps (fn name =>
    if Name_Space.is_concealed space name orelse not (pred name) then []
    else map (fn xname => (xname, (kind, name))) (accesses ctxt space name));

fun fixed_names ctxt =
  Variable.dest_fixes ctxt |> map_filter (fn (x, _) =>
    if x = "" orelse Name.is_internal x orelse Name.is_skolem x then NONE
    else SOME (x, (Markup.fixedN, x)));

(*not the parameters of class instances (e.g. partial_term_of_real_inst.partial_term_of_real):
  one writes the overloaded constant of the class instead*)
fun context_names ctxt =
  let val thy = Proof_Context.theory_of ctxt in
    fixed_names ctxt @
    space_names ctxt Markup.constantN (Proof_Context.const_space ctxt)
      (is_none o Axclass.inst_of_param thy) @
    space_names ctxt Markup.type_nameN (Proof_Context.type_space ctxt) (K true)
  end;

fun encode names =
  let open XML.Encode
  in pair int (list (pair string (pair string string))) (length names, names) end;

in

(* query operation: all names visible after a command, as one result *)

val _ =
  Query_Operation.register {name = "vscode_context_names", pri = Task_Queue.urgent_pri}
    (fn {state, output_result, ...} =>
      let
        val names =
          (case try Toplevel.context_of state of
            SOME ctxt => context_names ctxt
          | NONE => []);
      in output_result [YXML.string_of_body (encode names)] end);

end;
