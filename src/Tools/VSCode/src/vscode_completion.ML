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

(*the parameters of class instances (e.g. plus_nat_inst.plus_nat): the overloaded constant
  of the class is defined as one of them for each instance, and code generation works with
  them, but a term that names one matches no rule about the class's constant*)
fun inst_params ctxt =
  let val thy = Proof_Context.theory_of ctxt
  in filter (is_some o Axclass.inst_of_param thy) (Name_Space.get_names (Proof_Context.const_space ctxt)) end;

(*the names of the context, without the parameters of class instances*)
fun context_names ctxt params =
  let val excluded = Symtab.make_set params in
    fixed_names ctxt @
    space_names ctxt Markup.constantN (Proof_Context.const_space ctxt)
      (not o Symtab.defined excluded) @
    space_names ctxt Markup.type_nameN (Proof_Context.type_space ctxt) (K true)
  end;

(*the names, and the parameters of class instances: to filter them from the prover's own
  completion reports as well*)
fun encode (names, params) =
  let open XML.Encode
  in pair (list (pair string (pair string string))) (list string) (names, params) end;

in

(* query operation: all names visible after a command, as one result *)

val _ =
  Query_Operation.register {name = "vscode_context_names", pri = Task_Queue.urgent_pri}
    (fn {state, output_result, ...} =>
      let
        val result =
          (case try Toplevel.context_of state of
            SOME ctxt =>
              let val params = inst_params ctxt
              in (context_names ctxt params, params) end
          | NONE => ([], []));
      in output_result [YXML.string_of_body (encode result)] end);

end;
