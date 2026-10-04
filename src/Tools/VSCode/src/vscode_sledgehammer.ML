(*  Title:      Tools/VSCode/src/vscode_sledgehammer.ML

The query operation of the Sledgehammer panel, below the checking of the document.

Sledgehammer forks 24 prover slices per worker thread at once (Par_List.map), and a forked
task gets the priority of the task that forks it. HOL's operation runs in the print's task,
which Command.run_process enrolls with priority 0 whatever the print function asks for: the
priority of the theory execution, and above the proofs that it forks (Toplevel.future_proof,
Proof.future_terminal_proof: priority ~1). So a proof edited meanwhile was checked only
after every slice forked before it, up to the end of the run. Here Sledgehammer runs in a
task of its own at priority ~2, below every task of the document's checking, and a freed
worker checks the document first.

Loaded as a prelude of the prover process (Isabelle_Process.start, use_prelude), so that it
needs no heap of its own: plain ML over Pure, without antiquotations, and declaring nothing
at the toplevel (which would be printed on the process output). The operation itself refers
to Sledgehammer, so it is compiled only in a logic that contains it, and otherwise HOL's
operation stays as it is.
*)

local

(*as in HOL/Tools/Sledgehammer/sledgehammer_commands.ML, but for the task*)
val operation = "\
\Command.no_print_function \"sledgehammer_query\";\n\
\Query_Operation.register {name = \"sledgehammer\", pri = 0}\n\
\  (fn {state = st, args, writeln_result, ...} =>\n\
\    (case try Toplevel.proof_of st of\n\
\      SOME state0 =>\n\
\        let\n\
\          val [provers_arg, isar_proofs_arg, try0_arg] = args;\n\
\          val state =\n\
\            Proof.map_contexts\n\
\              (Try0_HOL.silence_methods #> Config.put SMT_Config.verbose false) state0;\n\
\          val params =\n\
\            Sledgehammer_Commands.default_params (Proof.theory_of state)\n\
\              ((if provers_arg = \"\" then [] else [(\"provers\", provers_arg)]) @\n\
\                [(\"isar_proofs\", if isar_proofs_arg = \"true\" then \"true\" else \"smart\"),\n\
\                 (\"try0\", try0_arg),\n\
\                 (\"debug\", \"false\"),\n\
\                 (\"verbose\", \"false\"),\n\
\                 (\"overlord\", \"false\")]);\n\
\          fun run () =\n\
\            ignore (Sledgehammer.run_sledgehammer params Sledgehammer_Prover.Normal\n\
\              (SOME writeln_result) 1 Sledgehammer_Fact.no_fact_override state);\n\
\        in\n\
\          Future.join ((singleton o Future.forks)\n\
\            {name = \"sledgehammer\", group = NONE, deps = [], pri = ~2, interrupts = true}\n\
\            run)\n\
\        end\n\
\    | NONE => error \"Unknown proof context\"));\n";

in

val _ =
  (case Thy_Info.lookup_theory "HOL.Sledgehammer" of
    SOME thy =>
      ML_Context.eval_source_in (SOME (Proof_Context.init_global thy)) ML_Compiler.flags
        (Input.string operation)
  | NONE => ());

end;
