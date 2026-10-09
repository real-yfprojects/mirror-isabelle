(*  Title:      Tools/VSCode/src/vscode_sledgehammer.ML

The query operation of the Sledgehammer panel, below the checking of the document, and jobs:
runs that go on while the text changes, several at a time (see job_operation below).

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

(*a job: the print function only takes the proof state, and the run goes on in a group of
  its own. The print belongs to the execution of the command, which an edit of the command
  or of anything before it cancels -- and typing the next step does edit the command, since
  a word that is not yet a keyword joins the span before it. Forked with group = NONE, the
  run would be a subgroup of that execution and go with it; a new root group outlives it.
  So the results cannot be results of the command, which may be gone by then: they go out
  as protocol messages, read by VSCode_Sledgehammer.Jobs.

  Arguments: the job's id, a goal of its own (stated with "have" in a proof, "lemma"
  outside one, as for the agent's candidates), the subgoal, a fact override as inside the
  parentheses of the sledgehammer command ("add: foo del: bar", or bare facts for only),
  then pairs of Sledgehammer parameters*)
val job_operation = "\
\local\n\
\  val jobs = Synchronized.var \"vscode_sledgehammer_jobs\" (Symtab.empty: Future.group Symtab.table);\n\
\\n\
\  fun report id kind body =\n\
\    Output.protocol_message\n\
\      [Markup.function \"vscode_sledgehammer_job\", (\"id\", id), (\"kind\", kind)] [body];\n\
\\n\
\  fun open_goal st \"\" = st\n\
\    | open_goal st goal =\n\
\        let\n\
\          val thy = Toplevel.theory_of st;\n\
\          val text = (if Toplevel.is_proof st then \"have \" else \"lemma \") ^ goal;\n\
\        in\n\
\          fold (Toplevel.command_exception false)\n\
\            (Outer_Syntax.parse_text thy (K thy) Position.none text) st\n\
\        end;\n\
\\n\
\  (*as parse_fact_override in HOL/Tools/Sledgehammer/sledgehammer_commands.ML*)\n\
\  fun override add del only = {add = add, del = del, only = only};\n\
\  val fact_refs = Scan.repeat1 (Scan.unless (Parse.name -- Args.colon) Parse.thm);\n\
\  val chunk =\n\
\    (Args.add |-- Args.colon |-- Scan.optional fact_refs [] >> (fn ns => override ns [] false))\n\
\    || (Args.del |-- Args.colon |-- Scan.optional fact_refs [] >> (fn ns => override [] ns false))\n\
\    || (fact_refs >> (fn ns => override ns [] true));\n\
\  fun merge (r1: Sledgehammer_Fact.fact_override) (r2: Sledgehammer_Fact.fact_override) =\n\
\    override (#add r1 @ #add r2) (#del r1 @ #del r2) (#only r1 andalso #only r2);\n\
\  fun fact_override _ \"\" = Sledgehammer_Fact.no_fact_override\n\
\    | fact_override ctxt text =\n\
\        Parse.read_embedded ctxt (Thy_Header.get_keywords' ctxt)\n\
\          (Scan.repeat chunk >> (fn rs => fold merge rs (override [] [] true)))\n\
\          (Input.string text);\n\
\\n\
\  fun pairs (a :: b :: rest) = (a, b) :: pairs rest\n\
\    | pairs _ = [];\n\
\in\n\
\\n\
\val _ =\n\
\  Protocol_Command.define \"vscode_sledgehammer_job.cancel\"\n\
\    (fn ids => ids |> List.app (fn id =>\n\
\      (case Synchronized.change_result jobs (fn tab =>\n\
\          (Symtab.lookup tab id, Symtab.delete_safe id tab)) of\n\
\        SOME group => Future.cancel_group group\n\
\      | NONE => ())));\n\
\\n\
\val _ =\n\
\  Query_Operation.register {name = \"vscode_sledgehammer_job\", pri = Task_Queue.urgent_pri}\n\
\    (fn {state = st, args, ...} =>\n\
\      (case args of\n\
\        id :: goal :: subgoal :: facts :: param_args =>\n\
\          let\n\
\            val state0 =\n\
\              (case try Toplevel.proof_of (open_goal st goal) of\n\
\                SOME state0 => state0\n\
\              | NONE => error \"No goal here: Sledgehammer needs a proof state\");\n\
\            val state =\n\
\              Proof.map_contexts\n\
\                (Try0_HOL.silence_methods #> Config.put SMT_Config.verbose false) state0;\n\
\            val params =\n\
\              Sledgehammer_Commands.default_params (Proof.theory_of state)\n\
\                (pairs param_args @\n\
\                  [(\"debug\", \"false\"), (\"verbose\", \"false\"), (\"overlord\", \"false\")]);\n\
\            val i = the_default 1 (Int.fromString subgoal);\n\
\            val override = fact_override (Proof.context_of state) facts;\n\
\            fun output s = report id \"message\" (YXML.parse_body s);\n\
\            fun run () =\n\
\              let\n\
\                val res =\n\
\                  Exn.capture_body (fn () =>\n\
\                    Sledgehammer.run_sledgehammer params Sledgehammer_Prover.Normal\n\
\                      (SOME output) i override state);\n\
\                val _ = Synchronized.change jobs (Symtab.delete_safe id);\n\
\              in\n\
\                (case res of\n\
\                  Exn.Res (_, (outcome, _)) =>\n\
\                    report id \"finished\"\n\
\                      [XML.Text (Sledgehammer.short_string_of_sledgehammer_outcome outcome)]\n\
\                | Exn.Exn exn =>\n\
\                    if Exn.is_interrupt exn then report id \"cancelled\" []\n\
\                    else report id \"error\" [XML.Text (Runtime.exn_message exn)])\n\
\              end;\n\
\            val group = Future.new_group NONE;\n\
\            val _ = Synchronized.change jobs (Symtab.update (id, group));\n\
\          in\n\
\            ignore (Future.forks\n\
\              {name = \"vscode_sledgehammer_job\", group = SOME group, deps = [], pri = ~2,\n\
\                interrupts = true} [run])\n\
\          end\n\
\      | _ => error \"Bad arguments\"));\n\
\\n\
\end;\n";

in

val _ =
  (case Thy_Info.lookup_theory "HOL.Sledgehammer" of
    SOME thy =>
      List.app (ML_Context.eval_source_in (SOME (Proof_Context.init_global thy))
        ML_Compiler.flags o Input.string) [operation, job_operation]
  | NONE => ());

end;
