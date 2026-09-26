/*  Title:      Tools/VSCode/src/vscode_query.scala
    Author:     Makarius

Query operations (find_theorems, find_consts) for Isabelle/VSCode, following the
Query panel of Isabelle/jEdit.
*/

package isabelle.vscode


import isabelle._


object VSCode_Query {
  /* operations offered to the client */

  val FIND_THEOREMS = "find_theorems"
  val FIND_CONSTS = "find_consts"

  val operations: List[String] = List(FIND_THEOREMS, FIND_CONSTS)
}

/*
  One Query_Operation per operation name, exactly as Query_Dockable does in
  Isabelle/jEdit; VSCode_Sledgehammer is the same mechanism with a fixed name.

  Arguments follow the jEdit panel:
    find_theorems: List(limit, allow_duplicates, query)
    find_consts:   List(query)
*/
class VSCode_Query(server: Language_Server) {
  private class Operation(name: String) {
    private def consume_status(status: Query_Operation.Status): Unit = {
      val message =
        status match {
          case Query_Operation.Status.waiting => "Waiting for evaluation of context ..."
          case Query_Operation.Status.running => "Running ..."
          case Query_Operation.Status.finished => "Finished"
        }
      server.channel.write(LSP.Query_Status(name, message))
    }

    private def consume_output(output: Editor.Output): Unit = {
      val content = XML.string_of_body(Pretty.unbreakable(output.messages))
      server.channel.write(LSP.Query_Output(name, content))
    }

    val query_operation =
      new Query_Operation(server.editor, (), name, consume_status, consume_output)
  }

  private val operations: Map[String, Operation] =
    VSCode_Query.operations.map(name => name -> new Operation(name)).toMap

  private def get(name: String): Option[Operation] = operations.get(name)

  def request(name: String, args: List[String]): Unit =
    get(name).foreach(op => server.editor.send_dispatcher { op.query_operation.apply_query(args) })

  def cancel(name: String): Unit =
    get(name).foreach(op => server.editor.send_dispatcher { op.query_operation.cancel_query() })

  def locate(name: String): Unit =
    get(name).foreach(op => server.editor.send_dispatcher { op.query_operation.locate_query() })

  def operations_response(): Unit =
    server.channel.write(LSP.Query_Operations_Response(VSCode_Query.operations))

  def init(): Unit = operations.valuesIterator.foreach(_.query_operation.activate())
  def exit(): Unit = operations.valuesIterator.foreach(_.query_operation.deactivate())
}
