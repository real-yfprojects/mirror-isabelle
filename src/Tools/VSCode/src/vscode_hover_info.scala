/*  Title:      Tools/VSCode/src/vscode_hover_info.scala

What the name under the mouse stands for, for the hover: the statement of a fact, the type
of a fixed variable or a constant, the term a term abbreviation is bound to, what a case
provides. The markup of the text only names these things; a query operation
(vscode_hover.ML) asks the context of a command, once for each name and execution of it.
*/

package isabelle.vscode


import isabelle._


object VSCode_Hover_Info {
  val print_function = "vscode_hover_info_query"

  /*the ML prelude, beside the one for completion*/
  val ml_resource = "isabelle/vscode/vscode_hover.ML"

  /*a name, by the kind of its entity (or "var" for a schematic variable), and the
    selection of a fact: "2" for assms(2)*/
  sealed case class Key(kind: String, name: String, selection: String = "") {
    def args: List[String] = List(kind, name, selection)
  }

  /*the kinds the query knows about*/
  val kinds: Set[String] =
    Set(Markup.FACT, Markup.FIXED, Markup.CONSTANT, Markup.CASE, Markup.VAR)

  /*the context to ask: the text after the command that binds a name, or before the command
    that refers to it -- whose own context may have closed the block of a local fact*/
  sealed case class Request(command: Command, exec: Option[Document_ID.Exec], key: Key)

  private sealed case class Entry(request: Request, instance: String, result: Option[XML.Body])

  private val max_entries = 32

  private def is_status(body: XML.Body): Boolean =
    body match {
      case List(XML.Elem(Markup(name, _), _)) =>
        name == Markup.RUNNING || name == Markup.FINISHED || name == Markup.ERROR
      case _ => false
    }
}

class VSCode_Hover_Info(server: Language_Server) {
  import VSCode_Hover_Info.{Entry, Request}

  /*most recent first*/
  private val entries = Synchronized(List.empty[Entry])


  /* overlays */

  private def overlay(insert: Boolean, entry: Entry): Unit =
    server.editor.send_dispatcher {
      val fn = VSCode_Hover_Info.print_function
      val args = entry.instance :: entry.request.key.args
      val command = entry.request.command
      if (insert) server.editor.insert_overlay(command, fn, args)
      else server.editor.remove_overlay(command, fn, args)
      server.editor.flush()
    }


  /* result */

  /*the info, once the query has finished: Nil when there is none*/
  private def result(snapshot: Document.Snapshot, entry: Entry): Option[XML.Body] = {
    val bodies =
      (for {
        case (_, XML.Elem(Markup(Markup.RESULT, Markup.Instance(instance)), body))
          <- snapshot.command_results(entry.request.command).iterator
        if instance == entry.instance
      } yield body).toList
    val finished =
      bodies.exists({ case List(XML.Elem(Markup(Markup.FINISHED, _), _)) => true case _ => false })
    if (finished) Some(bodies.filterNot(VSCode_Hover_Info.is_status).flatten) else None
  }

  /*the info for a request, or None while the prover has yet to give it: asks for it at once*/
  def get(snapshot: Document.Snapshot, request: Request): Option[XML.Body] = {
    val (res, inserted, removed) =
      entries.change_result { list =>
        list.find(_.request == request) match {
          case Some(Entry(_, _, Some(body))) => ((Some(body), None, Nil), list)
          case Some(entry) =>
            result(snapshot, entry) match {
              case Some(body) =>
                val entry1 = entry.copy(result = Some(body))
                ((Some(body), None, List(entry)), entry1 :: list.filterNot(_ == entry))
              case None => ((None, None, Nil), list)
            }
          case None =>
            val entry = Entry(request, Document_ID.make().toString, None)
            val (keep, drop) = (entry :: list).splitAt(VSCode_Hover_Info.max_entries)
            ((None, Some(entry), drop.filter(_.result.isEmpty)), keep)
        }
      }
    inserted.foreach(overlay(true, _))
    removed.foreach(overlay(false, _))
    res
  }

  def exit(): Unit = entries.change(_ => Nil)
}
