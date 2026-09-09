/*  Title:      Tools/VSCode/src/vscode_graphview.scala
    Author:     Makarius

Graph display for Isabelle/VSCode, following the Graphview panel of Isabelle/jEdit.
*/

package isabelle.vscode


import isabelle._


object VSCode_Graphview {
  /* Nodes carry an ident (stable, used for edges) and a name (what a reader sees). The
     node's XML content is the tooltip jEdit shows on hover; it is passed through as
     rendered markup, like every other panel's prover output. */
  def json_node(node: Graph_Display.Node, content: XML.Body): JSON.Object.T =
    JSON.Object(
      "ident" -> node.ident,
      "name" -> node.name,
      "content" -> XML.string_of_body(Pretty.unbreakable(content)))

  def json_graph(graph: Graph_Display.Graph): JSON.Object.T = {
    val nodes = graph.topological_order
    JSON.Object(
      "nodes" -> nodes.map(n => json_node(n, graph.get_node(n))),
      "edges" ->
        nodes.flatMap(from => graph.imm_succs(from).toList.map(to =>
          JSON.Object("from" -> from.ident, "to" -> to.ident))))
  }

  /* Graphs arrive inside command output, as a `graphview` markup element wrapping the
     encoded graph. jEdit picks them up through Active.Handler -- an active area the user
     clicks -- but Active lives in Tools/jEdit and has no counterpart here, so the server
     has to find the element itself. */
  def find_graphs(results: Command.Results): List[XML.Body] =
    (for {
      (_, elem) <- results.iterator
      graph <- find_graph_bodies(List(elem))
    } yield graph).toList

  private def find_graph_bodies(trees: List[XML.Tree]): List[XML.Body] =
    trees.flatMap {
      case XML.Elem(Markup(Markup.GRAPHVIEW, _), body) => List(body)
      case XML.Elem(_, body) => find_graph_bodies(body)
      case _ => Nil
    }
}

/*
  Unlike the Theories or Timing panels this is pull, not push: nothing appears unless the
  user asks for it with thy_deps, class_deps, locale_deps, thm_deps or code_deps. So the
  panel republishes on the same events as the others, but a command with no graph in its
  output publishes an empty graph rather than nothing -- otherwise moving the caret off a
  thy_deps would leave the previous graph on screen, looking current.
*/
class VSCode_Graphview(server: Language_Server) {
  private def publish(graph: Option[Graph_Display.Graph], error: Option[String]): Unit =
    server.channel.write(
      LSP.Graphview_Response(graph.map(VSCode_Graphview.json_graph), error))

  private def update(): Unit = {
    /* No is_outdated guard: see the note in vscode_simplifier_trace.scala. The server's
       snapshot carries pending edits from every open model, so requiring stability here
       means never finding anything. */
    val results =
      server.editor.current_node_snapshot(()) match {
        case Some(snapshot) =>
          server.editor.current_command((), snapshot) match {
            case Some(command) => snapshot.command_results(command)
            case None => Command.Results.empty
          }
        case None => Command.Results.empty
      }

    VSCode_Graphview.find_graphs(results).lastOption match {
      case None => publish(None, None)
      case Some(body) =>
        /* transitive_reduction_acyclic is what makes these readable: thy_deps on a real
           project is dense with edges implied by others, and jEdit reduces for the same
           reason. It throws on a cycle, which decode can produce from malformed input, so
           the failure is reported rather than taking the panel down. */
        Exn.capture {
          Graph_Display.decode_graph(body).transitive_reduction_acyclic
        } match {
          case Exn.Res(graph) => publish(Some(graph), None)
          case Exn.Exn(exn) => publish(None, Some(Exn.message(exn)))
        }
    }
  }

  def request(): Unit = server.editor.send_dispatcher { update() }

  /* main */

  private val commands_changed =
    Session.Consumer[Session.Commands_Changed](this.class_name) {
      _ => server.editor.send_dispatcher { update() }
    }

  private val caret_focus =
    Session.Consumer[Session.Caret_Focus.type](this.class_name) {
      _ => server.editor.send_dispatcher { update() }
    }

  def init(): Unit = {
    server.session.commands_changed += commands_changed
    server.session.caret_focus += caret_focus
  }

  def exit(): Unit = {
    server.session.commands_changed -= commands_changed
    server.session.caret_focus -= caret_focus
  }
}
