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
    /* topological_order is all_succs(minimals), so a cycle nothing else points into has
       no minimal node and would vanish from the picture. locale_deps can be cyclic. */
    val ordered = graph.topological_order
    val nodes = ordered ::: graph.keys.filterNot(ordered.toSet)
    JSON.Object(
      "nodes" -> nodes.map(n => json_node(n, graph.get_node(n))),
      "edges" ->
        nodes.flatMap(from => graph.imm_succs(from).toList.map(to =>
          JSON.Object("from" -> from.ident, "to" -> to.ident))))
  }

  /* Graphs arrive inside command output, as a `graphview` markup element wrapping the
     encoded graph. jEdit picks them up through Active.Handler -- an active area the user
     clicks -- but Active lives in Tools/jEdit and has no counterpart here, so the server
     has to find the element itself.

     Returned undecoded, as thunks: decoding can fail, and the caller reports that
     failure rather than letting it escape. */
  def find_graphs(results: Command.Results): List[() => Graph_Display.Graph] =
    (for {
      (_, elem) <- results.iterator
      graph <- find_graph_bodies(List(elem))
    } yield graph).toList

  /* The old Graph Browser format, which locale_deps still emits through
     Graph_Display.display_graph_old -- under `browser` markup, not `graphview`. One node
     per line, the `+` present only for an unfolded node:

       "name" "ident" "dir" + "path" > "parent_ident" ... ;

     jEdit never reads this: its Active.Handler writes it to a file and starts the
     separate `isabelle browser` program. Read back here into the entries decode_graph
     builds from the new format. The format quotes without escaping, so a name cannot
     contain a quote, and it carries no node content. */
  def parse_browser_graph(text: String): Graph_Display.Graph = {
    val token = """"([^"]*)"|(>)""".r
    Graph_Display.build_graph(
      for (line <- split_lines(text) if line.trim.nn.nonEmpty)
      yield {
        val tokens = token.findAllMatchIn(line).map(m => Option(m.group(1))).toList
        val (fields, rest) = tokens.span(_.isDefined)
        fields.flatten match {
          case name :: ident :: _ => ((ident, (name, Nil)), rest.drop(1).flatten)
          case _ => error("Malformed graph browser line: " + quote(line))
        }
      })
  }

  /* Graph_Display.display_graph emits the graph through YXML.output_markup_elem, which
     builds an XML.wrap_elem rather than a plain element. A Wrapped_Elem is physically

       XML.Elem(Markup("xml_elem", ("xml_name", "graphview") :: props),
         XML.Elem(Markup("xml_body", Nil), <encoded graph>) :: <visible text>)

     so the element's own name is "xml_elem", never "graphview", and the graph is its
     *first* body. Matching on the markup name alone walks straight past it -- which is
     what made this publish an empty graph while the Output panel plainly showed the
     command's "See graph". The plain-Elem case is kept in case a producer ever emits one
     unwrapped. display_graph_old wraps its `browser` element the same way. */
  private def find_graph_bodies(trees: List[XML.Tree]): List[() => Graph_Display.Graph] =
    trees.flatMap {
      case XML.Wrapped_Elem(Markup(Markup.GRAPHVIEW, _), body, _) =>
        List(() => Graph_Display.decode_graph(body))
      case XML.Wrapped_Elem(Markup(Markup.BROWSER, _), body, _) =>
        List(() => parse_browser_graph(XML.content(body)))
      case XML.Wrapped_Elem(_, body1, body2) => find_graph_bodies(body1 ::: body2)
      case XML.Elem(Markup(Markup.GRAPHVIEW, _), body) =>
        List(() => Graph_Display.decode_graph(body))
      case XML.Elem(Markup(Markup.BROWSER, _), body) =>
        List(() => parse_browser_graph(XML.content(body)))
      case XML.Elem(_, body) => find_graph_bodies(body)
      case _ => Nil
    }
}

/*
  Unlike the Theories or Timing panels this is pull, not push: nothing appears unless the
  user asks for it with thy_deps, class_deps, locale_deps or code_deps. So the
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
      case Some(decode) =>
        /* transitive_reduction_acyclic is what makes these readable: thy_deps on a real
           project is dense with edges implied by others, and jEdit reduces for the same
           reason. It throws on a cycle -- and locale_deps is legitimately cyclic, since
           two locales can each be a sublocale of the other. jEdit never meets that,
           because locale_deps goes to the old browser, so a cyclic graph is shown
           unreduced rather than refused. A decode failure is still reported. */
        Exn.capture {
          val graph = decode()
          try { graph.transitive_reduction_acyclic }
          catch { case ERROR(_) => graph }
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
