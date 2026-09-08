/*  Title:      Tools/VSCode/src/vscode_theories.scala
    Author:     Makarius

Status and timing of theories for Isabelle/VSCode, following the Theories and
Timing panels of Isabelle/jEdit.
*/

package isabelle.vscode


import isabelle._


object VSCode_Theories {
  def json_node(
    uri: String,
    theory: String,
    overall: Document_Status.Overall_Status,
    status: Document_Status.Node_Status
  ): JSON.Object.T =
    JSON.Object(
      "uri" -> uri,
      "theory" -> theory,
      "overall" -> overall.toString,
      "cumulated_time" -> status.cumulated_time.seconds,
      "max_time" -> status.max_time.seconds) ++ status.json

  def json_command(id: Document_ID.Command, name: String, time: Time): JSON.Object.T =
    JSON.Object("id" -> id, "name" -> name, "time" -> time.seconds)
}

/*
  Both jEdit panels are views of one Document_Status.Nodes_Status, recomputed from the
  current snapshot whenever commands change; only the presentation differs. So a single
  server-side component feeds both, and the client decides what to show.

  The timing threshold is what decides which commands are kept in Node_Status.command_timings
  at all, so it belongs on this side rather than being a client-side filter over everything:
  a fully processed session would otherwise ship one entry per command in the whole theory.
*/
class VSCode_Theories(server: Language_Server) {
  private val state = Synchronized(Document_Status.Nodes_Status.empty)

  private val threshold_ =
    Synchronized(server.options.seconds("editor_timing_threshold"))
  def threshold: Time = threshold_.value

  def set_threshold(seconds: Double): Unit = {
    threshold_.change(_ => Time.seconds(seconds max 0.0))
    // A new threshold changes which commands were collected, so recompute from scratch.
    state.change(_ => Document_Status.Nodes_Status.empty)
    update(publish = true)
  }

  /* update */

  private def update(
    domain: Option[Set[Document.Node.Name]] = None,
    trim: Boolean = false,
    publish: Boolean = false
  ): Unit = {
    val snapshot = server.session.snapshot()
    val now = Date.now()
    state.change(_.update_nodes(now, server.resources, snapshot.state, snapshot.version,
      threshold = threshold, domain = domain, trim = trim))
    if (publish) publish_status() else delay_publish.invoke()
  }

  private lazy val delay_publish: Delay =
    server.channel.Delay.last(server.options.seconds("vscode_output_delay")) { publish_status() }

  private def publish_status(): Unit = {
    val snapshot = server.session.snapshot()
    val now = Date.now()
    val nodes_status = state.value
    val limit = threshold

    val nodes =
      (for {
        name <- snapshot.version.nodes.topological_order.iterator
        status = nodes_status(name)
        if !status.is_empty && !status.suppressed && status.total > 0
      } yield {
        VSCode_Theories.json_node(Url.print_file_name(name.node), name.theory,
          nodes_status.overall_status(name), status)
      }).toList

    /* Commands of the theory the caret is in -- the Timing panel expands only that one,
       exactly as jEdit does, because command ids are only resolvable via a snapshot. */
    val current = server.editor.current_node(())
    val commands =
      (for {
        name <- current.iterator
        (command_id, timings) <- nodes_status(name).command_timings.iterator
        command <- snapshot.get_command(command_id).iterator
        t = timings.sum(now) if t.is_notable(limit)
      } yield VSCode_Theories.json_command(command_id, command.span.name, t)).toList

    server.channel.write(
      LSP.Theories_Response(
        phase = server.session.phase.print,
        threshold = limit.seconds,
        current = current.map(name => Url.print_file_name(name.node)),
        nodes = nodes,
        commands = commands))
  }

  def request(): Unit = update(publish = true)

  /* main */

  private val commands_changed =
    Session.Consumer[Session.Commands_Changed](this.class_name) {
      case changed => update(domain = Some(changed.nodes), trim = changed.assignment)
    }

  private val phase_changed =
    Session.Consumer[Session.Phase](this.class_name) {
      case _ => delay_publish.invoke()
    }

  def init(): Unit = {
    server.session.commands_changed += commands_changed
    server.session.phase_changed += phase_changed
  }

  def exit(): Unit = {
    server.session.commands_changed -= commands_changed
    server.session.phase_changed -= phase_changed
    delay_publish.revoke()
  }
}
