/*  Title:      Tools/VSCode/src/vscode_simplifier_trace.scala
    Author:     Makarius

Interactive simplifier trace for Isabelle/VSCode, following the Simplifier Trace
panel of Isabelle/jEdit.
*/

package isabelle.vscode


import isabelle._


/*
  Unlike every other panel here, this one is not a view of prover output: it is a
  conversation. With [[simp_trace_new]] enabled the simplifier *suspends* at a rewrite
  step and waits for an answer, so a question carries a serial the reply must quote, and
  until that reply arrives the proof does not proceed. That is the whole reason the panel
  is worth having -- a plain trace of a looping simpset is thousands of lines with no way
  to stop at the interesting one.

  Questions live in Simplifier_Trace's own manager thread, keyed by the command they came
  from. The panel therefore recomputes from the command under the caret, exactly as
  Simplifier_Trace_Dockable does, and republishes whenever commands change, the caret
  moves, or the manager signals a new question.
*/
class VSCode_Simplifier_Trace(server: Language_Server) {
  private val do_update = Synchronized(true)

  /* The command a reply belongs to. A reply quotes a serial, but the serial is only
     meaningful against the question set of one command, so both are remembered. */
  private val current = Synchronized((Document_ID.none, Command.Results.empty))

  def set_auto_update(enabled: Boolean): Unit = {
    do_update.change(_ => enabled)
    if (enabled) update()
  }

  private def answers_json(question: Simplifier_Trace.Question): List[JSON.Object.T] =
    question.answers.map(a => JSON.Object("name" -> a.name, "label" -> a.string))

  /* update */

  private def update(follow: Boolean = true): Unit = {
    val (id, results) =
      if (follow) {
        server.editor.current_node_snapshot(()) match {
          case Some(snapshot) if !snapshot.is_outdated =>
            server.editor.current_command((), snapshot) match {
              case Some(command) => (command.id, snapshot.command_results(command))
              case None => (Document_ID.none, Command.Results.empty)
            }
          case _ => current.value
        }
      }
      else current.value

    current.change(_ => (id, results))

    val context = Simplifier_Trace.handle_results(server.session, id, results)
    val questions = context.questions.values.toList

    /* Only the first question is answerable: the simplifier is suspended at one point,
       and the rest are queued behind it. The count is published so the panel can say so
       rather than implying the trace is done. */
    val head =
      questions.headOption.map { q =>
        JSON.Object(
          "serial" -> q.data.serial,
          "text" -> q.data.text,
          "content" -> XML.string_of_body(Pretty.unbreakable(q.data.content)),
          "answers" -> answers_json(q))
      }

    server.channel.write(
      LSP.Simplifier_Trace_Response(
        auto_update = do_update.value, pending = questions.length, question = head))
  }

  /* requests from the client */

  def request(): Unit = server.editor.send_dispatcher { update() }

  def reply(serial: Long, answer_name: String): Unit =
    Simplifier_Trace.all_answers.find(_.name == answer_name) match {
      case Some(answer) =>
        Simplifier_Trace.send_reply(server.session, serial, answer)
        /* The reply unblocks the simplifier, which produces the next question through
           trace_events; nothing to publish here beyond clearing this one. */
        server.editor.send_dispatcher { update() }
      case None =>
        server.channel.log_error_message("Unknown simplifier trace answer: " + answer_name)
    }

  def clear_memory(): Unit = {
    /* "Memory" is the simplifier remembering an answer for equivalent later steps, which
       is what makes "Continue (without asking)" bearable. Clearing it makes the next run
       ask again. */
    Simplifier_Trace.clear_memory(server.session)
    server.editor.send_dispatcher { update() }
  }

  /** The full trace of the current command, rather than the pending question. */
  def show_trace(): Unit =
    server.editor.send_dispatcher {
      val (_, results) = current.value
      val trace = Simplifier_Trace.generate_trace(server.session, results)
      val entries =
        trace.entries.map(data =>
          JSON.Object(
            "serial" -> data.serial,
            "text" -> data.text,
            "content" -> XML.string_of_body(Pretty.unbreakable(data.content))))
      server.channel.write(LSP.Simplifier_Trace_Full(entries))
    }

  /* main */

  /* Each outlet carries its own type, so one consumer cannot serve all three. */

  private def refresh(force: Boolean): Unit =
    if (force || do_update.value) server.editor.send_dispatcher { update() }

  private val commands_changed =
    Session.Consumer[Session.Commands_Changed](this.class_name) { _ => refresh(force = false) }

  private val caret_focus =
    Session.Consumer[Session.Caret_Focus.type](this.class_name) { _ => refresh(force = false) }

  /* A new question is published whether or not auto-update is on: the proof is now
     blocked on an answer, which is precisely when the panel must not stay stale. */
  private val trace_events =
    Session.Consumer[Simplifier_Trace.Event.type](this.class_name) { _ => refresh(force = true) }

  def init(): Unit = {
    server.session.commands_changed += commands_changed
    server.session.caret_focus += caret_focus
    server.session.trace_events += trace_events
  }

  def exit(): Unit = {
    server.session.commands_changed -= commands_changed
    server.session.caret_focus -= caret_focus
    server.session.trace_events -= trace_events
  }
}
