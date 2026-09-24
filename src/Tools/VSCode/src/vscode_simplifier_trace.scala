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

  /* Publish on both edges, and from the dispatcher like every other entry point here.
     The response is what carries auto_update, so refreshing only when enabling leaves the
     panel showing the old value after the user turns it off -- the one case where the
     client cannot infer the state for itself. */
  def set_auto_update(enabled: Boolean): Unit = {
    do_update.change(_ => enabled)
    server.editor.send_dispatcher { update() }
  }

  private def answers_json(question: Simplifier_Trace.Question): List[JSON.Object.T] =
    question.answers.map(a => JSON.Object("name" -> a.name, "label" -> a.string))


  /* rendering */

  /* As the State panel renders its output, and for the same three reasons.
     Simplifier_Trace.ML hands over `content` as a *list* of blocks -- "Instance of ...",
     "Trying to rewrite: ...", the matching terms -- so Pretty.separate is what puts
     anything at all between them; Pretty.formatted is what turns the blocks' breaks into
     real line ends and indentation at the panel's width; and make_html is what filters
     the body down to the markup meant to be seen. That last one is not cosmetic: a term
     from Syntax.pretty_term carries its typing as nested markup, which a client that
     simply displays every element renders inline, so "?f" arrives with its own type
     spliced into the middle of the term.

     This used to be XML.string_of_body(Pretty.unbreakable(...)), which does none of the
     three: one line, no separation, every zero-width break dropped outright (spaces(0) is
     Nil), and every invisible markup element served as text. */
  private def html_content(content: XML.Body): String = {
    val formatted =
      Pretty.formatted(Pretty.separate(content),
        margin = server.resources.message_margin, metric = Symbol.Metric)
    val node_context =
      new Browser_Info.Node_Context {
        override def make_ref(props: Properties.T, body: XML.Body): Option[XML.Elem] =
          for {
            thy_file <- Position.Def_File.unapply(props)
            def_line <- Position.Def_Line.unapply(props)
            platform_path <- server.session.store.source_file(thy_file)
            uri = File.uri(Path.explode(File.standard_path(platform_path)).absolute_file)
          } yield HTML.link(uri.toString + "#" + def_line, body)
      }
    val elements = Browser_Info.extra_elements.copy(entity = Markup.Elements.full)
    HTML.source(node_context.make_html(elements, formatted)).toString
  }

  /* update */

  /* Deliberately no `!snapshot.is_outdated` guard, though Simplifier_Trace_Dockable has
     one. It does not transfer: VSCode_Resources.snapshot builds pending_edits from *every*
     open model, and is_outdated is just !pending_edits.is_stable, so with more than one
     document open the snapshot is outdated almost always and the guard yields empty
     results forever. Dynamic_Output, which works, takes the caret's snapshot unguarded;
     this follows it. */
  private def update(follow: Boolean = true): Unit = {
    val (id, results) =
      if (follow) {
        server.editor.current_node_snapshot(()) match {
          case Some(snapshot) =>
            server.editor.current_command((), snapshot) match {
              case Some(command) => (command.id, snapshot.command_results(command))
              case None => (Document_ID.none, Command.Results.empty)
            }
          case None => current.value
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
          "content" -> html_content(q.data.content),
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

  /** The full trace of the current command, rather than the pending question.

      Sent flat, with what the client needs to rebuild the tree Simplifier_Trace_Window
      draws: the parent each item was emitted under, its kind (invocation, step, log,
      hint, ignore) and, for hints, whether the step succeeded. Without those three the
      trace is a list in emission order, which says what the simplifier looked at but not
      what it did or why -- a side-condition attempt is indistinguishable from a rewrite
      of the goal. `plain` is the one-line text of the same content, for summaries and
      search; XML.content skips the hidden typing bodies just as make_html does. */
  def show_trace(): Unit =
    server.editor.send_dispatcher {
      val (_, results) = current.value
      val trace = Simplifier_Trace.generate_trace(server.session, results)
      val entries =
        trace.entries.map(data =>
          JSON.Object(
            "serial" -> data.serial,
            "parent" -> data.parent,
            "kind" -> data.markup.stripPrefix("simp_trace_"),
            "text" -> data.text,
            "content" -> html_content(data.content),
            "plain" -> server.resources.output_text(XML.content(data.content))) ++
          JSON.optional("success" -> Simplifier_Trace.Success.unapply(data.props)))
      server.channel.write(LSP.Simplifier_Trace_Full(entries))
    }

  /* main */

  /* Each outlet carries its own type, so one consumer cannot serve all three. */

  private def refresh(force: Boolean): Unit =
    if (force || do_update.value) server.editor.send_dispatcher { update() }

  private val commands_changed =
    Session.Consumer[Session.Commands_Changed](getClass.getName) { _ => refresh(force = false) }

  private val caret_focus =
    Session.Consumer[Session.Caret_Focus.type](getClass.getName) { _ => refresh(force = false) }

  /* A new question is published whether or not auto-update is on: the proof is now
     blocked on an answer, which is precisely when the panel must not stay stale. */
  private val trace_events =
    Session.Consumer[Simplifier_Trace.Event.type](getClass.getName) { _ => refresh(force = true) }

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
