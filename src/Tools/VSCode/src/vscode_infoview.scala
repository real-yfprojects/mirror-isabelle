/*  Title:      Tools/VSCode/src/vscode_infoview.scala

One view of prover output for Isabelle/VSCode: the goals and messages of the command at
the caret, and of commands the user has pinned. The State and Output panels together,
after Lean's infoview.
*/

package isabelle.vscode


import isabelle._

import java.io.{File => JFile}


object VSCode_Infoview {
  /* The proof states apart from everything else. The prover prints the state into the
     results of every command, since the session runs with editor_output_state, and
     Editor.output merely drops it unless the editor's own option says otherwise; here it
     is kept, as a list of its own. Urgent messages come first, as in Editor.output. */
  def split(
    results: Command.Results,
    filter: XML.Elem => Boolean = _ => true
  ): (List[XML.Elem], List[XML.Elem]) = {
    val (states, other) =
      results.iterator.map(_._2).filter(msg => !Protocol.is_result(msg) && filter(msg))
        .toList.partition(Protocol.is_state)
    val (urgent, regular) = other.partition(Protocol.is_urgent)
    (states, urgent ::: regular)
  }

  def status(snapshot: Document.Snapshot, command: Command): String = {
    val status =
      Document_Status.Command_Status.merge(
        snapshot.state.command_states(snapshot.version, command).iterator.map(_.document_status))
    if (status.is_failed) "failed"
    else if (status.is_running) "running"
    else if (status.is_finished) "finished"
    else "unprocessed"
  }

  /* A pin holds on to a command while it lasts, and to the place where it started once an
     edit replaces it: the command there then becomes the pin's. Query_Operation, which the
     State panel pins with, holds the command alone, so its pin stops following the text at
     the first edit to that command. */
  final class Pin(val id: Long, val node_name: Document.Node.Name, var offset: Text.Offset) {
    var command: Option[Command] = None
    var published: Option[JSON.Object.T] = None
  }
}

class VSCode_Infoview(server: Language_Server) {
  /* Everything below is confined to the session's dispatcher thread: every entry point
     goes through send_dispatcher. */

  private var pins: List[VSCode_Infoview.Pin] = Nil
  private var margin: Option[Double] = None
  private var live: Option[JSON.Object.T] = None
  private var published: Option[JSON.T] = None

  /* Formatting and HTML are the expensive part and most updates change nothing, so
     rendered output is kept for as long as it is still shown. */
  private var rendered: Map[List[XML.Elem], String] = Map.empty
  private var rendered_next: Map[List[XML.Elem], String] = Map.empty

  private def render(output: List[XML.Elem]): String =
    if (output.isEmpty) ""
    else {
      val html =
        rendered.getOrElse(output, {
          val formatted =
            Pretty.formatted(Pretty.separate(output),
              margin = margin.getOrElse(server.resources.message_margin.toDouble),
              metric = Symbol.Metric)
          Pretty_Text_Panel.html(server.session, formatted)
        })
      rendered_next += (output -> html)
      html
    }

  private def line_of(model: VSCode_Model, offset: Text.Offset): Int =
    model.content.doc.position(offset min model.content.text_length).line

  /* The command's start in the text as the editor has it, which can be ahead of the
     snapshot's version by the edits still pending. */
  private def command_offset(snapshot: Document.Snapshot, command: Command): Option[Text.Offset] =
    snapshot.node.command_start(command).map(snapshot.convert)

  private def section(
    id: Option[Long],
    model: VSCode_Model,
    snapshot: Document.Snapshot,
    command: Command,
    line: Int,
    filter: XML.Elem => Boolean = _ => true
  ): JSON.Object.T = {
    val (states, messages) = VSCode_Infoview.split(snapshot.command_results(command), filter)
    val source =
      split_lines(command.source).map(_.trim).find(_.nonEmpty).getOrElse("")
    JSON.Object(
      "uri" -> Url.print_file_name(model.node_name.node),
      "line" -> line,
      "command" -> command.span.name,
      "source" -> server.resources.output_text(Symbol.explode(source).take(100).mkString),
      "status" -> VSCode_Infoview.status(snapshot, command),
      "goals" -> render(states),
      "messages" -> render(messages)) ++
    JSON.optional("id" -> id)
  }


  /* the command at the caret */

  /* As Editor.output: a snapshot with edits still pending shows nothing new, so the
     section stays as it was until the edits are in. */
  private def live_section(): Option[JSON.Object.T] =
    server.resources.get_caret() match {
      case None => None
      case Some(caret) =>
        val snapshot = server.resources.snapshot(caret.model)
        if (snapshot.is_outdated) live
        else {
          val thy_command_range = snapshot.loaded_theory_command(caret.offset)

          def filter(msg: XML.Elem): Boolean =
            (for {
              (command, command_range) <- thy_command_range
              msg_offset <- Position.Offset.unapply(msg.markup.properties)
            } yield command_range.contains(command.chunk.decode(msg_offset))) getOrElse true

          thy_command_range.map(_._1) orElse
            snapshot.current_command(caret.node_name, caret.offset) match {
            case None => None
            case Some(command) =>
              val offset =
                if (command.node_name == caret.node_name) command_offset(snapshot, command)
                else None
              val line = line_of(caret.model, offset.getOrElse(caret.offset))
              Some(section(None, caret.model, snapshot, command, line, filter))
          }
        }
    }


  /* pinned commands */

  private def pin_section(pin: VSCode_Infoview.Pin): Option[JSON.Object.T] =
    server.resources.get_model(pin.node_name) match {
      case None => pin.published.map(_ + ("stale" -> true))
      case Some(model) =>
        val snapshot = server.resources.snapshot(model)
        if (snapshot.is_outdated) pin.published
        else {
          val command =
            pin.command.filter(snapshot.node.commands.contains) orElse
              snapshot.current_command(pin.node_name, pin.offset)
          command match {
            case None => pin.published.map(_ + ("stale" -> true))
            case Some(cmd) =>
              pin.command = command
              for (offset <- command_offset(snapshot, cmd)) pin.offset = offset
              pin.published = Some(section(Some(pin.id), model, snapshot, cmd,
                line_of(model, pin.offset)))
              pin.published
          }
        }
    }

  private def update(): Unit = {
    rendered_next = Map.empty
    live = live_section()
    val message = LSP.Infoview_Response(live, pins.flatMap(pin_section))
    rendered = rendered_next
    if (!published.contains(message)) {
      server.channel.write(message)
      published = Some(message)
    }
  }

  def request(): Unit =
    server.editor.send_dispatcher { published = None; update() }

  def pin(id: Long, file: JFile, pos: Line.Position): Unit =
    server.editor.send_dispatcher {
      for {
        model <- server.resources.get_model(file)
        offset <- model.content.doc.offset(pos)
        if !pins.exists(_.id == id)
      } {
        pins = pins :+ new VSCode_Infoview.Pin(id, model.node_name, offset)
        update()
      }
    }

  def unpin(id: Long): Unit =
    server.editor.send_dispatcher {
      pins = pins.filterNot(_.id == id)
      update()
    }

  def set_margin(new_margin: Double): Unit =
    server.editor.send_dispatcher {
      if (!margin.contains(new_margin)) {
        margin = Some(new_margin)
        rendered = Map.empty
        update()
      }
    }


  /* main */

  private val commands_changed =
    Session.Consumer[Session.Commands_Changed](getClass.getName) {
      _ => server.editor.send_dispatcher { update() }
    }

  private val caret_focus =
    Session.Consumer[Session.Caret_Focus.type](getClass.getName) {
      _ => server.editor.send_dispatcher { update() }
    }

  def init(): Unit = {
    server.session.commands_changed += commands_changed
    server.session.caret_focus += caret_focus
  }

  def exit(): Unit = {
    server.session.commands_changed -= commands_changed
    server.session.caret_focus -= caret_focus
    server.editor.send_dispatcher {
      pins = Nil
      live = None
      published = None
      rendered = Map.empty
    }
  }
}
