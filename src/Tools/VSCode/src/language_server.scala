/*  Title:      Tools/VSCode/src/language_server.scala
    Author:     Makarius

Server for VS Code Language Server Protocol 2.0/3.0, see also
https://github.com/Microsoft/language-server-protocol
https://github.com/Microsoft/language-server-protocol/blob/master/protocol.md

PIDE protocol extensions depend on system option "vscode_pide_extensions".
*/

package isabelle.vscode


import isabelle._

import java.io.{File => JFile}

import scala.collection.mutable
import scala.annotation.tailrec


object Language_Server {
  /* build session */

  def build_session(options: Options, logic: String,
    build_progress: Progress = new Progress,
    session_dirs: List[Path] = Nil,
    include_sessions: List[String] = Nil,
    session_ancestor: Option[String] = None,
    session_requirements: Boolean = false,
    session_no_build: Boolean = false,
    build_started: String => Unit = _ => (),
    build_failed: String => Unit = _ => ()
  ): Sessions.Background = {
    val session_background =
      Sessions.background(
        options, logic, dirs = session_dirs,
        include_sessions = include_sessions, session_ancestor = session_ancestor,
        session_requirements = session_requirements).check_errors

    /* The session to build is the background's own, not the name that was asked for:
       with session_requirements (option -R) Sessions.background returns a synthetic
       "NAME_requirements(ANCESTOR)" session holding the theories NAME imports from other
       sessions, and that is also what session_heaps then loads. Building the named
       session instead builds the wrong thing and leaves the required heap missing, so
       -R started with "Missing heap image for session ..." and nothing was cached.
       Session.build, which Isabelle/jEdit uses for the same purpose, selects the
       background's session name. */
    def build(no_build: Boolean = false, progress: Progress = new Progress): Build.Results =
      Build.build(options,
        selection = Sessions.Selection.session(session_background.session_name),
        build_heap = true, no_build = no_build, dirs = session_dirs,
        infos = session_background.infos,
        progress = progress)

    if (!session_no_build && !build(no_build = true).ok) {
      // Report the session actually being built, which under -R is the requirements image.
      build_started(session_background.session_name)
      if (!build(progress = build_progress).ok) build_failed(session_background.session_name)
    }

    session_background
  }


  /* ML preludes */

  /*ML of the server, loaded into the prover at startup rather than compiled into a heap, so
    that it needs no heap of its own: isabelle-vscode's extended server brings it to a
    released distribution as a resource of a jar. Returns a temporary file for
    Isabelle_Process.start (use_prelude); missing says what is lost without it*/
  def ml_prelude(resource: String, name: String, log: Logger, missing: String): Option[JFile] = {
    val loader = getClass.getClassLoader
    val stream = if (loader == null) null else loader.getResourceAsStream(resource)
    if (stream == null) {
      log("No " + resource + ": " + missing)
      None
    }
    else {
      val text = using(stream)(s => new String(s.readAllBytes, UTF8.charset))
      val file = Isabelle_System.tmp_file(name, ext = "ML")
      File.write(file, text)
      Some(file)
    }
  }


  /* abstract editor operations */

  class Editor(server: Language_Server) extends isabelle.Editor {
    type Context = Unit


    /* PIDE session and document model */

    override def session: VSCode_Session = server.session
    override def flush(): Unit = session.resources.flush_input(session, server.channel)

    override def get_models(): Iterable[Document.Model] = session.resources.get_models()


    /* input from client */

    private val delay_input: Delay =
      Delay.last(server.options.seconds("vscode_input_delay"), server.channel.Error_Logger) {
        session.resources.flush_input(session, server.channel)
      }

    override def invoke(): Unit = delay_input.invoke()
    override def revoke(): Unit = delay_input.revoke()


    /* current situation */

    override def current_node(context: Unit): Option[Document.Node.Name] =
      session.resources.get_caret().map(_.model.node_name)
    override def current_node_snapshot(context: Unit): Option[Document.Snapshot] =
      session.resources.get_caret().map(caret => session.resources.snapshot(caret.model))

    override def node_snapshot(name: Document.Node.Name): Document.Snapshot = {
      session.resources.get_snapshot(name) match {
        case Some(snapshot) => snapshot
        case None => session.snapshot(name)
      }
    }

    def current_command(snapshot: Document.Snapshot): Option[Command] = {
      session.resources.get_caret() match {
        case Some(caret) if snapshot.loaded_theory_command(caret.offset).isEmpty =>
          snapshot.current_command(caret.node_name, caret.offset)
        case _ => None
      }
    }
    override def current_command(context: Unit, snapshot: Document.Snapshot): Option[Command] =
      current_command(snapshot)


    /* output messages */

    override def output_state(): Boolean =
      session.resources.options.bool("editor_output_state")


    /* overlays */

    override def node_overlays(name: Document.Node.Name): Document.Node.Overlays =
      session.resources.node_overlays(name)

    override def insert_overlay(command: Command, fn: String, args: List[String]): Unit =
      session.resources.insert_overlay(command, fn, args)

    override def remove_overlay(command: Command, fn: String, args: List[String]): Unit =
      session.resources.remove_overlay(command, fn, args)


    /* hyperlinks */

    override def hyperlink_command(
      snapshot: Document.Snapshot,
      id: Document_ID.Generic,
      offset: Symbol.Offset = 0,
      focus: Boolean = false,
    ): Option[Hyperlink] = {
      if (snapshot.is_outdated) None
      else
        snapshot.find_command_position(id, offset).map(node_pos =>
          new Hyperlink {
            def follow(unit: Unit): Unit = server.channel.write(LSP.Caret_Update(node_pos, focus))
          })
    }


    /* dispatcher thread */

    override def assert_dispatcher[A](body: => A): A = session.assert_dispatcher(body)
    override def require_dispatcher[A](body: => A): A = session.require_dispatcher(body)
    override def send_dispatcher(body: => Unit): Unit = session.send_dispatcher(body)
    override def send_wait_dispatcher(body: => Unit): Unit = session.send_wait_dispatcher(body)
  }
}

class Language_Server(
  val channel: Channel,
  val options: Options,
  session_name: String = Isabelle_System.default_logic(),
  include_sessions: List[String] = Nil,
  session_dirs: List[Path] = Nil,
  session_ancestor: Option[String] = None,
  session_requirements: Boolean = false,
  session_no_build: Boolean = false,
  modes: List[String] = Nil,
  log: Logger = new Logger
) {
  server =>

  val editor: Language_Server.Editor = new Language_Server.Editor(server)


  /* prover session */

  private val session_ = Synchronized(None: Option[VSCode_Session])
  def session: VSCode_Session = session_.value getOrElse error("Server inactive")
  def resources: VSCode_Resources = session.resources
  def ml_settings: ML_Settings = session.store.ml_settings

  private val sledgehammer = new VSCode_Sledgehammer(server)
  private val theories = new VSCode_Theories(server)
  private val simplifier_trace = new VSCode_Simplifier_Trace(server)
  private val graphview = new VSCode_Graphview(server)
  private val infoview = new VSCode_Infoview(server)
  private val query = new VSCode_Query(server)

  /* The completion options are declared in etc/options, which this code may run without:
     isabelle-vscode's extended server compiles it into a jar that goes ahead of a released
     distribution's own classes, and a jar carries no option declarations. An undeclared
     option cannot be read ("Unknown option"), and at session start that would fail the
     whole server, so fall back to the defaults declared in etc/options. */
  private def completion_limit: Int =
    if (options.defined("vscode_completion_limit")) options.int("vscode_completion_limit")
    else 1000

  private def completion_delay: Time =
    if (options.defined("vscode_completion_delay")) options.seconds("vscode_completion_delay")
    else Time.seconds(0.5)

  /*VS Code filters a list itself, so the more complete it is, the better*/
  private def prover_options: Options =
    options.int.update("completion_limit", completion_limit)

  private val context_names = new VSCode_Context_Names(server, completion_limit)

  def rendering_offset(node_pos: Line.Node_Position): Option[(VSCode_Rendering, Text.Offset)] =
    for {
      rendering <- resources.get_rendering(new JFile(node_pos.name))
      offset <- rendering.model.content.doc.offset(node_pos.pos)
    } yield (rendering, offset)

  private val dynamic_output = Dynamic_Output(server)


  /* input from client or file-system */

  private val file_watcher: File_Watcher =
    File_Watcher(sync_documents, options.seconds("vscode_load_delay"))

  private val delay_load: Delay =
    Delay.last(options.seconds("vscode_load_delay"), channel.Error_Logger) {
      val (invoke_input, invoke_load) =
        resources.resolve_dependencies(session, editor, file_watcher)
      if (invoke_input) editor.invoke()
      loading_.change(_ => invoke_load)
      if (invoke_load) delay_load.invoke()
    }

  /* Dependency resolution is asynchronous: an opened theory whose imports are not
     loaded yet has a failing header, which is a transient state rather than an error
     about the proof. Clients need to be able to tell the two apart. */
  private val loading_ = Synchronized(false)
  def loading: Boolean = loading_.value

  private def start_loading(): Unit = {
    loading_.change(_ => true)
    delay_load.invoke()
  }

  private def close_document(file: JFile): Unit = {
    if (resources.close_model(file)) {
      file_watcher.register_parent(file)
      sync_documents(Set(file))
      editor.invoke()
      delay_output.invoke()
    }
  }

  private def sync_documents(changed: Set[JFile]): Unit = {
    resources.sync_models(changed)
    editor.invoke()
    delay_output.invoke()
  }

  private def change_document(
    file: JFile,
    version: Long,
    changes: List[LSP.TextDocumentChange]
  ): Unit = {
    changes.foreach(change =>
      resources.change_model(session, editor, file, version, change.text, change.range))

    editor.invoke()
    delay_output.invoke()
  }


  /* caret handling */

  private val delay_caret_update: Delay =
    Delay.last(options.seconds("vscode_input_delay"), channel.Error_Logger) {
      session.caret_focus.post(Session.Caret_Focus)
    }

  private def update_caret(caret: Option[(JFile, Line.Position)]): Unit = {
    resources.update_caret(caret)
    delay_caret_update.invoke()
    editor.invoke()
  }


  /* preview */

  private lazy val preview_panel = new Preview_Panel(resources)

  private lazy val delay_preview: Delay =
    Delay.last(options.seconds("vscode_output_delay"), channel.Error_Logger) {
      if (preview_panel.flush(channel)) delay_preview.invoke()
    }

  private def preview_request(file: JFile, column: Int): Unit = {
    preview_panel.request(file, column)
    delay_preview.invoke()
  }


  /* output to client */

  private val delay_output: Delay =
    Delay.last(options.seconds("vscode_output_delay"), channel.Error_Logger) {
      if (resources.flush_output(channel)) delay_output.invoke()
    }

  def update_output(changed_nodes: Iterable[JFile]): Unit = {
    resources.update_output(changed_nodes)
    delay_output.invoke()
  }

  def update_output_visible(): Unit = {
    resources.update_output_visible()
    delay_output.invoke()
  }

  private val prover_output =
    Session.Consumer[Session.Commands_Changed](getClass.getName) {
      case changed =>
        update_output(changed.nodes.toList.map(resources.node_file(_)))
    }

  private val syslog_messages =
    Session.Consumer[Prover.Output](getClass.getName) {
      case output => channel.log_writeln(resources.output_text(XML.content(output.message)))
    }


  /* decoration request */

  private def decoration_request(file: JFile): Unit =
    resources.force_decorations(channel, file)


  /* init and exit */

  def init(id: LSP.Id): Unit = {
    def reply_ok(msg: String): Unit = {
      channel.write(LSP.Initialize.reply(id, ""))
      channel.writeln(msg)
    }

    def reply_error(msg: String): Unit = {
      channel.write(LSP.Initialize.reply(id, msg))
      channel.error_message(msg)
    }

    val try_session =
      try {
        val progress = channel.progress(verbose = true)
        /* Feed the build itself, not just the started/failed one-liners: build_progress
           defaults to the base Progress, whose output is a no-op, so the heap build ran
           entirely silent. It happens inside "initialize", which does not reply until it
           finishes, so a cold build was tens of minutes with nothing after "Build started
           for ..." -- indistinguishable from a hang. This progress is Progress.Status, so
           it also carries the long-running-command lines that tell a slow proof from a
           stuck one. */
        val session_background =
          Language_Server.build_session(options, session_name,
            build_progress = progress,
            session_dirs = session_dirs,
            include_sessions = include_sessions,
            session_ancestor = session_ancestor,
            session_requirements = session_requirements,
            session_no_build = session_no_build,
            build_started = { logic =>
              val msg = Build.build_logic_started(logic)
              progress.echo(msg)
              channel.writeln(msg) },
            build_failed = { logic =>
              val msg = Build.build_logic_failed(logic, editor = true)
              progress.echo(msg)
              error(msg) })

        val session_resources = new VSCode_Resources(options, session_background, log)
        val session_options = prover_options.bool.update("editor_output_state", true)
        val session =
          new VSCode_Session(session_options, session_resources) {
            override def deps_changed(): Unit = start_loading()
          }

        Some((session_background, session))
      }
      catch { case ERROR(msg) => reply_error(msg); None }

    for ((session_background, session) <- try_session) {
      val store = Store(options)
      val session_heaps =
        store.session_heaps(session_background, logic = session_background.session_name)

      session_.change(_ => Some(session))

      session.commands_changed += prover_output
      session.syslog_messages += syslog_messages

      dynamic_output.init()
      sledgehammer.init()
      theories.init()
      simplifier_trace.init()
      graphview.init()
      infoview.init()
      query.init()

      val prelude = List(VSCode_Context_Names.prelude(log), VSCode_Sledgehammer.prelude(log)).flatten
      try {
        Isabelle_Process.start(
          prover_options, session, session_background, session_heaps,
          use_prelude = prelude.map(file => File.platform_path(File.path(file))),
          modes = modes).await_startup()
        reply_ok(
          "Welcome to Isabelle/" + session_background.session_name +
          Isabelle_System.isabelle_heading())
      }
      catch { case ERROR(msg) => reply_error(msg) }
      finally { prelude.foreach(_.delete) }
    }
  }

  /* Stop the prover, whoever asked.

     Factored out of "shutdown" so that end of input can reuse it: the two differ only in
     whether there is still a client to answer. */
  private def stop_session(): String =
    session_.change_result({
      case Some(session) =>
        session.commands_changed -= prover_output
        session.syslog_messages -= syslog_messages

        dynamic_output.exit()

        delay_load.revoke()
        file_watcher.shutdown()
        editor.revoke()
        delay_output.revoke()
        delay_caret_update.revoke()
        delay_preview.revoke()
        sledgehammer.exit()
        theories.exit()
        simplifier_trace.exit()
        graphview.exit()
        infoview.exit()
        query.exit()
        context_names.exit()

        val result = session.stop()
        ((if (result.ok) "" else "Prover shutdown failed: " + result.rc), None)
      case None => ("Prover inactive", None)
    })

  def shutdown(id: LSP.Id): Unit =
    channel.write(LSP.Shutdown.reply(id, stop_session()))

  def exit(): Unit = {
    log("\n")
    sys.exit(if (session_.value.isEmpty) Process_Result.RC.ok else Process_Result.RC.failure)
  }


  /* completion */

  /*semantic completion needs the prover's report on the word being typed: wait for it off
    the message loop, which has to keep receiving the edits that produce it*/
  def completion(id: LSP.Id, node_pos: Line.Node_Position): Unit = {
    val delay = completion_delay
    def pending(rendering: VSCode_Rendering, offset: Text.Offset): Boolean =
      rendering.completion_pending(offset, context_names)
    def complete(rendering: VSCode_Rendering, offset: Text.Offset)
        : (List[LSP.CompletionItem], Boolean) =
      rendering.completion(node_pos, offset, context_names)

    rendering_offset(node_pos) match {
      case Some((rendering, offset)) if !delay.is_zero && pending(rendering, offset) =>
        val content = rendering.model.content
        val deadline = Time.now() + delay
        Isabelle_Thread.fork(name = "completion", daemon = true) {
          @tailrec def wait(): Option[(VSCode_Rendering, Text.Offset)] =
            rendering_offset(node_pos) match {
              case Some((rendering1, _)) if rendering1.model.content ne content => None
              case Some((rendering1, offset1))
              if pending(rendering1, offset1) && Time.now() < deadline =>
                Time.seconds(0.05).sleep()
                wait()
              case res => res
            }
          val (result, incomplete) =
            try {
              wait().map({ case (rendering1, offset1) =>
                complete(rendering1, offset1) }).getOrElse((Nil, false))
            }
            catch { case exn: Throwable if !Exn.is_interrupt(exn) =>
              channel.log_error_message(Exn.message(exn))
              (Nil, false)
            }
          channel.write(LSP.Completion.reply(id, result, incomplete))
        }
      case res =>
        val (result, incomplete) =
          (for ((rendering, offset) <- res) yield complete(rendering, offset))
            .getOrElse((Nil, false))
        channel.write(LSP.Completion.reply(id, result, incomplete))
    }
  }


  /* spell-checker dictionary */

  def update_dictionary(include: Boolean, permanent: Boolean): Unit = {
    for {
      spell_checker <- resources.spell_checker.get
      caret <- resources.get_caret()
      rendering = resources.rendering(caret.model)
      range = rendering.before_caret_range(caret.offset)
      Text.Info(_, word) <- Spell_Checker.current_word(rendering, range)
    } {
      spell_checker.update(word, include, permanent)
      update_output_visible()
    }
  }

  def reset_dictionary(): Unit = {
    for (spell_checker <- resources.spell_checker.get) {
      spell_checker.reset()
      update_output_visible()
    }
  }


  /* hover */

  def hover(id: LSP.Id, node_pos: Line.Node_Position): Unit = {
    val result =
      for {
        (rendering, offset) <- rendering_offset(node_pos)
        info <- rendering.tooltips(VSCode_Rendering.tooltip_elements, Text.Range(offset, offset + 1))
      } yield {
        val range = rendering.model.content.doc.range(info.range)
        val contents = info.info.map(t => LSP.MarkedString(resources.output_pretty_tooltip(List(t))))
        (range, contents)
      }
    channel.write(LSP.Hover.reply(id, result))
  }


  /* goto definition */

  def goto_definition(id: LSP.Id, node_pos: Line.Node_Position): Unit = {
    val result =
      (for ((rendering, offset) <- rendering_offset(node_pos))
        yield rendering.hyperlinks(Text.Range(offset, offset + 1))) getOrElse Nil
    channel.write(LSP.GotoDefinition.reply(id, result))
  }


  /* references */

  /*a search through the markup of every loaded node: off the message loop, which has to keep
    receiving edits meanwhile*/
  def references(id: LSP.Id, node_pos: Line.Node_Position, include_declaration: Boolean): Unit =
    Isabelle_Thread.fork(name = "references", daemon = true) {
      val result =
        try {
          (for ((rendering, offset) <- rendering_offset(node_pos))
            yield VSCode_Entities.references(resources, rendering, offset, include_declaration))
            .getOrElse(Nil)
        }
        catch { case exn: Throwable if !Exn.is_interrupt(exn) =>
          channel.log_error_message(Exn.message(exn))
          Nil
        }
      channel.write(LSP.References.reply(id, result))
    }


  /* dependent theories */

  /*reads every given file: off the message loop*/
  def dependents(id: LSP.Id, node_pos: Line.Node_Position, files: List[JFile]): Unit =
    Isabelle_Thread.fork(name = "dependents", daemon = true) {
      val result =
        try {
          (for ((rendering, offset) <- rendering_offset(node_pos))
            yield VSCode_Entities.dependents(resources, rendering, offset, files))
            .getOrElse(VSCode_Entities.Dependents(Nil, Nil, Nil))
        }
        catch { case exn: Throwable if !Exn.is_interrupt(exn) =>
          channel.log_error_message(Exn.message(exn))
          VSCode_Entities.Dependents(Nil, Nil, Nil)
        }
      channel.write(LSP.Dependents_Request.reply(id, result.names, result.theories,
        result.in_image))
    }

  /*load the theories that are not yet, as required, and tell how far the prover is with
    each: asked again, until all are checked*/
  def check_theories(id: LSP.Id, files: List[JFile]): Unit = {
    if (resources.load_theories(session, editor, files, file_watcher)) {
      start_loading()
      editor.invoke()
    }
    val snapshot = session.snapshot()
    val now = Date.now()
    val result =
      for (file <- files) yield {
        val (status, percentage) =
          resources.get_model(file) match {
            case None => ("failed", 0)
            case Some(model) =>
              val name = model.node_name
              val node = snapshot.version.nodes(name)
              if (node.header.errors.nonEmpty) ("failed", 0)
              else if (node.commands.isEmpty) ("pending", 0)
              else {
                val st =
                  Document_Status.Node_Status.make(now, snapshot.state, snapshot.version, name)
                if (st.consolidated) (if (st.ok) "checked" else "failed", 100)
                else ("pending", st.percentage)
              }
          }
        LSP.Check_Theories.theory(file, status, percentage)
      }
    channel.write(LSP.Check_Theories.reply(id, result))
  }


  /* document highlights */

  def goto_command(id: Long, offset: Symbol.Offset): Unit =
    for {
      snapshot <- editor.current_node_snapshot(())
      hyperlink <- editor.hyperlink_command(snapshot, id, offset = offset, focus = true)
    } hyperlink.follow(())

  def document_highlights(id: LSP.Id, node_pos: Line.Node_Position): Unit = {
    val result =
      (for ((rendering, offset) <- rendering_offset(node_pos))
        yield {
          val model = rendering.model
          rendering.caret_focus_ranges(Text.Range(offset, offset + 1), model.content.text_range)
            .map(r => LSP.DocumentHighlight.text(model.content.doc.range(r)))
        }) getOrElse Nil
    channel.write(LSP.DocumentHighlights.reply(id, result))
  }


  /* code actions */

  def code_action_request(id: LSP.Id, file: JFile, range: Line.Range): Unit = {
    for {
      model <- resources.get_model(file)
      version <- model.version
      doc = model.content.doc
      text_range <- doc.text_range(range)
    } {
      val snapshot = resources.snapshot(model)
      val results =
        snapshot.command_results(Text.Range(text_range.start - 1, text_range.stop + 1))
          .iterator.map(_._2).toList
      val actions =
        List.from(
          for {
            (snippet, props) <- Protocol.sendback_snippets(results).iterator
            id <- Position.Id.unapply(props)
            (node, command) <- snapshot.find_command(id)
            start <- node.command_start(command)
            range = command.core_range + start
            current_text <- model.get_text(range)
          } yield {
            val line_range = doc.range(range)
            val edit_text =
              if (props.contains(Markup.PADDING_COMMAND)) {
                val whole_line = doc.lines(line_range.start.line)
                val indent = whole_line.text.takeWhile(_.isWhitespace)
                current_text + "\n" + Library.prefix_lines(indent, snippet)
              }
              else current_text + snippet
            val edit = LSP.TextEdit(line_range, resources.output_edit(edit_text))
            LSP.CodeAction(snippet, List(LSP.TextDocumentEdit(file, Some(version), List(edit))))
          })
      channel.write(LSP.CodeActionRequest.reply(id, actions))
    }
  }


  /* indentation */

  /*answered in any case: the client waits for the reply, and the message loop would only
    log a failure*/
  private def indent_edits(file: JFile)(edits: VSCode_Rendering => List[LSP.TextEdit])
      : List[LSP.TextEdit] =
    resources.get_rendering(file) match {
      case Some(rendering) =>
        try { edits(rendering) }
        catch {
          case exn: Throwable if !Exn.is_interrupt(exn) =>
            channel.log_error_message(Exn.message(exn))
            Nil
        }
      case None => Nil
    }

  def on_type_formatting(
    id: LSP.Id,
    file: JFile,
    pos: Line.Position,
    ch: String,
    format: VSCode_Indent.Format
  ): Unit = {
    val edits =
      indent_edits(file) { rendering =>
        ch match {
          case "\n" => VSCode_Indent.on_newline(rendering, pos, format)
          case " " => VSCode_Indent.on_space(rendering, pos, format)
          case _ => Nil
        }
      }
    channel.write(LSP.OnTypeFormatting.reply(id, edits))
  }

  def range_formatting(
    id: LSP.Id,
    file: JFile,
    range: Line.Range,
    format: VSCode_Indent.Format
  ): Unit = {
    val edits = indent_edits(file)(VSCode_Indent.on_range(_, range, format))
    channel.write(LSP.RangeFormatting.reply(id, edits))
  }


  /* abbrevs */

  def abbrevs_request(): Unit = {
    val syntax = session.resources.session_base.overall_syntax
    channel.write(LSP.Abbrevs_Request.reply(syntax.abbrevs))
  }


  def documentation_request(): Unit =
    channel.write(LSP.Documentation_Response(ml_settings))


  /* main loop */

  def start(): Unit = {
    log("Server started " + Date.now())

    def handle(json: JSON.T): Unit = {
      try {
        json match {
          case LSP.Initialize(id) => init(id)
          case LSP.Initialized() =>
          case LSP.Shutdown(id) => shutdown(id)
          case LSP.Exit() => exit()
          case LSP.DidOpenTextDocument(file, _, version, text) =>
            change_document(file, version, List(LSP.TextDocumentChange(None, text)))
            start_loading()
          case LSP.DidChangeTextDocument(file, version, changes) =>
            change_document(file, version, changes)
          case LSP.DidCloseTextDocument(file) => close_document(file)
          case LSP.Completion(id, node_pos) => completion(id, node_pos)
          case LSP.Include_Word() => update_dictionary(true, false)
          case LSP.Include_Word_Permanently() => update_dictionary(true, true)
          case LSP.Exclude_Word() => update_dictionary(false, false)
          case LSP.Exclude_Word_Permanently() => update_dictionary(false, true)
          case LSP.Reset_Words() => reset_dictionary()
          case LSP.Hover(id, node_pos) => hover(id, node_pos)
          case LSP.GotoDefinition(id, node_pos) => goto_definition(id, node_pos)
          case LSP.References(id, node_pos, include_declaration) =>
            references(id, node_pos, include_declaration)
          case LSP.Dependents_Request(id, node_pos, files) => dependents(id, node_pos, files)
          case LSP.Check_Theories(id, files) => check_theories(id, files)
          case LSP.Goto_Command(id, offset) => goto_command(id, offset)
          case LSP.DocumentHighlights(id, node_pos) => document_highlights(id, node_pos)
          case LSP.CodeActionRequest(id, file, range) => code_action_request(id, file, range)
          case LSP.OnTypeFormatting(id, file, pos, ch, format) =>
            on_type_formatting(id, file, pos, ch, format)
          case LSP.RangeFormatting(id, file, range, format) =>
            range_formatting(id, file, range, format)
          case LSP.Decoration_Request(file) => decoration_request(file)
          case LSP.Caret_Update(caret) => update_caret(caret)
          case LSP.Output_Set_Margin(margin) => dynamic_output.set_margin(margin)
          case LSP.State_Init(id) => State_Panel.init(id, server)
          case LSP.State_Exit(state_id) => State_Panel.exit(state_id)
          case LSP.State_Locate(state_id) => State_Panel.locate(state_id)
          case LSP.State_Update(state_id) => State_Panel.update(state_id)
          case LSP.State_Auto_Update(state_id, enabled) =>
            State_Panel.auto_update(state_id, enabled)
          case LSP.State_Set_Margin(state_id, margin) => State_Panel.set_margin(state_id, margin)
          case LSP.Preview_Request(file, column) => preview_request(file, column)
          case LSP.Abbrevs_Request() => abbrevs_request()
          case LSP.Documentation_Request() => documentation_request()
          case LSP.Theories_Request() => theories.request()
          case LSP.Graphview_Request() => graphview.request()
          case LSP.Infoview_Request() => infoview.request()
          case LSP.Infoview_Pin(id, file, pos) => infoview.pin(id, file, pos)
          case LSP.Infoview_Unpin(id) => infoview.unpin(id)
          case LSP.Infoview_Set_Margin(margin) => infoview.set_margin(margin)
          case LSP.Simplifier_Trace_Request() => simplifier_trace.request()
          case LSP.Simplifier_Trace_Reply(serial, answer) =>
            simplifier_trace.reply(serial, answer)
          case LSP.Simplifier_Trace_Auto_Update(enabled) =>
            simplifier_trace.set_auto_update(enabled)
          case LSP.Simplifier_Trace_Clear_Memory() => simplifier_trace.clear_memory()
          case LSP.Simplifier_Trace_Show() => simplifier_trace.show_trace()
          case LSP.Theories_Set_Threshold(threshold) => theories.set_threshold(threshold)
          case LSP.Query_Operations_Request() => query.operations_response()
          case LSP.Query_Request(operation, args) => query.request(operation, args)
          case LSP.Query_Cancel(operation) => query.cancel(operation)
          case LSP.Query_Locate(operation) => query.locate(operation)
          case LSP.Sledgehammer_Provers_Request() => sledgehammer.provers()
          case LSP.Sledgehammer_Request(args) => sledgehammer.request(args)
          case LSP.Sledgehammer_Cancel() => sledgehammer.cancel()
          case LSP.Sledgehammer_Locate() => sledgehammer.locate()
          case LSP.Sledgehammer_Sendback(text) => sledgehammer.sendback(text)
          case _ => if (!LSP.ResponseMessage.is_empty(json)) log("### IGNORED")
        }
      }
      catch { case exn: Throwable => channel.log_error_message(Exn.message(exn)) }
    }

    @tailrec def loop(): Unit = {
      channel.read() match {
        case Some(json) =>
          json match {
            case bulk: List[_] => bulk.foreach(handle)
            case _ => handle(json)
          }
          loop()
        /* End of input: the client is gone without having said "shutdown"/"exit", which
           is what happens whenever an editor dies rather than closes -- a killed process,
           a crashed extension host, a terminated terminal.

           Merely returning here leaves the session running, and with it the prover and
           this JVM: nothing else holds a reference to the client, so nothing else will
           ever notice. Editors that spawn the server therefore accumulated a full prover
           stack per abandoned run, and there is nobody left to be told about it. So treat
           EOF as the shutdown the client did not get to send. */
        case None =>
          log("### TERMINATE")
          stop_session()
          exit()
      }
    }
    loop()
  }
}
