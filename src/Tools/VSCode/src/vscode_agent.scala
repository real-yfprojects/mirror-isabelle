/*  Title:      Tools/VSCode/src/vscode_agent.scala

Prover access for AI agents, behind the extension's MCP tools: the messages of a theory and
the goals at a command as plain text -- in Isabelle's ASCII notation, as the theory file has
it, so that what an agent reads it may write back -- and proof candidates or Sledgehammer
run on the state before a command (vscode_agent.ML) without editing the text.
*/

package isabelle.vscode


import isabelle._

import java.io.{File => JFile}

import scala.annotation.tailrec


object VSCode_Agent {
  val try_function = "vscode_agent_try_query"
  val sledgehammer_function = "vscode_agent_sledgehammer_query"

  def prelude(log: Logger): Option[JFile] =
    Language_Server.ml_prelude("isabelle/vscode/vscode_agent.ML", "vscode_agent", log,
      "no proof candidates and Sledgehammer for AI agents")

  val margin = 100.0

  /*Isabelle/Scala holds prover output with its symbols decoded: back to the ASCII of the
    theory file, without the marker of a reported position*/
  def ascii(text: String): String = Symbol.encode(text).replace("\\<^here>", "")

  def plain(body: XML.Body): String =
    if (body.isEmpty) ""
    else ascii(Pretty.string_of(body, margin = margin, metric = Symbol.Metric))

  def plain_elems(output: List[XML.Elem]): String =
    if (output.isEmpty) "" else plain(Pretty.separate(output))

  private val message_elements = Markup.Elements(Markup.ERROR, Markup.WARNING, Markup.LEGACY)

  private def severity(name: String): String =
    name match {
      case Markup.ERROR | Markup.ERROR_MESSAGE | Markup.BAD => "error"
      case Markup.LEGACY | Markup.LEGACY_MESSAGE => "legacy"
      case _ => "warning"
    }

  private def first_line(command: Command): String = {
    val line = split_lines(command.source).map(_.trim).find(_.nonEmpty).getOrElse("")
    ascii(Symbol.explode(line).take(120).mkString)
  }

  private def is_goal(keywords: Keyword.Keywords, command: Command): Boolean = {
    val kind = keywords.kinds.getOrElse(command.span.name, "")
    Keyword.theory_goal(kind) || Keyword.proof_goal(kind)
  }

  /*the proper command before another one*/
  private def proper_before(node: Document.Node, command: Command): Option[Command] =
    node.commands.reverse.iterator(command).drop(1).find(_.is_proper)

  /*what a query reports: its data, or the error it ended with*/
  sealed case class Result(body: XML.Body, error: Option[String])
}

class VSCode_Agent(server: Language_Server) {
  import VSCode_Agent._

  private def resources: VSCode_Resources = server.resources

  private def line_of(model: VSCode_Model, snapshot: Document.Snapshot, command: Command): Int =
    snapshot.node.command_start(command).map(snapshot.convert) match {
      case Some(offset) => model.content.doc.position(offset min model.content.text_length).line
      case None => 0
    }

  /*the goals that a command works on: those the command before it left -- as printed, or
    else asked of the prover, which prints states only for the text around the caret*/
  private def goals_before(
    model: VSCode_Model,
    snapshot: Document.Snapshot,
    keywords: Keyword.Keywords,
    command: Command,
    ask: Boolean
  ): String =
    proper_before(snapshot.node, command) match {
      case Some(prev) =>
        VSCode_Infoview.levels(snapshot, keywords, prev)._1 match {
          case Some((_, goals)) => plain_elems(goals)
          case None if ask => print_state(model, prev).getOrElse("")
          case None => ""
        }
      case None => ""
    }

  /*the commands after which the goals of the levels around a command stand, innermost
    first: the one before each goal statement that opens a level, found by the keywords as
    in VSCode_Infoview.levels, which reads them off printed states instead*/
  private def enclosing(
    snapshot: Document.Snapshot,
    keywords: Keyword.Keywords,
    command: Command
  ): List[Command] = {
    val node = snapshot.node
    if (!node.commands.contains(command)) Nil
    else {
      val result = List.newBuilder[Command]
      val it = node.commands.reverse.iterator(command).filterNot(_.is_ignored)
      var depth = 0
      var done = false
      while (!done && it.hasNext) {
        val cmd = it.next()
        val kind = keywords.kinds.getOrElse(cmd.span.name, "")
        if (Keyword.qed(kind)) depth += 1
        else if (Keyword.qed_global(kind) || Keyword.theory_goal(kind)) done = true
        else if (Keyword.proof_goal(kind)) {
          if (depth > 0) depth -= 1
          else result ++= proper_before(node, cmd)
        }
        else if (kind.nonEmpty && !Keyword.proof(kind) && !Keyword.vacuous(kind)) done = true
      }
      result.result()
    }
  }

  /*the proof state after a command, from Pure's query operation print_state*/
  private def print_state(model: VSCode_Model, command: Command): Option[String] =
    query_on(model, command, "print_state_query", Nil, Time.now() + Time.seconds(15)) match {
      case Right(Result(body, None)) => Some(plain(body)).filter(_.nonEmpty)
      case _ => None
    }


  /* report: the status and messages of a theory */

  def report(file: JFile): JSON.Object.T =
    resources.get_rendering(file) match {
      case None => JSON.Object("error" -> "The theory is not loaded")
      case Some(rendering) =>
        val model = rendering.model
        val snapshot = rendering.snapshot
        val node = snapshot.node
        val doc = model.content.doc
        val keywords = model.syntax().keywords

        val st =
          Document_Status.Node_Status.make(Date.now(), snapshot.state, snapshot.version,
            model.node_name)

        val infos =
          snapshot.cumulate[Command.Results](
            model.content.text_range, Command.Results.empty, message_elements,
              command_states =>
                {
                  case (res, Text.Info(_, msg @ XML.Elem(Markup.Bad(i), body)))
                  if body.nonEmpty => Some(res + (i -> msg))
                  case (res, Text.Info(_, msg)) =>
                    Command.State.get_result_proper(command_states, msg.markup.properties)
                      .map(res + _)
                }).filterNot(_.info.is_empty)

        var asks = 5
        val messages =
          (for {
            Text.Info(range, results) <- infos.iterator
            (_, XML.Elem(Markup(name, _), body)) <- results.iterator
          } yield {
            val line_range = doc.range(range)
            val message = plain(body)
            val goal =
              if (severity(name) != "error") None
              else {
                /*most errors of proof methods show the goal already*/
                val ask = asks > 0 && !message.contains("goal (")
                if (ask) asks -= 1
                node.command_iterator(snapshot.revert(range.start)).nextOption().map(_._1)
                  .map(goals_before(model, snapshot, keywords, _, ask)).filter(_.nonEmpty)
              }
            JSON.Object(
              "severity" -> severity(name),
              "line" -> line_range.start.line,
              "character" -> line_range.start.column,
              "end_line" -> line_range.stop.line,
              "end_character" -> line_range.stop.column,
              "message" -> message) ++
            JSON.optional("goal" -> goal)
          }).toList

        def count(name: String): Int = node.commands.iterator.count(_.span.name == name)

        JSON.Object(
          "outdated" -> snapshot.is_outdated,
          "percentage" -> st.percentage,
          "consolidated" -> st.consolidated,
          "ok" -> st.ok,
          "failed_commands" -> st.failed,
          "unprocessed_commands" -> st.unprocessed,
          "sorry" -> count("sorry"),
          "oops" -> count("oops"),
          "messages" -> messages)
    }


  /* state: the goals and messages of the command at a position */

  def state(node_pos: Line.Node_Position): JSON.Object.T =
    server.rendering_offset(node_pos) match {
      case None => JSON.Object("error" -> "The theory is not loaded")
      case Some((rendering, offset)) =>
        val model = rendering.model
        val snapshot = rendering.snapshot
        val keywords = model.syntax().keywords
        snapshot.current_command(model.node_name, offset) match {
          case None => JSON.Object("error" -> "There is no command at this position")
          case Some(command) =>
            val (states, messages) = VSCode_Infoview.split(snapshot.command_results(command))
            val goals =
              if (states.exists(VSCode_Infoview.has_goal)) plain_elems(states)
              else print_state(model, command).getOrElse(plain_elems(states))
            val (current, outer) = VSCode_Infoview.levels(snapshot, keywords, command)
            def level_text(cmd: Command, goals: String): JSON.Object.T =
              JSON.Object(
                "line" -> line_of(model, snapshot, cmd),
                "command" -> cmd.span.name,
                "source" -> first_line(cmd),
                "goals" -> goals)
            def level(cmd: Command, goals: List[XML.Elem]): JSON.Object.T =
              level_text(cmd, plain_elems(goals))
            val outer_levels =
              if (outer.nonEmpty) outer.map({ case (cmd, goals) => level(cmd, goals) })
              else {
                for {
                  cmd <- enclosing(snapshot, keywords, command).take(4)
                  goals <- print_state(model, cmd)
                } yield level_text(cmd, goals)
              }
            JSON.Object(
              "outdated" -> snapshot.is_outdated,
              "line" -> line_of(model, snapshot, command),
              "command" -> command.span.name,
              "source" -> first_line(command),
              "status" -> VSCode_Infoview.status(snapshot, command),
              "goals" -> goals,
              "outer" -> outer_levels,
              "messages" -> plain_elems(messages)) ++
            JSON.optional("current" ->
              current.collect({ case (cmd, goals) if cmd != command => level(cmd, goals) }))
        }
    }


  /* queries: candidates and Sledgehammer, on the state before a command */

  /*the command whose state the query reads: the one before the command at the position --
    or that command itself, if it states a goal and the agent states none, so that the line
    of a lemma means its goal*/
  private def query_command(node_pos: Line.Node_Position, has_goal: Boolean)
      : Either[String, (VSCode_Model, Command)] =
    server.rendering_offset(node_pos) match {
      case None => Left("The theory is not loaded")
      case Some((rendering, offset)) =>
        val model = rendering.model
        val snapshot = rendering.snapshot
        if (snapshot.is_outdated) Left("outdated")
        else {
          val node = snapshot.node
          val keywords = model.syntax().keywords
          val at =
            node.command_iterator(snapshot.revert(offset)).nextOption().map(_._1) orElse
              node.commands.reverse.iterator.find(_.is_proper)
          at match {
            case None => Left("There is no command at this position")
            case Some(command) =>
              val target =
                if (!has_goal && command.is_proper && is_goal(keywords, command)) Some(command)
                else proper_before(node, command)
              target match {
                case Some(cmd) => Right((model, cmd))
                case None => Left("There is no command before this position")
              }
          }
        }
    }

  private def overlay(insert: Boolean, command: Command, function: String, args: List[String])
      : Unit =
    server.editor.send_dispatcher {
      if (insert) server.editor.insert_overlay(command, function, args)
      else server.editor.remove_overlay(command, function, args)
      server.editor.flush()
    }

  /*the result of an instance of a query, once it has finished*/
  private def result(snapshot: Document.Snapshot, command: Command, instance: String)
      : Option[Result] = {
    val bodies =
      (for {
        case (_, XML.Elem(Markup(Markup.RESULT, Markup.Instance(i)), body))
          <- snapshot.command_results(command).iterator
        if i == instance
      } yield body).toList
    val finished =
      bodies.exists({ case List(XML.Elem(Markup(Markup.FINISHED, _), _)) => true case _ => false })
    if (!finished) None
    else {
      val error =
        bodies.collectFirst({ case List(XML.Elem(Markup(Markup.ERROR, _), msg)) => plain(msg) })
      val data =
        bodies.filterNot({
          case List(XML.Elem(Markup(name, _), _)) =>
            name == Markup.RUNNING || name == Markup.FINISHED || name == Markup.ERROR
          case _ => false
        }).flatten
      Some(Result(data, error))
    }
  }

  /*runs a query and waits for it, off the message loop; the overlay goes when it is done,
    or the deadline passes, or the theory changes underneath*/
  private def run_query(
    node_pos: Line.Node_Position,
    has_goal: Boolean,
    function: String,
    args: List[String],
    deadline: Time
  ): Either[String, Result] = {
    @tailrec def locate(): Either[String, (VSCode_Model, Command)] =
      query_command(node_pos, has_goal) match {
        case Left("outdated") if Time.now() < deadline =>
          Time.seconds(0.1).sleep()
          locate()
        case Left("outdated") => Left("The theory is still being edited; try again")
        case res => res
      }

    locate() match {
      case Left(msg) => Left(msg)
      case Right((model, command)) => query_on(model, command, function, args, deadline)
    }
  }

  /*a query on the state after a command*/
  private def query_on(
    model: VSCode_Model,
    command: Command,
    function: String,
    args: List[String],
    deadline: Time
  ): Either[String, Result] = {
    val instance = Document_ID.make().toString
    val overlay_args = instance :: args
    overlay(true, command, function, overlay_args)

    @tailrec def wait(): Either[String, Result] = {
      val snapshot = resources.snapshot(model)
      if (!snapshot.is_outdated && !snapshot.node.commands.contains(command)) {
        Left("The theory changed at this position while the prover worked; try again")
      }
      else {
        result(snapshot, command, instance) match {
          case Some(res) => Right(res)
          case None if Time.now() < deadline =>
            Time.seconds(0.05).sleep()
            wait()
          case None =>
            val status = VSCode_Infoview.status(snapshot, command)
            Left(
              if (status == "unprocessed" || status == "running") {
                "The prover has not reached this position yet (the command before it is " +
                  status + "): check the theory first, or allow more time"
              }
              else "The prover did not answer in time")
        }
      }
    }

    try { wait() }
    finally { overlay(false, command, function, overlay_args) }
  }

  private def json_props(props: Properties.T): JSON.Object.T =
    JSON.Object(props.map({ case (a, b) => a -> ascii(b) }): _*)

  def try_candidates(
    node_pos: Line.Node_Position,
    goal: String,
    candidates: List[String],
    timeout_ms: Int,
    stats: Boolean,
    watch_rules: List[String],
    watch_patterns: List[String],
    watch_limit: Int,
    deadline: Time
  ): JSON.Object.T = {
    /*plain strings: overlay arguments travel as YXML themselves*/
    def counted(xs: List[String]): List[String] = xs.length.toString :: xs
    val args =
      List(goal, timeout_ms.toString, if (stats) "true" else "", watch_limit.toString) :::
        counted(candidates) ::: counted(watch_rules) ::: counted(watch_patterns)
    run_query(node_pos, goal.nonEmpty, try_function, args, deadline) match {
      case Left(msg) => JSON.Object("error" -> msg)
      case Right(Result(_, Some(error))) => JSON.Object("error" -> error)
      case Right(Result(body, None)) =>
        try {
          import XML.Decode._
          val (header, cands) =
            pair(properties,
              list(pair(properties, pair(list(pair(string, pair(int, int))),
                pair(list(string), list(properties))))))(body)
          json_props(header) +
            ("candidates" -> cands.map({ case (props, (stats, (cycle, steps))) =>
              json_props(props) ++
              JSON.Object(
                "stats" -> stats.map({ case (rule, (applied, failed)) =>
                  JSON.Object("rule" -> ascii(rule), "applied" -> applied,
                    "condition_failed" -> failed) }),
                "cycle" -> cycle.map(ascii),
                "steps" -> steps.map(json_props))
            }))
        }
        catch { case _: XML.Error => JSON.Object("error" -> "Bad answer from the prover") }
    }
  }

  def sledgehammer(
    node_pos: Line.Node_Position,
    goal: String,
    timeout_s: Int,
    deadline: Time
  ): JSON.Object.T =
    run_query(node_pos, goal.nonEmpty, sledgehammer_function,
      List(goal, timeout_s.toString), deadline) match {
      case Left(msg) => JSON.Object("error" -> msg)
      case Right(Result(_, Some(error))) => JSON.Object("error" -> error)
      case Right(Result(body, None)) =>
        try { JSON.Object("messages" -> XML.Decode.list(XML.Decode.string)(body).map(ascii)) }
        catch { case _: XML.Error => JSON.Object("error" -> "Bad answer from the prover") }
    }
}
