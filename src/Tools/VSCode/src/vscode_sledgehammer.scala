/*  Title:      Tools/VSCode/src/vscode_sledgehammer.scala
    Author:     Diana Korchmar, LMU Muenchen
    Author:     Makarius

Control panel for Sledgehammer.

Besides the panel's query operation, which runs on one command and ends when that command
is edited, there are jobs: runs of their own (vscode_sledgehammer.ML), several at a time,
which go on while the text changes. A job starts as a query, whose print function only takes
the proof state and forks the run in a group of its own; its messages come back as protocol
messages, and go to the client as PIDE/sledgehammer_job_update. Its position is the
client's to follow through edits.
*/

package isabelle.vscode


import isabelle._

import java.io.{File => JFile}


object VSCode_Sledgehammer {
  /* ML prelude: the query operation below the checking of the document */

  def prelude(log: Logger): Option[JFile] =
    Language_Server.ml_prelude("isabelle/vscode/vscode_sledgehammer.ML", "vscode_sledgehammer",
      log, "while Sledgehammer runs, edits wait for its queued prover slices")


  /* jobs */

  val job_function = "vscode_sledgehammer_job_query"
  val job_protocol = "vscode_sledgehammer_job"
  val job_cancel_command = "vscode_sledgehammer_job.cancel"

  /*how long a job waits for the prover to reach its command*/
  val start_timeout: Time = Time.minutes(10)

  /*a job that has a slot: started once its print function has forked the run*/
  private sealed case class Active(params: LSP.Sledgehammer_Job_Params, started: Boolean)

  private sealed case class Jobs(
    max_parallel: Int = 2,
    queue: List[LSP.Sledgehammer_Job_Params] = Nil,
    active: Map[String, Active] = Map.empty,
    cancelled: Set[String] = Set.empty)

  /*what a job that someone waits for has said: messages as plain text, and how it ended*/
  private sealed case class Waiting(messages: List[String] = Nil, end: Option[Either[String, Unit]] = None)
}


class VSCode_Sledgehammer(server: Language_Server) {
  import VSCode_Sledgehammer._

  private val query_operation =
    new Query_Operation(server.editor, (), "sledgehammer", consume_status, consume_output)

  private def consume_status(status: Query_Operation.Status): Unit = {
    val message =
      status match {
        case Query_Operation.Status.waiting => "Waiting for evaluation of context ..."
        case Query_Operation.Status.running => "Sledgehammering ..."
        case Query_Operation.Status.finished => "Finished"
      }
    server.channel.write(LSP.Sledgehammer_Status(message))
  }

  private def consume_output(output: Editor.Output): Unit = {
    val content = XML.string_of_body(Pretty.unbreakable(output.messages))
    server.channel.write(LSP.Sledgehammer_Output(content))
  }

  def provers(): Unit =
    server.channel.write(
      LSP.Sledgehammer_Provers_Response(server.options.string("sledgehammer_provers")))

  def request(args: List[String]): Unit =
    server.editor.send_dispatcher { query_operation.apply_query(args) }

  def sendback(text: String): Unit =
    server.editor.send_dispatcher {
      for {
        (snapshot, command) <- query_operation.query_command()
        node_pos <- snapshot.find_command_position(command.id, 0)
      } {
        val node_pos1 = node_pos.advance(command.source(command.core_range))
        server.channel.write(LSP.Sledgehammer_Insert(node_pos1, text))
      }
    }

  def cancel(): Unit = server.editor.send_dispatcher { query_operation.cancel_query() }
  def locate(): Unit = server.editor.send_dispatcher { query_operation.locate_query() }


  /* jobs */

  private val jobs = Synchronized(Jobs())
  private val waiting = Synchronized(Map.empty[String, Waiting])

  private def update(id: String, status: String, message: String = "",
      proofs: List[String] = Nil, outcome: String = "", error: String = "",
      range: Option[Line.Range] = None): Unit =
    server.channel.write(LSP.Sledgehammer_Job_Update(id, status, message = message,
      proofs = proofs, outcome = outcome, error = error, range = range))

  /*a job's slot is free: the next one in the queue gets it*/
  private def finish(id: String, status: String, outcome: String = "", error: String = "")
      : Unit = {
    val (was_active, next) =
      jobs.change_result({ st =>
        if (!st.active.isDefinedAt(id)) ((false, Nil), st)
        else {
          val st1 = st.copy(active = st.active - id, cancelled = st.cancelled - id)
          val free = st1.max_parallel - st1.active.size
          val (next, rest) = st1.queue.splitAt(free max 0)
          ((true, next),
            st1.copy(queue = rest, active = st1.active ++ next.map(p => p.id -> Active(p, false))))
        }
      })
    if (was_active) {
      update(id, status, outcome = outcome, error = error)
      waiting.change(w => w.get(id) match {
        case Some(job) =>
          w + (id -> job.copy(end = Some(if (status == "error") Left(error) else Right(()))))
        case None => w
      })
    }
    next.foreach(launch)
  }

  private def is_cancelled(id: String): Boolean = jobs.value.cancelled(id)

  /*the query that starts a job: it holds its slot from now on. A command edited before the
    prover got to it is looked for again at the same position*/
  private def launch(p: LSP.Sledgehammer_Job_Params): Unit =
    Isabelle_Thread.fork(name = "sledgehammer_job", daemon = true) {
      update(p.id, "starting")
      val deadline = Time.now() + start_timeout
      val args =
        List(p.id, p.goal, p.subgoal.toString, p.facts) :::
          p.params.flatMap({
            case ("cache_dir", dir) if dir.nonEmpty =>
              List("cache_dir", File.standard_path(new JFile(dir)))
            case (a, b) => List(a, b)
          })
      @scala.annotation.tailrec def start(): Either[String, VSCode_Agent.Result] =
        server.agent.run_query(p.node_pos, p.goal.nonEmpty, job_function, args, deadline,
          at_command = p.at_command, stop = () => is_cancelled(p.id)) match {
          case Left(VSCode_Agent.changed_message) if Time.now() < deadline && !is_cancelled(p.id) =>
            start()
          case res => res
        }
      try {
        start() match {
          /*the run is forked: cancelled meanwhile, it is told to stop*/
          case Right(VSCode_Agent.Result(_, None, range)) =>
            val cancel_now =
              jobs.change_result(st =>
                st.active.get(p.id) match {
                  case Some(job) =>
                    (st.cancelled(p.id),
                      st.copy(active = st.active + (p.id -> job.copy(started = true))))
                  case None => (true, st)
                })
            if (cancel_now) { send_cancel(p.id); finish(p.id, "cancelled") }
            else update(p.id, "running", range = range)
          case _ if is_cancelled(p.id) => finish(p.id, "cancelled")
          case Right(VSCode_Agent.Result(_, Some(error), _)) => finish(p.id, "error", error = error)
          case Left(error) => finish(p.id, "error", error = error)
        }
      }
      catch {
        case exn: Throwable if !Exn.is_interrupt(exn) =>
          finish(p.id, "error", error = Exn.message(exn))
      }
    }

  private def send_cancel(id: String): Unit =
    server.session.protocol_command_raw(job_cancel_command, List(Bytes(id)))

  def job_start(p: LSP.Sledgehammer_Job_Params): Unit = {
    val now =
      jobs.change_result({ st0 =>
        val st = if (p.max_parallel > 0) st0.copy(max_parallel = p.max_parallel) else st0
        if (st.active.isDefinedAt(p.id) || st.queue.exists(_.id == p.id)) (None, st)
        else if (st.active.size < st.max_parallel) {
          (Some(true), st.copy(active = st.active + (p.id -> Active(p, false))))
        }
        else (Some(false), st.copy(queue = st.queue :+ p))
      })
    now match {
      case Some(true) => launch(p)
      case Some(false) => update(p.id, "queued")
      case None =>
    }
  }

  /*ends the job at once for the client; a run in the prover is told to stop, and what it
    still says is ignored*/
  def job_cancel(id: String): Unit = {
    val (queued, started) =
      jobs.change_result({ st =>
        if (st.queue.exists(_.id == id)) ((true, false), st.copy(queue = st.queue.filterNot(_.id == id)))
        else {
          st.active.get(id) match {
            case Some(job) => ((false, job.started), st.copy(cancelled = st.cancelled + id))
            case None => ((false, false), st)
          }
        }
      })
    if (queued) {
      update(id, "cancelled")
      waiting.change(w => w.get(id).fold(w)(job => w + (id -> job.copy(end = Some(Left("Cancelled"))))))
    }
    else if (started) {
      send_cancel(id)
      finish(id, "cancelled")
    }
    /*not yet started: the query that starts it sees the cancellation and ends it*/
  }

  /*a protocol message of the run: a message, or how it ended*/
  private def receive(msg: Prover.Protocol_Output): Boolean =
    (Properties.get(msg.properties, "id"), Properties.get(msg.properties, "kind")) match {
      case (Some(id), Some(kind)) =>
        val active = jobs.value.active.get(id)
        kind match {
          case "message" =>
            for (job <- active if !is_cancelled(id)) {
              val body = Symbol.decode_yxml(msg.text)
              val proofs =
                Protocol.sendback_snippets(body).map({ case (s, _) => server.resources.output_edit(s) })
              update(id, "running", message = XML.string_of_body(Pretty.unbreakable(body)),
                proofs = proofs)
              waiting.change(w => w.get(id).fold(w)(job =>
                w + (id -> job.copy(messages = job.messages :+ VSCode_Agent.ascii(XML.content(body))))))
              if (proofs.nonEmpty && job.params.stop_at_first) {
                send_cancel(id)
                finish(id, "finished", outcome = "some")
              }
            }
          case "finished" => finish(id, "finished", outcome = msg.text)
          case "cancelled" => finish(id, "cancelled")
          case "error" => finish(id, "error", error = msg.text)
          case _ =>
        }
        true
      case _ => false
    }

  private class Job_Handler extends Session.Protocol_Handler {
    override def functions: Session.Protocol_Functions = List(job_protocol -> receive)
  }

  /*a job that the caller waits for, as the agent does: its messages as plain text, or why it
    ended without*/
  def run_job(p: LSP.Sledgehammer_Job_Params, deadline: Time): Either[String, List[String]] = {
    waiting.change(_ + (p.id -> Waiting()))
    try {
      job_start(p)
      @scala.annotation.tailrec def wait(): Either[String, List[String]] = {
        val job = waiting.value(p.id)
        job.end match {
          case Some(Left(error)) => Left(error)
          case Some(Right(())) => Right(job.messages)
          case None if Time.now() < deadline =>
            Time.seconds(0.05).sleep()
            wait()
          case None =>
            job_cancel(p.id)
            Left("Sledgehammer did not finish in time")
        }
      }
      wait()
    }
    finally { waiting.change(_ - p.id) }
  }

  def init(): Unit = {
    query_operation.activate()
    server.session.init_protocol_handler(new Job_Handler)
  }

  def exit(): Unit = {
    query_operation.deactivate()
    jobs.change(_ => Jobs())
  }
}
