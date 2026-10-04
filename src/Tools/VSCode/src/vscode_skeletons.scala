/*  Title:      Tools/VSCode/src/vscode_skeletons.scala

Code skeletons as code actions: an Isar sketch of a pending goal, subgoal blocks for a proof
script, and what an instantiation still lacks. A query operation (vscode_skeletons.ML)
computes them from the state after a command, once for each command asked for; and the
sendbacks of a command's results -- found proofs and Isabelle's own outline of a proof
method's cases -- get a title and a kind.
*/

package isabelle.vscode


import isabelle._

import java.io.{File => JFile}

import scala.annotation.tailrec


object VSCode_Skeletons {
  val print_function = "vscode_skeletons_query"

  sealed case class Skeleton(title: String, kind: String, text: String) {
    def code_action_kind: String =
      if (kind == "skeleton") LSP.CodeActionKind.skeleton else LSP.CodeActionKind.suggestion
  }


  /* ML prelude */

  def prelude(log: Logger): Option[JFile] =
    Language_Server.ml_prelude("isabelle/vscode/vscode_skeletons.ML", "vscode_skeletons",
      log, "no code skeletons")


  /* sendbacks */

  /*Proof_Context.print_cases_proof: each top-level case indented by two spaces, "qed" last*/
  private val outline_case = """^  case\b""".r

  def is_outline(snippet: String): Boolean =
    outline_case.findPrefixOf(snippet).isDefined &&
      snippet.linesIterator.filter(_.trim.nonEmpty).toList.lastOption.contains("qed")

  def sendback_title(snippet: String): (String, String) =
    if (is_outline(snippet)) {
      val cases = snippet.linesIterator.count(outline_case.findPrefixOf(_).isDefined)
      ("Insert proof outline (" + cases + (if (cases == 1) " case)" else " cases)"),
        LSP.CodeActionKind.outline)
    }
    else {
      val lines = snippet.linesIterator.map(_.trim).filter(_.nonEmpty).toList
      val title =
        lines match {
          case List(line) => "Insert proof: " + line
          case line :: _ => "Insert proof: " + line + " … (" + lines.length + " lines)"
          case Nil => "Insert proof"
        }
      (title, LSP.CodeActionKind.proof)
    }


  /* commands that may have skeletons */

  /*which skeletons a command may have, if any: those of a proof, or of an instantiation*/
  sealed abstract class Target
  case object Proof_Target extends Target
  case object Instantiation_Target extends Target

  def target(keywords: Keyword.Keywords, command: Command): Option[Target] = {
    val name = command.span.name
    val kind = keywords.kinds.getOrElse(name, "")
    if (Keyword.theory_goal(kind) || Keyword.proof_goal(kind) || Keyword.prf_script(kind)) {
      Some(Proof_Target)
    }
    else if (name == "instantiation" || Keyword.theory_defn(kind)) Some(Instantiation_Target)
    else None
  }

  /*a proof that is only a placeholder, which a skeleton replaces*/
  private val placeholders = Set("sorry", "oops")

  /*where a skeleton goes: right after the command, where the text does not continue the
    proof or the instantiation already (Some(None)); or in place of a placeholder proof
    after it (Some(Some(placeholder)))*/
  def placement(
    keywords: Keyword.Keywords,
    node: Document.Node,
    command: Command,
    target: Target
  ): Option[Option[Command]] = {
    @tailrec def next_proper(command: Command): Option[Command] =
      node.commands.next(command) match {
        case Some(command1) if !command1.is_proper => next_proper(command1)
        case res => res
      }
    next_proper(command) match {
      case None => Some(None)
      case Some(next) =>
        val kind = keywords.kinds.getOrElse(next.span.name, "")
        target match {
          case Proof_Target if placeholders(next.span.name) => Some(Some(next))
          case Proof_Target => if (Keyword.proof(kind)) None else Some(None)
          case Instantiation_Target => if (Keyword.theory_end(kind)) Some(None) else None
        }
    }
  }


  /* entries */

  private sealed case class Entry(
    command: Command, instance: String, skeletons: Option[List[Skeleton]])

  private val max_entries = 8
}

class VSCode_Skeletons(server: Language_Server) {
  import VSCode_Skeletons.{Entry, Skeleton}

  /*most recent first*/
  private val entries = Synchronized(List.empty[Entry])


  /* overlays */

  private def overlay(insert: Boolean, entry: Entry): Unit =
    server.editor.send_dispatcher {
      val fn = VSCode_Skeletons.print_function
      val args = List(entry.instance)
      if (insert) server.editor.insert_overlay(entry.command, fn, args)
      else server.editor.remove_overlay(entry.command, fn, args)
      server.editor.flush()
    }


  /* skeletons */

  /*the result of the query, if it is there; none when it failed*/
  private def result(snapshot: Document.Snapshot, entry: Entry): Option[List[Skeleton]] = {
    val results =
      snapshot.command_results(entry.command).iterator.collect(
        { case (_, XML.Elem(Markup(Markup.RESULT, Markup.Instance(instance)), body))
            if instance == entry.instance => body })
    results.flatMap(body =>
      body match {
        case List(XML.Elem(Markup(Markup.FINISHED, _), _)) => Some(Nil)
        case _ =>
          try {
            import XML.Decode._
            Some(list(pair(string, pair(string, string)))(body).map(
              { case (title, (kind, text)) => Skeleton(title, kind, text) }))
          }
          catch { case _: XML.Error => None }
      }).nextOption()
  }

  /*the skeletons for the text after a command, or None while the prover has yet to report
    them: asks for them at once*/
  def get(snapshot: Document.Snapshot, command: Command): Option[List[Skeleton]] = {
    val (res, inserted, removed) =
      entries.change_result { list =>
        list.find(_.command == command) match {
          case Some(Entry(_, _, Some(skeletons))) => ((Some(skeletons), None, Nil), list)
          case Some(entry) =>
            result(snapshot, entry) match {
              case Some(skeletons) =>
                val entry1 = entry.copy(skeletons = Some(skeletons))
                ((Some(skeletons), None, List(entry)), entry1 :: list.filterNot(_ == entry))
              case None => ((None, None, Nil), list)
            }
          case None =>
            val entry = Entry(command, Document_ID.make().toString, None)
            val (keep, drop) = (entry :: list).splitAt(VSCode_Skeletons.max_entries)
            ((None, Some(entry), drop.filter(_.skeletons.isEmpty)), keep)
        }
      }
    inserted.foreach(overlay(true, _))
    removed.foreach(overlay(false, _))
    res
  }

  def exit(): Unit = entries.change(_ => Nil)
}
