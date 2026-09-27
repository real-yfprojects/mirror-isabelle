/*  Title:      Tools/VSCode/src/vscode_context_names.scala

The names visible in a formal context, for completion within inner syntax (terms, props,
types): there the prover reports names only for a name that it rejects, and a word being
typed is merely a free variable. A query operation (vscode_completion.ML) lists them all,
once for each command whose context is asked for, and completion filters that list.
*/

package isabelle.vscode


import isabelle._

import java.io.{File => JFile}

import scala.annotation.tailrec


object VSCode_Context_Names {
  type Name = (String, (String, String))  /*external name, kind, internal name*/

  val print_function = "vscode_context_names_query"


  /* ML prelude: the query operation, as a resource of this module */

  /*loaded into the prover at startup rather than compiled into Pure, so that it needs no
    heap of its own: isabelle-vscode's extended server brings it to a released distribution
    as part of a jar*/
  private val ml_resource = "isabelle/vscode/vscode_completion.ML"

  def prelude(log: Logger): Option[JFile] = {
    val loader = getClass.getClassLoader
    val stream = if (loader == null) null else loader.getResourceAsStream(ml_resource)
    if (stream == null) {
      log("No " + ml_resource + ": no completion of names within inner syntax")
      None
    }
    else {
      val text = using(stream)(s => new String(s.readAllBytes, UTF8.charset))
      val file = Isabelle_System.tmp_file("vscode_completion", ext = "ML")
      File.write(file, text)
      Some(file)
    }
  }


  /* matching */

  /*roughly what VS Code's own filter accepts: the first character of the word at the start
    of a part of the name, the others in order after it, ignoring case. So the list covers
    every extension of the word, and VS Code narrows it down by itself as the word grows*/
  def matches(word: String, xname: String, anywhere: Boolean = true): Boolean = {
    val w = Word.lowercase(word)
    val x = Word.lowercase(xname)

    @tailrec def rest(i: Int, j: Int): Boolean =
      i == w.length || (j < x.length && rest(if (x(j) == w(i)) i + 1 else i, j + 1))

    def start(j: Int): Boolean =
      j == 0 || anywhere && (x(j - 1) == '.' || x(j - 1) == '_')

    w.nonEmpty && x.indices.exists(j => start(j) && x(j) == w(0) && rest(1, j + 1))
  }

  /*a word with a qualifier ("PosReal.", "PosReal.pp") asks for the names under it: those
    that begin with it, the rest of the word matched as a word*/
  private def matches_qualified(qualifier: String, rest: String, xname: String): Boolean =
    xname.startsWith(qualifier) && (rest.isEmpty || matches(rest, xname.drop(qualifier.length)))

  private def kind_rank(kind: String): Int =
    kind match {
      case Markup.FIXED => 0
      case Markup.CONSTANT => 1
      case _ => 2
    }

  /*the names for a word, fixed variables first, and whether there are more than the limit.
    A name comes in each form that refers to it, the shortest first; a longer, qualified form
    only when the word begins it or names its qualifier -- otherwise List.append would follow
    append everywhere*/
  def select(names: List[Name], word: String, types_only: Boolean, limit: Int)
      : (List[Name], Boolean) = {
    val qualified =
      word.lastIndexOf('.') match {
        case -1 => None
        case i => Some((word.take(i + 1), word.drop(i + 1)))
      }
    val seen = scala.collection.mutable.Set.empty[(String, String)]
    val selected =
      names.filter({ case (xname, entity @ (kind, _)) =>
        val shortest = seen.add(entity)
        (!types_only || kind == Markup.TYPE_NAME) &&
          (qualified match {
            case Some((qualifier, rest)) => matches_qualified(qualifier, rest, xname)
            case None => matches(word, xname, anywhere = shortest)
          })
      })
      .sortBy({ case (xname, (kind, _)) =>
        (kind_rank(kind), !xname.startsWith(word), xname.length, xname) })
    (selected.take(limit), selected.length > limit)
  }


  /* entries */

  private sealed case class Entry(command: Command, instance: String, names: Option[List[Name]])

  private val max_entries = 4
}

class VSCode_Context_Names(server: Language_Server, limit: Int) {
  import VSCode_Context_Names.{Name, Entry}

  def completion_limit: Int = limit

  /*most recent first*/
  private val entries = Synchronized(List.empty[Entry])


  /* context: the command before the one at an offset of the current text */

  def context_command(snapshot: Document.Snapshot, offset: Text.Offset): Option[Command] = {
    val node = snapshot.node

    @tailrec def proper_before(command: Command): Option[Command] =
      node.commands.prev(command) match {
        case Some(command1) if !command1.is_proper => proper_before(command1)
        case res => res
      }

    for {
      (command, _) <- node.command_iterator(snapshot.revert(offset)).nextOption()
      context <- proper_before(command)
    } yield context
  }


  /* overlays */

  private def overlay(insert: Boolean, entry: Entry): Unit =
    server.editor.send_dispatcher {
      val fn = VSCode_Context_Names.print_function
      val args = List(entry.instance)
      if (insert) server.editor.insert_overlay(entry.command, fn, args)
      else server.editor.remove_overlay(entry.command, fn, args)
      server.editor.flush()
    }


  /* names */

  /*the result of the query, if it is there: its names, or none when it failed*/
  private def result(snapshot: Document.Snapshot, entry: Entry): Option[List[Name]] = {
    val results =
      for {
        case (_, XML.Elem(Markup(Markup.RESULT, Markup.Instance(instance)), body))
          <- snapshot.command_results(entry.command).iterator
        if instance == entry.instance
      } yield body

    val decoded =
      results.flatMap(body =>
        try {
          import XML.Decode._
          Some(pair(int, list(pair(string, pair(string, string))))(body)._2)
        }
        catch { case _: XML.Error => None }).nextOption()

    decoded orElse {
      val finished =
        snapshot.command_results(entry.command).iterator.exists(
          {
            case (_, XML.Elem(Markup(Markup.RESULT, Markup.Instance(instance)),
                List(XML.Elem(Markup(Markup.FINISHED, _), _)))) => instance == entry.instance
            case _ => false
          })
      if (finished) Some(Nil) else None
    }
  }

  /*the names visible to the text after a command, or None while the prover has yet to
    report them: asks for them at once*/
  def get(snapshot: Document.Snapshot, command: Command): Option[List[Name]] = {
    val (res, inserted, removed) =
      entries.change_result { list =>
        list.find(_.command == command) match {
          case Some(Entry(_, _, Some(names))) => ((Some(names), None, Nil), list)
          case Some(entry) =>
            result(snapshot, entry) match {
              case Some(names) =>
                val entry1 = entry.copy(names = Some(names))
                ((Some(names), None, List(entry)), entry1 :: list.filterNot(_ == entry))
              case None => ((None, None, Nil), list)
            }
          case None =>
            val entry = Entry(command, Document_ID.make().toString, None)
            val (keep, drop) = (entry :: list).splitAt(VSCode_Context_Names.max_entries)
            ((None, Some(entry), drop.filter(_.names.isEmpty)), keep)
        }
      }
    inserted.foreach(overlay(true, _))
    removed.foreach(overlay(false, _))
    res
  }

  def exit(): Unit = entries.change(_ => Nil)
}
