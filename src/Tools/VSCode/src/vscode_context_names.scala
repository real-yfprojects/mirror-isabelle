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

  /*what the query reports: the names of a context, and its parameters of class instances
    (plus_nat_inst.plus_nat), which completion never offers*/
  sealed case class Context(names: List[Name], inst_params: Set[String])

  val no_context: Context = Context(Nil, Set.empty)


  /* the prover's own reports */

  private val constant_prefix = Markup.CONSTANT + "."

  private def constant_of(item: Completion.Item): Option[String] =
    if (item.name.startsWith(constant_prefix)) Some(item.name.drop(constant_prefix.length))
    else None

  def has_constants(result: Completion.Result): Boolean =
    result.items.exists(constant_of(_).isDefined)

  /*a report of the prover without the parameters of class instances -- which it lists
    along with the other constants for a name that it rejects: exactly by the context's
    list, or by their shape (<class>_<type>_inst.<const>_<type>) while that is to come*/
  def without_inst_params(result: Completion.Result, inst_params: Option[Set[String]])
      : Option[Completion.Result] = {
    def is_param(c: String): Boolean =
      inst_params match {
        case Some(params) => params(c)
        case None =>
          Long_Name.explode(c).reverse match {
            case _ :: qualifier :: _ => qualifier.endsWith("_inst")
            case _ => false
          }
      }
    val items = result.items.filterNot(item => constant_of(item).exists(is_param))
    if (items.isEmpty) None else Some(result.copy(items = items))
  }


  /* ML prelude: the query operation, as a resource of this module */

  def prelude(log: Logger): Option[JFile] =
    Language_Server.ml_prelude("isabelle/vscode/vscode_completion.ML", "vscode_completion",
      log, "no completion of names within inner syntax")


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

  private sealed case class Entry(command: Command, instance: String, context: Option[Context])

  private val max_entries = 4
}

class VSCode_Context_Names(server: Language_Server, limit: Int) {
  import VSCode_Context_Names.{Context, Entry}

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

  /*the result of the query, if it is there: its context, or an empty one when it failed*/
  private def result(snapshot: Document.Snapshot, entry: Entry): Option[Context] = {
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
          val (names, inst_params) =
            pair(list(pair(string, pair(string, string))), list(string))(body)
          Some(Context(names, inst_params.toSet))
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
      if (finished) Some(VSCode_Context_Names.no_context) else None
    }
  }

  /*the context of the text after a command, or None while the prover has yet to report
    it: asks for it at once*/
  def get(snapshot: Document.Snapshot, command: Command): Option[Context] = {
    val (res, inserted, removed) =
      entries.change_result { list =>
        list.find(_.command == command) match {
          case Some(Entry(_, _, Some(context))) => ((Some(context), None, Nil), list)
          case Some(entry) =>
            result(snapshot, entry) match {
              case Some(context) =>
                val entry1 = entry.copy(context = Some(context))
                ((Some(context), None, List(entry)), entry1 :: list.filterNot(_ == entry))
              case None => ((None, None, Nil), list)
            }
          case None =>
            val entry = Entry(command, Document_ID.make().toString, None)
            val (keep, drop) = (entry :: list).splitAt(VSCode_Context_Names.max_entries)
            ((None, Some(entry), drop.filter(_.context.isEmpty)), keep)
        }
      }
    inserted.foreach(overlay(true, _))
    removed.foreach(overlay(false, _))
    res
  }

  def exit(): Unit = entries.change(_ => Nil)
}
