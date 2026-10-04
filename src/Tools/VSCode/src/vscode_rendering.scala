/*  Title:      Tools/VSCode/src/vscode_rendering.scala
    Author:     Makarius

Isabelle/VSCode-specific implementation of quasi-abstract rendering and
markup interpretation.
*/

package isabelle.vscode


import isabelle._

import java.io.{File => JFile}

import scala.annotation.tailrec


object VSCode_Rendering {
  /* completion */

  /*the names the prover reported for the words typed from one start: VS Code filters them
    itself (fuzzy, as the word grows), so they are kept whole rather than narrowed down --
    a complete list for a word covers every extension of it*/
  sealed case class Semantic_Cache(
    node_name: Document.Node.Name,
    start: Text.Offset,
    original: String,
    names: List[(String, (String, String))],
    complete: Option[String]
  ) {
    def covers(word: String): Boolean = complete.exists(word.startsWith)

    def add(word: String, more: Completion.Names): Semantic_Cache = {
      val fresh = more.names.toSet
      copy(
        names = more.names ::: names.filterNot(fresh),
        complete = complete orElse (if (more.total <= more.names.length) Some(word) else None))
    }
  }

  object Semantic_Cache {
    def make(
      node_name: Document.Node.Name,
      start: Text.Offset,
      word: String,
      names: Completion.Names
    ): Semantic_Cache = Semantic_Cache(node_name, start, word, Nil, None).add(word, names)
  }

  private val semantic_kinds: Map[String, Int] =
    Map(
      Markup.CONSTANT -> LSP.CompletionItemKind.Constant,
      Markup.FIXED -> LSP.CompletionItemKind.Variable,
      Markup.FACT -> LSP.CompletionItemKind.Reference,
      Markup.TYPE_NAME -> LSP.CompletionItemKind.Struct,
      Markup.CLASS -> LSP.CompletionItemKind.Class,
      Markup.LOCALE -> LSP.CompletionItemKind.Module,
      Markup.BUNDLE -> LSP.CompletionItemKind.Module,
      Markup.THEORY -> LSP.CompletionItemKind.Module,
      Markup.METHOD -> LSP.CompletionItemKind.Method,
      Markup.ATTRIBUTE -> LSP.CompletionItemKind.Property,
      Markup.COMMAND -> LSP.CompletionItemKind.Keyword,
      Markup.DOCUMENT_ANTIQUOTATION -> LSP.CompletionItemKind.Function,
      Markup.ML_ANTIQUOTATION -> LSP.CompletionItemKind.Function)

  private def semantic_kind(item: Completion.Item): Int =
    Long_Name.explode(item.name).headOption.flatMap(semantic_kinds.get)
      .getOrElse(LSP.CompletionItemKind.Value)

  private def syntax_kind(item: Completion.Item): Int =
    item.description match {
      case _ :: descr :: _ if descr.startsWith("(symbol") => LSP.CompletionItemKind.Operator
      case _ :: descr :: _ if descr.startsWith("(template") => LSP.CompletionItemKind.Snippet
      case _ :: "(keyword)" :: _ => LSP.CompletionItemKind.Keyword
      case _ => LSP.CompletionItemKind.Text
    }

  private def path_kind(item: Completion.Item): Int =
    item.description match {
      case _ :: "(directory)" :: _ => LSP.CompletionItemKind.Folder
      case _ => LSP.CompletionItemKind.File
    }

  private def snippet_escape(s: String): String =
    s.replace("\\", "\\\\").replace("$", "\\$").replace("}", "\\}")

  /*the inner languages whose words are names of the formal context*/
  private val inner_languages = Set("term", "prop", "type")

  /*word characters would commit a unique item while it is still being typed*/
  private val commit_characters: List[String] =
    (' ' to '~').filterNot(c => Symbol.is_ascii_letdig(c) || c == '.').toList.map(_.toString)


  /* decorations */

  private def color_decorations(
    prefix: String,
    types: Set[Rendering.Color.Value],
    colors: List[Text.Info[Rendering.Color.Value]]
  ): List[VSCode_Model.Decoration] = {
    val color_ranges =
      colors.foldLeft(Map.empty[Rendering.Color.Value, List[Text.Range]]) {
        case (m, Text.Info(range, c)) => m + (c -> (range :: m.getOrElse(c, Nil)))
      }
    types.toList.map(c =>
      VSCode_Model.Decoration.ranges(prefix + c.toString, color_ranges.getOrElse(c, Nil).reverse))
  }

  private val background_colors =
    Rendering.Color.background_colors - Rendering.Color.active - Rendering.Color.active_result -
      Rendering.Color.entity

  private val dotted_colors =
    Set(Rendering.Color.writeln, Rendering.Color.information, Rendering.Color.warning)


  /* semantic markup: what the text colours leave plain */

  /*Rendering.text_color paints delimiters like a string, and numerals and entities not at
    all, so inside a term only the variables stand out. The editor can colour the rest by
    category (as semantic tokens, through its colour theme); these categories only ever
    add to the text colours, never override them*/
  val semantic_categories: List[String] =
    List("constant", "type_name", "class", "operator", "numeral")

  private val semantic_entity_kinds =
    Map(Markup.CONSTANT -> "constant", Markup.TYPE_NAME -> "type_name", Markup.CLASS -> "class")

  private val semantic_elements =
    Rendering.text_color_elements ++ Markup.Elements(Markup.ENTITY, Markup.NUMERAL)

  // "" is markup that already has a text colour of its own: it wins, and yields nothing
  private def semantic_category(markup: Markup): Option[String] =
    markup match {
      case Markup.Entity(kind, _) => semantic_entity_kinds.get(kind)
      case Markup(Markup.NUMERAL, _) => Some("numeral")
      case Markup(Markup.DELIMITER, _) => Some("operator")
      case _ =>
        Rendering.get_text_color(markup) match {
          case None | Some(Rendering.Color.main) => None
          case Some(_) => Some("")
        }
    }

  // for one token carrying several markups, e.g. `+`: delimiter and constant `plus`
  private def semantic_rank(category: String): Int =
    category match {
      case "" => 0
      case "operator" => 1
      case "numeral" => 2
      case _ => 3
    }

  private def semantic_decorations(
    infos: List[Text.Info[String]]
  ): List[VSCode_Model.Decoration] = {
    val ranges =
      infos.foldLeft(Map.empty[String, List[Text.Range]]) {
        case (m, Text.Info(range, c)) => m + (c -> (range :: m.getOrElse(c, Nil)))
      }
    semantic_categories.map(c =>
      VSCode_Model.Decoration.ranges("semantic_" + c, ranges.getOrElse(c, Nil).reverse))
  }


  /* diagnostic messages */

  private val message_severity =
    Map(
      Markup.LEGACY -> LSP.DiagnosticSeverity.Warning,
      Markup.ERROR -> LSP.DiagnosticSeverity.Error)


  /* markup elements */

  private val diagnostics_elements =
    Markup.Elements(Markup.LEGACY, Markup.ERROR)

  private val background_elements =
    Rendering.background_elements - Markup.ENTITY -- Rendering.active_elements

  private val dotted_elements =
    Markup.Elements(Markup.WRITELN, Markup.INFORMATION, Markup.WARNING)

  val tooltip_elements: Markup.Elements =
    Markup.Elements(Markup.WRITELN, Markup.INFORMATION, Markup.WARNING, Markup.BAD) ++
    Rendering.tooltip_elements

  private val hyperlink_elements =
    Markup.Elements(Markup.ENTITY, Markup.PATH, Markup.POSITION)

  private val hover_info_elements = Markup.Elements(Markup.ENTITY, Markup.VAR)

  /*of the names on one range, the one a hover tells about: a case before the facts that
    are named like it, a fixed variable before what it is a skolem of*/
  private val hover_info_rank: Map[String, Int] =
    Map(Markup.CASE -> 0, Markup.VAR -> 1, Markup.FIXED -> 2, Markup.CONSTANT -> 3,
      Markup.FACT -> 4)

  private val indentation_elements =
    Markup.Elements(Markup.Command_Indent.name)
}

class VSCode_Rendering(snapshot: Document.Snapshot, val model: VSCode_Model)
extends Rendering(snapshot, model.session.resources.options, model.session) {
  rendering =>

  def resources: VSCode_Resources = model.session.resources

  override def get_text(range: Text.Range): Option[String] = model.get_text(range)


  /* completion */

  private def is_word_before(caret: Text.Offset): Boolean =
    caret > 0 && get_text(Text.Range(caret - 1, caret)).exists(s =>
      s.length == 1 && Completion.Word_Parsers.is_word_char(s(0)))

  /*the cache for the word ending at the caret, and that word*/
  private def cached_semantic(caret: Text.Offset): Option[(VSCode_Rendering.Semantic_Cache, String)] =
    for {
      cache <- resources.completion_cache.value
      if cache.node_name == model.node_name
      if cache.start < caret && !is_word_before(cache.start)
      word <- get_text(Text.Range(cache.start, caret))
      if Completion.Word_Parsers.is_word(word) && word.startsWith(cache.original)
    } yield (cache, word)

  /*no completion, semantic result, and whether it may still lack names*/
  private def vscode_semantic_completion(
    history: Completion.History,
    unicode_symbols: Boolean,
    completed_range: Option[Text.Range],
    caret: Text.Offset
  ): (Boolean, Option[Completion.Result], Boolean) = {
    def result(cache: VSCode_Rendering.Semantic_Cache, range: Text.Range, word: String)
        : (Boolean, Option[Completion.Result], Boolean) =
      (false,
        Completion.Names(cache.names.length, cache.names)
          .complete(range, history, unicode_symbols, word),
        !cache.covers(word))

    if (snapshot.is_outdated) {
      cached_semantic(caret) match {
        case Some((cache, word)) => result(cache, Text.Range(cache.start, caret), word)
        case None => (false, None, true)
      }
    }
    else {
      semantic_completion(completed_range, before_caret_range(caret)) match {
        case Some(Text.Info(_, Completion.No_Completion)) => (true, None, false)
        case Some(Text.Info(range, names: Completion.Names)) =>
          get_text(range) match {
            case Some(word) if Completion.Word_Parsers.is_word(word) =>
              val cache =
                resources.completion_cache.change_result { cache0 =>
                  val cache1 =
                    cache0 match {
                      case Some(c) if c.node_name == model.node_name && c.start == range.start &&
                        word.startsWith(c.original) => c.add(word, names)
                      case _ =>
                        VSCode_Rendering.Semantic_Cache.make(
                          model.node_name, range.start, word, names)
                    }
                  (cache1, Some(cache1))
                }
              result(cache, range, word)
            case Some(original) =>
              (false, names.complete(range, history, unicode_symbols, original),
                names.total > names.names.length)
            case None => (false, None, false)
          }
        case None => (false, None, true)
      }
    }
  }

  /*the innermost delimited language at a range, if its words are names of the context*/
  private def inner_language(range: Text.Range): Option[String] =
    snapshot.select(range, Rendering.language_elements, _ =>
      {
        case Text.Info(info_range, XML.Elem(Markup.Language(lang), _)) if lang.delimited =>
          Some((info_range.length, lang.name))
        case _ => None
      }).map(_.info).minByOption(_._1).map(_._2).filter(VSCode_Rendering.inner_languages)

  /*the name being typed: word characters before the caret, from a letter on*/
  private def word_range(caret: Text.Offset): Option[(Text.Range, String)] =
    for {
      text <- get_text(Text.Range((caret - 256) max 0, caret))
      n = text.reverseIterator.takeWhile(Completion.Word_Parsers.is_word_char).length
      if n > 0
      word = text.drop(text.length - n)
      if Symbol.is_ascii_letter(word(0))
    } yield (Text.Range(caret - n, caret), word)

  /*within inner syntax: the word before the caret, whether it has to be a type, and its
    context -- None while the prover has yet to report it*/
  private def inner_names(caret: Text.Offset, context_names: VSCode_Context_Names)
      : Option[(Text.Range, String, Boolean, Option[VSCode_Context_Names.Context])] =
    for {
      lang <- inner_language(before_caret_range(caret))
      (range, word) <- word_range(caret)
      command <- context_names.context_command(snapshot, caret)
    } yield (range, word, lang == "type", context_names.get(snapshot, command))

  /*the prover has yet to report on the word being typed, and may still do so: within inner
    syntax, only the names of the context are worth waiting for*/
  def completion_pending(caret: Text.Offset, context_names: VSCode_Context_Names): Boolean =
    is_word_before(caret) && {
      inner_names(caret, context_names) match {
        case Some((_, _, _, context)) => context.isEmpty
        case None => semantic_pending(caret)
      }
    }

  private def semantic_pending(caret: Text.Offset): Boolean =
    if (snapshot.is_outdated) {
      cached_semantic(caret).forall({ case (cache, word) => !cache.covers(word) })
    }
    else {
      val caret_range = before_caret_range(caret)
      semantic_completion(None, caret_range).isEmpty &&
        snapshot.node.command_iterator(caret_range).nextOption().exists(
          { case (command, _) =>
              !snapshot.state.command_status(snapshot.version, command).is_terminated })
    }

  /*the prover's own report first, without the parameters of class instances; within inner
    syntax, the names of the context otherwise*/
  private def semantic_or_context_completion(
    history: Completion.History,
    unicode_symbols: Boolean,
    completed_range: Option[Text.Range],
    caret: Text.Offset,
    context_names: VSCode_Context_Names
  ): (Boolean, Option[Completion.Result], Boolean) =
    vscode_semantic_completion(history, unicode_symbols, completed_range, caret) match {
      case (false, None, incomplete) =>
        inner_names(caret, context_names) match {
          case Some((range, word, types_only, Some(context))) =>
            val (selected, more) =
              VSCode_Context_Names.select(
                context.names, word, types_only, context_names.completion_limit)
            val result =
              Completion.Names(selected.length, selected)
                .complete(range, history, unicode_symbols, word)
            (false, result, more || result.isEmpty)
          case Some((_, _, _, None)) => (false, None, true)
          case None => (false, None, incomplete)
        }
      /*until the context's list is in, by their shape -- and asked again then*/
      case (false, Some(result), incomplete) if VSCode_Context_Names.has_constants(result) =>
        val context =
          context_names.context_command(snapshot, caret).flatMap(context_names.get(snapshot, _))
        val result1 =
          VSCode_Context_Names.without_inst_params(result, context.map(_.inst_params))
        (false, result1, incomplete || context.isEmpty && !result1.contains(result))
      case res => res
    }

  /*items, and whether more typing may bring names the list lacks: VS Code asks again only then,
    and otherwise filters the list itself*/
  def completion(
    node_pos: Line.Node_Position,
    caret: Text.Offset,
    context_names: VSCode_Context_Names
  ): (List[LSP.CompletionItem], Boolean) = {
    val doc = model.content.doc
    val line = node_pos.line
    val unicode = resources.unicode_symbols_edits
    doc.offset(Line.Position(line)) match {
      case None => (Nil, false)
      case Some(line_start) =>
        val history = Completion.History.empty
        val caret_range = before_caret_range(caret)

        val syntax = model.syntax()
        val syntax_completion =
          syntax.complete(history, unicode, explicit = false,
            line_start, doc.lines(line).text, caret - line_start,
            language_context(caret_range) getOrElse syntax.language_context)

        val (no_completion, semantic_completion, semantic_incomplete) =
          semantic_or_context_completion(
            history, unicode, syntax_completion.map(_.range), caret, context_names)

        if (no_completion) (Nil, false)
        else {
          val spell_completion = VSCode_Spell_Checker.completion(rendering, caret)
          val path_completion = rendering.path_completion(caret)

          def kinds(result: Option[Completion.Result], kind: Completion.Item => Int)
            : List[(Completion.Item, Int)] =
            result.toList.flatMap(_.items.map(item => item -> kind(item)))
          val item_kind =
            (kinds(semantic_completion, VSCode_Rendering.semantic_kind) :::
              kinds(syntax_completion, VSCode_Rendering.syntax_kind) :::
              kinds(spell_completion, _ => LSP.CompletionItemKind.Text) :::
              kinds(path_completion, VSCode_Rendering.path_kind)).toMap
          val semantic_items = semantic_completion.toList.flatMap(_.items).toSet

          val items =
            Completion.Result.merge(history,
              semantic_completion, syntax_completion, spell_completion, path_completion
            ) match {
              case None => Nil
              case Some(result) =>
                result.items.map(item => {
                  val (text, snippet) =
                    if (item.move == 0) (item.replacement, false)
                    else {
                      val (s1, s2) =
                        item.replacement.splitAt(item.replacement.length + item.move)
                      (VSCode_Rendering.snippet_escape(s1) + "$0" +
                        VSCode_Rendering.snippet_escape(s2), true)
                    }
                  LSP.CompletionItem(
                    label = item.replacement,
                    kind = Some(item_kind.getOrElse(item, LSP.CompletionItemKind.Text)),
                    detail = Some(item.description.mkString(" ")),
                    filter_text =
                      if (Completion.Word_Parsers.is_word(item.original)) None
                      else Some(item.original),
                    commit_characters =
                      if (result.unique && item.immediate) {
                        Some(VSCode_Rendering.commit_characters)
                      }
                      else None,
                    text = Some(text),
                    snippet = snippet,
                    range = Some(doc.range(item.range)),
                    data =
                      if (semantic_items(item)) {
                        VSCode_Hover_Info.completion_key(item).map(_.json)
                      }
                      else None)
                })
            }
          val all_items =
            (items ::: VSCode_Spell_Checker.menu_items(rendering, caret)).zipWithIndex.map(
              { case (item, i) => item.copy(sort_text = Some("%05d".format(i))) })
          (all_items, is_word_before(caret) && semantic_incomplete)
        }
    }
  }


  /* indentation */

  def indentation(range: Text.Range): Int =
    snapshot.select(range, VSCode_Rendering.indentation_elements, _ =>
      {
        case Text.Info(_, XML.Elem(Markup.Command_Indent(i), _)) => Some(i)
        case _ => None
      }).headOption.map(_.info).getOrElse(0)


  /* diagnostics */

  def diagnostics: List[Text.Info[Command.Results]] =
    snapshot.cumulate[Command.Results](
      model.content.text_range, Command.Results.empty, VSCode_Rendering.diagnostics_elements,
        command_states =>
          {
            case (res, Text.Info(_, msg @ XML.Elem(Markup.Bad(i), body)))
            if body.nonEmpty => Some(res + (i -> msg))

            case (res, Text.Info(_, msg)) =>
              Command.State.get_result_proper(command_states, msg.markup.properties).map(res + _)
          }).filterNot(info => info.info.is_empty)

  def diagnostics_output(results: List[Text.Info[Command.Results]]): List[LSP.Diagnostic] =
    (for {
      Text.Info(text_range, res) <- results.iterator
      range = model.content.doc.range(text_range)
      (_, XML.Elem(Markup(name, _), body)) <- res.iterator
    } yield {
      val message = resources.output_pretty_message(body)
      val severity = VSCode_Rendering.message_severity.get(name)
      LSP.Diagnostic(range, message, severity = severity)
    }).toList


  /* text color */

  def text_color(range: Text.Range): List[Text.Info[Rendering.Color.Value]] =
    snapshot.select(range, Rendering.text_color_elements, _ =>
      {
        case Text.Info(_, elem) => Rendering.get_text_color(elem.markup)
      })


  /* semantic markup */

  /*the innermost markup wins, as in text_color; among the markups of one token the
    category ranks decide, which is why the accumulated result carries its range.
    HOL's 0 and 1 are notation, not numeral tokens: a delimiter made of digits is
    reported as a numeral, which is what it reads as*/
  def semantic(range: Text.Range): List[Text.Info[String]] =
    snapshot.cumulate[Option[(Text.Range, String)]](
      range, None, VSCode_Rendering.semantic_elements, _ =>
        {
          case (acc, Text.Info(r, elem)) =>
            VSCode_Rendering.semantic_category(elem.markup).map(c =>
              acc match {
                case Some((r0, c0)) if r0 == r &&
                  VSCode_Rendering.semantic_rank(c0) <= VSCode_Rendering.semantic_rank(c) => acc
                case _ => Some((r, c))
              })
        }).flatMap(
          {
            case Text.Info(r, Some((_, c))) if c.nonEmpty =>
              val digits =
                c == "operator" &&
                  get_text(r).exists(s => s.nonEmpty && s.forall(Symbol.is_ascii_digit))
              Some(Text.Info(r, if (digits) "numeral" else c))
            case _ => None
          })


  /* text overview color */

  private sealed case class Color_Info(
    color: Rendering.Color.Value, offset: Text.Offset, end_offset: Text.Offset, end_line: Int)

  def text_overview_color: List[Text.Info[Rendering.Color.Value]] = {
    @tailrec def loop(
      offset: Text.Offset,
      line: Int,
      lines: List[Line],
      colors: List[Color_Info]
    ): List[Text.Info[Rendering.Color.Value]] = {
      if (lines.nonEmpty) {
        val end_offset = offset + lines.head.text.length
        val colors1 =
          (overview_color(Text.Range(offset, end_offset)), colors) match {
            case (Some(color), old :: rest) if color == old.color && line == old.end_line =>
              old.copy(end_offset = end_offset, end_line = line + 1) :: rest
            case (Some(color), _) =>
              Color_Info(color, offset, end_offset, line + 1) :: colors
            case (None, _) => colors
          }
        loop(end_offset + 1, line + 1, lines.tail, colors1)
      }
      else {
        colors.reverse.map(info =>
          Text.Info(Text.Range(info.offset, info.end_offset), info.color))
      }
    }
    loop(0, 0, model.content.doc.lines, Nil)
  }


  /* dotted underline */

  def dotted(range: Text.Range): List[Text.Info[Rendering.Color.Value]] =
    message_underline_color(VSCode_Rendering.dotted_elements, range)


  /* decorations */

  def decorations: List[VSCode_Model.Decoration] = // list of canonical length and order
    VSCode_Rendering.color_decorations("background_", VSCode_Rendering.background_colors,
      background(VSCode_Rendering.background_elements, model.content.text_range,
        Rendering.Focus.empty)) :::
    VSCode_Rendering.color_decorations("foreground_", Rendering.Color.foreground_colors,
      foreground(model.content.text_range)) :::
    VSCode_Rendering.color_decorations("text_", Rendering.Color.text_colors,
      snapshot.command_spans().flatMap(info => text_color(info.range))) :::
    VSCode_Rendering.semantic_decorations(
      snapshot.command_spans().flatMap(info => semantic(info.range))) :::
    VSCode_Rendering.color_decorations("text_overview_", Rendering.Color.text_overview_colors,
      text_overview_color) :::
    VSCode_Rendering.color_decorations("dotted_", VSCode_Rendering.dotted_colors,
      dotted(model.content.text_range)) :::
    List(VSCode_Spell_Checker.decoration(rendering))

  def decoration_output(decos: List[VSCode_Model.Decoration]): LSP.Decoration =
    LSP.Decoration(decos.map(deco =>
      LSP.Decoration_Entry(deco.typ,
        for (Text.Info(text_range, msgs) <- deco.content)
          yield {
            val range = model.content.doc.range(text_range)
            val hover_message =
              msgs.map(msg => LSP.MarkedString(resources.output_pretty_tooltip(msg)))
            LSP.Decoration_Range(range, hover_message = hover_message)
          })))


  /* hyperlinks */

  def hyperlink_source_file(
    source_name: String,
    line1: Int,
    range: Symbol.Range
  ): Option[Line.Node_Range] = {
    for {
      platform_path <- model.session.store.source_file(source_name)
      file <-
        (try { Some(File.absolute(new JFile(platform_path))) }
         catch { case ERROR(_) => None })
    }
    yield {
      Line.Node_Range(file.getPath,
        if (range.start > 0) {
          resources.get_file_content(resources.node_name(file)) match {
            case Some(text) =>
              val chunk = Symbol.Text_Chunk(text)
              val doc = Line.Document(text)
              doc.range(chunk.decode(range))
            case _ =>
              Line.Range(Line.Position((line1 - 1) max 0))
          }
        }
        else Line.Range(Line.Position((line1 - 1) max 0)))
    }
  }

  def hyperlink_command(id: Document_ID.Generic, range: Symbol.Range): Option[Line.Node_Range] =
    if (snapshot.is_outdated) None
    else
      for {
        start <- snapshot.find_command_position(id, range.start)
        stop <- snapshot.find_command_position(id, range.stop)
      } yield Line.Node_Range(start.name, Line.Range(start.pos, stop.pos))

  def hyperlink_position(pos: Position.T): Option[Line.Node_Range] =
    pos match {
      case Position.Item_File(name, line, range) => hyperlink_source_file(name, line, range)
      case Position.Item_Id(id, range) => hyperlink_command(id, range)
      case _ => None
    }

  def hyperlink_def_position(pos: Position.T): Option[Line.Node_Range] =
    pos match {
      case Position.Item_Def_File(name, line, range) => hyperlink_source_file(name, line, range)
      case Position.Item_Def_Id(id, range) => hyperlink_command(id, range)
      case _ => None
    }

  /*a link to where an entity is defined, for a hover in Markdown: a file URI whose
    fragment VS Code reads as the line and column to open it at*/
  def hover_link(props: Properties.T): Option[String] =
    hyperlink_def_position(props).map(loc =>
      Url.print_file_name(loc.name) + "#L" + (loc.range.start.line + 1) + "," +
        (loc.range.start.column + 1))


  /* hover info */

  private val Fact_Selection = """\(([0-9]+(?:-[0-9]*)?(?:,[0-9]+(?:-[0-9]*)?)*)\)""".r

  /*the selection after the name of a fact, "2" of assms(2)*/
  private def fact_selection(stop: Text.Offset): String = {
    val text = model.content.text
    if (stop < text.length && text(stop) == '(') {
      Fact_Selection.findPrefixMatchOf(text.substring(stop, (stop + 64) min text.length)) match {
        case Some(m) => m.group(1)
        case None => ""
      }
    }
    else ""
  }

  /*the first execution of a command: another one means that its context may differ*/
  private def command_exec(command: Command): Option[Document_ID.Exec] =
    for {
      assignment <- snapshot.state.assignments.get(snapshot.version.id)
      execs <- assignment.command_execs.get(command.id)
      exec <- execs.headOption
    } yield exec

  /*the next command with a context of its own*/
  @tailrec private def proper_after(command: Command): Option[Command] =
    snapshot.node.commands.next(command) match {
      case Some(command1) if !command1.is_proper => proper_after(command1)
      case res => res
    }

  /*what a name that completion offers at an offset stands for is asked of the context
    the names come from, which is before the command being written*/
  def completion_info_request(
    offset: Text.Offset,
    key: VSCode_Hover_Info.Key,
    context_names: VSCode_Context_Names
  ): Option[VSCode_Hover_Info.Request] =
    context_names.context_command(snapshot, offset).map(command =>
      VSCode_Hover_Info.Request(command, command_exec(command), key))

  /*the name at an offset that the hover info query knows about, with the contexts to ask,
    the first one that knows it answers: a fact that a command refers to is in the context
    before it, as that command may close the block of a local fact; everything else is in
    the context after its command -- or, for a name that a command binds by proving
    something (obtain, have h:), after the next one, which ends a proof by a single method;
    a later context is asked only when an earlier one has nothing*/
  def hover_request(offset: Text.Offset, context_names: VSCode_Context_Names)
      : Option[(Text.Range, List[VSCode_Hover_Info.Request])] = {
    if (snapshot.is_outdated) None
    else {
      val keys =
        snapshot.cumulate[List[(Text.Range, VSCode_Hover_Info.Key, Boolean)]](
          Text.Range(offset, offset + 1), Nil, VSCode_Rendering.hover_info_elements, _ =>
            {
              case (keys, Text.Info(r0, XML.Elem(markup @ Markup.Entity(kind, name), _)))
              if VSCode_Hover_Info.kinds(kind) && name.nonEmpty =>
                val is_def = Markup.Entity.Def.unapply(markup).isDefined
                Some((snapshot.convert(r0), VSCode_Hover_Info.Key(kind, name), is_def) :: keys)
              case (keys, Text.Info(r0, XML.Elem(Markup(Markup.VAR, Markup.Name(name)), _))) =>
                Some((snapshot.convert(r0), VSCode_Hover_Info.Key(Markup.VAR, name), false) :: keys)
              case _ => None
            }).flatMap(_.info)

      keys.sortBy({ case (r, key, _) =>
        (r.length, VSCode_Rendering.hover_info_rank.getOrElse(key.kind, 9)) }).headOption
      .flatMap({ case (range, key0, is_def) =>
        val ref_fact = key0.kind == Markup.FACT && !is_def
        val key = if (ref_fact) key0.copy(selection = fact_selection(range.stop)) else key0
        val contexts =
          if (ref_fact) context_names.context_command(snapshot, offset).toList
          else {
            snapshot.node.command_iterator(snapshot.revert(offset)).nextOption().toList
              .flatMap({ case (command, _) =>
                command :: proper_after(command).toList })
          }
        if (contexts.isEmpty) None
        else {
          Some((range, contexts.map(command =>
            VSCode_Hover_Info.Request(command, command_exec(command), key))))
        }
      })
    }
  }

  def hyperlinks(range: Text.Range): List[Line.Node_Range] =
    snapshot.cumulate[List[Line.Node_Range]](
      range, Nil, VSCode_Rendering.hyperlink_elements, _ =>
        {
          case (links, Text.Info(_, XML.Elem(Markup.Path(name), _))) =>
            val file = perhaps_append_file(snapshot.node_name, name)
            Some(Line.Node_Range(file) :: links)

          case (links, Text.Info(info_range, XML.Elem(Markup(Markup.ENTITY, props), _))) =>
            hyperlink_def_position(props).map(_ :: links)

          case (links, Text.Info(info_range, XML.Elem(Markup(Markup.POSITION, props), _))) =>
            hyperlink_position(props).map(_ :: links)

          case _ => None
        }) match { case Text.Info(_, links) :: _ => links.reverse case _ => Nil }
}
