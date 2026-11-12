/*  Title:      Tools/VSCode/src/vscode_indent.scala

Indentation according to Isabelle/Isar outer syntax, for LSP formatting requests: the
rule of Isabelle/jEdit (Text_Structure.Indent_Rule), over Line.Document.
*/

package isabelle.vscode


import isabelle._

import scala.collection.Searching


object VSCode_Indent {
  /*the defaults of jedit_structure_limit and jedit_indent_script_limit, as constants: this
    code may run without the declarations of etc/options (isabelle-vscode compiles it into a
    jar ahead of a released distribution)*/
  val structure_limit = 1000
  val script_limit = 20


  /* formatting options of the request */

  sealed case class Format(tab_size: Int, insert_spaces: Boolean) {
    val indent_size: Int = tab_size max 1

    def width(line: String): Int =
      line.iterator.takeWhile(c => c == ' ' || c == '\t').foldLeft(0) {
        case (w, ' ') => w + 1
        case (w, _) => (w / indent_size + 1) * indent_size
      }

    def whitespace(width: Int): String =
      if (insert_spaces) Symbol.spaces(width)
      else "\t" * (width / indent_size) + Symbol.spaces(width % indent_size)
  }

  def leading_whitespace(line: String): String =
    line.takeWhile(c => c == ' ' || c == '\t')


  /* lines with tokens and scanner state, as jEdit keeps them per buffer line */

  object Lines {
    /*the lines up to the first one that differs are taken from the previous scan: the
      scanner state of a line depends on every line before it, so without that each
      request would explode the whole theory up to the caret -- 0.4-2 s near the end of a
      theory of 3000 lines, while the prover was busy with it*/
    def apply(
      keywords: Keyword.Keywords,
      doc: Line.Document,
      upto: Int,
      previous: Option[Lines] = None
    ): Lines = {
      val text = doc.lines.iterator.take(upto + 1).map(_.text).toVector
      val starts = text.scanLeft(0)((i, line) => i + line.length + 1).init

      val tokens = Vector.newBuilder[List[Token]]
      val before = Vector.newBuilder[Scan.Line_Context]
      val after = Vector.newBuilder[Scan.Line_Context]
      val structure = Vector.newBuilder[Line_Structure]
      var ctxt: Scan.Line_Context = Scan.Finished
      var struct = Line_Structure.init

      val reused =
        previous match {
          case Some(prev) if prev.keywords eq keywords =>
            val common = text.length min prev.count
            val n = Range(0, common).find(i => text(i) != prev.text(i)).getOrElse(common)
            if (n > 0) {
              tokens ++= prev.tokens.iterator.take(n)
              before ++= prev.before.iterator.take(n)
              after ++= prev.after.iterator.take(n)
              structure ++= prev.structure.iterator.take(n)
              ctxt = prev.after(n - 1)
              struct = prev.structure(n - 1)
            }
            n
          case _ => 0
        }

      for (line <- text.iterator.drop(reused)) {
        before += ctxt
        val (toks, ctxt1) = Token.explode_line(keywords, line, ctxt)
        struct = struct.update(keywords, toks)
        tokens += toks
        after += ctxt1
        structure += struct
        ctxt = ctxt1
      }
      new Lines(keywords, text, starts,
        tokens.result(), before.result(), after.result(), structure.result())
    }

    /*one theory at a time: the one being edited*/
    private val cache = Synchronized[Option[(Document.Node.Name, Lines)]](None)

    def scan(
      node_name: Document.Node.Name,
      keywords: Keyword.Keywords,
      doc: Line.Document,
      upto: Int
    ): Lines = {
      val previous =
        cache.value match {
          case Some((name, lines)) if name == node_name => Some(lines)
          case _ => None
        }
      val lines = apply(keywords, doc, upto, previous)
      cache.change(_ => Some((node_name, lines)))
      lines
    }
  }

  final class Lines private(
    val keywords: Keyword.Keywords,
    val text: Vector[String],
    starts: Vector[Text.Offset],
    private val tokens: Vector[List[Token]],
    val before: Vector[Scan.Line_Context],
    private val after: Vector[Scan.Line_Context],
    val structure: Vector[Line_Structure]
  ) {
    def count: Int = text.length

    def line_start(line: Int): Text.Offset = starts(line)

    def line_of(offset: Text.Offset): Int =
      starts.search(offset) match {
        case Searching.Found(i) => i
        case Searching.InsertionPoint(i) => i - 1
      }

    /*proper tokens and comments, like Text_Structure.Navigator with comments*/
    def line_tokens(line: Int): List[Text.Info[Token]] = {
      val toks = tokens(line)
      val offsets = toks.scanLeft(starts(line))((i, tok) => i + tok.source.length)
      for ((tok, i) <- toks zip offsets if !tok.is_space)
        yield Text.Info(Text.Range(i, i + tok.source.length), tok)
    }

    def iterator(line: Int, lim: Int = structure_limit): Iterator[Text.Info[Token]] =
      Range(line max 0, (line + lim) min count).iterator.flatMap(line_tokens)

    def reverse_iterator(line: Int, lim: Int = structure_limit): Iterator[Text.Info[Token]] =
      Range(line min (count - 1), (line - lim) max -1, -1).iterator
        .flatMap(l => line_tokens(l).reverseIterator)
  }


  /* indentation of one line */

  private val keyword_open = Keyword.theory_goal_kinds ++ Keyword.proof_open_kinds
  private val keyword_close = Keyword.proof_close_kinds

  /*Text_Structure.Indent_Rule, with indentation overridden for the lines already
    re-indented by the same request.

    jEdit gives a blank line 0 and indents it once a keyword is typed there. With
    predict_blank, for a line that ENTER has just opened, it gets what a command typed
    there would get instead -- or, within open brackets, the indentation of a continuation
    of the line before. A continuation throughout would be wrong after a complete command:
    after the qed of a lemma it is 2, where the next lemma goes to 0.*/
  def indentation(
    lines: Lines,
    format: Format,
    script: Text.Range => Int,
    current_line: Int,
    overrides: Map[Int, Int] = Map.empty,
    predict_blank: Boolean = false
  ): Int = {
    val keywords = lines.keywords
    val indent_size = format.indent_size

    def line_indent(line: Int): Int =
      if (line < 0 || line >= lines.count) 0
      else overrides.getOrElse(line, format.width(lines.text(line)))

    def line_head(line: Int): Option[Text.Info[Token]] =
      lines.iterator(line, 1).nextOption()

    def head_is_quasi_command(line: Int): Boolean =
      line_head(line) match {
        case None => false
        case Some(Text.Info(_, tok)) => keywords.is_quasi_command(tok)
      }

    val prev_line: Int =
      Range.inclusive(current_line - 1, 0, -1).find(line =>
        lines.before(line) == Scan.Finished &&
        (!lines.structure(line).improper || lines.structure(line).blank)) getOrElse -1

    def prev_line_command: Option[Token] =
      lines.reverse_iterator(prev_line, 1).
        collectFirst({ case Text.Info(_, tok) if tok.is_begin_or_command => tok })

    def prev_line_span: Iterator[Token] =
      lines.reverse_iterator(prev_line, 1).map(_.info).takeWhile(tok => !tok.is_begin_or_command)

    def prev_span: Iterator[Token] =
      lines.reverse_iterator(prev_line).map(_.info).takeWhile(tok => !tok.is_begin_or_command)

    def script_indent(info: Text.Info[Token]): Int =
      if (keywords.is_command(info.info, Keyword.prf_script_kinds))
        (script(info.range) min script_limit) max 0
      else 0

    def indent_indent(tok: Token): Int =
      if (keywords.is_command(tok, keyword_open)) indent_size
      else if (keywords.is_command(tok, keyword_close)) { - indent_size }
      else 0

    def indent_offset(tok: Token): Int =
      if (keywords.is_command(tok, Keyword.proof_enclose_kinds)) indent_size
      else 0

    def indent_structure: Int =
      lines.reverse_iterator(current_line - 1).scanLeft((0, false))(
        { case ((ind, _), Text.Info(range, tok)) =>
            val ind1 = ind + indent_indent(tok)
            if (tok.is_begin_or_command && !keywords.is_command(tok, Keyword.prf_script_kinds)) {
              val line = lines.line_of(range.start)
              line_head(line) match {
                case Some(info) if info.info == tok =>
                  (ind1 + indent_offset(tok) + line_indent(line), true)
                case _ => (ind1, false)
              }
            }
            else (ind1, false)
        }).collectFirst({ case (i, true) => i }).getOrElse(0)

    def indent_brackets: Int =
      prev_line_span.foldLeft(0) {
        case (i, tok) =>
          if (tok.is_open_bracket) i + indent_size
          else if (tok.is_close_bracket) i - indent_size
          else i
      }

    def indent_extra: Int =
      if (prev_span.exists(keywords.is_quasi_command)) indent_size
      else 0

    def indent_continuation: Int =
      prev_line_command match {
        case None =>
          val extra = if (head_is_quasi_command(prev_line)) indent_extra else 0
          line_indent(prev_line) + indent_brackets + extra
        case Some(prev_tok) =>
          indent_structure + indent_brackets + indent_size -
          indent_offset(prev_tok) - indent_indent(prev_tok)
      }

    val indent =
      if (lines.before(current_line) != Scan.Finished) line_indent(current_line)
      else if (lines.structure(current_line).blank) {
        if (!predict_blank) 0
        else if (indent_brackets > 0) indent_continuation
        else indent_structure
      }
      else {
        line_head(current_line) match {
          case Some(info) =>
            val tok = info.info
            if (tok.is_begin ||
                keywords.is_before_command(tok) ||
                keywords.is_command(tok, Keyword.theory_kinds)) 0
            else if (keywords.is_command(tok, Keyword.proof_enclose_kinds))
              indent_structure + script_indent(info) - indent_offset(tok)
            else if (keywords.is_command(tok, Keyword.proof_kinds))
              (indent_structure + script_indent(info) - indent_offset(tok)) max indent_size
            else if (tok.is_command) indent_structure - indent_offset(tok)
            else {
              prev_line_command match {
                case None =>
                  val extra =
                    (keywords.is_quasi_command(tok), head_is_quasi_command(prev_line)) match {
                      case (true, true) | (false, false) => 0
                      case (true, false) => - indent_extra
                      case (false, true) => indent_extra
                    }
                  line_indent(prev_line) + indent_brackets + extra - indent_offset(tok)
                case Some(prev_tok) =>
                  indent_structure + indent_brackets + indent_size - indent_offset(tok) -
                  indent_offset(prev_tok) - indent_indent(prev_tok)
              }
            }
          case None => indent_continuation
        }
      }

    indent max 0
  }


  /* requests */

  private class Request(rendering: VSCode_Rendering, format: Format, upto: Int) {
    val lines: Lines = {
      val model = rendering.model
      Lines.scan(model.node_name, model.syntax().keywords, model.content.doc, upto)
    }
    private var overrides = Map.empty[Int, Int]
    private val edits = List.newBuilder[LSP.TextEdit]

    private val script: Text.Range => Int = range => rendering.indentation(range)

    def head(line: Int): Option[Text.Info[Token]] = lines.iterator(line, 1).nextOption()

    def is_indent_command(info: Text.Info[Token]): Boolean =
      lines.keywords.is_indent_command(info.info)

    def set(line: Int, indent: Int): Unit = {
      overrides += (line -> indent)
      val old_whitespace = leading_whitespace(lines.text(line))
      val new_whitespace = format.whitespace(indent)
      if (old_whitespace != new_whitespace) {
        val range = Line.Range(Line.Position(line), Line.Position(line, old_whitespace.length))
        edits += LSP.TextEdit(range, new_whitespace)
      }
    }

    def indent(line: Int, predict_blank: Boolean = false): Unit =
      set(line, indentation(lines, format, script, line, overrides, predict_blank))

    def result: List[LSP.TextEdit] = edits.result()
  }

  private def applicable(rendering: VSCode_Rendering, line: Int): Boolean = {
    val model = rendering.model
    model.is_theory && model.syntax().has_tokens &&
      0 <= line && line < model.content.doc.lines.length
  }

  /*ENTER, as Isabelle.newline in jEdit: re-indent the line left behind if it starts with a
    keyword (or clear it if it is blank), then indent the new one*/
  def on_newline(rendering: VSCode_Rendering, pos: Line.Position, format: Format)
      : List[LSP.TextEdit] =
    if (!applicable(rendering, pos.line) || pos.line == 0) Nil
    else {
      val request = new Request(rendering, format, pos.line)
      val old_line = pos.line - 1
      if (request.lines.text(old_line).forall(c => c == ' ' || c == '\t')) request.set(old_line, 0)
      else if (request.head(old_line).exists(request.is_indent_command)) request.indent(old_line)
      request.indent(pos.line, predict_blank = true)
      request.result
    }

  /*a space after a keyword at the start of the line, as Isabelle.indent_input in jEdit*/
  def on_space(rendering: VSCode_Rendering, pos: Line.Position, format: Format)
      : List[LSP.TextEdit] =
    if (!applicable(rendering, pos.line) || pos.column == 0) Nil
    else {
      val request = new Request(rendering, format, pos.line)
      val keyword_stop = request.lines.line_start(pos.line) + pos.column - 1
      request.head(pos.line) match {
        case Some(info) if info.range.stop == keyword_stop && request.is_indent_command(info) =>
          request.indent(pos.line)
        case _ =>
      }
      request.result
    }

  /*Format Selection, as the jEdit action indent-lines: each line in turn, so that later
    lines see the indentation given to earlier ones*/
  def on_range(rendering: VSCode_Rendering, range: Line.Range, format: Format)
      : List[LSP.TextEdit] = {
    val last =
      if (range.stop.column == 0 && range.stop.line > range.start.line) range.stop.line - 1
      else range.stop.line
    val last1 = last min (rendering.model.content.doc.lines.length - 1)
    if (!applicable(rendering, range.start.line) || last1 < range.start.line) Nil
    else {
      val request = new Request(rendering, format, last1)
      for (line <- range.start.line to last1) request.indent(line)
      request.result
    }
  }
}
