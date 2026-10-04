/*  Title:      Tools/VSCode/src/vscode_entities.scala

The occurrences of formal entities across all nodes the session has loaded: the open
theories, the theories and files they import, as far as the prover has checked them.

Occurrences are found by identity, not by name: a fixed variable and a constant of the same
name are different entities. Entity markup gives two kinds of identity. The serial ("def" at
the binding, "ref" at each use) is what document highlights go by, but it is not enough: a
command may read a binding twice (lemma fixes x shows ...) and give each reading its own
serial. The other is where the name is bound: every reference carries that position, and a
definition is at it. That also unites entities bound by the very same name, like a constant
and, for the equations of its definition, the fixed variable of its specification. Entities
that the session image defines are bound in no loaded node, only in a source file.

So a theory that nobody has checked has no occurrences yet. The dependents of an entity are
the theories that may have some: those that import where it is bound and spell its name.
*/

package isabelle.vscode


import isabelle._

import java.io.{File => JFile}

import scala.annotation.tailrec


object VSCode_Entities {
  /* binding: where a name is bound, as references give it */

  sealed case class Binding(source: String, range: Symbol.Range, base_name: String)

  /*a derived name (foo_def for foo) may be bound at the same position: only the same name*/
  private def base_name(markup: Markup): String =
    Long_Name.base_name(Markup.Name.get(markup.properties))

  private def ref_binding(markup: Markup): Option[Binding] = {
    val props = markup.properties
    val source =
      Position.Def_Id.unapply(props).map("id:" + _) orElse
      Position.Def_File.unapply(props).map("file:" + _)
    for (s <- source; r <- Position.Def_Range.unapply(props))
      yield Binding(s, r, base_name(markup))
  }

  /*the markup of a definition within the text carries no position, which is where it is:
    the symbols of its command before it (in theories, not in loaded files)*/
  private def def_binding(snapshot: Document.Snapshot, info: Text.Info[Markup]): Option[Binding] =
    if (snapshot.commands_loading.nonEmpty) None
    else {
      val range = snapshot.revert(info.range)
      snapshot.node.command_iterator(range.start).nextOption() match {
        case Some((command, start)) if range.stop - start <= command.source.length =>
          def offset(i: Text.Offset): Symbol.Offset =
            Symbol.length(command.source.substring(0, i - start)) + 1
          Some(Binding("id:" + command.id, Text.Range(offset(range.start), offset(range.stop)),
            base_name(info.info)))
        case _ => None
      }
    }


  /* occurrences */

  sealed case class Occurrence(
    node_range: Line.Node_Range,
    markup: Markup,
    binding: Option[Binding]
  ) {
    def serial: Long = Markup.Entity.Occ.unapply(markup).get
    def is_def: Boolean = Markup.Entity.Def.unapply(markup).isDefined
    def kind: String = Markup.Kind.get(markup.properties)
    def name: String = Markup.Name.get(markup.properties)  /*internal name*/
  }

  /*names: a cheap test of the base name first, which every match shares*/
  private def entity_occurrences(
    rendering: VSCode_Rendering,
    range: Text.Range,
    names: String => Boolean,
    pred: (Long, Option[Binding]) => Boolean
  ): List[Occurrence] = {
    val snapshot = rendering.snapshot
    val doc = rendering.model.content.doc
    val node = rendering.model.node_name.node
    for {
      info <- snapshot.cumulate[List[Text.Info[Markup]]](
        range, Nil, Rendering.entity_elements, _ =>
          {
            case (infos, Text.Info(r, XML.Elem(markup @ Markup.Entity.Occ(_), _)))
            if names(base_name(markup)) => Some(Text.Info(r, markup) :: infos)
            case _ => None
          }).flatMap(_.info).distinct
      serial <- Markup.Entity.Occ.unapply(info.info)
      binding =
        if (Markup.Entity.Def.unapply(info.info).isDefined) def_binding(snapshot, info)
        else ref_binding(info.info)
      if pred(serial, binding)
    } yield Occurrence(Line.Node_Range(node, doc.range(info.range)), info.info, binding)
  }

  /*as caret_focus: the entities bound there, else those referred to; at the end of a word,
    the entities of its last character*/
  def focus(rendering: VSCode_Rendering, offset: Text.Offset): List[Occurrence] = {
    def at(range: Text.Range): List[Occurrence] = {
      val occs = entity_occurrences(rendering, range, _ => true, (_, _) => true)
      val defs = occs.filter(_.is_def)
      if (defs.nonEmpty) defs else occs
    }
    at(Text.Range(offset, offset + 1)) match {
      case Nil if offset > 0 => at(Text.Range(offset - 1, offset))
      case occs => occs
    }
  }

  /*every occurrence of the same names: of the same entities, or bound at the same place*/
  def occurrences(resources: VSCode_Resources, entities: List[Occurrence]): List[Occurrence] =
    if (entities.isEmpty) Nil
    else {
      val names = entities.map(occ => base_name(occ.markup)).toSet
      val serials = entities.map(_.serial).toSet
      val bindings = entities.flatMap(_.binding).toSet
      def pred(serial: Long, binding: Option[Binding]): Boolean =
        serials(serial) || binding.exists(bindings)

      for {
        model <- resources.get_models().toList
        rendering = resources.rendering(model)
        occ <- entity_occurrences(rendering, model.content.text_range, names, pred)
      } yield occ
    }


  /* references */

  def references(
    resources: VSCode_Resources,
    rendering: VSCode_Rendering,
    offset: Text.Offset,
    include_declaration: Boolean
  ): List[Line.Node_Range] = {
    val occs = occurrences(resources, focus(rendering, offset))

    /*a binding in no loaded node (but in the session image): the position of its source*/
    val external_defs =
      if (!include_declaration) Nil
      else {
        val bound = occs.filter(_.is_def).flatMap(_.binding).toSet
        occs.filter(occ => !occ.is_def && occ.binding.exists(b => !bound(b)))
          .distinctBy(_.binding)
          .flatMap(occ => rendering.hyperlink_def_position(occ.markup.properties))
      }

    (external_defs ::: occs.filter(occ => include_declaration || !occ.is_def).map(_.node_range))
      .distinct
  }


  /* dependents: unloaded theories that may refer to these entities */

  sealed case class Dependents(
    names: List[String],
    theories: List[JFile],
    in_image: List[JFile]
  )

  /*the theory where an entity is bound, if it is in a loaded node*/
  private def binding_theory(rendering: VSCode_Rendering, occ: Occurrence): Option[String] = {
    val snapshot = rendering.snapshot
    if (occ.is_def) {
      snapshot.commands_loading.headOption.map(_.node_name.theory) orElse
        Some(snapshot.node_name.theory)
    }
    else {
      for {
        id <- Position.Def_Id.unapply(occ.markup.properties)
        (_, command) <- snapshot.find_command(id)
      } yield command.node_name.theory
    }
  }

  private def is_name_char(c: Char): Boolean =
    Symbol.is_ascii_letdig(c) || c == '_' || c == '\''

  /*a name as a word of its own (also qualified): over-approximated, as it is only a filter*/
  def mentions(text: String, name: String): Boolean = {
    def boundary(i: Int): Boolean = i < 0 || i >= text.length || !is_name_char(text(i))
    @tailrec def from(i: Int): Boolean = {
      val j = text.indexOf(name, i)
      j >= 0 && ((boundary(j - 1) && boundary(j + name.length)) || from(j + 1))
    }
    name.nonEmpty && from(0)
  }

  /*Of the given theory files, those that no loaded node has: the ones that import (perhaps
    indirectly) where the entities are bound and mention one of their names. An entity of
    the session image is imported by all of them. Files of theories in the image are not
    checked again, only listed. A theory that uses an entity by notation only, never by its
    name, is not found.*/
  def dependents(
    resources: VSCode_Resources,
    rendering: VSCode_Rendering,
    offset: Text.Offset,
    files: List[JFile]
  ): Dependents = {
    val focus_occs = focus(rendering, offset)
    val names = focus_occs.map(occ => base_name(occ.markup)).distinct
    val targets = focus_occs.map(binding_theory(rendering, _))
    val restrict = if (targets.forall(_.isDefined)) Some(targets.flatten.toSet) else None

    lazy val unloaded =
      for {
        file <- files.distinct
        if resources.get_model(file).isEmpty
        name = resources.node_name(file)
        if name.is_theory
        text <- resources.read_file_content(name)
      } yield (file, name, text)
    lazy val (in_image, outside) = unloaded.partition(u => resources.loaded_theory(u._2))
    def mentioning(us: List[(JFile, Document.Node.Name, String)]) =
      us.filter(u => names.exists(mentions(u._3, _)))

    /*imports by theory: of the loaded nodes as the prover has them, of the other files by
      their headers; a theory of the session image imports no project theory*/
    lazy val imports: Map[String, List[String]] =
      (rendering.snapshot.version.nodes.iterator.map({ case (name, node) =>
        name.theory -> node.header.imports.map(_.theory) }) ++
      outside.iterator.map({ case (_, name, text) =>
        name.theory -> resources.check_thy(name, Scan.char_reader(text)).imports.map(_.theory)
      })).toMap

    def reaches(theory: String, targets: Set[String]): Boolean = {
      @tailrec def search(seen: Set[String], todo: List[String]): Boolean =
        todo match {
          case Nil => false
          case t :: _ if targets(t) => true
          case t :: ts if seen(t) => search(seen, ts)
          case t :: ts => search(seen + t, imports.getOrElse(t, Nil) ::: ts)
        }
      search(Set.empty, imports.getOrElse(theory, Nil))
    }

    if (names.isEmpty) Dependents(Nil, Nil, Nil)
    else {
      val theories =
        mentioning(outside).filter(u => restrict.forall(reaches(u._2.theory, _))).map(_._1)
      Dependents(names, theories, mentioning(in_image).map(_._1))
    }
  }
}
