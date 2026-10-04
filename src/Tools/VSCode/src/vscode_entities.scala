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
*/

package isabelle.vscode


import isabelle._


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
}
