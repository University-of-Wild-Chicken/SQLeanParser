import SQLean.RenderContract.ExpressionPreservation

/-! Every independent expression-collation derivation survives parameter-only
translation. Argument order, contextual coercion, collation strength and exact
stored identity remain unchanged. -/
namespace SQLean.RenderContract
open Advanced SelectContract
set_option maxHeartbeats 1000000

@[simp] theorem collation_subscript_expressions_translated (subscript : Subscript) :
    (translateSubscript subscript).expressions =
      subscript.expressions.map translateExpr := by
  cases subscript with
  | index expr => simp only [translateSubscript, Subscript.expressions, List.map_cons, List.map_nil]
  | slice lower upper =>
      cases lower <;> cases upper <;>
        simp only [translateSubscript, Subscript.expressions, Option.toList,
          List.map_append, List.map_cons, List.map_nil]

@[simp] theorem collation_subscripts_expressions_translated (subscripts : List Subscript) :
    (subscripts.map translateSubscript).flatMap Subscript.expressions =
      (subscripts.flatMap Subscript.expressions).map translateExpr := by
  simp only [List.flatMap_map, List.map_flatMap,
    collation_subscript_expressions_translated]

theorem expr_collation_valid_translated
    (valid : ExprCollationValid profile params scope expr type derivation) :
    ExprCollationValid profile params scope (translateExpr expr) type derivation := by
  induction valid using ExprCollationValid.rec
    (motive_2 := fun exprs types derivations _ =>
      ExprCollationListValid profile params scope (exprs.map translateExpr) types derivations)
    (motive_3 := fun target exprs derivation _ =>
      ArrayCollationValid profile params scope target (exprs.map translateExpr) derivation)
    (motive_4 := fun target exprs types derivations _ =>
      ArrayElementsCollationValid profile params scope target (exprs.map translateExpr) types derivations)
  case atom typed atom =>
    exact .atom (expr_valid_translated typed) (collation_atom_translated atom)
  case parameter present identity supported =>
    simpa only [translateExpr] using
      ExprCollationValid.parameter present
        (identity.trans (translateParameter_index _).symm) supported
  case column resolved =>
    simpa only [translateExpr] using ExprCollationValid.column resolved
  case application typed children application coercions merge ihChildren =>
    exact .application (expr_valid_translated typed)
      ihChildren
      (collation_application_translated application)
      (by simpa only [contextual_collations_translated] using coercions) merge
  case independent typed children shape ihChildren =>
    exact .independent (expr_valid_translated typed)
      ihChildren
      (independent_collation_children_translated shape)
  case cast typed child supported ihChild =>
    simpa only [translateExpr, coerced_collation_translated] using
      ExprCollationValid.cast (by simpa only [translateExpr, List.attach_map_val] using expr_valid_translated typed)
        ihChild supported
  case collate typed child resolved allowed ihChild =>
    simpa only [translateExpr] using
      ExprCollationValid.collate (by simpa only [translateExpr, List.attach_map_val] using expr_valid_translated typed)
        ihChild resolved
        (by simpa only [scalar_input_translated] using allowed)
  case castArray typed supported elements ihElements =>
    simpa only [translateExpr, List.attach_map_val] using
      ExprCollationValid.castArray (by simpa only [translateExpr, List.attach_map_val] using expr_valid_translated typed) supported
        ihElements
  case subscript typed base bounds ihBase ihBounds =>
    simpa only [translateExpr, List.attach_map_val] using
      ExprCollationValid.subscript (by simpa only [translateExpr, List.attach_map_val] using expr_valid_translated typed)
        ihBase
        (by simpa only [collation_subscripts_expressions_translated] using
          ihBounds)
  case rowComparison typed left right selected pairs ihLeft ihRight =>
    simpa only [translateExpr, List.attach_map_val] using
      ExprCollationValid.rowComparison (by simpa only [translateExpr, List.attach_map_val] using expr_valid_translated typed)
        ihLeft
        ihRight
        (by simpa only [scalar_inputs_translated] using selected)
        (comparison_collations_translated pairs)
  case rowDistinct typed left right selected pairs ihLeft ihRight =>
    simpa only [translateExpr, List.attach_map_val] using
      ExprCollationValid.rowDistinct (by simpa only [translateExpr, List.attach_map_val] using expr_valid_translated typed)
        ihLeft
        ihRight
        (by simpa only [scalar_inputs_translated] using selected)
        (comparison_collations_translated pairs)
  case inList typed child children contexts ihChild ihChildren =>
    simpa only [translateExpr, List.attach_map_val] using
      ExprCollationValid.inList
        (by simpa only [translateExpr, List.attach_map_val] using expr_valid_translated typed)
        ihChild ihChildren (in_collations_translated contexts)
  case between typed args low high pairs ihArgs =>
    simpa only [translateExpr, List.map_cons, List.map_nil] using
      ExprCollationValid.between (by simpa only [translateExpr, List.attach_map_val] using expr_valid_translated typed)
        ihArgs
        (by simpa only [scalar_input_translated] using low)
        (by simpa only [scalar_input_translated] using high)
        (comparison_collations_translated pairs)
  case extract typed child selected ihChild =>
    simpa only [translateExpr] using
      ExprCollationValid.extract (by simpa only [translateExpr, List.attach_map_val] using expr_valid_translated typed)
        ihChild
        (by simpa only [scalar_input_translated] using selected)
  case defaultCall typed children callee arguments ihChildren =>
    simpa only [translateExpr, List.attach_map_val] using
      ExprCollationValid.defaultCall (by simpa only [translateExpr, List.attach_map_val] using expr_valid_translated typed)
        ihChildren callee
        (by simpa only [List.map_map, Function.comp_def, scalar_inputs_translated] using arguments)
  case namedCall typed children callee arguments ihChildren =>
    simpa only [translateExpr, List.attach_map_val] using
      ExprCollationValid.namedCall (by simpa only [translateExpr, List.attach_map_val] using expr_valid_translated typed)
        (by simpa only [translated_call_expressions] using
          ihChildren) callee
        (by simpa only [translated_call_names, translated_call_expressions,
          scalar_inputs_translated] using arguments)
  case substring typed children arguments selected targets coercions merge ihChildren =>
    simpa only [translateExpr, List.attach_map_val] using
      ExprCollationValid.substring (by simpa only [translateExpr, List.attach_map_val] using expr_valid_translated typed)
        ihChildren
        (by simpa only [scalar_inputs_translated] using arguments) selected targets
        (by simpa only [coerced_collations_translated] using coercions) merge
  case searchedCase typed conditions results coercions merge ihConditions ihResults =>
    simp only [translateExpr_case, Option.map_none]
    apply ExprCollationValid.searchedCase
    · simpa only [translateExpr_case, Option.map_none] using expr_valid_translated typed
    · simpa only [List.map_map, Function.comp_def] using
        ihConditions
    · simpa only [List.map_map, Function.comp_def, List.map_append, Option.toList_map] using
        ihResults
    · rw [← coerced_collations_translated] at coercions
      simpa only [List.map_map, Function.comp_def, List.map_append, Option.toList_map,
        List.length_map] using coercions
    · exact merge
  case simpleCase typed operandValid conditions comparisons results coercions merge ihOperand ihConditions ihResults =>
    simp only [translateExpr_case, Option.map_some]
    apply ExprCollationValid.simpleCase
    · simpa only [translateExpr_case, Option.map_some] using expr_valid_translated typed
    · exact ihOperand
    · simpa only [List.map_map, Function.comp_def] using
        ihConditions
    · simpa only [List.map_map, Function.comp_def, case_operand_type_translated,
        coerced_collation_translated] using case_condition_collations_translated comparisons
    · simpa only [List.map_map, Function.comp_def, List.map_append, Option.toList_map] using
        ihResults
    · rw [← coerced_collations_translated] at coercions
      simpa only [List.map_map, Function.comp_def, List.map_append, Option.toList_map,
        List.length_map] using coercions
    · exact merge
  case nil => exact .nil
  case cons head tail ihHead ihTail =>
    simpa only [List.map_cons] using ExprCollationListValid.cons ihHead ihTail
  case targeted elements coercions merge ihElements =>
    exact .targeted ihElements
      (by simpa only [List.length_map, scalar_inputs_translated,
        coerced_collations_translated] using coercions) merge
  case nil => exact .nil
  case ordinary category head tail ihHead ihTail =>
    simpa only [List.map_cons] using
      ArrayElementsCollationValid.ordinary ((ordinary_array_element_translated _).mpr category)
        ihHead ihTail
  case nested head tail ihHead ihTail =>
    simpa only [List.map_cons, translateExpr, List.attach_map_val] using
      ArrayElementsCollationValid.nested ihHead ihTail

theorem expr_collation_list_valid_translated
    (valid : ExprCollationListValid profile params scope exprs types derivations) :
    ExprCollationListValid profile params scope (exprs.map translateExpr) types derivations := by
  induction valid using ExprCollationListValid.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
  all_goals try exact True.intro
  case nil => exact .nil
  case cons head tail _ ihTail =>
    simpa only [List.map_cons] using
      ExprCollationListValid.cons (expr_collation_valid_translated head) ihTail

theorem array_collation_valid_translated
    (valid : ArrayCollationValid profile params scope target exprs derivation) :
    ArrayCollationValid profile params scope target (exprs.map translateExpr) derivation := by
  induction valid using ArrayCollationValid.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_4 := fun target exprs types derivations _ =>
      ArrayElementsCollationValid profile params scope target (exprs.map translateExpr) types derivations)
  all_goals try exact True.intro
  case targeted elements coercions merge ihElements =>
    exact .targeted ihElements
      (by simpa only [List.length_map, scalar_inputs_translated,
        coerced_collations_translated] using coercions) merge
  case nil => exact .nil
  case ordinary category head tail _ ihTail =>
    simpa only [List.map_cons] using
      ArrayElementsCollationValid.ordinary ((ordinary_array_element_translated _).mpr category)
        (expr_collation_valid_translated head) ihTail
  case nested head tail ihHead ihTail =>
    simpa only [List.map_cons, translateExpr, List.attach_map_val] using
      ArrayElementsCollationValid.nested ihHead ihTail

theorem array_elements_collation_valid_translated
    (valid : ArrayElementsCollationValid profile params scope target exprs types derivations) :
    ArrayElementsCollationValid profile params scope target (exprs.map translateExpr) types derivations := by
  induction valid using ArrayElementsCollationValid.rec
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ => True)
    (motive_3 := fun target exprs derivation _ =>
      ArrayCollationValid profile params scope target (exprs.map translateExpr) derivation)
  all_goals try exact True.intro
  case targeted elements coercions merge ihElements =>
    exact .targeted ihElements
      (by simpa only [List.length_map, scalar_inputs_translated,
        coerced_collations_translated] using coercions) merge
  case nil => exact .nil
  case ordinary category head tail _ ihTail =>
    simpa only [List.map_cons] using
      ArrayElementsCollationValid.ordinary ((ordinary_array_element_translated _).mpr category)
        (expr_collation_valid_translated head) ihTail
  case nested head tail ihHead ihTail =>
    simpa only [List.map_cons, translateExpr, List.attach_map_val] using
      ArrayElementsCollationValid.nested ihHead ihTail

end SQLean.RenderContract
