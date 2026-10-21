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


private theorem list_member_bound {es : List Advanced.Expr} (h : sizeOf es ≤ bound) :
    ∀ e ∈ es, sizeOf e ≤ bound := by
  intro e member
  have := List.sizeOf_lt_of_mem member
  omega

private theorem application_children_size (application : CollationApplication expr es types targets) :
    ∀ e ∈ es, sizeOf e < sizeOf expr := by
  cases application <;> intro e member
  all_goals try { simp at member; rcases member with rfl | rfl <;> simp <;> omega }
  all_goals try { simp at member; subst e; simp; omega }
  all_goals { have := List.sizeOf_lt_of_mem member; simp at this ⊢; omega }

private theorem independent_children_size (shape : IndependentCollationChildren expr es) :
    ∀ e ∈ es, sizeOf e < sizeOf expr := by
  cases shape <;> intro e member
  all_goals try { simp at member; subst e; simp; omega }
  all_goals { have := List.sizeOf_lt_of_mem member; simp at this ⊢; omega }

private theorem subscript_member_size {expr : Advanced.Expr} {subscript : Subscript} (member : expr ∈ subscript.expressions) :
    sizeOf expr < sizeOf subscript := by
  cases subscript with
  | index arg => simp only [Subscript.expressions, List.mem_singleton] at member; subst expr; simp
  | slice lo hi =>
    cases lo <;> cases hi <;> simp [Subscript.expressions] at member
    all_goals first | (subst expr; simp; omega) | (rcases member with rfl | rfl <;> simp <;> omega)

private theorem subscripts_member_size {expr : Advanced.Expr} {indices : List Subscript} (member : expr ∈ indices.flatMap Subscript.expressions) :
    sizeOf expr < sizeOf indices := by
  obtain ⟨index, indexMem, exprMem⟩ := List.mem_flatMap.mp member
  have := List.sizeOf_lt_of_mem indexMem
  have := subscript_member_size exprMem
  omega

private theorem call_expr_member_size {expr : Advanced.Expr} {args : List CallArgument} (member : expr ∈ args.map CallArgument.expression) :
    sizeOf expr < sizeOf args := by
  obtain ⟨arg, argMem, rfl⟩ := List.mem_map.mp member
  have argSize : sizeOf arg < sizeOf args := List.sizeOf_lt_of_mem argMem
  cases arg <;> simp only [CallArgument.expression] <;> simp at argSize ⊢ <;> omega

private theorem branch_first_size {expr : Advanced.Expr} {branches : List (Advanced.Expr × Advanced.Expr)} (member : expr ∈ branches.map (Prod.fst : Advanced.Expr × Advanced.Expr → Advanced.Expr)) :
    sizeOf expr < sizeOf branches := by
  obtain ⟨pair, pairMem, rfl⟩ := List.mem_map.mp member
  have pairSize : sizeOf pair < sizeOf branches := List.sizeOf_lt_of_mem pairMem
  cases pair
  simp at pairSize ⊢
  omega

private theorem branch_result_size {expr : Advanced.Expr} {branches : List (Advanced.Expr × Advanced.Expr)} {otherwise : Option Advanced.Expr} (member : expr ∈ branches.map (Prod.snd : Advanced.Expr × Advanced.Expr → Advanced.Expr) ++ otherwise.toList) :
    sizeOf expr < sizeOf branches + sizeOf otherwise := by
  rcases List.mem_append.mp member with h | h
  · obtain ⟨pair, pairMem, rfl⟩ := List.mem_map.mp h
    have pairSize : sizeOf pair < sizeOf branches := List.sizeOf_lt_of_mem pairMem
    cases pair
    simp at pairSize ⊢
    omega
  · cases otherwise <;> simp_all <;> omega

macro "collation_small" : tactic => `(tactic|
  first
  | assumption
  | (simp_all; omega)
  | (intro e member
     first
     | (have := List.sizeOf_lt_of_mem member; simp_all; omega)
     | (have := subscripts_member_size member; simp_all; omega)
     | (have := call_expr_member_size member; simp_all; omega)
     | (have := branch_first_size member; simp_all; omega)
     | (have := branch_result_size member; simp_all; omega)
     | (simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> simp at small <;> omega)))

private theorem expr_collation_transport
    (valid : ExprCollationValidCore sq profile params env scope expr type derivation) :
    ∀ bound, SubqueriesTranslated sq bound → sizeOf expr ≤ bound →
      ExprCollationValidCore sq profile params env scope (translateExpr expr) type derivation := by
  induction valid using ExprCollationValidCore.rec
    (motive_2 := fun env scope exprs types derivations _ =>
      ∀ bound, SubqueriesTranslated sq bound → (∀ e ∈ exprs, sizeOf e ≤ bound) →
        ExprCollationListValidCore sq profile params env scope (exprs.map translateExpr) types derivations)
    (motive_3 := fun env scope target exprs derivation _ =>
      ∀ bound, SubqueriesTranslated sq bound → (∀ e ∈ exprs, sizeOf e ≤ bound) →
        ArrayCollationValidCore sq profile params env scope target (exprs.map translateExpr) derivation)
    (motive_4 := fun env scope target exprs types derivations _ =>
      ∀ bound, SubqueriesTranslated sq bound → (∀ e ∈ exprs, sizeOf e ≤ bound) →
        ArrayElementsCollationValidCore sq profile params env scope target (exprs.map translateExpr) types derivations)
  case atom typed atom =>
    intro bound preserved small
    exact .atom (expr_valid_translated_core preserved typed (by collation_small)) (collation_atom_translated atom)
  case foldedInteger typed folded =>
    intro bound preserved small
    exact .foldedInteger (expr_valid_translated_core preserved typed small)
      (by simpa only [raw_integer_value_translated] using folded)
  case «exists» query =>
    intro bound preserved small
    simpa only [translateExpr] using
      ExprCollationValidCore.exists (preserved _ _ _ _ (by simp_all; omega) query)
  case scalarQuery query reentry =>
    intro bound preserved small
    simpa only [translateExpr] using
      ExprCollationValidCore.scalarQuery (preserved _ _ _ _ (by simp_all; omega) query) reentry
  case inQuery typed left query selected arguments merge ihLeft =>
    intro bound preserved small
    simpa only [translateExpr, coerced_collation_translated] using
      ExprCollationValidCore.inQuery
        (by simpa only [translateExpr] using expr_valid_translated_core preserved typed small)
        (ihLeft bound preserved (by collation_small))
        (preserved _ _ _ _ (by simp_all; omega) query)
        (by simpa only [scalar_input_translated] using selected) arguments
        (by simpa only [coerced_collation_translated] using merge)
  case inRowQuery typed left query selected pairs ihLeft =>
    intro bound preserved small
    simpa only [translateExpr, List.attach_map_val] using
      ExprCollationValidCore.inRowQuery
        (by simpa only [translateExpr, List.attach_map_val] using
          expr_valid_translated_core preserved typed (by collation_small))
        (ihLeft bound preserved (by collation_small))
        (preserved _ _ _ _ (by simp_all; omega) query)
        (by simpa only [scalar_inputs_translated] using selected)
        (subquery_comparison_collations_translated pairs)
  case parameter present identity supported =>
    intro bound preserved small
    simpa only [translateExpr] using
      ExprCollationValidCore.parameter present
        (identity.trans (translateParameter_index _).symm) supported
  case column resolved =>
    intro bound preserved small
    simpa only [translateExpr] using ExprCollationValidCore.column resolved
  case application typed children application coercions merge ihChildren =>
    intro bound preserved small
    have childrenSmall : ∀ e ∈ _, sizeOf e ≤ bound := fun e h => Nat.le_trans (Nat.le_of_lt (application_children_size application e h)) small
    exact .application (expr_valid_translated_core preserved typed (by collation_small))
      (ihChildren bound preserved (by collation_small))
      (collation_application_translated application)
      (by simpa only [contextual_collations_translated] using coercions) merge
  case independent typed children shape ihChildren =>
    intro bound preserved small
    have childrenSmall : ∀ e ∈ _, sizeOf e ≤ bound := fun e h => Nat.le_trans (Nat.le_of_lt (independent_children_size shape e h)) small
    exact .independent (expr_valid_translated_core preserved typed (by collation_small))
      (ihChildren bound preserved (by collation_small))
      (independent_collation_children_translated shape)
  case cast typed child supported ihChild =>
    intro bound preserved small
    simpa only [translateExpr, coerced_collation_translated] using
      ExprCollationValidCore.cast (by simpa only [translateExpr, List.attach_map_val] using expr_valid_translated_core preserved typed (by collation_small))
        (ihChild bound preserved (by collation_small)) supported
  case collate typed child resolved allowed ihChild =>
    intro bound preserved small
    simpa only [translateExpr] using
      ExprCollationValidCore.collate (by simpa only [translateExpr, List.attach_map_val] using expr_valid_translated_core preserved typed (by collation_small))
        (ihChild bound preserved (by collation_small)) resolved
        (by simpa only [scalar_input_translated] using allowed)
  case castArray typed supported elements ihElements =>
    intro bound preserved small
    simpa only [translateExpr, List.attach_map_val] using
      ExprCollationValidCore.castArray (by simpa only [translateExpr, List.attach_map_val] using expr_valid_translated_core preserved typed (by collation_small)) supported
        (ihElements bound preserved (by collation_small))
  case subscript typed base bounds ihBase ihBounds =>
    intro bound preserved small
    simpa only [translateExpr, List.attach_map_val] using
      ExprCollationValidCore.subscript (by simpa only [translateExpr, List.attach_map_val] using expr_valid_translated_core preserved typed (by collation_small))
        (ihBase bound preserved (by collation_small))
        (by simpa only [collation_subscripts_expressions_translated] using
          (ihBounds bound preserved (by collation_small)))
  case rowComparison typed left right selected pairs ihLeft ihRight =>
    intro bound preserved small
    simpa only [translateExpr, List.attach_map_val] using
      ExprCollationValidCore.rowComparison (by simpa only [translateExpr, List.attach_map_val] using expr_valid_translated_core preserved typed (by collation_small))
        (ihLeft bound preserved (by collation_small))
        (ihRight bound preserved (by collation_small))
        (by simpa only [scalar_inputs_translated] using selected)
        (comparison_collations_translated pairs)
  case rowDistinct typed left right selected pairs ihLeft ihRight =>
    intro bound preserved small
    simpa only [translateExpr, List.attach_map_val] using
      ExprCollationValidCore.rowDistinct (by simpa only [translateExpr, List.attach_map_val] using expr_valid_translated_core preserved typed (by collation_small))
        (ihLeft bound preserved (by collation_small))
        (ihRight bound preserved (by collation_small))
        (by simpa only [scalar_inputs_translated] using selected)
        (comparison_collations_translated pairs)
  case inList typed child children contexts ihChild ihChildren =>
    intro bound preserved small
    simpa only [translateExpr, List.attach_map_val] using
      ExprCollationValidCore.inList
        (by simpa only [translateExpr, List.attach_map_val] using expr_valid_translated_core preserved typed (by collation_small))
        (ihChild bound preserved (by collation_small)) (ihChildren bound preserved (by collation_small)) (in_collations_translated contexts)
  case between typed args low high pairs ihArgs =>
    intro bound preserved small
    simpa only [translateExpr, List.map_cons, List.map_nil] using
      ExprCollationValidCore.between (by simpa only [translateExpr, List.attach_map_val] using expr_valid_translated_core preserved typed (by collation_small))
        (ihArgs bound preserved (by collation_small))
        (by simpa only [scalar_input_translated] using low)
        (by simpa only [scalar_input_translated] using high)
        (comparison_collations_translated pairs)
  case extract typed child selected ihChild =>
    intro bound preserved small
    simpa only [translateExpr] using
      ExprCollationValidCore.extract (by simpa only [translateExpr, List.attach_map_val] using expr_valid_translated_core preserved typed (by collation_small))
        (ihChild bound preserved (by collation_small))
        (by simpa only [scalar_input_translated] using selected)
  case defaultCall typed children callee arguments ihChildren =>
    intro bound preserved small
    simpa only [translateExpr, List.attach_map_val] using
      ExprCollationValidCore.defaultCall (by simpa only [translateExpr, List.attach_map_val] using expr_valid_translated_core preserved typed (by collation_small))
        (ihChildren bound preserved (by collation_small)) callee
        (by simpa only [List.map_map, Function.comp_def, scalar_inputs_translated] using arguments)
  case namedCall typed children callee arguments ihChildren =>
    intro bound preserved small
    simpa only [translateExpr, List.attach_map_val] using
      ExprCollationValidCore.namedCall (by simpa only [translateExpr, List.attach_map_val] using expr_valid_translated_core preserved typed (by collation_small))
        (by simpa only [translated_call_expressions] using
          (ihChildren bound preserved (by collation_small))) callee
        (by simpa only [translated_call_names, translated_call_expressions,
          scalar_inputs_translated] using arguments)
  case substring typed children arguments selected targets coercions merge ihChildren =>
    intro bound preserved small
    simpa only [translateExpr, List.attach_map_val] using
      ExprCollationValidCore.substring (by simpa only [translateExpr, List.attach_map_val] using expr_valid_translated_core preserved typed (by collation_small))
        (ihChildren bound preserved (by collation_small))
        (by simpa only [scalar_inputs_translated] using arguments) selected targets
        (by simpa only [coerced_collations_translated] using coercions) merge
  case searchedCase typed conditions results coercions merge ihConditions ihResults =>
    intro bound preserved small
    simp only [translateExpr_case, Option.map_none]
    apply ExprCollationValidCore.searchedCase
    · simpa only [translateExpr_case, Option.map_none] using expr_valid_translated_core preserved typed (by collation_small)
    · simpa only [List.map_map, Function.comp_def] using
        (ihConditions bound preserved (by collation_small))
    · simpa only [List.map_map, Function.comp_def, List.map_append, Option.toList_map] using
        (ihResults bound preserved (by collation_small))
    · rw [← coerced_collations_translated] at coercions
      simpa only [List.map_map, Function.comp_def, List.map_append, Option.toList_map,
        List.length_map] using coercions
    · exact merge
  case simpleCase typed operandValid conditions comparisons results coercions merge ihOperand ihConditions ihResults =>
    intro bound preserved small
    simp only [translateExpr_case, Option.map_some]
    apply ExprCollationValidCore.simpleCase
    · simpa only [translateExpr_case, Option.map_some] using expr_valid_translated_core preserved typed (by collation_small)
    · exact (ihOperand bound preserved (by collation_small))
    · simpa only [List.map_map, Function.comp_def] using
        (ihConditions bound preserved (by collation_small))
    · simpa only [List.map_map, Function.comp_def, case_operand_type_translated,
        coerced_collation_translated] using case_condition_collations_translated comparisons
    · simpa only [List.map_map, Function.comp_def, List.map_append, Option.toList_map] using
        (ihResults bound preserved (by collation_small))
    · rw [← coerced_collations_translated] at coercions
      simpa only [List.map_map, Function.comp_def, List.map_append, Option.toList_map,
        List.length_map] using coercions
    · exact merge
  case nil => intros; exact .nil
  case cons head tail ihHead ihTail bound preserved small =>
    have headSmall := small _ (List.mem_cons_self ..)
    simpa only [List.map_cons] using ExprCollationListValidCore.cons (ihHead bound preserved (by collation_small)) (ihTail bound preserved (fun e h => small e (List.mem_cons_of_mem _ h)))
  case targeted elements coercions merge ihElements bound preserved small =>
    exact .targeted (ihElements bound preserved (by collation_small))
      (by simpa only [List.length_map, scalar_inputs_translated,
        coerced_collations_translated] using coercions) merge
  case nil => intros; exact .nil
  case ordinary category head tail ihHead ihTail bound preserved small =>
    have headSmall := small _ (List.mem_cons_self ..)
    simpa only [List.map_cons] using
      ArrayElementsCollationValidCore.ordinary ((ordinary_array_element_translated _).mpr category)
        (ihHead bound preserved (by collation_small)) (ihTail bound preserved (fun e h => small e (List.mem_cons_of_mem _ h)))
  case nested head tail ihHead ihTail bound preserved small =>
    have headSmall := small _ (List.mem_cons_self ..)
    simpa only [List.map_cons, translateExpr, List.attach_map_val] using
      ArrayElementsCollationValidCore.nested (ihHead bound preserved (by
        intro e h
        have := List.sizeOf_lt_of_mem h
        simp at headSmall
        omega)) (ihTail bound preserved (fun e h => small e (List.mem_cons_of_mem _ h)))


theorem expr_collation_valid_translated_core
    (preserved : SubqueriesTranslated sq bound)
    (valid : ExprCollationValidCore sq profile params env scope expr type derivation)
    (small : sizeOf expr ≤ bound := by simp_all <;> omega) :
    ExprCollationValidCore sq profile params env scope (translateExpr expr) type derivation :=
  expr_collation_transport valid bound preserved small

theorem expr_collation_list_valid_translated_core
    (preserved : SubqueriesTranslated sq bound)
    (valid : ExprCollationListValidCore sq profile params env scope exprs types derivations)
    (small : ∀ e ∈ exprs, sizeOf e ≤ bound) :
    ExprCollationListValidCore sq profile params env scope (exprs.map translateExpr) types derivations := by
  cases valid with
  | nil => exact .nil
  | cons head tail =>
    exact .cons (expr_collation_valid_translated_core preserved head (small _ (List.mem_cons_self ..)))
      (expr_collation_list_valid_translated_core preserved tail (fun e h => small e (List.mem_cons_of_mem _ h)))
termination_by exprs

mutual
  theorem array_collation_valid_translated_core
      (preserved : SubqueriesTranslated sq bound)
      (valid : ArrayCollationValidCore sq profile params env scope target exprs derivation)
      (small : ∀ e ∈ exprs, sizeOf e ≤ bound) :
      ArrayCollationValidCore sq profile params env scope target (exprs.map translateExpr) derivation := by
    cases valid with
    | targeted elements coercions merge =>
      exact .targeted (array_elements_collation_valid_translated_core preserved elements small)
        (by simpa only [List.length_map, scalar_inputs_translated, coerced_collations_translated] using coercions) merge
  termination_by (sizeOf exprs, 1)

  theorem array_elements_collation_valid_translated_core
      (preserved : SubqueriesTranslated sq bound)
      (valid : ArrayElementsCollationValidCore sq profile params env scope target exprs types derivations)
      (small : ∀ e ∈ exprs, sizeOf e ≤ bound) :
      ArrayElementsCollationValidCore sq profile params env scope target (exprs.map translateExpr) types derivations := by
    cases valid with
    | nil => exact .nil
    | ordinary category head tail =>
      exact .ordinary ((ordinary_array_element_translated _).mpr category)
        (expr_collation_valid_translated_core preserved head (small _ (List.mem_cons_self ..)))
        (array_elements_collation_valid_translated_core preserved tail (fun e h => small e (List.mem_cons_of_mem _ h)))
    | nested head tail =>
      have headSmall := small _ (List.mem_cons_self ..)
      simpa only [List.map_cons, translateExpr, List.attach_map_val] using
        ArrayElementsCollationValidCore.nested
          (array_collation_valid_translated_core preserved head (by
            intro e h
            have := List.sizeOf_lt_of_mem h
            simp at headSmall
            omega))
          (array_elements_collation_valid_translated_core preserved tail (fun e h => small e (List.mem_cons_of_mem _ h)))
  termination_by (sizeOf exprs, 0)
end

private theorem no_subqueries_collation_translated (bound : Nat) :
    SubqueriesTranslated NoSubqueries bound := by
  intro env query output uses small impossible
  exact False.elim impossible

theorem expr_collation_valid_translated
    (valid : ExprCollationValid profile params scope expr type derivation) :
    ExprCollationValid profile params scope (translateExpr expr) type derivation :=
  expr_collation_valid_translated_core (no_subqueries_collation_translated (sizeOf expr)) valid

theorem expr_collation_list_valid_translated
    (valid : ExprCollationListValid profile params scope exprs types derivations) :
    ExprCollationListValid profile params scope (exprs.map translateExpr) types derivations :=
  expr_collation_list_valid_translated_core (no_subqueries_collation_translated (sizeOf exprs)) valid
    (list_member_bound (Nat.le_refl _))

theorem array_collation_valid_translated
    (valid : ArrayCollationValid profile params scope target exprs derivation) :
    ArrayCollationValid profile params scope target (exprs.map translateExpr) derivation :=
  array_collation_valid_translated_core (no_subqueries_collation_translated (sizeOf exprs)) valid
    (list_member_bound (Nat.le_refl _))

theorem array_elements_collation_valid_translated
    (valid : ArrayElementsCollationValid profile params scope target exprs types derivations) :
    ArrayElementsCollationValid profile params scope target (exprs.map translateExpr) types derivations :=
  array_elements_collation_valid_translated_core (no_subqueries_collation_translated (sizeOf exprs)) valid
    (list_member_bound (Nat.le_refl _))

end SQLean.RenderContract
