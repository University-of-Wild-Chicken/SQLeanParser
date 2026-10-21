import SQLean.RenderContract.Translation
import SQLean.SelectContract.CollationRules

/-! Parameter-only translation preserves the independent local collation
premises. These proofs neither consult executable inference nor interpret
locale-sensitive query evaluation. -/
namespace SQLean.RenderContract
open Advanced SelectContract
set_option maxHeartbeats 1000000

private theorem collation_translate_case (operand : Option Advanced.Expr)
    (branches : List (Advanced.Expr × Advanced.Expr)) (otherwise : Option Advanced.Expr) :
    translateExpr (.caseExpr operand branches otherwise) =
      .caseExpr (operand.map translateExpr)
        (branches.map fun pair => (translateExpr pair.1, translateExpr pair.2))
        (otherwise.map translateExpr) := by
  rw [translateExpr.eq_def]
  simp only [List.attach_map_val (f := fun pair : Advanced.Expr × Advanced.Expr =>
    (translateExpr pair.1, translateExpr pair.2))]
  cases operand <;> cases otherwise <;> rfl

@[simp] theorem collation_scalar_input_translated (expr : Advanced.Expr) (type : ExprType) :
    scalarInput (translateExpr expr) type = scalarInput expr type := by
  cases expr <;> simp only [translateExpr, collation_translate_case, scalarInput]
  exact collation_scalar_input_translated _ _
termination_by sizeOf expr
decreasing_by all_goals (simp_all <;> omega)

@[simp] theorem collation_scalar_inputs_translated (exprs : List Advanced.Expr)
    (types : List ExprType) :
    scalarInputs (exprs.map translateExpr) types = scalarInputs exprs types := by
  induction exprs generalizing types with
  | nil => cases types <;> rfl
  | cons expr exprs ih =>
      cases types with
      | nil => rfl
      | cons type types =>
          simpa only [scalarInputs, List.zip_cons_cons, List.map_cons,
            collation_scalar_input_translated] using
            congrArg (scalarInput expr type :: ·) (ih types)

@[simp] theorem coerced_collation_translated (expr : Advanced.Expr) (type : ExprType)
    (target : ScalarType) (derivation : CollationDerivation) :
    coercedCollation (translateExpr expr) type target derivation =
      coercedCollation expr type target derivation := by
  cases expr <;> simp only [translateExpr, collation_translate_case, coercedCollation, scalarInput]
  split
  · rfl
  · exact coerced_collation_translated _ _ _ _
termination_by sizeOf expr
decreasing_by all_goals (simp_all <;> omega)

@[simp] theorem coerced_collations_translated (exprs : List Advanced.Expr)
    (types : List ExprType) (derivations : List CollationDerivation)
    (targets : List ScalarType) :
    coercedCollations (exprs.map translateExpr) types derivations targets =
      coercedCollations exprs types derivations targets := by
  induction exprs generalizing types derivations targets with
  | nil => cases types <;> cases derivations <;> cases targets <;> rfl
  | cons expr exprs ih =>
      cases types <;> cases derivations <;> cases targets <;>
        simp only [List.map_cons, coercedCollations, coerced_collation_translated, ih]

@[simp] theorem contextual_collations_translated (exprs : List Advanced.Expr)
    (types : List ExprType) (derivations : List CollationDerivation)
    (targets : List (Option ScalarType)) :
    contextualCollations (exprs.map translateExpr) types derivations targets =
      contextualCollations exprs types derivations targets := by
  induction exprs generalizing types derivations targets with
  | nil => cases types <;> cases derivations <;> cases targets <;> rfl
  | cons expr exprs ih =>
      cases types <;> cases derivations <;> cases targets <;>
        simp only [List.map_cons, contextualCollations, coerced_collation_translated, ih]

@[simp] theorem projected_collation_translated (expr : Advanced.Expr) (type : ExprType)
    (derivation : CollationDerivation) :
    projectedCollation (translateExpr expr) type derivation = projectedCollation expr type derivation := by
  simp only [projectedCollation, coerced_collation_translated]

@[simp] theorem unknown_collation_sort_key_translated (profile : Profile) (expr : Advanced.Expr) :
    unknownCollationSortKey profile (translateExpr expr) = unknownCollationSortKey profile expr := by
  cases expr <;> simp only [translateExpr, collation_translate_case, unknownCollationSortKey]
  rw [unknown_collation_sort_key_translated]
termination_by sizeOf expr
decreasing_by all_goals (simp_all <;> omega)

@[simp] theorem pending_origin_translated (expr : Advanced.Expr) (type : ExprType) :
    pendingOrigin (translateExpr expr) type = pendingOrigin expr type := by
  simp only [pendingOrigin, collation_scalar_input_translated]
  cases expr <;> cases scalarInput _ type <;> simp only [translateExpr, collation_translate_case]

@[simp] theorem case_operand_type_translated (expr : Advanced.Expr) (type : ExprType) :
    caseOperandType type (translateExpr expr) = caseOperandType type expr := by
  simp only [caseOperandType, collation_scalar_input_translated]

private theorem collation_ordinary_distinct_translated (expr : Advanced.Expr) :
    OrdinaryDistinctOperand (translateExpr expr) ↔ OrdinaryDistinctOperand expr := by
  cases expr <;> simp only [translateExpr, collation_translate_case, OrdinaryDistinctOperand]

theorem collation_application_translated
    (application : CollationApplication expr exprs types targets) :
    CollationApplication (translateExpr expr) (exprs.map translateExpr) types targets := by
  cases application with
  | boolean op ordinary =>
      simp only [translateExpr, List.map_cons, List.map_nil]
      exact .boolean op ordinary
  | arithmetic op ordinary selected =>
      simp only [translateExpr, List.map_cons, List.map_nil]
      exact .arithmetic op ordinary selected
  | comparison op selected =>
      simp only [translateExpr, List.map_cons, List.map_nil]
      apply CollationApplication.comparison op
      simpa only [collation_scalar_input_translated] using selected
  | concat selected =>
      simp only [translateExpr, List.map_cons, List.map_nil]
      apply CollationApplication.concat
      simpa only [collation_scalar_input_translated] using selected
  | arrayConcat selected =>
      simp only [translateExpr, List.map_cons, List.map_nil]
      apply CollationApplication.arrayConcat
      simpa only [collation_scalar_input_translated] using selected
  | distinct left right selected =>
      simp only [translateExpr, List.map_cons, List.map_nil]
      apply CollationApplication.distinct
      · exact (collation_ordinary_distinct_translated _).mpr left
      · exact (collation_ordinary_distinct_translated _).mpr right
      · simpa only [collation_scalar_input_translated] using selected
  | unary selected =>
      simp only [translateExpr, List.map_cons, List.map_nil]
      exact .unary selected
  | pattern selected =>
      simp only [translateExpr, List.map_cons, List.map_nil]
      apply CollationApplication.pattern
      simpa only [collation_scalar_input_translated] using selected
  | byteaPattern left right =>
      simp only [translateExpr, List.map_cons, List.map_nil]
      exact .byteaPattern left right
  | ilike selected =>
      simp only [translateExpr, List.map_cons, List.map_nil]
      apply CollationApplication.ilike
      simpa only [collation_scalar_input_translated] using selected
  | regex selected =>
      simp only [translateExpr, List.map_cons, List.map_nil]
      apply CollationApplication.regex
      simpa only [collation_scalar_input_translated] using selected
  | jsonAccess selected =>
      simp only [translateExpr, List.map_cons, List.map_nil]
      apply CollationApplication.jsonAccess
      simpa only [collation_scalar_input_translated] using selected
  | jsonExistence selected =>
      simp only [translateExpr, List.map_cons, List.map_nil]
      apply CollationApplication.jsonExistence
      simpa only [collation_scalar_input_translated] using selected
  | containment selected =>
      simp only [translateExpr, List.map_cons, List.map_nil]
      apply CollationApplication.containment
      simpa only [collation_scalar_input_translated] using selected
  | arrayContainment selected =>
      simp only [translateExpr, List.map_cons, List.map_nil]
      apply CollationApplication.arrayContainment
      simpa only [collation_scalar_input_translated] using selected
  | overlap selected =>
      simp only [translateExpr, List.map_cons, List.map_nil]
      apply CollationApplication.overlap
      simpa only [collation_scalar_input_translated] using selected
  | array common =>
      simp only [translateExpr, List.attach_map_val]
      simpa only [List.length_map] using
        CollationApplication.array (es := exprs.map translateExpr)
          (by simpa only [collation_scalar_inputs_translated] using common)
  | call callee selected =>
      simp only [translateExpr, List.attach_map_val]
      apply CollationApplication.call callee
      simpa only [collation_scalar_inputs_translated] using selected
  | variadicCall callee kind =>
      simp only [translateExpr, List.attach_map_val]
      simpa only [List.length_map] using
        CollationApplication.variadicCall (es := exprs.map translateExpr) callee kind
  | @concatWS name separator es separatorType ts callee =>
      simp only [translateExpr, List.attach_map_val, List.map_cons]
      simpa only [List.length_map] using
        CollationApplication.concatWS (separator := translateExpr separator)
          (es := es.map translateExpr) (separatorType := separatorType) (ts := ts) callee
  | coalesce common =>
      simp only [translateExpr, List.attach_map_val]
      simpa only [List.length_map] using
        CollationApplication.coalesce (es := exprs.map translateExpr)
          (by simpa only [collation_scalar_inputs_translated] using common)
  | greatest common =>
      simp only [translateExpr, List.attach_map_val]
      simpa only [List.length_map] using
        CollationApplication.greatest (es := exprs.map translateExpr)
          (by simpa only [collation_scalar_inputs_translated] using common)
  | least common =>
      simp only [translateExpr, List.attach_map_val]
      simpa only [List.length_map] using
        CollationApplication.least (es := exprs.map translateExpr)
          (by simpa only [collation_scalar_inputs_translated] using common)
  | nullIf selected =>
      simp only [translateExpr, List.map_cons, List.map_nil]
      apply CollationApplication.nullIf
      simpa only [collation_scalar_input_translated] using selected
  | quantified selected inputs =>
      simp only [translateExpr, List.map_cons, List.map_nil]
      apply CollationApplication.quantified ?_ inputs
      simpa only [collation_scalar_input_translated] using selected

theorem collation_atom_translated (atom : CollationAtom expr type derivation) :
    CollationAtom (translateExpr expr) type derivation := by
  cases atom <;> simp only [translateExpr] <;> constructor

theorem independent_collation_children_translated
    (shape : IndependentCollationChildren expr exprs) :
    IndependentCollationChildren (translateExpr expr) (exprs.map translateExpr) := by
  cases shape with
  | isNull =>
      simp only [translateExpr, List.map_cons, List.map_nil]
      exact .isNull
  | isNullRow =>
      simp only [translateExpr, List.attach_map_val]
      exact .isNullRow
  | distinctNullLeft =>
      simp only [translateExpr, List.map_cons, List.map_nil]
      exact .distinctNullLeft
  | distinctNullRight =>
      simp only [translateExpr, List.map_cons, List.map_nil]
      exact .distinctNullRight
  | distinctRowNullLeft =>
      simp only [translateExpr, List.attach_map_val]
      exact .distinctRowNullLeft
  | distinctRowNullRight =>
      simp only [translateExpr, List.attach_map_val]
      exact .distinctRowNullRight

theorem comparison_collations_translated
    (pairs : ComparisonCollations as ats ads bs bts bds signatures) :
    ComparisonCollations (as.map translateExpr) ats ads
      (bs.map translateExpr) bts bds signatures := by
  induction pairs with
  | nil => exact .nil
  | cons coercion merge tail ih =>
      simp only [List.map_cons]
      exact .cons (by
        rw [← contextual_collations_translated] at coercion
        simpa only [List.map_cons, List.map_nil] using coercion) merge ih

theorem subquery_comparison_collations_translated
    (pairs : SubqueryComparisonCollations exprs types derivations columns signatures) :
    SubqueryComparisonCollations (exprs.map translateExpr) types derivations columns signatures := by
  induction pairs with
  | nil => exact .nil
  | cons arguments merge tail ih =>
      simp only [List.map_cons]
      exact .cons arguments (by simpa only [coerced_collation_translated] using merge) ih

theorem case_condition_collations_translated
    (conditions : CaseConditionCollations operand derivation exprs types derivations) :
    CaseConditionCollations operand derivation (exprs.map translateExpr) types derivations := by
  induction conditions with
  | nil => exact .nil
  | cons selected arguments merge tail ih =>
      simp only [List.map_cons]
      exact .cons (by simpa only [collation_scalar_input_translated] using selected)
        arguments (by simpa only [coerced_collation_translated] using merge) ih

mutual
  @[simp] theorem collation_no_var_expr_translated (expr : Advanced.Expr) :
      collationNoVarExpr (translateExpr expr) = collationNoVarExpr expr := by
    cases expr with
    | literal value => simp only [translateExpr, collationNoVarExpr]
    | null => simp only [translateExpr, collationNoVarExpr]
    | contextValue value => simp only [translateExpr, collationNoVarExpr]
    | decimal raw => simp only [translateExpr, collationNoVarExpr]
    | parameter parameter => simp only [translateExpr, collationNoVarExpr]
    | column qualifier name schema => simp only [translateExpr, collationNoVarExpr]
    | countAll => simp only [translateExpr, collationNoVarExpr]
    | collate arg name => simp only [translateExpr, collationNoVarExpr, collation_no_var_expr_translated arg]
    | inQuery arg query => simp only [translateExpr, collationNoVarExpr, collation_no_var_expr_translated arg]
    | «exists» query => simp only [translateExpr, collationNoVarExpr]
    | scalarQuery query => simp only [translateExpr, collationNoVarExpr]
    | binary op left right =>
      simp only [translateExpr, collationNoVarExpr, collation_no_var_expr_translated left, collation_no_var_expr_translated right]
    | concat left right =>
      simp only [translateExpr, collationNoVarExpr, collation_no_var_expr_translated left, collation_no_var_expr_translated right]
    | distinctFrom left right negated =>
      simp only [translateExpr, collationNoVarExpr, collation_no_var_expr_translated left, collation_no_var_expr_translated right]
    | pattern arg pattern insensitive =>
      simp only [translateExpr, collationNoVarExpr, collation_no_var_expr_translated arg, collation_no_var_expr_translated pattern]
    | regex arg pattern insensitive negated =>
      simp only [translateExpr, collationNoVarExpr, collation_no_var_expr_translated arg, collation_no_var_expr_translated pattern]
    | jsonAccess op arg key =>
      simp only [translateExpr, collationNoVarExpr, collation_no_var_expr_translated arg, collation_no_var_expr_translated key]
    | jsonExistence op arg keys =>
      simp only [translateExpr, collationNoVarExpr, collation_no_var_expr_translated arg, collation_no_var_expr_translated keys]
    | containment left right containedBy =>
      simp only [translateExpr, collationNoVarExpr, collation_no_var_expr_translated left, collation_no_var_expr_translated right]
    | overlap left right =>
      simp only [translateExpr, collationNoVarExpr, collation_no_var_expr_translated left, collation_no_var_expr_translated right]
    | quantifiedComparison op quantifier left right =>
      simp only [translateExpr, collationNoVarExpr, collation_no_var_expr_translated left, collation_no_var_expr_translated right]
    | nullIf left right =>
      simp only [translateExpr, collationNoVarExpr, collation_no_var_expr_translated left, collation_no_var_expr_translated right]
    | filteredAggregate aggregate predicate =>
      simp only [translateExpr, collationNoVarExpr, collation_no_var_expr_translated aggregate, collation_no_var_expr_translated predicate]
    | unary op arg =>
      simp only [translateExpr, collationNoVarExpr, collation_no_var_expr_translated arg]
    | aggregate fn arg distinct =>
      simp only [translateExpr, collationNoVarExpr, collation_no_var_expr_translated arg]
    | isNull arg negated =>
      simp only [translateExpr, collationNoVarExpr, collation_no_var_expr_translated arg]
    | extract field arg =>
      simp only [translateExpr, collationNoVarExpr, collation_no_var_expr_translated arg]
    | cast arg target =>
      simp only [translateExpr, collationNoVarExpr, collation_no_var_expr_translated arg]
    | between arg lower upper negated =>
      simp only [translateExpr, collationNoVarExpr, collation_no_var_expr_translated arg, collation_no_var_expr_translated lower, collation_no_var_expr_translated upper]
    | array elements =>
      simp only [translateExpr, List.attach_map_val, collationNoVarExpr, collation_no_var_exprs_translated elements]
    | row elements =>
      simp only [translateExpr, List.attach_map_val, collationNoVarExpr, collation_no_var_exprs_translated elements]
    | substring form args =>
      simp only [translateExpr, List.attach_map_val, collationNoVarExpr, collation_no_var_exprs_translated args]
    | call name args =>
      simp only [translateExpr, List.attach_map_val, collationNoVarExpr, collation_no_var_exprs_translated args]
    | coalesce args =>
      simp only [translateExpr, List.attach_map_val, collationNoVarExpr, collation_no_var_exprs_translated args]
    | greatest args =>
      simp only [translateExpr, List.attach_map_val, collationNoVarExpr, collation_no_var_exprs_translated args]
    | least args =>
      simp only [translateExpr, List.attach_map_val, collationNoVarExpr, collation_no_var_exprs_translated args]
    | namedCall name args =>
      simp only [translateExpr, List.attach_map_val, collationNoVarExpr, collation_no_var_arguments_translated args]
    | subscript base indices =>
      simp only [translateExpr, List.attach_map_val, collationNoVarExpr,
        collation_no_var_expr_translated base, collation_no_var_subscripts_translated indices]
    | inList arg values =>
      simp only [translateExpr, List.attach_map_val, collationNoVarExpr,
        collation_no_var_expr_translated arg, collation_no_var_exprs_translated values]
    | caseExpr operand branches otherwise =>
      cases operand with
      | none =>
        cases otherwise with
        | none => simp only [translateExpr, collationNoVarExpr,
            List.attach_map_val (f := fun pair : Advanced.Expr × Advanced.Expr =>
              (translateExpr pair.1, translateExpr pair.2)), collation_no_var_branches_translated branches]
        | some value => simp only [translateExpr, collationNoVarExpr,
            List.attach_map_val (f := fun pair : Advanced.Expr × Advanced.Expr =>
              (translateExpr pair.1, translateExpr pair.2)), collation_no_var_branches_translated branches,
            collation_no_var_expr_translated value]
      | some arg =>
        cases otherwise with
        | none => simp only [translateExpr, collationNoVarExpr,
            List.attach_map_val (f := fun pair : Advanced.Expr × Advanced.Expr =>
              (translateExpr pair.1, translateExpr pair.2)), collation_no_var_branches_translated branches,
            collation_no_var_expr_translated arg]
        | some value => simp only [translateExpr, collationNoVarExpr,
            List.attach_map_val (f := fun pair : Advanced.Expr × Advanced.Expr =>
              (translateExpr pair.1, translateExpr pair.2)), collation_no_var_branches_translated branches,
            collation_no_var_expr_translated arg, collation_no_var_expr_translated value]
  termination_by sizeOf expr
  decreasing_by all_goals (simp_all <;> omega)

  @[simp] theorem collation_no_var_exprs_translated (exprs : List Advanced.Expr) :
      collationNoVarExprs (exprs.map translateExpr) = collationNoVarExprs exprs := by
    cases exprs with
    | nil => rfl
    | cons head tail =>
      simp only [List.map_cons, collationNoVarExprs,
        collation_no_var_expr_translated head, collation_no_var_exprs_translated tail]
  termination_by sizeOf exprs
  decreasing_by all_goals (simp_all <;> omega)

  @[simp] theorem collation_no_var_arguments_translated (args : List CallArgument) :
      collationNoVarArguments (args.map translateCallArgument) = collationNoVarArguments args := by
    cases args with
    | nil => rfl
    | cons head tail =>
      cases head with
      | positional value =>
        simp only [List.map_cons, translateCallArgument, collationNoVarArguments,
          collation_no_var_expr_translated value, collation_no_var_arguments_translated tail]
      | named name value spelling =>
        simp only [List.map_cons, translateCallArgument, collationNoVarArguments,
          collation_no_var_expr_translated value, collation_no_var_arguments_translated tail]
  termination_by sizeOf args
  decreasing_by all_goals (simp_all <;> omega)

  @[simp] theorem collation_no_var_subscripts_translated (indices : List Subscript) :
      collationNoVarSubscripts (indices.map translateSubscript) = collationNoVarSubscripts indices := by
    cases indices with
    | nil => rfl
    | cons head tail =>
      cases head with
      | index value =>
        simp only [List.map_cons, translateSubscript, collationNoVarSubscripts,
          collation_no_var_expr_translated value, collation_no_var_subscripts_translated tail]
      | slice lower upper =>
        cases lower with
        | none =>
          cases upper with
          | none => simp only [List.map_cons, translateSubscript, collationNoVarSubscripts,
              collation_no_var_subscripts_translated tail]
          | some value => simp only [List.map_cons, translateSubscript, collationNoVarSubscripts,
              collation_no_var_expr_translated value, collation_no_var_subscripts_translated tail]
        | some value =>
          cases upper with
          | none => simp only [List.map_cons, translateSubscript, collationNoVarSubscripts,
              collation_no_var_expr_translated value, collation_no_var_subscripts_translated tail]
          | some other => simp only [List.map_cons, translateSubscript, collationNoVarSubscripts,
              collation_no_var_expr_translated value, collation_no_var_expr_translated other,
              collation_no_var_subscripts_translated tail]
  termination_by sizeOf indices
  decreasing_by all_goals (simp_all <;> omega)

  @[simp] theorem collation_no_var_branches_translated (branches : List (Advanced.Expr × Advanced.Expr)) :
      collationNoVarBranches (branches.map fun pair => (translateExpr pair.1, translateExpr pair.2)) =
        collationNoVarBranches branches := by
    cases branches with
    | nil => rfl
    | cons head tail =>
      cases head with
      | mk condition value =>
        simp only [List.map_cons, collationNoVarBranches,
          collation_no_var_expr_translated condition, collation_no_var_expr_translated value,
          collation_no_var_branches_translated tail]
  termination_by sizeOf branches
  decreasing_by all_goals (simp_all <;> omega)
end

/-- Translation changes only the expression component of an IN-analysis row. -/
def translateInCollationArgument (row : Advanced.Expr × ExprType × CollationDerivation) :
    Advanced.Expr × ExprType × CollationDerivation := (translateExpr row.1, row.2)

@[simp] theorem in_collation_arguments_translated (es : List Advanced.Expr)
    (types : List ExprType) (derivations : List CollationDerivation) :
    inCollationArguments (es.map translateExpr) types derivations =
      (inCollationArguments es types derivations).map translateInCollationArgument := by
  induction es generalizing types derivations with
  | nil => rfl
  | cons head tail ih =>
      cases types <;> cases derivations <;> try rfl
      simpa only [inCollationArguments, List.zip_cons_cons, List.map_cons,
        translateInCollationArgument] using congrArg ((translateExpr head, _, _) :: ·) (ih _ _)

@[simp] theorem in_constant_arguments_translated (es : List Advanced.Expr)
    (types : List ExprType) (derivations : List CollationDerivation) :
    inConstantArguments (es.map translateExpr) types derivations =
      (inConstantArguments es types derivations).map translateInCollationArgument := by
  simp only [inConstantArguments, in_collation_arguments_translated]
  induction inCollationArguments es types derivations with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.map_cons, List.filter_cons, translateInCollationArgument,
        collation_no_var_expr_translated]
      split <;> simp_all only [List.map_cons, translateInCollationArgument]

@[simp] theorem in_variable_arguments_translated (es : List Advanced.Expr)
    (types : List ExprType) (derivations : List CollationDerivation) :
    inVariableArguments (es.map translateExpr) types derivations =
      (inVariableArguments es types derivations).map translateInCollationArgument := by
  simp only [inVariableArguments, in_collation_arguments_translated]
  induction inCollationArguments es types derivations with
  | nil => rfl
  | cons row rows ih =>
      simp only [List.map_cons, List.filter_cons, translateInCollationArgument,
        collation_no_var_expr_translated]
      split <;> simp_all only [List.map_cons, translateInCollationArgument]

theorem in_scalar_collations_translated
    (pairs : InScalarCollations arg type derivation rows) :
    InScalarCollations (translateExpr arg) type derivation
      (rows.map translateInCollationArgument) := by
  induction pairs with
  | nil => exact .nil
  | cons selected coercions merged tail ih =>
      simp only [List.map_cons, translateInCollationArgument]
      exact .cons (by simpa only [collation_scalar_input_translated] using selected)
        (by rw [← contextual_collations_translated] at coercions
            simpa only [List.map_cons, List.map_nil] using coercions) merged ih

theorem in_collations_translated
    (contexts : InCollations arg type derivation es types derivations) :
    InCollations (translateExpr arg) type derivation (es.map translateExpr) types derivations := by
  cases contexts with
  | scalar few pairs =>
      exact .scalar (by simpa only [in_constant_arguments_translated, List.length_map] using few)
        (by simpa only [in_collation_arguments_translated] using in_scalar_collations_translated pairs)
  | noCommon common pairs =>
      refine InCollations.noCommon ?_ ?_
      · simpa only [in_constant_arguments_translated, List.map_map, Function.comp_def,
          translateInCollationArgument, collation_scalar_input_translated] using common
      · simpa only [in_collation_arguments_translated] using in_scalar_collations_translated pairs
  | arrays common noArrayType pairs =>
      refine InCollations.arrays ?_ noArrayType ?_
      · simpa only [in_constant_arguments_translated, List.map_map, Function.comp_def,
          translateInCollationArgument, collation_scalar_input_translated] using common
      · simpa only [in_collation_arguments_translated] using in_scalar_collations_translated pairs
  | @grouped base coerced arrayInput signature leftType rightType input many common hasArrayType coercions arrayMerge selected inputs merged pairs =>
      refine InCollations.grouped (input := input) ?_ ?_ hasArrayType ?_ arrayMerge selected inputs ?_ ?_
      · simpa only [in_constant_arguments_translated, List.length_map] using many
      · simpa only [in_constant_arguments_translated, List.map_map, Function.comp_def,
          translateInCollationArgument, collation_scalar_input_translated] using common
      · simp only [in_constant_arguments_translated, List.map_map, Function.comp_def,
          translateInCollationArgument, List.length_map]
        rw [← coerced_collations_translated] at coercions
        simpa only [List.map_map, Function.comp_def] using coercions
      · simpa only [coerced_collation_translated] using merged
      · simpa only [in_variable_arguments_translated] using in_scalar_collations_translated pairs

end SQLean.RenderContract
