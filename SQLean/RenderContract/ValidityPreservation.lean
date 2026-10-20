import SQLean.RenderContract.Translation
import SQLean.SelectContract.Spec

/-! Parameter translation preserves the independent basic SELECT judgment.

The derivations below do not import the parser, renderer, executable checker,
or render certificate. They preserve the exact output labels, concrete types,
nullability, and index-keyed parameter environment for every valid basic SELECT.
This is a static preservation theorem, not an interpretation of database
execution or a claim that every advanced construct has basic-tier validity.
-/
namespace SQLean.RenderContract
open Advanced SelectContract
set_option maxHeartbeats 1000000

@[simp] theorem translateExpr_case (operand : Option Advanced.Expr)
    (branches : List (Advanced.Expr × Advanced.Expr)) (otherwise : Option Advanced.Expr) :
    translateExpr (.caseExpr operand branches otherwise) =
      .caseExpr (operand.map translateExpr)
        (branches.map fun pair => (translateExpr pair.1, translateExpr pair.2))
        (otherwise.map translateExpr) := by
  rw [translateExpr.eq_def]
  simp only [List.attach_map_val (f := fun pair : Advanced.Expr × Advanced.Expr =>
    (translateExpr pair.1, translateExpr pair.2))]
  cases operand <;> cases otherwise <;> rfl

@[simp] theorem translateParameter_index (parameter : Parameter) :
    parameterIndex (translateParameter parameter) = parameterIndex parameter := by
  cases parameter <;> rfl

@[simp] theorem ordinary_unary_translated (op : UnOp) (expr : Advanced.Expr) :
    OrdinaryUnary op (translateExpr expr) ↔ OrdinaryUnary op expr := by
  cases op <;> cases expr <;> simp [OrdinaryUnary, translateExpr]

@[simp] theorem ordinary_cast_translated (expr : Advanced.Expr) (target : DataType) :
    OrdinaryCast (translateExpr expr) target ↔ OrdinaryCast expr target := by
  cases expr <;> simp only [OrdinaryCast, translateExpr, translateExpr_case]

@[simp] theorem ordinary_array_element_translated (expr : Advanced.Expr) :
    OrdinaryArrayElement (translateExpr expr) ↔ OrdinaryArrayElement expr := by
  cases expr <;> simp only [OrdinaryArrayElement, translateExpr, translateExpr_case]

@[simp] theorem scalar_input_translated (expr : Advanced.Expr) (type : ExprType) :
    scalarInput (translateExpr expr) type = scalarInput expr type := by
  cases expr <;> simp [translateExpr, scalarInput]

@[simp] theorem scalar_inputs_translated (exprs : List Advanced.Expr) (types : List ExprType) :
    scalarInputs (exprs.map translateExpr) types = scalarInputs exprs types := by
  induction exprs generalizing types with
  | nil => cases types <;> rfl
  | cons expr exprs ih =>
    cases types with
    | nil => rfl
    | cons type types =>
      simpa only [scalarInputs, List.zip_cons_cons, List.map_cons, scalar_input_translated] using
        congrArg (scalarInput expr type :: ·) (ih types)

@[simp] theorem translateSubscript_slice (lower upper : Option Advanced.Expr) :
    translateSubscript (.slice lower upper) =
      .slice (lower.map translateExpr) (upper.map translateExpr) := by
  rw [translateSubscript.eq_def]
  cases lower <;> cases upper <;> rfl

@[simp] theorem subscript_isSlice_translated (subscript : Advanced.Subscript) :
    (translateSubscript subscript).isSlice = subscript.isSlice := by
  cases subscript <;> simp only [translateSubscript_slice, translateSubscript,
    Advanced.Subscript.isSlice]

@[simp] theorem subscripts_any_slice_translated (subscripts : List Advanced.Subscript) :
    (subscripts.map translateSubscript).any Advanced.Subscript.isSlice =
      subscripts.any Advanced.Subscript.isSlice := by
  simp only [List.any_map, Function.comp_def, subscript_isSlice_translated]

@[simp] theorem optional_subscript_bound_translated (expr : Option Advanced.Expr) (type : ExprType) :
    optionalSubscriptBoundSignature (expr.map translateExpr) type =
      optionalSubscriptBoundSignature expr type := by
  cases expr <;> simp only [Option.map, optionalSubscriptBoundSignature, scalar_input_translated]

mutual
  /-- Each scalar typing derivation survives the explicit parameter translation,
  with parameter occurrences translated in their original order. -/
  theorem expr_valid_translated
      (valid : ExprValid params scope expr type uses) :
      ExprValid params scope (translateExpr expr) type (uses.map translateParameter) := by
    cases valid with
    | int range => simpa only [translateExpr, List.map_nil] using ExprValid.int range
    | bigInt large range => simpa only [translateExpr, List.map_nil] using ExprValid.bigInt large range
    | numericInt large => simpa only [translateExpr, List.map_nil] using ExprValid.numericInt large
    | decimal lexical => simpa only [translateExpr, List.map_nil] using ExprValid.decimal lexical
    | minInt32 => simpa only [translateExpr, List.map_nil] using ExprValid.minInt32
    | minInt64 => simpa only [translateExpr, List.map_nil] using ExprValid.minInt64
    | text => simpa only [translateExpr, List.map_nil] using ExprValid.text
    | bool => simpa only [translateExpr, List.map_nil] using ExprValid.bool
    | null => simpa only [translateExpr, List.map_nil] using ExprValid.null
    | parameter present identity supported =>
        simpa only [translateExpr, List.map_cons, List.map_nil] using
          ExprValid.parameter present
            (identity.trans (translateParameter_index _).symm) supported
    | column resolved =>
        simpa only [translateExpr, List.map_nil] using ExprValid.column resolved
    | binary left right signature =>
        simpa only [translateExpr, List.map_append] using
          ExprValid.binary (expr_valid_translated left) (expr_valid_translated right) signature
    | concat left right signature =>
        simpa only [translateExpr, List.map_append, scalar_input_translated] using
          ExprValid.concat (expr_valid_translated left) (expr_valid_translated right)
            (by simpa only [scalar_input_translated] using signature)
    | rowComparison left right signature =>
        simpa only [translateExpr, List.attach_map_val, List.map_append] using
          ExprValid.rowComparison (expr_list_valid_translated left) (expr_list_valid_translated right)
            (by simpa only [scalar_inputs_translated] using signature)
    | quantifiedComparison left right signature =>
        simpa only [translateExpr, List.map_append] using
          ExprValid.quantifiedComparison (expr_valid_translated left) (expr_valid_translated right)
            (by simpa only [scalar_input_translated] using signature)
    | subscript base bounds nonempty dimensions =>
        simpa only [translateExpr, List.attach_map_val, List.map_append,
          subscripts_any_slice_translated] using
          ExprValid.subscript (expr_valid_translated base) (subscripts_valid_translated bounds)
            (by simpa using nonempty) (by simpa using dimensions)
    | unary arg signature ordinary =>
        simpa only [translateExpr] using ExprValid.unary (expr_valid_translated arg) signature
          ((ordinary_unary_translated _ _).mpr ordinary)
    | isNull arg =>
        simpa only [translateExpr] using ExprValid.isNull (expr_valid_translated arg)
    | pattern arg pattern signature =>
        simpa only [translateExpr, List.map_append] using
          ExprValid.pattern (expr_valid_translated arg) (expr_valid_translated pattern) signature
    | cast arg supported declaration allowed ordinary =>
        simpa only [translateExpr] using ExprValid.cast (expr_valid_translated arg)
          supported declaration allowed ((ordinary_cast_translated _ _).mpr ordinary)
    | array args signature =>
        simpa only [translateExpr, List.attach_map_val] using
          ExprValid.array (expr_list_valid_translated args) (by simpa using signature)
    | castArray args supported declaration =>
        simpa only [translateExpr, List.attach_map_val] using
          ExprValid.castArray (array_valid_translated args) supported declaration
    | call args signature =>
        simpa only [translateExpr, List.attach_map_val] using
          ExprValid.call (expr_list_valid_translated args) (by simpa using signature)
    | coalesce args signature =>
        simpa only [translateExpr, List.attach_map_val] using
          ExprValid.coalesce (expr_list_valid_translated args) (by simpa using signature)
    | greatest args signature =>
        simpa only [translateExpr, List.attach_map_val] using
          ExprValid.greatest (expr_list_valid_translated args) (by simpa using signature)
    | least args signature =>
        simpa only [translateExpr, List.attach_map_val] using
          ExprValid.least (expr_list_valid_translated args) (by simpa using signature)
    | nullIf left right signature =>
        simpa only [translateExpr, List.map_append] using
          ExprValid.nullIf (expr_valid_translated left) (expr_valid_translated right)
            (by simpa using signature)
    | @caseExpr operand ta ua branches conditions results ub otherwise te ue result
        operandValid branchesValid otherwiseValid signature =>
        have transformedSignature :
            caseSignature ((operand.map translateExpr).map fun expr => scalarInput expr ta)
              (scalarInputs ((branches.map fun pair => (translateExpr pair.1, translateExpr pair.2)).map Prod.fst) conditions)
              (scalarInputs ((branches.map fun pair => (translateExpr pair.1, translateExpr pair.2)).map Prod.snd) results)
              (((otherwise.map translateExpr).map fun expr => scalarInput expr te).getD (.unknown true)) =
              some result := by
          have fstMap :
              (branches.map (fun pair => (translateExpr pair.1, translateExpr pair.2))).map Prod.fst =
                (branches.map Prod.fst).map translateExpr := by simp only [List.map_map, Function.comp_def]
          have sndMap :
              (branches.map (fun pair => (translateExpr pair.1, translateExpr pair.2))).map Prod.snd =
                (branches.map Prod.snd).map translateExpr := by simp only [List.map_map, Function.comp_def]
          simpa only [fstMap, sndMap, scalar_inputs_translated, Option.map_map, Function.comp_def,
            scalar_input_translated] using signature
        have resultValid := ExprValid.caseExpr
          (optional_expr_valid_translated operandValid) (branches_valid_translated branchesValid)
          (optional_expr_valid_translated otherwiseValid) transformedSignature
        simpa only [translateExpr_case, List.map_append] using resultValid
    | inList arg values nonempty signature =>
        simpa only [translateExpr, List.attach_map_val, List.map_append] using
          ExprValid.inList (expr_valid_translated arg) (expr_list_valid_translated values)
            (by simpa using nonempty) signature
    | between arg lower upper signature =>
        simpa only [translateExpr, List.map_append] using
          ExprValid.between (expr_valid_translated arg) (expr_valid_translated lower)
            (expr_valid_translated upper) signature
  termination_by sizeOf expr
  decreasing_by all_goals (simp <;> omega)

  theorem expr_list_valid_translated
      (valid : ExprListValid params scope exprs types uses) :
      ExprListValid params scope (exprs.map translateExpr) types
        (uses.map translateParameter) := by
    cases valid with
    | nil => exact ExprListValid.nil
    | cons head tail =>
        simpa only [List.map_cons, List.map_append] using
          ExprListValid.cons (expr_valid_translated head) (expr_list_valid_translated tail)
  termination_by sizeOf exprs
  decreasing_by all_goals (simp <;> omega)

  /-- Target-directed array elaboration preserves the exact target declaration
  and original occurrence sequence, including nested empty constructors. -/
  theorem array_valid_translated
      (valid : ArrayValid params scope target exprs uses) :
      ArrayValid params scope target (exprs.map translateExpr)
        (uses.map translateParameter) := by
    cases valid with
    | targeted args signature =>
        exact ArrayValid.targeted (array_elements_valid_translated args)
          (by simpa only [scalar_inputs_translated] using signature)
  termination_by sizeOf exprs + 1
  decreasing_by subst_vars; omega

  theorem array_elements_valid_translated
      (valid : ArrayElementsValid params scope target exprs types uses) :
      ArrayElementsValid params scope target (exprs.map translateExpr) types
        (uses.map translateParameter) := by
    cases valid with
    | nil => exact ArrayElementsValid.nil
    | ordinary category head tail =>
        simpa only [List.map_cons, List.map_append] using
          ArrayElementsValid.ordinary ((ordinary_array_element_translated _).mpr category)
            (expr_valid_translated head) (array_elements_valid_translated tail)
    | nested head tail =>
        simpa only [List.map_cons, List.map_append, translateExpr, List.attach_map_val] using
          ArrayElementsValid.nested (array_valid_translated head)
            (array_elements_valid_translated tail)
  termination_by sizeOf exprs
  decreasing_by all_goals (simp <;> omega)

  theorem optional_expr_valid_translated
      (valid : OptionalExprValid params scope expr type uses) :
      OptionalExprValid params scope (expr.map translateExpr) type (uses.map translateParameter) := by
    cases valid with
    | absent => exact OptionalExprValid.absent
    | present typed => exact OptionalExprValid.present (expr_valid_translated typed)
  termination_by sizeOf expr
  decreasing_by all_goals (simp <;> omega)

  /-- Group boundaries, omitted endpoints and lower-before-upper occurrence
  order survive the parameter-only transformation. -/
  theorem subscripts_valid_translated
      (valid : SubscriptsValid params scope subscripts uses) :
      SubscriptsValid params scope (subscripts.map translateSubscript)
        (uses.map translateParameter) := by
    cases valid with
    | nil => exact SubscriptsValid.nil
    | index bound signature tail =>
        simpa only [List.map_cons, translateSubscript, List.map_append] using
          SubscriptsValid.index (expr_valid_translated bound)
            (by simpa only [scalar_input_translated] using signature)
            (subscripts_valid_translated tail)
    | slice lower upper lowerSignature upperSignature tail =>
        simpa only [List.map_cons, translateSubscript_slice, List.map_append] using
          SubscriptsValid.slice (optional_expr_valid_translated lower)
            (optional_expr_valid_translated upper)
            (by simpa only [optional_subscript_bound_translated] using lowerSignature)
            (by simpa only [optional_subscript_bound_translated] using upperSignature)
            (subscripts_valid_translated tail)
  termination_by sizeOf subscripts
  decreasing_by all_goals (simp <;> omega)

  theorem branches_valid_translated
      (valid : BranchesValid params scope branches conditions results uses) :
      BranchesValid params scope
        (branches.map fun branch => (translateExpr branch.1, translateExpr branch.2))
        conditions results (uses.map translateParameter) := by
    cases valid with
    | nil => exact BranchesValid.nil
    | cons conditionTyped resultTyped tail =>
      simpa only [List.map_cons, List.map_append] using
        BranchesValid.cons (expr_valid_translated conditionTyped) (expr_valid_translated resultTyped)
          (branches_valid_translated tail)
  termination_by sizeOf branches
  decreasing_by all_goals (simp <;> omega)
end

@[simp] theorem array_origin_translated (expr : Advanced.Expr) :
    arrayOrigin (translateExpr expr) = arrayOrigin expr := by
  cases expr with
  | cast arg target =>
      simp only [translateExpr, arrayOrigin, array_origin_translated arg]
  | _ => simp only [translateExpr, translateExpr_case, arrayOrigin]
termination_by sizeOf expr
decreasing_by all_goals (simp_all <;> omega)

@[simp] theorem output_label_translated (expr : Advanced.Expr) :
    outputLabel (translateExpr expr) = outputLabel expr := by
  cases expr with
  | cast arg target =>
      simp only [translateExpr, outputLabel, output_label_translated arg]
  | subscript arg indices =>
      simp only [translateExpr, outputLabel, output_label_translated arg]
  | caseExpr operand branches otherwise =>
      cases otherwise with
      | none =>
          simp only [translateExpr_case, outputLabel, Option.map_none]
      | some arg =>
          simp only [translateExpr_case, outputLabel, Option.map_some,
            output_label_translated arg]
  | _ => simp only [translateExpr, outputLabel]
termination_by sizeOf expr
decreasing_by all_goals (simp_all <;> omega)

@[simp] theorem translated_output_name (expr : Advanced.Expr) (alias : Option Name) :
    outputName (translateExpr expr) alias = outputName expr alias := by
  simp only [outputName, output_label_translated]

theorem items_valid_translated (valid : ItemsValid params scope items output uses) :
    ItemsValid params scope (items.map translateSelectItem) output
      (uses.map translateParameter) := by
  induction valid with
  | nil => exact ItemsValid.nil
  | expression typed aliasValid tail ih =>
      simpa only [List.map_cons, translateSelectItem, List.map_append, translated_output_name] using
        ItemsValid.expression (expr_valid_translated typed) aliasValid ih
  | all bindings nonempty tail ih =>
      simpa only [List.map_cons, translateSelectItem] using ItemsValid.all bindings nonempty ih

theorem predicate_valid_translated (valid : PredicateValid params scope predicate uses) :
    PredicateValid params scope (predicate.map translateExpr)
      (uses.map translateParameter) := by
  cases valid with
  | absent => exact PredicateValid.absent
  | present typed boolean =>
      exact PredicateValid.present (expr_valid_translated typed) boolean

/-- Relation identity and NULL-extension ancestry do not depend on parameter
notation, including for sources outside the independent validity fragment. -/
@[simp] theorem from_relations_translated (source : Advanced.From) :
    fromRelations (translateSource source) = fromRelations source := by
  cases source with
  | table name alias columns => simp only [translateSource, fromRelations]
  | derived query alias columns lateral => simp only [translateSource, fromRelations]
  | join kind left right condition =>
      simp only [translateSource, fromRelations,
        from_relations_translated left, from_relations_translated right]
termination_by sizeOf source
decreasing_by all_goals (simp_all <;> omega)

@[simp] theorem source_relations_translated (source : Option Advanced.From) :
    sourceRelations (source.map translateSource) = sourceRelations source := by
  cases source <;> simp [sourceRelations]

@[simp] theorem from_derived_names_translated (source : Advanced.From) :
    fromDerivedNames (translateSource source) = fromDerivedNames source := by
  cases source with
  | table name alias columns => simp only [translateSource, fromDerivedNames]
  | derived query alias columns lateral => simp only [translateSource, fromDerivedNames]
  | join kind left right condition =>
      simp only [translateSource, fromDerivedNames,
        from_derived_names_translated left, from_derived_names_translated right]
termination_by sizeOf source
decreasing_by all_goals (simp_all <;> omega)

@[simp] theorem source_derived_names_translated (source : Option Advanced.From) :
    sourceDerivedNames (source.map translateSource) = sourceDerivedNames source := by
  cases source <;> simp [sourceDerivedNames]

@[simp] theorem join_aliases_distinct_translated (left right : Advanced.From) :
    JoinAliasesDistinct (translateSource left) (translateSource right) ↔
      JoinAliasesDistinct left right := by
  simp only [JoinAliasesDistinct, from_relations_translated]

@[simp] theorem translated_sort_expression (expr : Advanced.Expr) :
    SortExpression (translateExpr expr) ↔ SortExpression expr := by
  cases expr <;> simp only [translateExpr, translateExpr_case, SortExpression]

theorem sort_valid_translated (valid : SortValid params scope output distinct expr uses) :
    SortValid params scope output distinct (translateExpr expr)
      (uses.map translateParameter) := by
  cases valid with
  | ordinal positive inRange orderable =>
      simpa only [translateExpr, List.map_nil] using SortValid.ordinal positive inRange orderable
  | outputName resolved orderable =>
      simpa only [translateExpr, List.map_nil] using SortValid.outputName resolved orderable
  | inputName noOutput ordinary typed orderable =>
      simpa only [translateExpr] using
        SortValid.inputName noOutput ordinary
          (by simpa only [translateExpr] using expr_valid_translated typed) orderable
  | expression ordinary typed category orderable =>
      exact SortValid.expression ordinary (expr_valid_translated typed)
        ((translated_sort_expression _).mpr category) orderable

theorem orders_valid_translated (valid : OrdersValid params scope output distinct orders uses) :
    OrdersValid params scope output distinct (orders.map translateOrderBy)
      (uses.map translateParameter) := by
  induction valid with
  | nil => exact OrdersValid.nil
  | cons head tail ih =>
      simpa only [List.map_cons, List.map_append, translateOrderBy] using
        OrdersValid.cons (sort_valid_translated head) ih

theorem parameter_order_translated (ordered : ParameterOrder uses) :
    ParameterOrder (uses.map translateParameter) := by
  apply Or.inl
  intro parameter member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  rcases ordered with numbered | anonymous
  · have positive := numbered original present
    cases original with
    | numbered _ => exact positive
    | anonymous _ => exact False.elim positive
  · rw [anonymous] at present
    obtain ⟨index, inRange, rfl⟩ := List.mem_map.mp present
    simp only [translateParameter, NumberedPositive]
    omega

/-- Translation preserves closed pagination typing and its contextual widening. -/
theorem pagination_valid_translated (valid : PaginationValid params bound uses) :
    PaginationValid params (bound.map translateExpr) (uses.map translateParameter) := by
  cases valid with
  | absent => exact .absent
  | present typed coercion =>
      exact .present (expr_valid_translated typed) coercion

/-- The local pagination certificate remains useful independently of coverage
for the query body, while parameter identities and occurrence order survive. -/
theorem pagination_bounds_valid_translated
    (valid : PaginationBoundsValid profile params query limitUses offsetUses) :
    PaginationBoundsValid profile params (translateParameters query)
      (limitUses.map translateParameter) (offsetUses.map translateParameter) := by
  cases valid with
  | bounds environment limitValid offsetValid =>
      apply PaginationBoundsValid.bounds environment
      · have translated := pagination_valid_translated limitValid
        simp only [translateParameters]
        split <;> simp_all
      · have translated := pagination_valid_translated offsetValid
        simp only [translateParameters]
        split <;> simp_all

@[simp] theorem lock_target_translated (source : Option Advanced.From) (target : Name) :
    LockTarget (source.map translateSource) target ↔ LockTarget source target := by
  simp only [LockTarget, source_relations_translated, source_derived_names_translated]

@[simp] theorem lock_targets_translated (source : Option Advanced.From) (targets : List Name) :
    LockTargets (source.map translateSource) targets ↔ LockTargets source targets := by
  simp only [LockTargets, source_relations_translated, source_derived_names_translated, lock_target_translated]

theorem locking_valid_translated (valid : LockingValid source distinct clauses) :
    LockingValid (source.map translateSource) distinct clauses := by
  induction valid with
  | nil => exact .nil
  | cons ordinary targets tail ih =>
    exact .cons ordinary ((lock_targets_translated _ _).mpr targets) ih

mutual
  /-- The complete source derivation survives translation: ON predicates retain
  their child scope, outer joins retain exact output nullability, USING/NATURAL
  retain both qualified order and merged row order, and occurrences remain in
  left-source, right-source, ON order. Implicit key comparisons add no parameters. -/
  theorem source_valid_translated (valid : SourceValid profile catalog params source scope uses) :
      SourceValid profile catalog params (source.map translateSource) scope
        (uses.map translateParameter) := by
    cases valid with
    | empty => exact SourceValid.empty
    | table present sameName aliasValid columns =>
        simpa only [Option.map_some, translateSource, List.map_nil] using
          SourceValid.table present sameName aliasValid columns
    | cross leftValid rightValid aliases =>
        simpa only [Option.map_some, translateSource, translateJoinCondition, List.map_append] using
          SourceValid.cross (source_valid_translated leftValid) (source_valid_translated rightValid)
            ((join_aliases_distinct_translated _ _).mpr aliases)
    | on leftValid rightValid aliases kindValid condition =>
        simpa only [Option.map_some, translateSource, translateJoinCondition, List.map_append] using
          SourceValid.on (source_valid_translated leftValid) (source_valid_translated rightValid)
            ((join_aliases_distinct_translated _ _).mpr aliases)
            kindValid (predicate_valid_translated condition)
    | «using» leftValid rightValid aliases kindValid nonempty unique keysValid =>
        simpa only [Option.map_some, translateSource, translateJoinCondition, List.map_append] using
          SourceValid.using (source_valid_translated leftValid) (source_valid_translated rightValid)
            ((join_aliases_distinct_translated _ _).mpr aliases)
            kindValid nonempty unique keysValid
    | natural leftValid rightValid aliases kindValid unique keysValid =>
        simpa only [Option.map_some, translateSource, translateJoinCondition, List.map_append] using
          SourceValid.natural (source_valid_translated leftValid) (source_valid_translated rightValid)
            ((join_aliases_distinct_translated _ _).mpr aliases)
            kindValid unique keysValid
    | derived queryValid aliasValid columnsValid nonLateral =>
        simpa only [Option.map_some, translateSource] using
          SourceValid.derived (query_valid_translated queryValid) aliasValid columnsValid nonLateral
  termination_by sizeOf source
  decreasing_by all_goals (simp_all <;> omega)

  /-- Every internal query derivation retains its complete occurrence list,
  including recursively nested derived sources. No child restarts numbering. -/
  theorem query_valid_translated
      (valid : QueryValid profile catalog params query output uses) :
      QueryValid profile catalog params (translateParameters query) output
        (uses.map translateParameter) := by
    cases valid with
    | @basic scope sourceUses output selectUses whereUses orderBy orderUses limit limitUses
        offset offsetUses locking offsetFirst select source items nonempty distinctComparable
        predicate orders limitValid offsetValid lockingValid noGrouping noHaving noDistinctOn =>
      cases offsetFirst <;>
        simp only [translateParameters, translateQueryBody, List.attach_map_val,
          List.map_nil, Bool.false_eq_true, ↓reduceIte, List.map_append]
      all_goals
        apply QueryValid.basic
        · have translated := source_valid_translated source
          simp only [translateSelect]
          cases relation : select.source <;> simpa [relation] using translated
        · simpa only [translateSelect, List.attach_map_val] using items_valid_translated items
        · exact nonempty
        · simpa only [translateSelect] using distinctComparable
        · have translated := predicate_valid_translated predicate
          simp only [translateSelect]
          cases condition : select.whereClause <;> simpa [condition] using translated
        · simpa only [translateSelect] using orders_valid_translated orders
        · have translated := pagination_valid_translated limitValid
          split <;> simp_all only [Option.map_none, Option.map_some] <;> exact translated
        · have translated := pagination_valid_translated offsetValid
          split <;> simp_all only [Option.map_none, Option.map_some] <;> exact translated
        · have translated := locking_valid_translated lockingValid
          simp only [translateSelect]
          cases relation : select.source <;> simpa [relation] using translated
        · simp only [translateSelect, List.attach_map_val, noGrouping, List.map_nil]
        · simp only [translateSelect]
          split <;> simp_all
        · simp only [translateSelect, List.attach_map_val, noDistinctOn, List.map_nil]
  termination_by sizeOf query
  decreasing_by all_goals (cases select; simp_all; omega)
end

/-- Translating anonymous occurrences to numbered parameters preserves every
independent basic SELECT validity derivation, with exactly the same environment
and ordered output schema. No parser/renderer success is a hypothesis. The
notation condition is applied once, over all nested query occurrences. -/
theorem translateParameters_valid
    (valid : SelectValid profile catalog params query output) :
    SelectValid profile catalog params (translateParameters query) output := by
  cases valid with
  | certified environment supported queryValid parameterOrder =>
      exact .certified environment supported (query_valid_translated queryValid)
        (parameter_order_translated parameterOrder)

end SQLean.RenderContract
