import SQLean.RenderContract.ValuesPreservation
import SQLean.RenderContract.LabelPreservation
import SQLean.RenderContract.RecursionPreservation
import SQLean.SelectContract.Spec

namespace SQLean.RenderContract
open Advanced SelectContract
set_option maxHeartbeats 1000000

@[simp] theorem array_origin_translated (expr : Advanced.Expr) :
    arrayOrigin (translateExpr expr) = arrayOrigin expr := by
  cases expr with
  | cast arg target =>
      simp only [translateExpr, arrayOrigin, array_origin_translated arg]
  | _ => simp only [translateExpr, translateExpr_case, arrayOrigin]
termination_by sizeOf expr
decreasing_by all_goals (simp_all <;> omega)

@[simp] theorem translated_output_name (expr : Advanced.Expr) (alias : Option Name) :
    outputName (translateExpr expr) alias = outputName expr alias := by
  simp only [outputName, output_label_translated]

theorem items_valid_translated_core
    (preserved : SubqueriesTranslated sq ceiling) (valid : ItemsValidCore sq profile params env scope items output uses)
    (small : sizeOf items ≤ ceiling := by simp_all <;> omega) :
    ItemsValidCore sq profile params env scope (items.map translateSelectItem) output
      (uses.map translateParameter) := by
  cases valid with
  | nil => exact ItemsValid.nil
  | expression typed collation labelValid aliasValid tail =>
      simpa only [List.map_cons, translateSelectItem, List.map_append, translated_output_name, projected_collation_translated] using
        ItemsValid.expression (expr_valid_translated_core preserved typed) (expr_collation_valid_translated_core preserved collation) (expr_label_valid_translated_core preserved labelValid) aliasValid (items_valid_translated_core preserved tail)
  | all bindings nonempty tail =>
      simpa only [List.map_cons, translateSelectItem] using ItemsValid.all bindings nonempty (items_valid_translated_core preserved tail)
termination_by sizeOf items
decreasing_by all_goals subst_vars; all_goals (try simp); all_goals omega


theorem items_input_valid_translated_core
    (preserved : SubqueriesTranslated sq ceiling) (valid : ItemsInputValidCore sq profile params env scope items output uses)
    (small : sizeOf items ≤ ceiling := by simp_all <;> omega) :
    ItemsInputValidCore sq profile params env scope (items.map translateSelectItem) output
      (uses.map translateParameter) := by
  cases valid with
  | nil => exact .nil
  | expression typed collation labelValid aliasValid tail =>
      simpa only [List.map_cons, translateSelectItem, List.map_append,
        translated_output_name, scalar_input_translated, pending_origin_translated,
        unknown_collation_sort_key_translated] using
        ItemsInputValid.expression (expr_valid_translated_core preserved typed) (expr_collation_valid_translated_core preserved collation) (expr_label_valid_translated_core preserved labelValid) aliasValid (items_input_valid_translated_core preserved tail)
  | all bindings nonempty tail =>
      simpa only [List.map_cons, translateSelectItem] using ItemsInputValid.all bindings nonempty (items_input_valid_translated_core preserved tail)
termination_by sizeOf items
decreasing_by all_goals subst_vars; all_goals (try simp); all_goals omega


@[simp] theorem projection_expressions_translated (items : List Advanced.SelectItem) (names : List Name) (name : Name) :
    projectionExpressions (items.map translateSelectItem) names name =
      (projectionExpressions items names name).map translateExpr := by
  induction items generalizing names with
  | nil => rfl
  | cons item items ih =>
    cases names with
    | nil => rfl
    | cons column names =>
      simp [projectionExpressions] at ih
      cases item with
      | all qualifier schema =>
        simpa [projectionExpressions, translateSelectItem] using ih names
      | expression expr alias =>
        by_cases matched : column = name <;>
          simp [projectionExpressions, translateSelectItem, ih, matched]

@[simp] theorem pure_projection_translated (items : List Advanced.SelectItem) :
    pureProjection (items.map translateSelectItem) = pureProjection items := by
  induction items with
  | nil => rfl
  | cons item items ih =>
    cases item <;> simp_all [pureProjection, translateSelectItem]

theorem same_output_expressions_translated (same : SameOutputExpressions profile items output name) :
    SameOutputExpressions profile (items.map translateSelectItem) output name := by
  obtain ⟨pure, same⟩ := same
  refine ⟨by simpa using pure, ?_⟩
  rw [projection_expressions_translated]
  cases found : projectionExpressions items (output.map OutputColumn.name) name with
  | nil => simp_all
  | cons first rest =>
    simp only [found] at same
    simp only [List.map_cons]
    intro expr member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    rcases same original present with identical | normalized
    · exact Or.inl (congrArg translateExpr identical)
    · exact Or.inr (by simpa only [unknown_collation_sort_key_translated] using normalized)

theorem predicate_valid_translated_core
    (preserved : SubqueriesTranslated sq ceiling) (valid : PredicateValidCore sq profile params env scope predicate uses)
    (small : sizeOf predicate ≤ ceiling := by simp_all <;> omega) :
    PredicateValidCore sq profile params env scope (predicate.map translateExpr)
      (uses.map translateParameter) := by
  cases valid with
  | absent => exact PredicateValid.absent
  | present typed collation boolean =>
      exact PredicateValid.present (expr_valid_translated_core preserved typed) (expr_collation_valid_translated_core preserved collation) boolean

/-- Relation identity and NULL-extension ancestry do not depend on parameter
notation, including for sources outside the independent validity fragment. -/
@[simp] theorem from_relations_translated (source : Advanced.From) :
    fromRelations (translateSource source) = fromRelations source := by
  cases source with
  | table name alias columns schema => simp only [translateSource, fromRelations]
  | derivedAnonymous query lateral => simp only [translateSource, fromRelations]
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
  | table name alias columns schema => simp only [translateSource, fromDerivedNames]
  | derivedAnonymous query lateral => simp only [translateSource, fromDerivedNames]
  | derived query alias columns lateral => simp only [translateSource, fromDerivedNames]
  | join kind left right condition =>
      simp only [translateSource, fromDerivedNames,
        from_derived_names_translated left, from_derived_names_translated right]
termination_by sizeOf source
decreasing_by all_goals (simp_all <;> omega)

@[simp] theorem source_derived_names_translated (source : Option Advanced.From) :
    sourceDerivedNames (source.map translateSource) = sourceDerivedNames source := by
  cases source <;> simp [sourceDerivedNames]

@[simp] theorem sort_syntax_translated (expr : Advanced.Expr) :
    sortSyntax (translateExpr expr) = sortSyntax expr := by
  cases expr with
  | unary op arg =>
      cases op <;> simp only [translateExpr, sortSyntax]
      rw [sort_syntax_translated arg]
  | _ => simp only [translateExpr, translateExpr_case, sortSyntax]
termination_by sizeOf expr

@[simp] theorem translated_sort_expression (expr : Advanced.Expr) :
    SortExpression (translateExpr expr) ↔ SortExpression expr := by
  unfold SortExpression
  rw [sort_syntax_translated]
  cases expr <;> simp only [translateExpr, translateExpr_case]


theorem sort_valid_translated_core
    (preserved : SubqueriesTranslated sq ceiling) (valid : SortValidCore sq profile params env scope projection output distinct expr uses)
    (small : sizeOf expr ≤ ceiling := by simp_all <;> omega) :
    SortValidCore sq profile params env scope (projection.map translateSelectItem) output distinct (translateExpr expr)
      (uses.map translateParameter) := by
  cases valid with
  | ordinal constant positive inRange orderable =>
      exact SortValid.ordinal (by simpa only [sort_syntax_translated] using constant)
        positive inRange orderable
  | outputName resolved orderable =>
      simpa only [translateExpr, List.map_nil] using SortValid.outputName resolved orderable
  | repeatedName same resolved orderable =>
      simpa only [translateExpr, List.map_nil] using
        SortValid.repeatedName (same_output_expressions_translated same) resolved orderable
  | inputName noOutput ordinary typed orderable =>
      simpa only [translateExpr] using
        SortValid.inputName noOutput ordinary
          (by simpa only [translateExpr] using expr_valid_translated_core preserved typed) orderable
  | expression ordinary typed category orderable =>
      exact SortValid.expression ordinary (expr_valid_translated_core preserved typed)
        ((translated_sort_expression _).mpr category) orderable

theorem sort_collation_valid_translated_core
    (preserved : SubqueriesTranslated sq ceiling)
    (valid : SortCollationValidCore sq profile params env scope pending expr)
    (small : sizeOf expr ≤ ceiling := by simp_all <;> omega) :
    SortCollationValidCore sq profile params env scope pending (translateExpr expr) := by
  cases valid with
  | ordinal constant resolved determinate =>
      exact .ordinal (by simpa only [sort_syntax_translated] using constant) resolved determinate
  | outputName resolved determinate =>
      simpa only [translateExpr] using SortCollationValid.outputName resolved determinate
  | inputName noOutput collation determinate =>
      simpa only [translateExpr] using SortCollationValid.inputName noOutput
        (by simpa only [translateExpr] using expr_collation_valid_translated_core preserved collation) determinate
  | expression category collation determinate =>
      exact .expression ((translated_sort_expression _).mpr category)
        (expr_collation_valid_translated_core preserved collation) determinate

theorem orders_collation_valid_translated_core
    (preserved : SubqueriesTranslated sq ceiling)
    (valid : OrdersCollationValidCore sq profile params env scope pending orders)
    (small : sizeOf orders ≤ ceiling := by simp_all <;> omega) :
    OrdersCollationValidCore sq profile params env scope pending (orders.map translateOrderBy) := by
  cases valid with
  | nil => exact .nil
  | @cons _ _ _ _ item head tail =>
      cases item
      simpa only [List.map_cons, translateOrderBy] using
        OrdersCollationValid.cons (sort_collation_valid_translated_core preserved head) (orders_collation_valid_translated_core preserved tail)
termination_by sizeOf orders
decreasing_by all_goals subst_vars; all_goals (try simp); all_goals omega


@[simp] theorem unknown_sort_key_translated (profile : Profile) (expr : Advanced.Expr) :
    unknownSortKey profile (translateExpr expr) = unknownSortKey profile expr := by
  exact unknown_collation_sort_key_translated profile expr

@[simp] theorem projection_sort_keys_translated (profile : Profile) (items : List Advanced.SelectItem)
    (output : List OutputColumn) :
    projectionSortKeys profile (items.map translateSelectItem) output = projectionSortKeys profile items output := by
  induction items generalizing output with
  | nil => rfl
  | cons item items ih =>
    cases output with
    | nil => rfl
    | cons column output =>
      simp only [projectionSortKeys] at ih
      cases item <;> simp [projectionSortKeys, translateSelectItem, unknown_sort_key_translated, ih]

@[simp] theorem sort_target_index_translated (profile : Profile)
    (keys : List (Name × Option UnknownSortValue)) (resolved : List Nat)
    (expr : Advanced.Expr) :
    sortTargetIndex profile keys resolved (translateExpr expr) =
      sortTargetIndex profile keys resolved expr := by
  unfold sortTargetIndex
  rw [sort_syntax_translated]
  cases sortSyntax expr <;> try rfl
  all_goals cases expr <;> simp only [translateExpr, translateExpr_case,
    unknownSortKey, unknownCollationSortKey, unknown_collation_sort_key_translated]

@[simp] theorem order_sequence_safe_translated (profile : Profile)
    (keys : List (Name × Option UnknownSortValue)) (resolved : List Nat)
    (orders : List Advanced.OrderBy) :
    orderSequenceSafe profile keys resolved (orders.map translateOrderBy) =
      orderSequenceSafe profile keys resolved orders := by
  induction orders generalizing resolved with
  | nil => rfl
  | cons order orders ih =>
    simp only [List.map_cons, orderSequenceSafe, translateOrderBy, sort_target_index_translated, ih]
    cases order.expr <;> simp only [translateExpr, translateExpr_case]

@[simp] theorem order_resolved_indices_translated (profile : Profile)
    (keys : List (Name × Option UnknownSortValue)) (resolved : List Nat)
    (orders : List Advanced.OrderBy) :
    orderResolvedIndices profile keys resolved (orders.map translateOrderBy) =
      orderResolvedIndices profile keys resolved orders := by
  induction orders generalizing resolved with
  | nil => rfl
  | cons order orders ih =>
    simp only [List.map_cons, orderResolvedIndices, translateOrderBy, sort_target_index_translated, ih]

theorem order_sequence_valid_translated (safe : OrderSequenceSafe profile projection output orders) :
    OrderSequenceSafe profile (projection.map translateSelectItem) output (orders.map translateOrderBy) := by
  simpa only [OrderSequenceSafe, pure_projection_translated, projection_sort_keys_translated,
    order_sequence_safe_translated] using safe

theorem sort_list_valid_translated_core
    (preserved : SubqueriesTranslated sq ceiling) (valid : SortListValidCore sq profile params env scope projection output distinct orders uses)
    (small : sizeOf orders ≤ ceiling := by simp_all <;> omega) :
    SortListValidCore sq profile params env scope (projection.map translateSelectItem) output distinct (orders.map translateOrderBy)
      (uses.map translateParameter) := by
  cases valid with
  | nil => exact .nil
  | @cons _ _ _ _ _ _ _ _ item head tail =>
      cases item
      simpa only [List.map_cons, List.map_append, translateOrderBy] using
        SortListValid.cons (sort_valid_translated_core preserved head) (sort_list_valid_translated_core preserved tail)
termination_by sizeOf orders
decreasing_by all_goals subst_vars; all_goals (try simp); all_goals omega


theorem orders_valid_translated_core
    (preserved : SubqueriesTranslated sq ceiling) (valid : OrdersValidCore sq profile params env scope projection output distinct orders uses)
    (small : sizeOf orders ≤ ceiling := by simp_all <;> omega) :
    OrdersValidCore sq profile params env scope (projection.map translateSelectItem) output distinct (orders.map translateOrderBy)
      (uses.map translateParameter) := by
  cases valid with
  | nil => exact .nil
  | checked items sequence =>
    exact .checked (sort_list_valid_translated_core preserved items) (order_sequence_valid_translated sequence)

@[simp] theorem resolve_leaf_inputs_translated (profile : Profile) (distinct : Bool)
    (orders : List Advanced.OrderBy) (columns : List PendingColumn) :
    resolveLeafInputs profile distinct (orders.map translateOrderBy) columns =
      resolveLeafInputs profile distinct orders columns := by
  simp only [resolveLeafInputs, order_resolved_indices_translated]

theorem set_sort_valid_translated (valid : SetSortValid output expr) :
    SetSortValid output (translateExpr expr) := by
  cases valid with
  | ordinal constant positive inRange orderable =>
    exact .ordinal (by simpa using constant) positive inRange orderable
  | outputName resolved orderable =>
    simpa only [translateExpr] using SetSortValid.outputName resolved orderable

theorem set_orders_valid_translated (valid : SetOrdersValid output orders) :
    SetOrdersValid output (orders.map translateOrderBy) := by
  induction valid with
  | nil => exact .nil
  | cons head tail ih =>
    simpa only [List.map_cons, translateOrderBy] using SetOrdersValid.cons (set_sort_valid_translated head) ih

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
theorem pagination_valid_translated_core
    (preserved : SubqueriesTranslated sq ceiling) (valid : PaginationValidCore sq profile params env bound uses)
    (small : sizeOf bound ≤ ceiling := by simp_all <;> omega) :
    PaginationValidCore sq profile params env (bound.map translateExpr) (uses.map translateParameter) := by
  cases valid with
  | absent => exact .absent
  | present typed collation coercion =>
      exact .present (expr_valid_translated_core preserved typed) (expr_collation_valid_translated_core preserved collation) coercion

theorem pagination_valid_translated (valid : PaginationValid profile params bound uses) :
    PaginationValid profile params (bound.map translateExpr) (uses.map translateParameter) :=
  pagination_valid_translated_core
    (by intro env query output uses small impossible; exact False.elim impossible)
    valid (Nat.le_refl (sizeOf bound))

/-- The local pagination certificate remains useful independently of coverage
for the query body, while parameter identities and occurrence order survive. -/
theorem pagination_bounds_valid_translated
    (valid : PaginationBoundsValid profile params query limitUses offsetUses) :
    PaginationBoundsValid profile params (translateParameters query)
      (limitUses.map translateParameter) (offsetUses.map translateParameter) := by
  cases valid with
  | bounds environment collations limitValid offsetValid =>
      apply PaginationBoundsValid.bounds environment collations
      · have translated := pagination_valid_translated limitValid
        simp only [translateParameters]
        split <;> simp_all
      · have translated := pagination_valid_translated offsetValid
        simp only [translateParameters]
        split <;> simp_all

private theorem closed_subqueries_translated (ceiling : Nat) :
    SubqueriesTranslated NoSubqueries ceiling := by
  intro env query output uses small impossible
  exact False.elim impossible

theorem items_valid_translated (valid : ItemsValid profile params scope items output uses) :
    ItemsValid profile params scope (items.map translateSelectItem) output (uses.map translateParameter) :=
  items_valid_translated_core (closed_subqueries_translated (sizeOf items)) valid

theorem items_input_valid_translated (valid : ItemsInputValid profile params scope items output uses) :
    ItemsInputValid profile params scope (items.map translateSelectItem) output (uses.map translateParameter) :=
  items_input_valid_translated_core (closed_subqueries_translated (sizeOf items)) valid

theorem predicate_valid_translated (valid : PredicateValid profile params scope predicate uses) :
    PredicateValid profile params scope (predicate.map translateExpr) (uses.map translateParameter) :=
  predicate_valid_translated_core (closed_subqueries_translated (sizeOf predicate)) valid

theorem sort_valid_translated (valid : SortValid profile params scope projection output distinct expr uses) :
    SortValid profile params scope (projection.map translateSelectItem) output distinct (translateExpr expr)
      (uses.map translateParameter) :=
  sort_valid_translated_core (closed_subqueries_translated (sizeOf expr)) valid

theorem sort_collation_valid_translated (valid : SortCollationValid profile params scope pending expr) :
    SortCollationValid profile params scope pending (translateExpr expr) :=
  sort_collation_valid_translated_core (closed_subqueries_translated (sizeOf expr)) valid

theorem orders_collation_valid_translated (valid : OrdersCollationValid profile params scope pending orders) :
    OrdersCollationValid profile params scope pending (orders.map translateOrderBy) :=
  orders_collation_valid_translated_core (closed_subqueries_translated (sizeOf orders)) valid

theorem sort_list_valid_translated (valid : SortListValid profile params scope projection output distinct orders uses) :
    SortListValid profile params scope (projection.map translateSelectItem) output distinct
      (orders.map translateOrderBy) (uses.map translateParameter) :=
  sort_list_valid_translated_core (closed_subqueries_translated (sizeOf orders)) valid

theorem orders_valid_translated (valid : OrdersValid profile params scope projection output distinct orders uses) :
    OrdersValid profile params scope (projection.map translateSelectItem) output distinct
      (orders.map translateOrderBy) (uses.map translateParameter) :=
  orders_valid_translated_core (closed_subqueries_translated (sizeOf orders)) valid

/- Source transport below preserves the exact scope, including namespace
identity, aliases, order and NULL-extension flags. Locking premises therefore
remain the same propositions; no name is re-resolved after translation. -/

@[simp] theorem without_with_translated (query : Advanced.Query) :
    withoutWith (translateParameters query) = translateParameters (withoutWith query) := by
  cases query
  simp [withoutWith, translateParameters]


private theorem translated_query_ctes (query : Advanced.Query) :
    (translateParameters query).ctes = query.ctes.map translateCTE := by
  rw [translateParameters]
  simp only [List.attach_map_val]

private theorem translated_query_recursive (query : Advanced.Query) :
    (translateParameters query).recursive = query.recursive := by
  rw [translateParameters]

private theorem translated_cte_query (cte : Advanced.CTE) :
    (translateCTE cte).query = translateParameters cte.query := by rw [translateCTE]
private theorem translated_cte_name (cte : Advanced.CTE) :
    (translateCTE cte).name = cte.name := by rw [translateCTE]
private theorem translated_cte_columns (cte : Advanced.CTE) :
    (translateCTE cte).columns = cte.columns := by rw [translateCTE]

private theorem cte_names_valid_translated (ctes : List Advanced.CTE)
    (valid : CTENamesValid ctes) : CTENamesValid (ctes.map translateCTE) := by
  simpa only [CTENamesValid, recursive_cte_names_translated, List.mem_map,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, translated_cte_name] using valid

private theorem query_ctes_size_lt (query : Advanced.Query) :
    sizeOf query.ctes < sizeOf query := by cases query; simp; omega

private theorem without_with_size_lt (query : Advanced.Query) (nonempty : query.ctes ≠ []) :
    sizeOf (withoutWith query) < sizeOf query := by
  cases query with
  | mk body ctes recursive orderBy limit offset locking offsetFirst =>
    cases ctes with
    | nil => exact False.elim (nonempty rfl)
    | cons head tail => cases head; simp [withoutWith]; omega


mutual
  /-- The complete source derivation survives translation: ON predicates retain
  their child scope, outer joins retain exact output nullability, USING/NATURAL
  retain both qualified order and merged row order, and occurrences remain in
  left-source, right-source, ON order. Implicit key comparisons add no parameters. -/
  theorem source_valid_translated (valid : SourceValid profile catalog params env source scope uses) :
      SourceValid profile catalog params env (source.map translateSource) scope
        (uses.map translateParameter) := by
    have preserved : SubqueriesTranslated (QueryValid profile catalog params) (sizeOf source) := by
      intro childEnv child childOutput childUses smaller childValid
      exact query_valid_translated childValid
    cases valid with
    | empty => exact SourceValid.empty
    | table unshadowed present sameName aliasValid columns =>
        simpa only [Option.map_some, translateSource, List.map_nil] using
          SourceValid.table unshadowed present sameName aliasValid columns
    | tableRenamed unshadowed present resolved aliasValid columns aliasesValid =>
        simpa only [Option.map_some, translateSource, List.map_nil] using
          SourceValid.tableRenamed unshadowed present resolved aliasValid columns aliasesValid
    | cte resolved aliasValid columnsValid aliasRequired =>
        simpa only [Option.map_some, translateSource, List.map_nil] using
          SourceValid.cte resolved aliasValid columnsValid aliasRequired
    | cross leftValid rightValid aliases =>
        simpa only [Option.map_some, translateSource, translateJoinCondition, List.map_append] using
          SourceValid.cross (source_valid_translated leftValid) (source_valid_translated rightValid)
            aliases
    | on leftValid rightValid aliases kindValid condition =>
        simpa only [Option.map_some, translateSource, translateJoinCondition, List.map_append] using
          SourceValid.on (source_valid_translated leftValid) (source_valid_translated rightValid)
            aliases
            kindValid (predicate_valid_translated_core preserved condition)
    | «using» leftValid rightValid aliases kindValid nonempty unique keysValid =>
        simpa only [Option.map_some, translateSource, translateJoinCondition, List.map_append] using
          SourceValid.using (source_valid_translated leftValid) (source_valid_translated rightValid)
            aliases
            kindValid nonempty unique keysValid
    | natural leftValid rightValid aliases kindValid unique keysValid =>
        simpa only [Option.map_some, translateSource, translateJoinCondition, List.map_append] using
          SourceValid.natural (source_valid_translated leftValid) (source_valid_translated rightValid)
            aliases
            kindValid unique keysValid
    | derivedAnonymous queryValid nonLateral =>
        simpa only [Option.map_some, translateSource] using
          SourceValid.derivedAnonymous (query_valid_translated queryValid) nonLateral
    | derived queryValid aliasValid columnsValid nonLateral =>
        simpa only [Option.map_some, translateSource] using
          SourceValid.derived (query_valid_translated queryValid) aliasValid columnsValid nonLateral
  termination_by 2 * sizeOf source
  decreasing_by all_goals (simp_all <;> omega)

  /-- Every internal query derivation retains its complete occurrence list,
  including recursively nested derived sources. No child restarts numbering. -/
  theorem query_valid_translated
      (valid : QueryValid profile catalog params env query output uses) :
      QueryValid profile catalog params env (translateParameters query) output
        (uses.map translateParameter) := by
    have preserved : SubqueriesTranslated (QueryValid profile catalog params) (sizeOf query) := by
      intro childEnv child childOutput childUses smaller childValid
      exact query_valid_translated childValid
    cases valid with
    | @basic ctes env visible cteUses scope sourceUses output selectUses pending whereUses orderBy orderUses limit limitUses
        offset offsetUses locking offsetFirst select names definitions source items inputs nonempty distinctComparable distinctCollations
        predicate orders orderCollations limitValid offsetValid lockingValid noGrouping noHaving noDistinctOn =>
      have itemSize : sizeOf select.items < sizeOf select := by cases select; simp; omega
      have whereSize : sizeOf select.whereClause < sizeOf select := by cases select; simp; omega
      cases offsetFirst <;>
        simp only [translateParameters, translateQueryBody, List.attach_map_val,
          Bool.false_eq_true, ↓reduceIte, List.map_append]
      all_goals
        apply QueryValid.basic (pending := pending)
        · simpa [CTENamesValid, List.map_map, Function.comp_def, translateCTE] using names
        · simpa only [List.attach_map_val] using ctes_valid_translated definitions
        · have translated := source_valid_translated source
          simp only [translateSelect]
          cases relation : select.source <;> simpa [relation] using translated
        · simpa only [translateSelect, List.attach_map_val] using items_valid_translated_core preserved items
        · simpa only [translateSelect, List.attach_map_val] using items_input_valid_translated_core preserved inputs
        · exact nonempty
        · simpa only [translateSelect] using distinctComparable
        · simpa only [translateSelect] using distinctCollations
        · have translated := predicate_valid_translated_core preserved predicate
          simp only [translateSelect]
          cases condition : select.whereClause <;> simpa [condition] using translated
        · simpa only [translateSelect, List.attach_map_val] using orders_valid_translated_core preserved orders
        · exact orders_collation_valid_translated_core preserved orderCollations
        · have translated := pagination_valid_translated_core preserved limitValid
          split <;> simp_all only [Option.map_none, Option.map_some] <;> exact translated
        · have translated := pagination_valid_translated_core preserved offsetValid
          split <;> simp_all only [Option.map_none, Option.map_some] <;> exact translated
        · simpa only [translateSelect] using lockingValid
        · simp only [translateSelect, List.attach_map_val, noGrouping, List.map_nil]
        · simp only [translateSelect]
          split <;> simp_all
        · simp only [translateSelect, List.attach_map_val, noDistinctOn, List.map_nil]
    | @values ctes env visible cteUses rows cells rowUses output orderBy limit limitUses offset offsetUses offsetFirst
        names definitions shape cellsValid columns nonempty orders limitValid offsetValid =>
      cases offsetFirst <;>
        simp only [translateParameters, translate_values_body, List.attach_map_val,
          Bool.false_eq_true, ↓reduceIte, List.map_append]
      all_goals
        apply QueryValid.values (cells := cells)
        · simpa [CTENamesValid, List.map_map, Function.comp_def, translateCTE] using names
        · exact ctes_valid_translated definitions
        · simpa only [values_shape_translated] using shape
        · exact values_rows_valid_translated_core preserved cellsValid
        · exact columns
        · exact nonempty
        · exact set_orders_valid_translated orders
        · have translated := pagination_valid_translated_core preserved limitValid
          split <;> simp_all only [Option.map_none, Option.map_some] <;> exact translated
        · have translated := pagination_valid_translated_core preserved offsetValid
          split <;> simp_all only [Option.map_none, Option.map_some] <;> exact translated
    | @set ctes env visible cteUses left leftInputs leftUses right rightInputs rightUses op all output
        orderBy limit limitUses offset offsetUses offsetFirst names definitions leftValid rightValid
        leftUnlocked rightUnlocked columns nonempty orders limitValid offsetValid =>
      cases offsetFirst <;>
        simp only [translateParameters, translateQueryBody, List.attach_map_val,
          Bool.false_eq_true, ↓reduceIte, List.map_append]
      all_goals
        apply QueryValid.set
        · simpa [CTENamesValid, List.map_map, Function.comp_def, translateCTE] using names
        · exact ctes_valid_translated definitions
        · simpa only [translateParameters, List.attach_map_val] using set_operand_valid_translated leftValid
        · simpa only [translateParameters, List.attach_map_val] using set_operand_valid_translated rightValid
        · simpa only [translateParameters] using leftUnlocked
        · simpa only [translateParameters] using rightUnlocked
        · exact columns
        · exact nonempty
        · exact set_orders_valid_translated orders
        · have translated := pagination_valid_translated_core preserved limitValid
          split <;> simp_all only [Option.map_none, Option.map_some] <;> exact translated
        · have translated := pagination_valid_translated_core preserved offsetValid
          split <;> simp_all only [Option.map_none, Option.map_some] <;> exact translated
    | @recursiveWith env visible cteUses query output bodyUses nonemptyDefinitions names recursiveFlag definitions body =>
      simp only [List.map_append]
      apply QueryValid.recursiveWith
      · rw [translated_query_ctes]
        intro empty
        exact nonemptyDefinitions (List.map_eq_nil_iff.mp empty)
      · rw [translated_query_ctes]
        exact cte_names_valid_translated _ names
      · simpa only [translated_query_recursive] using recursiveFlag
      · simpa only [translated_query_ctes, recursive_outer_env_translated] using
          recursive_ctes_valid_translated definitions
      · simpa only [without_with_translated] using query_valid_translated body
  termination_by 2 * sizeOf query
  decreasing_by
    all_goals (try have withoutSize := without_with_size_lt _ nonemptyDefinitions)
    all_goals (try have ctesSize := query_ctes_size_lt query)
    all_goals subst_vars
    all_goals (try cases select) <;> (try cases query) <;> (try simp at withoutSize) <;> (try simp at smaller) <;> simp <;> omega

  theorem set_operand_valid_translated
      (valid : SetOperandValid profile catalog params env query output uses) :
      SetOperandValid profile catalog params env (translateParameters query) output
        (uses.map translateParameter) := by
    have preserved : SubqueriesTranslated (QueryValid profile catalog params) (sizeOf query) := by
      intro childEnv child childOutput childUses smaller childValid
      exact query_valid_translated childValid
    cases valid with
    | @basic ctes env visible cteUses scope sourceUses output selectUses pending whereUses orderBy orderUses limit limitUses
        offset offsetUses locking offsetFirst select names definitions source items inputs nonempty distinctComparable distinctCollations
        predicate orders orderCollations limitValid offsetValid lockingValid noGrouping noHaving noDistinctOn =>
      have itemSize : sizeOf select.items < sizeOf select := by cases select; simp; omega
      have whereSize : sizeOf select.whereClause < sizeOf select := by cases select; simp; omega
      cases offsetFirst <;>
        simp only [translateParameters, translateQueryBody, List.attach_map_val,
          Bool.false_eq_true, ↓reduceIte, List.map_append]
      all_goals
        rw [← resolve_leaf_inputs_translated profile select.distinct orderBy pending]
        simp only [translateSelect]
        apply SetOperandValid.basic (pending := pending) (output := output)
        · simpa [CTENamesValid, List.map_map, Function.comp_def, translateCTE] using names
        · simpa only [List.attach_map_val] using ctes_valid_translated definitions
        · have translated := source_valid_translated source
          cases relation : select.source <;> simpa [relation] using translated
        · simpa only [translateSelect, List.attach_map_val] using items_valid_translated_core preserved items
        · simpa only [translateSelect, List.attach_map_val] using items_input_valid_translated_core preserved inputs
        · exact nonempty
        · simpa only [translateSelect] using distinctComparable
        · simpa only [translateSelect] using distinctCollations
        · have translated := predicate_valid_translated_core preserved predicate
          cases condition : select.whereClause <;> simpa [condition] using translated
        · simpa only [translateSelect, List.attach_map_val] using orders_valid_translated_core preserved orders
        · exact orders_collation_valid_translated_core preserved orderCollations
        · have translated := pagination_valid_translated_core preserved limitValid
          split <;> simp_all only [Option.map_none, Option.map_some] <;> exact translated
        · have translated := pagination_valid_translated_core preserved offsetValid
          split <;> simp_all only [Option.map_none, Option.map_some] <;> exact translated
        · simpa only [translateSelect] using lockingValid
        · simp only [List.attach_map_val, noGrouping, List.map_nil]
        · cases select
          simp only at noHaving
          subst_vars
          rfl
        · simp only [List.attach_map_val, noDistinctOn, List.map_nil]
    | values complete =>
      have translated := query_valid_translated complete
      simp only [translateParameters, translateQueryBody, List.attach_map_val] at translated ⊢
      exact SetOperandValid.values translated
    | set complete =>
      have translated := query_valid_translated complete
      simp only [translateParameters, translateQueryBody, List.attach_map_val] at translated ⊢
      exact SetOperandValid.set translated
    | @recursiveWith env visible cteUses query output bodyUses nonemptyDefinitions names recursiveFlag definitions body =>
      simp only [List.map_append]
      apply SetOperandValid.recursiveWith
      · rw [translated_query_ctes]
        intro empty
        exact nonemptyDefinitions (List.map_eq_nil_iff.mp empty)
      · rw [translated_query_ctes]
        exact cte_names_valid_translated _ names
      · simpa only [translated_query_recursive] using recursiveFlag
      · simpa only [translated_query_ctes, recursive_outer_env_translated] using
          recursive_ctes_valid_translated definitions
      · simpa only [without_with_translated] using set_operand_valid_translated body
  termination_by 2 * sizeOf query + 1
  decreasing_by
    all_goals (try have withoutSize := without_with_size_lt _ nonemptyDefinitions)
    all_goals (try have ctesSize := query_ctes_size_lt query)
    all_goals subst_vars
    all_goals (try cases select) <;> (try cases query) <;> (try simp at withoutSize) <;> (try simp at smaller) <;> simp <;> omega

  /-- Definition order and exposed names are unchanged; each body contributes
  its translated occurrences once, independently of references. -/
  theorem ctes_valid_translated
      (valid : CTEsValid profile catalog params env ctes visible uses) :
      CTEsValid profile catalog params env (ctes.map translateCTE) visible
        (uses.map translateParameter) := by
    cases valid with
    | nil => exact .nil
    | @cons env output uses remaining visible restUses head body aliases tail =>
        simpa only [List.map_cons, List.map_append, translateCTE] using
          CTEsValid.cons (head := {head with query := translateParameters head.query}) (query_valid_translated body)
            aliases (ctes_valid_translated tail)
  termination_by 2 * sizeOf ctes
  decreasing_by all_goals subst_vars; cases head; simp; omega

  theorem recursive_cte_valid_translated
      (valid : RecursiveCTEValid profile catalog params env cte output uses) :
      RecursiveCTEValid profile catalog params env (translateCTE cte) output
        (uses.map translateParameter) := by
    cases valid with
    | union names notShadowed prefixFree definitions anchorFree stepReference anchor anchorInputs
        aliases step leftUnlocked rightUnlocked merged sameTypes collation =>
      rw [translateCTE, translateParameters, translateQueryBody]
      simp only [List.attach_map_val, List.map_append]
      apply RecursiveCTEValid.union
      · exact cte_names_valid_translated _ names
      · simpa only [List.mem_map, forall_exists_index, and_imp,
          forall_apply_eq_imp_iff₂, translated_cte_name] using notShadowed
      · simpa only [recursive_cte_references_translated] using prefixFree
      · exact ctes_valid_translated definitions
      · simpa only [recursive_references_translated] using anchorFree
      · simpa only [recursive_references_translated] using stepReference
      · exact query_valid_translated anchor
      · exact set_operand_valid_translated anchorInputs
      · exact aliases
      · exact set_operand_valid_translated step
      · simpa only [translateParameters] using leftUnlocked
      · simpa only [translateParameters] using rightUnlocked
      · exact merged
      · exact sameTypes
      · exact collation
  termination_by 2 * sizeOf cte
  decreasing_by all_goals simp <;> omega

  theorem recursive_ctes_valid_translated
      (valid : RecursiveCTEsValid profile catalog params env ctes visible uses) :
      RecursiveCTEsValid profile catalog params env (ctes.map translateCTE) visible
        (uses.map translateParameter) := by
    cases valid with
    | nil => exact .nil
    | @ordinary remaining env output uses visible restUses head forwardFree noSelf body aliases tail =>
      simp only [List.map_cons, List.map_append]
      apply RecursiveCTEsValid.ordinary
        (output := output)
      · simpa only [translated_cte_query] using (no_forward_cte_references_translated _ _).mpr forwardFree
      · simpa only [translated_cte_name, translated_cte_query, recursive_references_translated] using noSelf
      · simpa only [translated_cte_query] using query_valid_translated body
      · simpa only [translated_cte_columns] using aliases
      · simpa only [translated_cte_name, translated_cte_columns] using recursive_ctes_valid_translated tail
    | @recursive remaining env head output uses visible restUses forwardFree body tail =>
      simp only [List.map_cons, List.map_append]
      apply RecursiveCTEsValid.recursive
      · simpa only [translated_cte_query] using (no_forward_cte_references_translated _ _).mpr forwardFree
      · exact recursive_cte_valid_translated body
      · simpa only [translated_cte_name] using recursive_ctes_valid_translated tail
  termination_by 2 * sizeOf ctes
  decreasing_by all_goals cases head <;> simp <;> omega
end

/-- Translating anonymous occurrences to numbered parameters preserves every
independent basic SELECT validity derivation, with exactly the same environment
and ordered output schema. No parser/renderer success is a hypothesis. The
notation condition is applied once, over all nested query occurrences. -/
theorem translateParameters_valid
    (valid : SelectValid profile catalog params query output) :
    SelectValid profile catalog params (translateParameters query) output := by
  cases valid with
  | certified environment collations supported queryValid parameterOrder =>
      exact .certified environment collations supported (query_valid_translated queryValid)
        (parameter_order_translated parameterOrder)

end SQLean.RenderContract
