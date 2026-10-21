import SQLean.SelectContract.ValuesChecker

namespace SQLean.SelectContract
open Advanced

structure SourceCertificate (profile : Profile) (catalog : Catalog) (params : ParameterEnv) (env : CTEEnv) (source : Option Advanced.From) where
  scope : Scope
  uses : List Parameter
  valid : SourceValid profile catalog params env source scope uses

private def tableColumns (table : CatalogTable) (columns : List Advanced.Column) :
    Except Failure {bindings : List OutputColumn // TableColumns table columns bindings} :=
  match columns with
  | [] => .ok ⟨[], .nil⟩
  | col :: cols => do
      match supported : concreteType col.type with
      | none => .error (unsupported "column_type" "Column type is outside the concrete PostgreSQL scalar profile")
      | some base =>
          let rest ← tableColumns table cols
          .ok ⟨⟨col.name, ⟨base, columnNullable table col⟩, tableColumnCollation table col base⟩ :: rest.val,
            .cons supported rest.property⟩

private def checkJoinKeys (kind : JoinKind) (left right : List OutputColumn)
    (keys : List Name) :
    Except Failure {merged : List OutputColumn // JoinKeysValid kind left right keys merged} :=
  match keys with
  | [] => .ok ⟨[], .nil⟩
  | key :: keys => do
      match leftResolved : left.filter (fun col => col.name == key) with
      | [leftColumn] =>
        match rightResolved : right.filter (fun col => col.name == key) with
        | [rightColumn] =>
          match equality : equalityOverload (.known leftColumn.type) (.known rightColumn.type) with
          | none => .error (operatorFailure [some leftColumn.type, some rightColumn.type] false "join_key_equality" s!"JOIN key '{key}' has no supported equality operator")
          | some operator =>
            match common : conditionalBase [.known leftColumn.type, .known rightColumn.type] with
            | none => .error (invalid "join_key_common_type" s!"JOIN key '{key}' has no common PostgreSQL scalar type")
            | some base =>
              match equalityCoercions : contextualCollations
                  [.column none key, .column none key] [some leftColumn.type, some rightColumn.type]
                  [.stored leftColumn.collation, .stored rightColumn.collation]
                  (concreteCollationTargets operator.inputs) with
              | none => .error (unsupported "join_collation_coercion" "JOIN equality collation coercions lack an independent rule")
              | some coerced =>
                match equalityCollation : CollationDerivation.mergeList coerced with
                | none => .error (invalid "collation_conflict" "JOIN equality inputs have conflicting explicit collations")
                | some _ =>
                  match resultCollation : mergedKeyCollation kind leftColumn rightColumn base with
                  | none => .error (invalid "collation_conflict" "JOIN merged output has conflicting explicit collations")
                  | some collation =>
                    let tail ← checkJoinKeys kind left right keys
                    .ok ⟨⟨key, ⟨base, mergedKeyNullable kind leftColumn.type rightColumn.type⟩, collation⟩ :: tail.val,
                      .cons leftResolved rightResolved equality common equalityCoercions equalityCollation resultCollation tail.property⟩
        | _ => .error (invalid "join_key_binding" s!"JOIN key '{key}' must occur exactly once in the right exposed row")
      | _ => .error (invalid "join_key_binding" s!"JOIN key '{key}' must occur exactly once in the left exposed row")

structure ItemsCertificateCore (subqueries : SubqueryJudgment) (env : CTEEnv) (profile : Profile) (params : ParameterEnv) (scope : Scope) (items : List Advanced.SelectItem) where
  output : List OutputColumn
  uses : List Parameter
  valid : ItemsValidCore subqueries profile params env scope items output uses

private structure ItemsAnalysisCore (subqueries : SubqueryJudgment) (env : CTEEnv) (profile : Profile) (params : ParameterEnv) (scope : Scope) (items : List Advanced.SelectItem)
    extends ItemsCertificateCore subqueries env profile params scope items where
  inputs : List PendingColumn
  inputValid : ItemsInputValidCore subqueries profile params env scope items inputs uses

private def checkItemsCore (subqueries : SubqueryJudgment) (env : CTEEnv)
    (checkSubquery : SubqueryChecker subqueries env) (fuel : Nat) (profile : Profile) (params : ParameterEnv) (scope : Scope) (items : List Advanced.SelectItem) :
    Except Failure (ItemsAnalysisCore subqueries env profile params scope items) :=
  match fuel with
  | 0 => .error exhausted
  | fuel + 1 => match items with
    | [] => .ok ⟨⟨[], [], .nil⟩, [], .nil⟩
    | .expression expr alias :: items => do
        if goodAlias : ∀ name ∈ alias, name ≠ "" then
          let item ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope expr
          let label ← checkExprLabel subqueries env checkSubquery fuel expr
          let tail ← checkItemsCore subqueries env checkSubquery fuel profile params scope items
          .ok ⟨⟨⟨alias.getD label.label.2, projectedType item.type, projectedCollation expr item.type item.derivation⟩ :: tail.output, item.uses ++ tail.uses,
            .expression item.valid item.collationValid label.valid goodAlias tail.valid⟩,
            ⟨alias.getD label.label.2, scalarInput expr item.type, item.derivation, pendingOrigin expr item.type, unknownCollationSortKey profile expr⟩ :: tail.inputs,
            .expression item.valid item.collationValid label.valid goodAlias tail.inputValid⟩
        else .error (invalid "empty_alias" "A projection alias must be nonempty")
    | .all qualifier schema :: items => do
        checkNamespace scope qualifier schema
        let selected := scope.columns qualifier schema
        if nonempty : selected ≠ [] then
          let tail ← checkItemsCore subqueries env checkSubquery fuel profile params scope items
          .ok ⟨⟨selected ++ tail.output, tail.uses, .all rfl nonempty tail.valid⟩,
            knownColumns selected ++ tail.inputs, .all rfl nonempty tail.inputValid⟩
        else .error (invalid "wildcard_binding" "Wildcard must identify a nonempty visible input scope")

private def checkPredicateCore (subqueries : SubqueryJudgment) (env : CTEEnv)
    (checkSubquery : SubqueryChecker subqueries env) (fuel : Nat) (profile : Profile) (params : ParameterEnv) (scope : Scope) (expr : Option Advanced.Expr) :
    Except Failure {uses : List Parameter // PredicateValidCore subqueries profile params env scope expr uses} :=
  match expr with
  | none => .ok ⟨[], .absent⟩
  | some expr => do
      if uncontextualizedString expr then
        throw (unsupported "predicate_string_coercion"
          "Contextual Boolean conversion of an unknown string literal is not implemented yet")
      let arg ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope expr
      if boolean : acceptsBase .bool arg.type = true then
        .ok ⟨arg.uses, .present arg.valid arg.collationValid boolean⟩
      else .error (invalid "predicate_type" "WHERE requires a Boolean expression")

private def checkSortCore (subqueries : SubqueryJudgment) (env : CTEEnv)
    (checkSubquery : SubqueryChecker subqueries env) (fuel : Nat) (profile : Profile) (params : ParameterEnv) (scope : Scope) (projection : List Advanced.SelectItem) (output : List OutputColumn)
    (distinct : Bool) (expr : Advanced.Expr) :
    Except Failure {uses : List Parameter // SortValidCore subqueries profile params env scope projection output distinct expr uses} :=
  match category : sortSyntax expr with
  | .integer position =>
      if positive : 0 < position then
        if inRange : position.toNat ≤ output.length then
          if orderable : OrdinalOrderable output position.toNat then
            .ok ⟨[], .ordinal category positive inRange orderable⟩
          else .error (operatorFailure [((output[position.toNat - 1]?).map OutputColumn.type)] false
              "order_type" "ORDER BY output type has no PostgreSQL ordering operator")
        else .error (invalid "order_position" "ORDER BY position exceeds expanded output width")
      else .error (invalid "order_position" "ORDER BY positions are one-based")
  | .numericConstant | .otherConstant =>
      .error (invalid "order_constant" "A bare ORDER BY constant must be an INT4 integer ordinal")
  | .expression => match expr with
    | .column none name none =>
        match found : output.filter (·.name == name) with
        | [column] =>
            if orderable : column.type.base.orderable = true then .ok ⟨[], .outputName found orderable⟩
            else .error (operatorFailure [some column.type] false
                "order_type" "ORDER BY output type has no PostgreSQL ordering operator")
        | [] => do
            if ordinary : distinct = false then
              let typed ← checkExprCore subqueries env checkSubquery fuel params scope (.column none name)
              if orderable : typed.type.orderable = true then
                .ok ⟨typed.uses, .inputName found ordinary typed.valid orderable⟩
              else .error (operatorFailure [typed.type] false
                  "order_type" "ORDER BY input type has no PostgreSQL ordering operator")
            else .error (unsupported "distinct_order_expression" "DISTINCT ordering by an input name requires projected-expression identity rules; use an output label or position")
        | column :: _remaining =>
            if same : SameOutputExpressions profile projection output name then
              if orderable : column.type.base.orderable = true then
                .ok ⟨[], .repeatedName same found orderable⟩
              else .error (operatorFailure [some column.type] false
                "order_type" "ORDER BY output type has no PostgreSQL ordering operator")
            else .error (unsupported "output_expression_identity"
              s!"Repeated ORDER BY label '{name}' requires transformed projection-expression identity")
    | expr => do
        if ordinary : distinct = false then
          if category : SortExpression expr then
            let typed ← checkExprCore subqueries env checkSubquery fuel params scope expr
            if orderable : typed.type.orderable = true then
              .ok ⟨typed.uses, .expression ordinary typed.valid category orderable⟩
            else .error (operatorFailure [typed.type] false
                "order_type" "ORDER BY expression type has no PostgreSQL ordering operator")
          else .error (invalid "order_category" "Unclassified ORDER BY syntax")
        else .error (unsupported "distinct_order_expression" "This milestone supports DISTINCT ordering by output name or position")
private def checkSortListCore (subqueries : SubqueryJudgment) (env : CTEEnv)
    (checkSubquery : SubqueryChecker subqueries env) (fuel : Nat) (profile : Profile) (params : ParameterEnv) (scope : Scope) (projection : List Advanced.SelectItem) (output : List OutputColumn)
    (distinct : Bool) (items : List Advanced.OrderBy) :
    Except Failure {uses : List Parameter // SortListValidCore subqueries profile params env scope projection output distinct items uses} :=
  match fuel with
  | 0 => .error exhausted
  | fuel + 1 => match items with
    | [] => .ok ⟨[], .nil⟩
    | item :: items => do
        let head ← checkSortCore subqueries env checkSubquery fuel profile params scope projection output distinct item.expr
        let tail ← checkSortListCore subqueries env checkSubquery fuel profile params scope projection output distinct items
        .ok ⟨head.val ++ tail.val, .cons head.property tail.property⟩

private def checkOrdersCore (subqueries : SubqueryJudgment) (env : CTEEnv)
    (checkSubquery : SubqueryChecker subqueries env) (fuel : Nat) (profile : Profile) (params : ParameterEnv) (scope : Scope)
    (projection : List Advanced.SelectItem) (output : List OutputColumn) (distinct : Bool)
    (items : List Advanced.OrderBy) :
    Except Failure {uses : List Parameter // OrdersValidCore subqueries profile params env scope projection output distinct items uses} := do
  if sequence : OrderSequenceSafe profile projection output items then
    let checked ← checkSortListCore subqueries env checkSubquery fuel profile params scope projection output distinct items
    .ok ⟨checked.val, .checked checked.property sequence⟩
  else .error (invalid "ambiguous_output"
    "Earlier ORDER BY entries resolved only some identical unknown targets; the repeated name is ambiguous")

private def checkSortCollationCore (subqueries : SubqueryJudgment) (env : CTEEnv)
    (checkSubquery : SubqueryChecker subqueries env) (fuel : Nat) (profile : Profile) (params : ParameterEnv)
    (scope : Scope) (pending : List PendingColumn) (expr : Advanced.Expr) :
    Except Failure {_u : Unit // SortCollationValidCore subqueries profile params env scope pending expr} := do
  match category : sortSyntax expr with
  | .integer position =>
      match resolved : pending[position.toNat - 1]? with
      | none => .error (invalid "order_position" "ORDER BY position exceeds expanded output width")
      | some column =>
        if determinate : column.derivation.determinate = true then
          .ok ⟨(), .ordinal category resolved determinate⟩
        else .error (invalid "collation_conflict" "ORDER BY target has an indeterminate collation")
  | .numericConstant | .otherConstant =>
      .error (invalid "order_constant" "A bare ORDER BY constant must be an INT4 integer ordinal")
  | .expression => match exprEq : expr with
    | .column none name none =>
      match resolved : pending.find? (fun column => column.name == name) with
      | some column =>
        if determinate : column.derivation.determinate = true then
          .ok ⟨(), by rw [exprEq]; exact .outputName resolved determinate⟩
        else .error (invalid "collation_conflict" "ORDER BY target has an indeterminate collation")
      | none => do
        let typed ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope (.column none name)
        if determinate : typed.derivation.determinate = true then
          .ok ⟨(), by rw [exprEq]; exact .inputName resolved typed.collationValid determinate⟩
        else .error (invalid "collation_conflict" "ORDER BY input has an indeterminate collation")
    | expr =>
      if expression : SortExpression expr then
        let typed ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope expr
        if determinate : typed.derivation.determinate = true then
          .ok ⟨(), by rw [exprEq]; exact .expression expression typed.collationValid determinate⟩
        else .error (invalid "collation_conflict" "ORDER BY expression has an indeterminate collation")
      else .error (invalid "order_category" "Unclassified ORDER BY syntax")

private def checkOrdersCollationCore (subqueries : SubqueryJudgment) (env : CTEEnv)
    (checkSubquery : SubqueryChecker subqueries env) (fuel : Nat) (profile : Profile) (params : ParameterEnv)
    (scope : Scope) (pending : List PendingColumn) (items : List Advanced.OrderBy) :
    Except Failure {_u : Unit // OrdersCollationValidCore subqueries profile params env scope pending items} :=
  match fuel with
  | 0 => .error exhausted
  | fuel + 1 => match items with
    | [] => .ok ⟨(), .nil⟩
    | item :: items => do
      let head ← checkSortCollationCore subqueries env checkSubquery fuel profile params scope pending item.expr
      let tail ← checkOrdersCollationCore subqueries env checkSubquery fuel profile params scope pending items
      .ok ⟨(), .cons head.property tail.property⟩

private def checkSetColumns (fuel : Nat) (op : SetOp) (all : Bool)
    (left right : List PendingColumn) :
    Except Failure {output : List OutputColumn // SetColumnsValid op all left right output} :=
  match fuel with
  | 0 => .error exhausted
  | fuel + 1 => match left, right with
    | [], [] => .ok ⟨[], .nil⟩
    | l :: ls, r :: rs => do
        match common : conditionalBase [l.input, r.input] with
        | none => .error (invalid "set_common_type" "Corresponding set columns have no common PostgreSQL type")
        | some base =>
            if leftCoercion : acceptsInput l.input base = true then
              if rightCoercion : acceptsInput r.input base = true then
                if grouping : SetGroupingAllowed op all base then
                  match collation : CollationDerivation.merge
                      (pendingCoercion l.origin l.input l.derivation base)
                      (pendingCoercion r.origin r.input r.derivation base) with
                  | none => .error (invalid "collation_conflict" "Set columns have conflicting explicit collations")
                  | some derivation =>
                    if determinate : (op = .union ∧ all = true) ∨ derivation.determinate = true then
                      let tail ← checkSetColumns fuel op all ls rs
                      .ok ⟨⟨l.name, ⟨base, l.input.nullable || r.input.nullable⟩, derivation.identity⟩ :: tail.val,
                        .cons common leftCoercion rightCoercion grouping collation determinate tail.property⟩
                    else .error (invalid "collation_conflict" "Set duplicate matching requires a determinate collation")
                else .error (invalid "set_equality"
                  "Set duplicate/group matching requires equality, including array element equality")
              else .error (invalid "set_right_coercion" "The right set column cannot acquire the selected common type")
            else .error (invalid "set_left_coercion" "The left set column cannot acquire the selected common type")
    | _, _ => .error (invalid "set_width" "Set operands must have the same number of output columns")

private def checkSetSort (output : List OutputColumn) (expr : Advanced.Expr) :
    Except Failure {_u : Unit // SetSortValid output expr} :=
  match category : sortSyntax expr with
  | .integer position =>
      if positive : 0 < position then
        if inRange : position.toNat ≤ output.length then
          if orderable : OrdinalOrderable output position.toNat then
            .ok ⟨(), .ordinal category positive inRange orderable⟩
          else .error (invalid "order_type" "The set output has no ordering operator")
        else .error (invalid "order_position" "ORDER BY position exceeds set output width")
      else .error (invalid "order_position" "ORDER BY positions are one-based")
  | .numericConstant | .otherConstant =>
      .error (invalid "order_constant" "A bare ORDER BY constant must be an INT4 integer ordinal")
  | .expression => match expr with
    | .column none name none =>
      match found : output.filter (·.name == name) with
      | [column] =>
        if orderable : column.type.base.orderable = true then .ok ⟨(), .outputName found orderable⟩
        else .error (invalid "order_type" "The set output has no ordering operator")
      | [] => .error (invalid "set_order_name" "Set ORDER BY must name a left-result output column")
      | _ => .error (invalid "ambiguous_output" "Set ORDER BY output label is ambiguous")
    | _ => .error (invalid "set_order_expression" "Set ORDER BY admits only output names or ordinals")

private def checkSetOrders (fuel : Nat) (output : List OutputColumn) (items : List Advanced.OrderBy) :
    Except Failure {_u : Unit // SetOrdersValid output items} :=
  match fuel with
  | 0 => .error exhausted
  | fuel + 1 => match items with
    | [] => .ok ⟨(), .nil⟩
    | item :: items => do
      let head ← checkSetSort output item.expr
      let tail ← checkSetOrders fuel output items
      .ok ⟨(), .cons head.property tail.property⟩

/-- Check one pagination expression in an empty local scope. This proves a
static coercion to a row count, not nonnegativity of its eventual runtime value. -/
def checkPaginationCore (subqueries : SubqueryJudgment) (env : CTEEnv)
    (checkSubquery : SubqueryChecker subqueries env) (fuel : Nat) (profile : Profile) (params : ParameterEnv) (expr : Option Advanced.Expr) :
    Except Failure {uses : List Parameter // PaginationValidCore subqueries profile params env expr uses} :=
  match fuel with
  | 0 => .error exhausted
  | fuel + 1 => match expr with
    | none => .ok ⟨[], .absent⟩
    | some expr => do
        if uncontextualizedString expr then
          throw (unsupported "pagination_string_literal" "Contextual conversion of an unknown string literal to a row count is outside this profile")
        let arg ← checkCompleteExprCore subqueries env checkSubquery fuel profile params .empty expr
        match typeEq : arg.type with
        | none =>
            .ok ⟨arg.uses, .present (by simpa only [typeEq] using arg.valid) (by simpa only [typeEq] using arg.collationValid) .unknownNull⟩
        | some ⟨.int32, nullable⟩ =>
            .ok ⟨arg.uses, .present (by simpa only [typeEq] using arg.valid) (by simpa only [typeEq] using arg.collationValid) (.int32Widen nullable)⟩
        | some ⟨.smallInt, nullable⟩ =>
            .ok ⟨arg.uses, .present (by simpa only [typeEq] using arg.valid) (by simpa only [typeEq] using arg.collationValid) (.smallIntWiden nullable)⟩
        | some ⟨.int64, nullable⟩ =>
            .ok ⟨arg.uses, .present (by simpa only [typeEq] using arg.valid) (by simpa only [typeEq] using arg.collationValid) (.int64Identity nullable)⟩
        | some ⟨.numeric modifiers, nullable⟩ =>
            .ok ⟨arg.uses, .present (by simpa only [typeEq] using arg.valid) (by simpa only [typeEq] using arg.collationValid) (.numericAssignment modifiers nullable)⟩
        | some ⟨.real, nullable⟩ =>
            .ok ⟨arg.uses, .present (by simpa only [typeEq] using arg.valid) (by simpa only [typeEq] using arg.collationValid) (.realAssignment nullable)⟩
        | some ⟨.doublePrecision, nullable⟩ =>
            .ok ⟨arg.uses, .present (by simpa only [typeEq] using arg.valid) (by simpa only [typeEq] using arg.collationValid) (.doubleAssignment nullable)⟩
        | some _ =>
            .error (invalid "pagination_type" "Pagination requires a numeric expression assignable to INT8 or untyped NULL")

abbrev ItemsCertificate := ItemsCertificateCore NoSubqueries []
abbrev checkPagination := checkPaginationCore NoSubqueries [] noSubqueryChecker

/-- Certify only the outer LIMIT/OFFSET expressions of an exact query.
The body may be outside the basic SELECT fragment. This API does not establish
query-wide parameter notation or any property of unexamined query clauses. -/
def checkPaginationBounds (profile : Profile) (params : ParameterEnv) (query : Advanced.Query)
    (fuel : Nat := 1024) : Except Failure (PaginationBoundsCertificate profile params query) := do
  if fuel = 0 then throw exhausted
  if environment : ParametersWellFormed params then
    if collations : profile.collations.WellFormed then
      let limit ← checkPagination fuel profile params query.limit
      let offset ← checkPagination fuel profile params query.offset
      .ok ⟨limit.val, offset.val, .bounds environment collations limit.property offset.property⟩
    else .error (invalid "invalid_collation_environment" "Pagination requires a well-formed collation snapshot")
  else if ParametersWellFormed (precisionDiagnosticParameters params) then
    .error intervalPrecisionFailure
  else .error (invalid "invalid_environment" "Parameter metadata violates index uniqueness, positivity or type-declaration rules")

/-- Pagination-only soundness has no premise asserting validity of the body. -/
theorem checkPaginationBounds_sound
    (profile : Profile) (params : ParameterEnv) (query : Advanced.Query)
    (fuel : Nat) (certificate : PaginationBoundsCertificate profile params query)
    (_success : checkPaginationBounds profile params query fuel = .ok certificate) :
    PaginationBoundsValid profile params query certificate.limitUses certificate.offsetUses :=
  certificate.valid

structure LockingCertificate (scope : Scope) (distinct : Bool)
    (clauses : List Advanced.LockingClause) : Type where
  valid : LockingValid scope distinct clauses

/-- OF selects the first matching relation, independently of column ambiguity. -/
def checkLocking (scope : Scope) (distinct : Bool)
    (clauses : List Advanced.LockingClause) :
    Except Failure (LockingCertificate scope distinct clauses) :=
  match clauses with
  | [] => .ok ⟨.nil⟩
  | clause :: clauses => do
    if ordinary : distinct = false then
      let selected := if clause.targets.isEmpty then scope.relations else
        clause.targets.filterMap (fun target => scope.relations.find? (fun relation => relation.visible && relation.name == target))
      if !clause.targets.isEmpty && selected.any (fun relation => relation.origin == .cte) then
        throw (invalid "locking_cte" "An explicit OF target cannot name a WITH query")
      if selected.any (fun relation => relation.origin == .derived) then
        throw (unsupported "derived_locking"
          "Row-lock propagation through a selected derived source is not independently modeled")
      if selected.any (fun relation => relation.origin.isBase && relation.nullable) then
        throw (invalid "locking_nullable" "A nullable-side base relation cannot receive a row lock")
      if targets : LockTargets scope clause.targets then
        let tail ← checkLocking scope distinct clauses
        .ok ⟨.cons ordinary targets tail.valid⟩
      else .error (invalid "locking_target" "FOR locking targets must select nonnullable base relations")
    else .error (invalid "locking_distinct" "Row locking cannot be combined with DISTINCT")

/-- Diagnostic traversal only. Nested query aggregates belong to their own
query level; unsupported correlation still cannot acquire a basic certificate.
Resource exhaustion remains Inconclusive rather than an invalidity claim. -/
private def currentAggregate : Nat → Advanced.Expr → Except Failure Bool
  | 0, _ => .error exhausted
  | fuel + 1, expr => do
    match expr with
    | .countAll | .aggregate .. | .filteredAggregate .. => pure true
    | _ =>
      let children : List Advanced.Expr := match expr with
        | .binary _ a b | .pattern a b _ | .nullIf a b
        | .quantifiedComparison _ _ a b | .concat a b | .regex a b .. | .jsonAccess _ a b | .jsonExistence _ a b
        | .containment a b _ | .overlap a b | .distinctFrom a b _ => [a, b]
        | .unary _ a | .cast a _ | .collate a _ | .extract _ a | .isNull a _ | .inQuery a _ | .quantifiedQuery _ _ a _ => [a]
        | .subscript base indices => base :: indices.flatMap Advanced.Subscript.expressions
        | .namedCall _ args => args.map CallArgument.expression
        | .array args | .row args | .call _ args | .substring _ args
        | .coalesce args | .greatest args | .least args => args
        | .caseExpr operand branches otherwise =>
          operand.toList ++ branches.flatMap (fun (branch : Advanced.Expr × Advanced.Expr) =>
            [branch.1, branch.2]) ++ otherwise.toList
        | .inList arg values => arg :: values
        | .between arg lower upper _ => [arg, lower, upper]
        | _ => []
      children.foldlM (fun found child => do
        let childAggregate ← currentAggregate fuel child
        pure (found || childAggregate)) false

private def checkLockingShape (fuel : Nat) (query : Advanced.Query) : Except Failure Unit := do
  if query.locking.isEmpty then pure () else
  match query.body with
  | .values _ => .error (invalid "locking_values" "Row locking cannot apply to a VALUES result")
  | .set .. => .error (invalid "locking_set_operation" "Row locking cannot apply to a set-operation result")
  | .select select =>
    if select.distinct || !select.distinctOn.isEmpty then
      .error (invalid "locking_distinct" "Row locking cannot be combined with DISTINCT or DISTINCT ON")
    else if !select.groupBy.isEmpty || select.having.isSome then
      .error (invalid "locking_grouping" "Row locking cannot be combined with GROUP BY or HAVING")
    else
      let exprs := select.items.filterMap (fun item => match item with
          | .all .. => none | .expression expr _ => some expr) ++
        select.whereClause.toList ++ query.orderBy.map Advanced.OrderBy.expr ++
        query.limit.toList ++ query.offset.toList
      let aggregate ← exprs.foldlM (fun found expr => do
        let present ← currentAggregate fuel expr
        pure (found || present)) false
      if aggregate then .error (invalid "locking_aggregate" "Row locking cannot apply to an aggregate query")
      else pure ()

structure QueryCertificate (profile : Profile) (catalog : Catalog) (params : ParameterEnv)
    (env : CTEEnv) (query : Advanced.Query) where
  output : List OutputColumn
  uses : List Parameter
  valid : QueryValid profile catalog params env query output uses

private structure QueryAnalysis (profile : Profile) (catalog : Catalog) (params : ParameterEnv)
    (env : CTEEnv) (query : Advanced.Query) extends QueryCertificate profile catalog params env query where
  inputs : List PendingColumn
  operandValid : SetOperandValid profile catalog params env query inputs uses

structure CTEsCertificate (profile : Profile) (catalog : Catalog) (params : ParameterEnv)
    (env : CTEEnv) (ctes : List Advanced.CTE) where
  visible : CTEEnv
  uses : List Parameter
  valid : CTEsValid profile catalog params env ctes visible uses

private structure RecursiveCTEsCertificate (profile : Profile) (catalog : Catalog) (params : ParameterEnv)
    (env : CTEEnv) (ctes : List Advanced.CTE) where
  visible : CTEEnv
  uses : List Parameter
  valid : RecursiveCTEsValid profile catalog params env ctes visible uses

private structure RecursiveCTECertificate (profile : Profile) (catalog : Catalog) (params : ParameterEnv)
    (env : CTEEnv) (cte : Advanced.CTE) where
  output : List OutputColumn
  uses : List Parameter
  valid : RecursiveCTEValid profile catalog params env cte output uses

private def expressionSubqueryResult
    (result : Except Failure (QueryAnalysis profile catalog params env query)) :
    Except Failure (SubqueryCertificate (QueryValid profile catalog params) env query) :=
  match result with
  | .ok checked => .ok ⟨checked.output, checked.uses, checked.valid⟩
  | .error (.invalid diagnostic) =>
    if ["column_binding", "relation_reference"].contains diagnostic.code then
      .error (unsupported "subquery_correlation"
        "A nested name may resolve to an outer row; correlated expression subqueries require a separate scope rule")
    else if diagnostic.code == "empty_projection" then
      .error (unsupported "subquery_projection"
        "A zero-column subquery requires an independent empty-output query rule")
    else if diagnostic.code == "locking_nullable" then
      .error (unsupported "subquery_planning_lock"
        "Nullable-side locking in a subquery depends on whether its plan is evaluated")
    else .error (.invalid diagnostic)
  | .error failure => .error failure


mutual
  private def checkSource (fuel : Nat) (profile : Profile) (catalog : Catalog) (params : ParameterEnv)
      (env : CTEEnv) (source : Option Advanced.From) :
      Except Failure (SourceCertificate profile catalog params env source) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => match source with
    | none => .ok ⟨.empty, [], .empty⟩
    | some (.table name alias columns schema) => do
        if schema == some "pg_temp" then
          throw (unsupported "namespace_alias" "The pg_temp schema alias requires explicit schema-alias resolution")
        if goodAlias : ∀ name ∈ alias, name ≠ "" then
          if unshadowed : schema.isSome = true ∨ env.lookup name = none then
            match found : catalog.filter (fun table => table.matchesReference name schema) with
            | [table] =>
                have member : table ∈ catalog.filter (fun t => t.matchesReference name schema) := by rw [found]; simp
                have facts := List.mem_filter.mp member
                let bindings ← tableColumns table table.columns
                if noRenaming : columns = [] then
                  .ok ⟨Scope.ofTable table.identity alias bindings.val, [],
                    noRenaming ▸ .table unshadowed facts.1 (by simpa using facts.2) goodAlias bindings.property⟩
                else match aliasEq : alias with
                  | none => .error (invalid "table_column_aliases" "A table column alias list requires a relation alias")
                  | some aliasName =>
                      if aliasesValid : ColumnAliasesValid columns bindings.val then
                        .ok ⟨Scope.ofTable table.identity (some aliasName) (renameOutput columns bindings.val), [], by
                          rw [aliasEq]
                          exact .tableRenamed unshadowed facts.1 (by simpa using facts.2)
                            (goodAlias aliasName (by simp [aliasEq])) bindings.property aliasesValid⟩
                      else .error (invalid "table_column_aliases"
                        "Table column aliases must be nonempty and cannot exceed the column count")
            | _ =>
                if schema.isSome && catalog.any (fun table => table.schema.isNone && table.name == name) then
                  .error (unsupported "relation_schema_metadata" "Legacy catalog metadata does not identify this schema-qualified relation")
                else .error (invalid "relation_binding" s!"Relation '{name}' must resolve to exactly one catalog entry")
          else
            have schemaNone : schema = none := by
              cases schema <;> simp_all
            match found : env.lookup name with
            | none => False.elim (unshadowed (Or.inr found))
            | some binding =>
                if columnsValid : ColumnAliasesValid columns binding.output then
                  if aliasRequired : columns = [] ∨ alias.isSome = true then
                    .ok ⟨Scope.ofCTE name alias (renameOutput columns binding.output), [], by
                      rw [schemaNone]
                      exact .cte found goodAlias columnsValid aliasRequired⟩
                  else .error (invalid "cte_reference_aliases" "A CTE reference column alias list requires a relation alias")
                else .error (invalid "cte_reference_aliases" "CTE reference aliases cannot exceed its width or contain empty names")
        else .error (invalid "empty_alias" "A relation alias must be nonempty")
    | some (.derivedAnonymous query lateral) => do
        if nonLateral : lateral = false then
          let child ← checkQueryCore fuel profile catalog params env query
          .ok ⟨Scope.ofAnonymousOutput child.output, child.uses, .derivedAnonymous child.valid nonLateral⟩
        else .error (unsupported "lateral_source" "Independent correlated LATERAL source rules are not implemented yet")
    | some (.derived query alias columns lateral) => do
        if nonLateral : lateral = false then
          if aliasValid : alias ≠ "" then
            let child ← checkQueryCore fuel profile catalog params env query
            if columnsValid : ColumnAliasesValid columns child.output then
              .ok ⟨Scope.ofOutput alias (renameOutput columns child.output), child.uses,
                .derived child.valid aliasValid columnsValid nonLateral⟩
            else .error (invalid "derived_column_aliases" "Derived column aliases must be nonempty and cannot exceed the output width")
          else .error (invalid "empty_alias" "A derived relation alias must be nonempty")
        else .error (unsupported "lateral_source" "Independent correlated LATERAL source rules are not implemented yet")
    | some (.join kind left right condition) => do
        match conditionEq : condition with
        | .using keys =>
          if kindValid : kind ≠ .cross then
            if nonempty : keys ≠ [] then
              if unique : keys.Nodup then
                let leftValid ← checkSource fuel profile catalog params env (some left)
                let rightValid ← checkSource fuel profile catalog params env (some right)
                if aliases : JoinAliasesDistinct leftValid.scope rightValid.scope then
                  let merged ← checkJoinKeys kind leftValid.scope.output rightValid.scope.output keys
                  .ok ⟨mergedJoinScope kind leftValid.scope rightValid.scope keys merged.val,
                    leftValid.uses ++ rightValid.uses, by
                      rw [conditionEq]
                      exact .using leftValid.valid rightValid.valid aliases kindValid nonempty unique merged.property⟩
                else .error (invalid "duplicate_relation_alias" "Visible relation aliases must be distinct")
              else .error (invalid "duplicate_join_key" "JOIN USING keys must be distinct")
            else .error (invalid "empty_join_keys" "JOIN USING requires at least one key")
          else .error (invalid "join_condition" "CROSS JOIN cannot carry USING")
        | .natural =>
          if kindValid : kind ≠ .cross then
            let leftValid ← checkSource fuel profile catalog params env (some left)
            let rightValid ← checkSource fuel profile catalog params env (some right)
            if aliases : JoinAliasesDistinct leftValid.scope rightValid.scope then
              let keys := naturalJoinKeys leftValid.scope.output rightValid.scope.output
              if unique : keys.Nodup then
                let merged ← checkJoinKeys kind leftValid.scope.output rightValid.scope.output keys
                .ok ⟨mergedJoinScope kind leftValid.scope rightValid.scope keys merged.val,
                  leftValid.uses ++ rightValid.uses, by
                    rw [conditionEq]
                    exact .natural leftValid.valid rightValid.valid aliases kindValid unique merged.property⟩
              else .error (invalid "duplicate_join_key" "NATURAL JOIN finds repeated exposed key names")
            else .error (invalid "duplicate_relation_alias" "Visible relation aliases must be distinct")
          else .error (invalid "join_condition" "CROSS JOIN cannot be NATURAL")
        | .none =>
          if cross : kind = .cross then
            let leftValid ← checkSource fuel profile catalog params env (some left)
            let rightValid ← checkSource fuel profile catalog params env (some right)
            if aliases : JoinAliasesDistinct leftValid.scope rightValid.scope then
              .ok ⟨leftValid.scope ++ rightValid.scope, leftValid.uses ++ rightValid.uses,
                by rw [conditionEq, cross]; exact .cross leftValid.valid rightValid.valid aliases⟩
            else .error (invalid "duplicate_relation_alias" "Visible relation aliases must be distinct")
          else .error (invalid "join_condition" "An ordinary join requires an ON condition")
        | .on expr =>
          if kindValid : kind ≠ .cross then
            if uncontextualizedString expr then
              throw (unsupported "predicate_string_coercion"
                "Contextual Boolean conversion of an unknown string literal is not implemented yet")
            let leftValid ← checkSource fuel profile catalog params env (some left)
            let rightValid ← checkSource fuel profile catalog params env (some right)
            if aliases : JoinAliasesDistinct leftValid.scope rightValid.scope then
              let predicate ← checkCompleteExprCore (QueryValid profile catalog params) env
                (fun child => expressionSubqueryResult (checkQueryCore fuel profile catalog params env child))
                fuel profile params (leftValid.scope ++ rightValid.scope) expr
              if boolean : acceptsBase .bool predicate.type = true then
                .ok ⟨joinScope kind leftValid.scope rightValid.scope,
                  leftValid.uses ++ rightValid.uses ++ predicate.uses,
                  by
                    rw [conditionEq]
                    exact .on leftValid.valid rightValid.valid aliases kindValid
                      (.present predicate.valid predicate.collationValid boolean)⟩
              else .error (invalid "join_predicate_type" "JOIN ON requires a Boolean expression")
            else .error (invalid "duplicate_relation_alias" "Visible relation aliases must be distinct")
          else .error (invalid "join_condition" "CROSS JOIN cannot carry an ON condition")


  private def checkQueryCore (fuel : Nat) (profile : Profile) (catalog : Catalog)
      (params : ParameterEnv) (env : CTEEnv) (query : Advanced.Query) :
      Except Failure (QueryAnalysis profile catalog params env query) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => do
      checkLockingShape fuel query
      match queryEq : query with
      | ⟨body, ctes, recursive, orderBy, limit, offset, locking, offsetFirst⟩ =>
        if noRecursive : recursive = false then
          if namesValid : CTENamesValid ctes then
            let definitions ← checkCTEs fuel profile catalog params env ctes
            let checkSubquery : SubqueryChecker (QueryValid profile catalog params) definitions.visible :=
              fun child => expressionSubqueryResult (checkQueryCore fuel profile catalog params definitions.visible child)
            match bodyEq : body with
            | .values rows =>
              if unlocked : locking = [] then
                if shape : valuesShape rows = true then
                  let cells ← checkValuesRows (QueryValid profile catalog params) definitions.visible
                    checkSubquery fuel profile params rows
                  let columns ← checkValuesColumns fuel 0 (valuesTranspose cells.cells)
                  if nonempty : columns.val ≠ [] then
                    let orders ← checkSetOrders fuel columns.val orderBy
                    let checkedLimit ← checkPaginationCore (QueryValid profile catalog params) definitions.visible checkSubquery fuel profile params limit
                    let checkedOffset ← checkPaginationCore (QueryValid profile catalog params) definitions.visible checkSubquery fuel profile params offset
                    let uses := definitions.uses ++ cells.uses ++
                      if offsetFirst then checkedOffset.val ++ checkedLimit.val else checkedLimit.val ++ checkedOffset.val
                    have complete : QueryValid profile catalog params env query columns.val uses := by
                      rw [queryEq, bodyEq, noRecursive, unlocked]
                      exact .values namesValid definitions.valid shape cells.valid columns.property nonempty
                        orders.property checkedLimit.property checkedOffset.property
                    .ok ⟨⟨columns.val, uses, complete⟩, knownColumns columns.val, by
                      dsimp only
                      rw [queryEq, bodyEq]
                      exact .values (by simpa only [queryEq, bodyEq] using complete)⟩
                  else .error (invalid "values_arity" "VALUES must expose positive column arity")
                else .error (invalid "values_arity" "VALUES requires nonempty, equally sized rows")
              else .error (invalid "locking_values" "Row locking cannot apply to a VALUES result")
            | .set op all left right =>
              if unlocked : locking = [] then
                if leftUnlocked : left.locking = [] then
                  if rightUnlocked : right.locking = [] then
                    let l ← checkQueryCore fuel profile catalog params definitions.visible left
                    let r ← checkQueryCore fuel profile catalog params definitions.visible right
                    let columns ← checkSetColumns fuel op all l.inputs r.inputs
                    if nonempty : columns.val ≠ [] then
                      let orders ← checkSetOrders fuel columns.val orderBy
                      let checkedLimit ← checkPaginationCore (QueryValid profile catalog params) definitions.visible checkSubquery fuel profile params limit
                      let checkedOffset ← checkPaginationCore (QueryValid profile catalog params) definitions.visible checkSubquery fuel profile params offset
                      let uses := definitions.uses ++ l.uses ++ r.uses ++
                        if offsetFirst then checkedOffset.val ++ checkedLimit.val else checkedLimit.val ++ checkedOffset.val
                      have complete : QueryValid profile catalog params env query columns.val uses := by
                        rw [queryEq, bodyEq, noRecursive, unlocked]
                        exact .set namesValid definitions.valid l.operandValid r.operandValid
                          leftUnlocked rightUnlocked columns.property nonempty orders.property
                          checkedLimit.property checkedOffset.property
                      .ok ⟨⟨columns.val, uses, complete⟩, knownColumns columns.val, by
                        dsimp only
                        rw [queryEq, bodyEq]
                        exact .set (by simpa only [queryEq, bodyEq] using complete)⟩
                    else .error (invalid "empty_projection" "Set operands must produce output columns")
                  else .error (invalid "locking_set_operand" "A direct set operand cannot have row-locking clauses")
                else .error (invalid "locking_set_operand" "A direct set operand cannot have row-locking clauses")
              else .error (invalid "locking_set_operation" "Row locking cannot apply to a set-operation result")
            | .select select =>
              if noGrouping : select.groupBy = [] then
                if noHaving : select.having = none then
                  if noDistinctOn : select.distinctOn = [] then
                    let source ← checkSource fuel profile catalog params definitions.visible select.source
                    let items ← checkItemsCore (QueryValid profile catalog params) definitions.visible checkSubquery fuel profile params source.scope select.items
                    if nonempty : items.output ≠ [] then
                      if distinctComparable : DistinctAllowed select.distinct items.output then
                        if distinctCollations : DistinctCollations select.distinct items.inputs then
                          let predicate ← checkPredicateCore (QueryValid profile catalog params) definitions.visible checkSubquery fuel profile params source.scope select.whereClause
                          let orders ← checkOrdersCore (QueryValid profile catalog params) definitions.visible checkSubquery fuel profile params source.scope select.items items.output select.distinct orderBy
                          let orderCollations ← checkOrdersCollationCore (QueryValid profile catalog params) definitions.visible checkSubquery fuel profile params source.scope items.inputs orderBy
                          let checkedLimit ← checkPaginationCore (QueryValid profile catalog params) definitions.visible checkSubquery fuel profile params limit
                          let checkedOffset ← checkPaginationCore (QueryValid profile catalog params) definitions.visible checkSubquery fuel profile params offset
                          let checkedLocking ← checkLocking source.scope select.distinct locking
                          .ok ⟨⟨items.output,
                            (definitions.uses ++ if offsetFirst then items.uses ++ source.uses ++ predicate.val ++ orders.val ++ checkedOffset.val ++ checkedLimit.val
                             else items.uses ++ source.uses ++ predicate.val ++ orders.val ++ checkedLimit.val ++ checkedOffset.val), by
                            rw [queryEq, bodyEq, noRecursive]
                            exact .basic namesValid definitions.valid source.valid items.valid items.inputValid nonempty distinctComparable distinctCollations predicate.property
                              orders.property orderCollations.property checkedLimit.property checkedOffset.property checkedLocking.valid
                              noGrouping noHaving noDistinctOn⟩,
                            resolveLeafInputs profile select.distinct orderBy items.inputs, by
                              dsimp only
                              rw [queryEq, bodyEq, noRecursive]
                              exact .basic namesValid definitions.valid source.valid items.valid items.inputValid
                                nonempty distinctComparable distinctCollations predicate.property orders.property orderCollations.property checkedLimit.property
                                checkedOffset.property checkedLocking.valid noGrouping noHaving noDistinctOn⟩
                        else .error (invalid "collation_conflict" "DISTINCT requires determinate output collations")
                      else .error (operatorFailure (items.output.map (fun column => some column.type)) false
                        "distinct_type" "DISTINCT output type has no PostgreSQL equality operator")
                    else .error (invalid "empty_projection" "SELECT must produce at least one output column")
                  else .error (unsupported "distinct_on" "DISTINCT ON requires a separate dialect extension")
                else .error (unsupported "having" "Independent HAVING and grouped-query rules are not implemented yet")
              else .error (unsupported "group_by" "Independent grouping rules are not implemented yet")
          else .error (invalid "cte_names" "WITH names must be nonempty and unique within the local definition list")
        else if nonemptyDefinitions : ctes ≠ [] then
          if namesValid : CTENamesValid ctes then
            let definitions ← checkRecursiveCTEs fuel profile catalog params (recursiveOuterEnv env ctes) ctes
            let checkedBody ← checkQueryCore fuel profile catalog params definitions.visible (withoutWith query)
            have recursiveFlag : query.recursive = true := by
              rw [queryEq]
              cases recursive <;> simp_all
            .ok ⟨⟨checkedBody.output, definitions.uses ++ checkedBody.uses, by
                apply QueryValid.recursiveWith
                · simpa only [queryEq] using nonemptyDefinitions
                · simpa only [queryEq] using namesValid
                · exact recursiveFlag
                · simpa only [queryEq] using definitions.valid
                · exact checkedBody.valid⟩,
              checkedBody.inputs, by
                apply SetOperandValid.recursiveWith
                · simpa only [queryEq] using nonemptyDefinitions
                · simpa only [queryEq] using namesValid
                · exact recursiveFlag
                · simpa only [queryEq] using definitions.valid
                · exact checkedBody.operandValid⟩
          else .error (invalid "cte_names" "WITH names must be nonempty and unique")
        else .error (invalid "recursive_empty" "WITH RECURSIVE requires a definition")

  private def checkCTEs (fuel : Nat) (profile : Profile) (catalog : Catalog)
      (params : ParameterEnv) (env : CTEEnv) (ctes : List Advanced.CTE) :
      Except Failure (CTEsCertificate profile catalog params env ctes) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => match ctes with
      | [] => .ok ⟨env, [], .nil⟩
      | head :: remaining => do
        let child ← match checkQueryCore fuel profile catalog params env head.query with
          | .ok child => .ok child
          | .error (.invalid diagnostic) =>
              if diagnostic.code == "locking_nullable" then
                .error (unsupported "cte_planning_lock"
                  "Nullable-side row locking is a planning restriction; an unused WITH definition may not be planned")
              else .error (.invalid diagnostic)
          | .error failure => .error failure
        if aliases : ColumnAliasesValid head.columns child.output then
          let tail ← checkCTEs fuel profile catalog params
            (⟨head.name, renameOutput head.columns child.output⟩ :: env) remaining
          .ok ⟨tail.visible, child.uses ++ tail.uses, .cons child.valid aliases tail.valid⟩
        else .error (invalid "cte_column_aliases"
          "WITH column aliases must be nonempty and cannot exceed the certified output width")

  private def checkRecursiveCTE (fuel : Nat) (profile : Profile) (catalog : Catalog)
      (params : ParameterEnv) (env : CTEEnv) (head : Advanced.CTE) :
      Except Failure (RecursiveCTECertificate profile catalog params env head) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => do
      match headEq : head with
      | ⟨name, query, aliases⟩ =>
        match queryEq : query with
        | ⟨body, ctes, recursive, orderBy, limit, offset, locking, offsetFirst⟩ =>
          if noRecursive : recursive = false then
            if noOrder : orderBy = [] then
              if noLimit : limit = none then
                if noOffset : offset = none then
                  if noLocks : locking = [] then
                    match bodyEq : body with
                    | .values _ => .error (invalid "recursive_shape" "A recursive definition must have root UNION or UNION ALL")
                    | .select _ => .error (invalid "recursive_shape" "A recursive definition must have root UNION or UNION ALL")
                    | .set op all left right =>
                      if unionOp : op = .union then
                        if names : CTENamesValid ctes then
                          if notShadowed : ∀ cte ∈ ctes, cte.name ≠ name then
                            if prefixFree : (recursiveCTEReferences name false false ctes).count = 0 then
                              if anchorFree : (recursiveReferences name false false left).count = 0 then
                                if stepReference : recursiveReferences name false true right = ⟨1, true⟩ then
                                  if leftUnlocked : left.locking = [] then
                                    if rightUnlocked : right.locking = [] then
                                      let definitions ← checkCTEs fuel profile catalog params env ctes
                                      let anchor ← checkQueryCore fuel profile catalog params definitions.visible left
                                      if columnAliases : ColumnAliasesValid aliases anchor.output then
                                        let binding : CTEBinding := ⟨name, recursiveOutput (renameOutput aliases anchor.output)⟩
                                        let step ← checkQueryCore fuel profile catalog params (binding :: definitions.visible) right
                                        let merged ← checkSetColumns fuel .union all anchor.inputs step.inputs
                                        if sameTypes : merged.val.map (fun column => column.type.base) = anchor.output.map (fun column => column.type.base) then
                                          if collation : merged.val.map OutputColumn.collation = anchor.output.map OutputColumn.collation then
                                            .ok ⟨binding.output, definitions.uses ++ anchor.uses ++ step.uses, by
                                              rw [headEq, queryEq, bodyEq, unionOp, noRecursive, noOrder, noLimit, noOffset, noLocks]
                                              exact .union names notShadowed prefixFree definitions.valid anchorFree stepReference
                                                anchor.valid anchor.operandValid columnAliases step.operandValid leftUnlocked rightUnlocked
                                                merged.property sameTypes collation⟩
                                          else .error (invalid "recursive_collation" "Recursive result collation must equal the complete anchor collation in every position")
                                        else .error (invalid "recursive_type" "Recursive result type and typmod must equal the complete anchor type in every position")
                                      else .error (invalid "cte_column_aliases" "WITH aliases cannot exceed the anchor output width")
                                    else .error (invalid "locking_set_operand" "A direct recursive set operand cannot have row-locking clauses")
                                  else .error (invalid "locking_set_operand" "A direct recursive set operand cannot have row-locking clauses")
                                else .error (invalid "recursive_reference" "The recursive arm requires exactly one self reference in a permitted position")
                              else .error (invalid "recursive_reference" "The anchor cannot contain a self reference")
                            else .error (invalid "recursive_reference" "WITH definitions attached to the recursive UNION cannot reference its output")
                          else .error (invalid "recursive_reference" "A body-local WITH definition cannot shadow an active recursive binding")
                        else .error (invalid "cte_names" "WITH names must be nonempty and unique")
                      else .error (invalid "recursive_shape" "A recursive definition must have root UNION or UNION ALL")
                  else .error (invalid "recursive_modifiers" "A recursive UNION cannot have row-locking clauses")
                else .error (invalid "recursive_modifiers" "A recursive UNION cannot have OFFSET")
              else .error (invalid "recursive_modifiers" "A recursive UNION cannot have LIMIT")
            else .error (invalid "recursive_modifiers" "A recursive UNION cannot have ORDER BY")
          else .error (unsupported "recursive_body_with" "An actual recursive UNION with its own RECURSIVE WITH prefix needs a separate scope rule")

  private def checkRecursiveCTEs (fuel : Nat) (profile : Profile) (catalog : Catalog)
      (params : ParameterEnv) (env : CTEEnv) (ctes : List Advanced.CTE) :
      Except Failure (RecursiveCTEsCertificate profile catalog params env ctes) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => match ctes with
      | [] => .ok ⟨env, [], .nil⟩
      | head :: remaining => do
        if forwardFree : NoForwardCTEReferences remaining head.query then
          if noSelf : (recursiveReferences head.name false true head.query).count = 0 then
            let child ← match checkQueryCore fuel profile catalog params env head.query with
              | .error (.invalid diagnostic) =>
                if diagnostic.code == "locking_nullable" then
                  .error (unsupported "cte_planning_lock" "Unused WITH definitions may avoid nullable-side locking planning checks")
                else .error (.invalid diagnostic)
              | result => result
            if aliases : ColumnAliasesValid head.columns child.output then
              let tail ← checkRecursiveCTEs fuel profile catalog params
                (⟨head.name, renameOutput head.columns child.output⟩ :: env) remaining
              .ok ⟨tail.visible, child.uses ++ tail.uses, .ordinary forwardFree noSelf child.valid aliases tail.valid⟩
            else .error (invalid "cte_column_aliases" "WITH column aliases cannot exceed the certified output width")
          else
            let child ← match checkRecursiveCTE fuel profile catalog params env head with
              | .error (.invalid diagnostic) =>
                if diagnostic.code == "locking_nullable" then
                  .error (unsupported "cte_planning_lock" "Unused recursive WITH definitions may avoid nullable-side locking planning checks")
                else .error (.invalid diagnostic)
              | result => result
            let tail ← checkRecursiveCTEs fuel profile catalog params (⟨head.name, child.output⟩ :: env) remaining
            .ok ⟨tail.visible, child.uses ++ tail.uses, .recursive forwardFree child.valid tail.valid⟩
        else .error (unsupported "recursive_dependency" "Forward and mutually dependent WITH definitions require a dependency-order extension")

end

/-- Validate exact metadata and complete statement parameter notation once.
Nested query checks collect occurrences without restarting anonymous indices. -/
def checkQuery (profile : Profile) (catalog : Catalog) (params : ParameterEnv) (query : Advanced.Query)
    (fuel : Nat := 1024) : Except Failure (Certificate profile catalog params query) := do
  if fuel = 0 then throw exhausted
  if environment : WellFormedEnvironment catalog params then
    if catalog.any (fun table => table.schema == some "pg_temp") then
      throw (unsupported "namespace_alias" "Catalog metadata cannot treat pg_temp as a distinct physical schema")
    if supported : SupportedEnvironment catalog params then
      if collations : CollationEnvironment profile catalog then
        let checked ← checkQueryCore fuel profile catalog params [] query
        if parameterOrder : ParameterOrder checked.uses then
          .ok ⟨checked.output, .certified environment collations supported checked.valid parameterOrder⟩
        else .error (invalid "parameter_notation" "Use positive numbered parameters or consecutive anonymous parameters, without mixing styles")
      else .error (invalid "invalid_collation_environment" "Collation metadata must identify eligible objects and unique collatable columns")
    else .error (unsupported "environment_type" "A catalog or parameter type is outside the concrete PostgreSQL scalar inventory")
  else if WellFormedEnvironment (precisionDiagnosticCatalog catalog)
      (precisionDiagnosticParameters params) then
    .error intervalPrecisionFailure
  else .error (invalid "invalid_environment" "Catalog or parameter metadata violates uniqueness, naming, type-declaration or key rules")

/-- Soundness is against Spec.SelectValid, not an abbreviation for checker
success. The theorem needs no operational fuel premise beyond success. -/
theorem checkQuery_sound
    (profile : Profile) (catalog : Catalog) (params : ParameterEnv) (query : Advanced.Query)
    (fuel : Nat) (certificate : Certificate profile catalog params query)
    (_success : checkQuery profile catalog params query fuel = .ok certificate) :
    SelectValid profile catalog params query certificate.output := certificate.valid

end SQLean.SelectContract
