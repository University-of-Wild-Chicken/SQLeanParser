import SQLean.SelectContract.Spec

/-! Proof-producing bounded implementation of the independent SELECT rules.
Every successful branch constructs a Spec derivation. Exhausted operational
fuel is Inconclusive; missing coverage is Unsupported, never validity evidence.
-/
namespace SQLean.SelectContract
open Advanced

private def invalid (code message : String) : Failure := .invalid ⟨code, message⟩
private def unsupported (code message : String) : Failure := .unsupported ⟨code, message⟩
private def exhausted : Failure := .inconclusive ⟨"resource_limit", "SELECT contract checking exhausted its recursion budget"⟩

structure ExprCertificate (params : ParameterEnv) (scope : Scope) (expr : Advanced.Expr) where
  type : ExprType
  uses : List Parameter
  valid : ExprValid params scope expr type uses

structure ExprListCertificate (params : ParameterEnv) (scope : Scope) (exprs : List Advanced.Expr) where
  types : List ExprType
  uses : List Parameter
  valid : ExprListValid params scope exprs types uses

mutual
  def checkExpr (fuel : Nat) (params : ParameterEnv) (scope : Scope) (expr : Advanced.Expr) :
      Except Failure (ExprCertificate params scope expr) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => match expr with
      | .literal (.int n) =>
          if range : n ≤ 2147483647 then
            .ok ⟨some ⟨.int32, false⟩, [], .int range⟩
          else .error (unsupported "integer_literal_range" "Integer literal requires a concrete type beyond INT32")
      | .literal (.text _) => .ok ⟨some ⟨.text, false⟩, [], .text⟩
      | .literal (.bool _) => .ok ⟨some ⟨.bool, false⟩, [], .bool⟩
      | .null => .ok ⟨none, [], .null⟩
      | .decimal _ => .error (unsupported "decimal_type" "Decimal and floating-point types have no rule in this milestone")
      | .parameter parameter => do
          match found : params.filter (fun binding => binding.index == parameterIndex parameter) with
          | [binding] =>
              have member : binding ∈ params.filter (fun b => b.index == parameterIndex parameter) := by
                rw [found]; simp
              have facts := List.mem_filter.mp member
              match supported : concreteType binding.type with
              | none => .error (unsupported "parameter_type" "Parameter type is outside the concrete INT32/TEXT/BOOL profile")
              | some base => .ok ⟨some ⟨base, binding.nullable⟩, [parameter],
                  .parameter facts.1 (by simpa using facts.2) supported⟩
          | _ => .error (invalid "parameter_binding" "Parameter must resolve to exactly one declared binding")
      | .column qualifier name =>
          match found : scope.filter (fun (b : Binding) => b.column.name == name &&
              match qualifier with | none => true | some q => b.qualifier == q) with
          | [binding] => .ok ⟨some binding.column.type, [], .column found⟩
          | _ => .error (invalid "column_binding" s!"Column '{name}' must resolve to exactly one visible binding")
      | .binary op a b => do
          let left ← checkExpr fuel params scope a
          let right ← checkExpr fuel params scope b
          match signature : binarySignature op left.type right.type with
          | none => .error (invalid "operator_signature" "Binary operands have no applicable profile signature")
          | some type => .ok ⟨type, left.uses ++ right.uses, .binary left.valid right.valid signature⟩
      | .unary op a => do
          let arg ← checkExpr fuel params scope a
          match signature : unarySignature op arg.type with
          | none => .error (invalid "operator_signature" "Unary operand has no applicable profile signature")
          | some type => .ok ⟨type, arg.uses, .unary arg.valid signature⟩
      | .isNull a negated => do
          let arg ← checkExpr fuel params scope a
          .ok ⟨some ⟨.bool, false⟩, arg.uses, .isNull (negated := negated) arg.valid⟩
      | .pattern a b insensitive =>
          if h : insensitive = false then do
            let arg ← checkExpr fuel params scope a
            let pattern ← checkExpr fuel params scope b
            match signature : patternSignature arg.type pattern.type with
            | none => .error (invalid "pattern_signature" "LIKE requires TEXT operands")
            | some type => .ok ⟨type, arg.uses ++ pattern.uses, h ▸ .pattern arg.valid pattern.valid signature⟩
          else .error (unsupported "ilike" "ILIKE requires a separate dialect extension")
      | .cast a target => do
          if declaration : DataTypeWellFormed target then
            match supported : concreteType target with
            | none => .error (unsupported "cast_type" "Cast target is outside the concrete INT32/TEXT/BOOL profile")
            | some base =>
                let arg ← checkExpr fuel params scope a
                .ok ⟨castSignature arg.type base, arg.uses, .cast arg.valid supported⟩
          else .error (invalid "type_declaration" "Cast target has invalid type modifiers")
      | .inList a values => do
          if nonempty : values ≠ [] then
            let arg ← checkExpr fuel params scope a
            let items ← checkExprList fuel params scope values
            match signature : comparisonListSignature (arg.type :: items.types) with
            | none => .error (invalid "comparison_signature" "IN operands have no common concrete comparison type")
            | some type => .ok ⟨type, arg.uses ++ items.uses, .inList arg.valid items.valid nonempty signature⟩
          else .error (invalid "empty_in_list" "IN requires at least one value")
      | .between a b c negated => do
          let arg ← checkExpr fuel params scope a
          let lower ← checkExpr fuel params scope b
          let upper ← checkExpr fuel params scope c
          match signature : comparisonListSignature [arg.type, lower.type, upper.type] with
          | none => .error (invalid "comparison_signature" "BETWEEN operands have no common concrete comparison type")
          | some type => .ok ⟨type, arg.uses ++ lower.uses ++ upper.uses,
              .between (negated := negated) arg.valid lower.valid upper.valid signature⟩
      | .countAll | .aggregate .. | .filteredAggregate .. =>
          .error (unsupported "aggregate" "Independent aggregate and grouped-query rules are not implemented yet")
      | .inQuery .. | .exists .. | .scalarQuery .. =>
          .error (unsupported "subquery" "Independent subquery and correlation rules are not implemented yet")

  def checkExprList (fuel : Nat) (params : ParameterEnv) (scope : Scope) (exprs : List Advanced.Expr) :
      Except Failure (ExprListCertificate params scope exprs) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => match exprs with
      | [] => .ok ⟨[], [], .nil⟩
      | expr :: exprs => do
          let head ← checkExpr fuel params scope expr
          let tail ← checkExprList fuel params scope exprs
          .ok ⟨head.type :: tail.types, head.uses ++ tail.uses, .cons head.valid tail.valid⟩
end

structure SourceCertificate (catalog : Catalog) (source : Option Advanced.From) where
  scope : Scope
  valid : SourceValid catalog source scope

private def tableColumns (table : CatalogTable) (qualifier : Name) (columns : List Advanced.Column) :
    Except Failure {scope : Scope // TableColumns table qualifier columns scope} :=
  match columns with
  | [] => .ok ⟨[], .nil⟩
  | col :: cols => do
      match supported : concreteType col.type with
      | none => .error (unsupported "column_type" "Column type is outside the concrete INT32/TEXT/BOOL profile")
      | some base =>
          let rest ← tableColumns table qualifier cols
          .ok ⟨⟨qualifier, ⟨col.name, ⟨base, columnNullable table col⟩⟩⟩ :: rest.val,
            .cons supported rest.property⟩

private def checkSource (catalog : Catalog) (source : Option Advanced.From) :
    Except Failure (SourceCertificate catalog source) :=
  match source with
  | none => .ok ⟨[], .empty⟩
  | some (.table name alias columns) => do
      if noRenaming : columns = [] then
        if goodAlias : ∀ name ∈ alias, name ≠ "" then
          match found : catalog.filter (fun table => table.name == name) with
          | [table] =>
              have member : table ∈ catalog.filter (fun t => t.name == name) := by rw [found]; simp
              have facts := List.mem_filter.mp member
              let bindings ← tableColumns table (alias.getD name) table.columns
              .ok ⟨bindings.val, noRenaming ▸ .table facts.1 (by simpa using facts.2) goodAlias bindings.property⟩
          | _ => .error (invalid "relation_binding" s!"Relation '{name}' must resolve to exactly one catalog entry")
        else .error (invalid "empty_alias" "A relation alias must be nonempty")
      else .error (unsupported "source_column_renaming" "Independent source column-renaming rules are not implemented yet")
  | some (.derived ..) => .error (unsupported "derived_source" "Independent derived-source rules are not implemented yet")
  | some (.join ..) => .error (unsupported "join" "Independent join rules are not implemented yet")

structure ItemsCertificate (params : ParameterEnv) (scope : Scope) (items : List Advanced.SelectItem) where
  output : List OutputColumn
  uses : List Parameter
  valid : ItemsValid params scope items output uses

private def checkItems (fuel : Nat) (params : ParameterEnv) (scope : Scope) (items : List Advanced.SelectItem) :
    Except Failure (ItemsCertificate params scope items) :=
  match fuel with
  | 0 => .error exhausted
  | fuel + 1 => match items with
    | [] => .ok ⟨[], [], .nil⟩
    | .expression expr alias :: items => do
        if goodAlias : ∀ name ∈ alias, name ≠ "" then
          let item ← checkExpr fuel params scope expr
          let tail ← checkItems fuel params scope items
          .ok ⟨⟨outputName expr alias, projectedType item.type⟩ :: tail.output, item.uses ++ tail.uses,
            .expression item.valid goodAlias tail.valid⟩
        else .error (invalid "empty_alias" "A projection alias must be nonempty")
    | .all qualifier :: items => do
        let selected := scope.filter (fun b => match qualifier with | none => true | some q => b.qualifier == q)
        if nonempty : selected ≠ [] then
          let tail ← checkItems fuel params scope items
          .ok ⟨selected.map Binding.column ++ tail.output, tail.uses, .all rfl nonempty tail.valid⟩
        else .error (invalid "wildcard_binding" "Wildcard must identify a nonempty visible input scope")

private def checkPredicate (fuel : Nat) (params : ParameterEnv) (scope : Scope) (expr : Option Advanced.Expr) :
    Except Failure {uses : List Parameter // PredicateValid params scope expr uses} :=
  match expr with
  | none => .ok ⟨[], .absent⟩
  | some expr => do
      let arg ← checkExpr fuel params scope expr
      if boolean : acceptsBase .bool arg.type = true then
        .ok ⟨arg.uses, .present arg.valid boolean⟩
      else .error (invalid "predicate_type" "WHERE requires a Boolean expression")

private def checkSort (fuel : Nat) (params : ParameterEnv) (scope : Scope) (output : List OutputColumn)
    (distinct : Bool) (expr : Advanced.Expr) :
    Except Failure {uses : List Parameter // SortValid params scope output distinct expr uses} :=
  match expr with
  | .literal (.int n) =>
      if positive : 0 < n then
        if inRange : n ≤ output.length then .ok ⟨[], .ordinal positive inRange⟩
        else .error (invalid "order_position" "ORDER BY position exceeds expanded output width")
      else .error (invalid "order_position" "ORDER BY positions are one-based")
  | .column none name =>
      match found : output.filter (·.name == name) with
      | [_column] => .ok ⟨[], .outputName found⟩
      | [] => do
          if ordinary : distinct = false then
            let typed ← checkExpr fuel params scope (.column none name)
            .ok ⟨typed.uses, .inputName found ordinary typed.valid⟩
          else .error (unsupported "distinct_order_expression" "DISTINCT ordering by an input name requires projected-expression identity rules; use an output label or position")
      | _ => .error (invalid "ambiguous_output" s!"ORDER BY label '{name}' is ambiguous")
  | expr => do
      if ordinary : distinct = false then
        if category : SortExpression expr then
          let typed ← checkExpr fuel params scope expr
          .ok ⟨typed.uses, .expression ordinary typed.valid category⟩
        else .error (invalid "order_category" "Unclassified ORDER BY syntax")
      else .error (unsupported "distinct_order_expression" "This milestone supports DISTINCT ordering by output name or position")

private def checkOrders (fuel : Nat) (params : ParameterEnv) (scope : Scope) (output : List OutputColumn)
    (distinct : Bool) (items : List Advanced.OrderBy) :
    Except Failure {uses : List Parameter // OrdersValid params scope output distinct items uses} :=
  match fuel with
  | 0 => .error exhausted
  | fuel + 1 => match items with
    | [] => .ok ⟨[], .nil⟩
    | item :: items => do
        let head ← checkSort fuel params scope output distinct item.expr
        let tail ← checkOrders fuel params scope output distinct items
        .ok ⟨head.val ++ tail.val, .cons head.property tail.property⟩

/-- The success payload contains an independent declarative derivation indexed by
all exact inputs. No prevalidation by the legacy executable checker is used. -/
def checkQuery (profile : Profile) (catalog : Catalog) (params : ParameterEnv) (query : Advanced.Query)
    (fuel : Nat := 1024) : Except Failure (Certificate profile catalog params query) := do
  if fuel = 0 then .error exhausted else
  if environment : WellFormedEnvironment catalog params then
    if supported : SupportedEnvironment catalog params then
      match queryEq : query with
      | ⟨body, ctes, recursive, orderBy, limit, offset⟩ =>
        if noCTEs : ctes = [] then
          if noRecursive : recursive = false then
            match bodyEq : body with
            | .set .. => .error (unsupported "set_operation" "Independent set-operation rules are not implemented yet")
            | .select select =>
              if noGrouping : select.groupBy = [] then
                if noHaving : select.having = none then
                  if noDistinctOn : select.distinctOn = [] then
                    let source ← checkSource catalog select.source
                    let items ← checkItems fuel params source.scope select.items
                    if nonempty : items.output ≠ [] then
                      let predicate ← checkPredicate fuel params source.scope select.whereClause
                      let orders ← checkOrders fuel params source.scope items.output select.distinct orderBy
                      if parameterOrder : ParameterOrder (items.uses ++ predicate.val ++ orders.val) then
                        .ok ⟨items.output, by
                          rw [queryEq, bodyEq, noCTEs, noRecursive]
                          exact .basic environment supported source.valid items.valid nonempty predicate.property
                            orders.property parameterOrder noGrouping noHaving noDistinctOn⟩
                      else .error (invalid "parameter_notation" "Use positive numbered parameters or consecutive anonymous parameters, without mixing styles")
                    else .error (invalid "empty_projection" "SELECT must produce at least one output column")
                  else .error (unsupported "distinct_on" "DISTINCT ON requires a separate dialect extension")
                else .error (unsupported "having" "Independent HAVING and grouped-query rules are not implemented yet")
              else .error (unsupported "group_by" "Independent grouping rules are not implemented yet")
          else .error (unsupported "recursive_cte" "Independent recursive CTE rules are not implemented yet")
        else .error (unsupported "cte" "Independent CTE rules are not implemented yet")
    else .error (unsupported "environment_type" "Every catalog and parameter type must be exactly INT32, TEXT or BOOL in this milestone")
  else .error (invalid "invalid_environment" "Catalog or parameter metadata violates uniqueness, naming, type-declaration or key rules")

/-- Soundness is against Spec.SelectValid, not an abbreviation for checker
success. The theorem needs no operational fuel premise beyond success. -/
theorem checkQuery_sound
    (profile : Profile) (catalog : Catalog) (params : ParameterEnv) (query : Advanced.Query)
    (fuel : Nat) (certificate : Certificate profile catalog params query)
    (_success : checkQuery profile catalog params query fuel = .ok certificate) :
    SelectValid profile catalog params query certificate.output := certificate.valid

end SQLean.SelectContract
