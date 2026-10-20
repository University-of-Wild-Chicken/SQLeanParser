import SQLean.AdvancedDDL

/-! Statement checks compose query typing, target-column checks, conflict-key
metadata, and catalog transitions. Certificates attest these executable static
checks; they do not prove row constraints, successful casts, or DDL execution. -/
namespace SQLean.Advanced

structure StatementResult where
  outputTypes : List SqlType
  catalog : Catalog
  deriving Repr, BEq, Inhabited

private def invalid (message : String) : Except ValidationError α := .error ⟨message⟩

private def findTarget (catalog : Catalog) (name : Name) : Except ValidationError CatalogTable :=
  match catalog.findTable name with
  | some table => pure table
  | none => invalid s!"unknown table '{name}'"

private def targetColumn (table : TableDef) (name : Name) : Except ValidationError ColumnDef :=
  match table.findColumn name with
  | some column => pure column
  | none => invalid s!"unknown target column '{name}'"

private def checkPredicate (schema : Schema) (params : ParameterEnv) (scope : Scope)
    (expr : Option Expr) : Except ValidationError Unit := do
  if let some expr := expr then
    let type ← inferExpr 1024 schema params [scope] false expr
    requireCheck (type.isNone || (finalizeType type).base == .bool) "predicate must be boolean"

private def checkAssignments (schema : Schema) (params : ParameterEnv) (table : TableDef)
    (scope : Scope) (assignments : List Assignment) : Except ValidationError Unit := do
  let names := assignments.map Assignment.column
  requireCheck (!assignments.isEmpty && names.eraseDups.length == names.length)
    "assignments must be nonempty with distinct target columns"
  for assignment in assignments do
    let target ← targetColumn table assignment.column
    let source ← inferExpr 1024 schema params [scope] false assignment.value
    requireCheck (assignmentCompatible source target.type) s!"assignment type mismatch for '{target.name}'"

private def returningTypes (schema : Schema) (params : ParameterEnv) (table : TableDef)
    (alias : Option Name) (items : List SelectItem) : Except ValidationError (List SqlType) := do
  let scope := Scope.ofTable table alias
  let mut types := []
  for item in items do
    match item with
    | .all qualifier schema =>
        requireCheck schema.isNone "schema-qualified RETURNING requires an exact namespace model"
        requireCheck (qualifier.isNone || qualifier == some (alias.getD table.name))
          "unknown RETURNING qualifier"
        types := types ++ table.columns.map ColumnDef.type
    | .expression expr alias =>
        requireCheck (alias != some "") "empty RETURNING alias"
        types := types ++ [finalizeType (← inferExpr 1024 schema params [scope] false expr)]
  pure types

private def checkConflict (schema : Schema) (params : ParameterEnv) (table : CatalogTable)
    (alias : Option Name) (conflict : OnConflict) : Except ValidationError Unit := do
  if let some target := conflict.target then
    let names ← match target with
      | .columns names => pure names
      | .constraint name =>
        match table.namedKeys.find? (·.1 == name) with
        | some key => pure key.2
        | none => invalid s!"unknown conflict constraint '{name}'"
    requireCheck (!names.isEmpty && names.eraseDups.length == names.length)
      "conflict target must contain distinct columns"
    requireCheck (table.keys.any (fun key => key.length == names.length && names.all key.contains))
      "conflict target is not a declared unique key"
  match conflict.action with
  | .nothing => pure ()
  | .update assignments predicate =>
      requireCheck conflict.target.isSome "ON CONFLICT DO UPDATE requires a conflict target"
      requireCheck (alias.getD table.name != "excluded") "target must not hide EXCLUDED in an upsert"
      let target := table.toTableDef
      let scope := Scope.ofTable target alias
      let excluded := Scope.ofTable target (some "excluded")
      let scope := { scope with
        qualified := scope.qualified ++ excluded.qualified
        output := scope.output ++ excluded.output }
      checkAssignments schema params target scope assignments
      checkPredicate schema params scope predicate

private def checkInsert (catalog : Catalog) (params : ParameterEnv) (query : Insert) :
    Except ValidationError (List SqlType) := do
  let table ← findTarget catalog query.table
  let schema := catalog.toSchema
  let target := table.toTableDef
  requireCheck (query.alias != some "") "empty target alias"
  let names := if query.columns.isEmpty then table.columns.map Column.name else query.columns
  requireCheck (!names.isEmpty && names.eraseDups.length == names.length) "invalid INSERT target columns"
  let targets ← names.mapM (targetColumn target)
  for column in table.columns do
    if !names.contains column.name then
      let actual ← targetColumn target column.name
      requireCheck (actual.type.isNullable || column.defaultValue.isSome)
        s!"omitted required column '{column.name}' has no default"
  match query.source with
  | .values rows =>
      requireCheck (!rows.isEmpty) "INSERT VALUES needs rows"
      for row in rows do
        requireCheck (row.length == targets.length) "INSERT row arity mismatch"
        for (expr, column) in row.zip targets do
          let type ← inferExpr 1024 schema params [] false expr
          requireCheck (assignmentCompatible type column.type)
            s!"INSERT value type mismatch for '{column.name}'"
  | .query source => checkQueryAgainst schema params source (targets.map ColumnDef.type)
  | .defaultValues =>
      requireCheck query.columns.isEmpty "DEFAULT VALUES cannot specify target columns in this subset"
      for column in table.columns do
        let actual ← targetColumn target column.name
        requireCheck (actual.type.isNullable || column.defaultValue.isSome)
          s!"required column '{column.name}' has no default"
  if let some conflict := query.onConflict then checkConflict schema params table query.alias conflict
  returningTypes schema params target query.alias query.returning

private def itemParameters (items : List SelectItem) : List Parameter :=
  items.flatMap fun item => match item with
    | .all .. => [] | .expression expr _ => expressionParameters 1024 expr

private def assignmentsParameters (items : List Assignment) : List Parameter :=
  items.flatMap fun item => expressionParameters 1024 item.value

private def statementParameters : Statement → List Parameter
  | .query query => queryParameters 1024 query
  | .insert query =>
    (match query.source with
     | .values rows => rows.flatten.flatMap (expressionParameters 1024)
     | .query source => queryParameters 1024 source
     | .defaultValues => []) ++
    query.onConflict.toList.flatMap (fun conflict => match conflict.action with
      | .nothing => []
      | .update assignments predicate => assignmentsParameters assignments ++
          predicate.toList.flatMap (expressionParameters 1024)) ++ itemParameters query.returning
  | .update query => assignmentsParameters query.assignments ++
      query.whereClause.toList.flatMap (expressionParameters 1024) ++ itemParameters query.returning
  | .delete query => query.whereClause.toList.flatMap (expressionParameters 1024) ++ itemParameters query.returning
  | _ => []

/-- Execute static checks and compute a catalog transition without executing SQL. -/
def checkStatementDetailed (catalog : Catalog) (params : ParameterEnv) (statement : Statement) :
    Except ValidationError StatementResult := do
  checkCatalogDefaults catalog
  requireCheck (!catalog.schemaAware) "schema-aware catalogs require the independent SELECT contract"
  checkParameterEnv params
  checkParameterUses (statementParameters statement)
  match statement with
  | .query query =>
      let columns ← checkQuery catalog.toSchema params query
      pure ⟨columns.map ColumnDef.type, catalog⟩
  | .insert query => pure ⟨← checkInsert catalog params query, catalog⟩
  | .update query =>
      let table ← findTarget catalog query.table
      requireCheck (query.alias != some "") "empty target alias"
      let target := table.toTableDef
      let scope := Scope.ofTable target query.alias
      checkAssignments catalog.toSchema params target scope query.assignments
      checkPredicate catalog.toSchema params scope query.whereClause
      pure ⟨← returningTypes catalog.toSchema params target query.alias query.returning, catalog⟩
  | .delete query =>
      let table ← findTarget catalog query.table
      requireCheck (query.alias != some "") "empty target alias"
      let target := table.toTableDef
      checkPredicate catalog.toSchema params (Scope.ofTable target query.alias) query.whereClause
      pure ⟨← returningTypes catalog.toSchema params target query.alias query.returning, catalog⟩
  | .createTable query => pure ⟨[], ← createTableCatalog catalog query⟩
  | .alterTable name actions => pure ⟨[], ← alterTableCatalog catalog name actions⟩
  | .dropTable name ifExists _cascade => pure ⟨[], ← dropTableCatalog catalog name ifExists⟩

def checkStatement (catalog : Catalog) (params : ParameterEnv) (statement : Statement) :
    Except ValidationError (List SqlType) :=
  (checkStatementDetailed catalog params statement).map StatementResult.outputTypes

/-- The advanced certificate's explicit contract is acceptance by the bounded
static specification above, not the older independent declarative relation. -/
abbrev StatementValid (catalog : Catalog) (params : ParameterEnv) (statement : Statement)
    (types : List SqlType) : Prop := checkStatement catalog params statement = .ok types

structure CertifiedStatement (catalog : Catalog) (params : ParameterEnv) (statement : Statement) where
  outputTypes : List SqlType
  valid : StatementValid catalog params statement outputTypes

def certifyStatement (catalog : Catalog) (params : ParameterEnv) (statement : Statement) :
    Except ValidationError (CertifiedStatement catalog params statement) :=
  match h : checkStatement catalog params statement with
  | .error error => .error error
  | .ok types => .ok ⟨types, h⟩

theorem certifyStatement_complete (valid : StatementValid catalog params statement types) :
    certifyStatement catalog params statement = .ok ⟨types, valid⟩ := by
  unfold certifyStatement
  split
  · rename_i error h
    have impossible := h.symm.trans valid
    contradiction
  · rename_i inferred h
    have equal : inferred = types := Except.ok.inj (h.symm.trans valid)
    cases equal
    rfl

theorem checkStatement_iff : checkStatement catalog params statement = .ok types ↔
    StatementValid catalog params statement types := Iff.rfl

/-- Apply a sequence of checked schema transitions in memory. Each next statement
sees the preceding DDL catalog; this is not a database transaction executor. -/
def checkStatements (catalog : Catalog) (params : ParameterEnv) (statements : List Statement) :
    Except ValidationError (List StatementResult) := do
  let mut catalog := catalog
  let mut results := []
  for statement in statements do
    let result ← checkStatementDetailed catalog params statement
    catalog := result.catalog
    results := results ++ [result]
  pure results

end SQLean.Advanced
