import SQLean.AdvancedCatalog
import SQLean.AdvancedQueryValidation

namespace SQLean.Advanced

private def invalid (message : String) : Except ValidationError α := .error ⟨message⟩

private def defaultExpression : Nat → Expr → Bool
  | 0, _ => false
  | _ + 1, .literal _ | _ + 1, .null | _ + 1, .decimal _ => true
  | n + 1, .quantifiedComparison _ _ left right | n + 1, .binary _ left right | n + 1, .pattern left right _ | n + 1, .nullIf left right =>
      defaultExpression n left && defaultExpression n right
  | n + 1, .unary _ arg | n + 1, .cast arg _ | n + 1, .isNull arg _ => defaultExpression n arg
  | n + 1, .array args | n + 1, .call _ args | n + 1, .coalesce args | n + 1, .greatest args | n + 1, .least args =>
      args.all (defaultExpression n)
  | n + 1, .caseExpr operand branches otherwise => operand.all (defaultExpression n) &&
      branches.all (fun branch => defaultExpression n branch.1 && defaultExpression n branch.2) &&
      otherwise.all (defaultExpression n)
  | n + 1, .inList arg values => defaultExpression n arg && values.all (defaultExpression n)
  | n + 1, .between arg lower upper _ =>
      defaultExpression n arg && defaultExpression n lower && defaultExpression n upper
  | _ + 1, _ => false

def checkColumnDefault (schema : Schema) (column : Column) : Except ValidationError Unit := do
  requireCheck (validDataType column.type) s!"invalid type for column '{column.name}'"
  if let some value := column.defaultValue then
    requireCheck (defaultExpression 1024 value)
      "defaults must be scalar expressions without columns, subqueries or parameters"
    let type ← inferExpr 1024 schema [] [] false value
    requireCheck (assignmentCompatible type column.sqlType)
      s!"default does not match column '{column.name}'"

def checkCatalogDefaults (catalog : Catalog) : Except ValidationError Unit := do
  checkCatalog catalog
  for table in catalog do
    for column in table.columns do
      checkColumnDefault catalog.toSchema
        (if table.primaryKey.contains column.name then { column with nullable := some false } else column)

def createTableCatalog (catalog : Catalog) (query : CreateTable) : Except ValidationError Catalog := do
  requireCheck (!query.name.isEmpty && !query.columns.isEmpty) "CREATE TABLE needs a name and columns"
  let columnPrimaries := query.columns.filter (·.primaryKey)
  let tablePrimaries := query.constraints.filterMap fun constraint => match constraint with
    | .primaryKey names => some names | _ => none
  requireCheck (columnPrimaries.length + tablePrimaries.length ≤ 1) "multiple primary keys"
  let primary := match tablePrimaries with
    | names :: _ => names
    | [] => columnPrimaries.map Column.name
  let table : CatalogTable := {
    name := query.name
    columns := query.columns.map fun col =>
      if primary.contains col.name then { col with nullable := some false } else col
    primaryKey := primary
    uniqueKeys := query.constraints.filterMap fun constraint => match constraint with
      | .unique names => some names | _ => none }
  checkCatalogDefaults [table]
  if (catalog.findTable query.name).isSome then
    if query.ifNotExists then pure catalog else invalid s!"table '{query.name}' already exists"
  else pure (catalog ++ [table])

private def findColumn (table : CatalogTable) (name : Name) : Except ValidationError Column :=
  match table.columns.find? (·.name == name) with
  | some column => pure column
  | none => invalid s!"unknown column '{name}'"

private def replaceColumn (table : CatalogTable) (name : Name) (column : Column) : CatalogTable :=
  { table with columns := table.columns.map fun old => if old.name == name then column else old }

private def alterOne (catalog : Catalog) (table : CatalogTable) (action : AlterAction) :
    Except ValidationError CatalogTable := do
  match action with
  | .addColumn column ifNotExists =>
      if table.columns.any (·.name == column.name) then
        if ifNotExists then return table else return ← invalid s!"duplicate column '{column.name}'"
      requireCheck (!column.name.isEmpty && !(table.columns.any (·.name == column.name)))
        s!"duplicate or empty column '{column.name}'"
      requireCheck (!column.primaryKey || (table.primaryKey.isEmpty && !(table.columns.any (·.primaryKey))))
        "multiple primary keys"
      checkColumnDefault catalog.toSchema column
      pure { table with
        columns := table.columns ++ [column]
        primaryKey := if column.primaryKey then [column.name] else table.primaryKey }
  | .dropColumn name ifExists _cascade =>
      if !(table.columns.any (·.name == name)) then
        if ifExists then pure table else invalid s!"unknown column '{name}'"
      else
        let columns := table.columns.filter (·.name != name)
        requireCheck (!columns.isEmpty) "zero-column tables are outside the supported catalog"
        pure { table with
          columns := columns
          uniqueKeys := table.uniqueKeys.filter (fun key => !key.contains name)
          primaryKey := if table.primaryKey.contains name then [] else table.primaryKey
          namedKeys := table.namedKeys.filter (fun key => !key.2.contains name) }
  | .renameColumn name newName =>
      let column ← findColumn table name
      requireCheck (!newName.isEmpty && !(table.columns.any (·.name == newName)))
        s!"duplicate or empty column '{newName}'"
      let rename := fun key : List Name => key.map fun old => if old == name then newName else old
      pure { (replaceColumn table name { column with name := newName }) with
        uniqueKeys := table.uniqueKeys.map rename
        primaryKey := rename table.primaryKey
        namedKeys := table.namedKeys.map fun (key, names) => (key, rename names) }
  | .renameTable newName =>
      requireCheck (!newName.isEmpty && !(catalog.any (·.name == newName)))
        s!"duplicate or empty table '{newName}'"
      pure { table with name := newName }
  | .setType name type =>
      let column ← findColumn table name
      requireCheck (validDataType type) "invalid ALTER COLUMN type"
      requireCheck (column.type.sqlType == type.sqlType ||
        (column.type.sqlType.numeric && type.sqlType.numeric))
        "ALTER COLUMN TYPE requires a compatible type; USING conversions are unsupported"
      let changed := { column with type }
      checkColumnDefault catalog.toSchema changed
      pure (replaceColumn table name changed)
  | .setNotNull name =>
      let column ← findColumn table name
      pure (replaceColumn table name { column with nullable := some false })
  | .dropNotNull name =>
      let column ← findColumn table name
      requireCheck (!column.primaryKey && !table.primaryKey.contains name) "a primary key must remain NOT NULL"
      pure (replaceColumn table name { column with nullable := some true })
  | .setDefault name value =>
      let column ← findColumn table name
      let changed := { column with defaultValue := some value }
      checkColumnDefault catalog.toSchema changed
      pure (replaceColumn table name changed)
  | .dropDefault name =>
      let column ← findColumn table name
      pure (replaceColumn table name { column with defaultValue := none })

def alterTableCatalog (catalog : Catalog) (name : Name) (actions : List AlterAction) :
    Except ValidationError Catalog := do
  let some table := catalog.findTable name | invalid s!"unknown table '{name}'"
  requireCheck (!actions.isEmpty) "ALTER TABLE needs an action"
  let targets := actions.map fun action => match action with
    | .addColumn column _ => column.name
    | .dropColumn column _ _ | .renameColumn column _ | .setType column _
    | .setNotNull column | .dropNotNull column | .setDefault column _ | .dropDefault column => column
    | .renameTable _ => ""
  requireCheck (targets.eraseDups.length == targets.length)
    "multiple ALTER actions on one column require PostgreSQL phase ordering and are unsupported"
  requireCheck (actions.length == 1 || !(actions.any fun action => match action with
    | .renameTable _ | .renameColumn _ _ => true | _ => false))
    "RENAME must be a standalone ALTER TABLE action"
  let changed ← actions.foldlM (alterOne catalog) table
  let result := catalog.map fun old => if old.name == name then changed else old
  checkCatalogDefaults result
  pure result

def dropTableCatalog (catalog : Catalog) (name : Name) (ifExists : Bool) :
    Except ValidationError Catalog := do
  requireCheck (!name.isEmpty) "empty table name"
  requireCheck (ifExists || (catalog.findTable name).isSome) s!"unknown table '{name}'"
  pure (catalog.filter (·.name != name))

end SQLean.Advanced
