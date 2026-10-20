import SQLean.RelationalValidation
import SQLean.CatalogSyntax

/-! Catalog metadata for DDL and conflict-target checking. This describes schema
structure, not current rows, indexes' physical state, or concurrent transactions. -/
namespace SQLean.Advanced

def Column.sqlType (column : Column) : SqlType :=
  if column.primaryKey || column.nullable == some false then column.type.sqlType
  else column.type.sqlType.asNullable

def CatalogTable.toTableDef (table : CatalogTable) : TableDef :=
  ⟨table.name, table.columns.map fun column =>
    ⟨column.name, if table.primaryKey.contains column.name then column.type.sqlType else column.sqlType⟩⟩

def Catalog.toSchema (catalog : Catalog) : Schema := catalog.map CatalogTable.toTableDef

def DataType.ofSqlType : SqlType → DataType
  | .nullable base => ofSqlType base
  | .array element =>
      let type := ofSqlType element
      { type with name := .array type.name }
  | type => ⟨match type with
   | .opaque name => match name with
     | .date => .date | .time => .time | .timeTZ => .timeTZ
     | .timestamp => .timestamp | .timestampTZ => .timestampTZ
     | .interval => .interval | .uuid => .uuid | .json => .json
     | .jsonb => .jsonb | .bytea => .bytea
   | .int => .int | .text => .text | .bool => .bool | _ => .real, []⟩

def Catalog.ofSchema (schema : Schema) : Catalog :=
  schema.map fun table => { name := table.name, columns := table.columns.map fun column =>
    { name := column.name, type := DataType.ofSqlType column.type,
      nullable := some column.type.isNullable } }

def Catalog.findTable (catalog : Catalog) (name : Name) : Option CatalogTable :=
  catalog.find? (·.name == name)

def Catalog.putTable (catalog : Catalog) (table : CatalogTable) : Catalog :=
  if catalog.any (·.name == table.name) then
    catalog.map (fun old => if old.name == table.name then table else old)
  else catalog ++ [table]

def CatalogTable.keys (table : CatalogTable) : List (List Name) :=
  table.uniqueKeys ++ (if table.primaryKey.isEmpty then [] else [table.primaryKey]) ++
  table.namedKeys.map Prod.snd ++
  (table.columns.filter (fun col => col.primaryKey || col.unique)).map (fun col => [col.name])

def validDataType (type : DataType) : Bool :=
  match type.name.scalarBase, type.modifiers with
  | .varchar, [] | .char, [] | .numeric, [] => true
  | .varchar, [length] | .char, [length] => length > 0 && length ≤ 10485760
  | .numeric, [precision] => precision > 0 && precision ≤ 1000
  | .numeric, [precision, scale] => precision > 0 && precision ≤ 1000 && scale ≤ 1000
  | .varchar, _ | .char, _ | .numeric, _ => false
  | .time, [precision] | .timeTZ, [precision] | .timestamp, [precision]
  | .timestampTZ, [precision] | .interval, [precision] => precision ≤ 6
  | _, modifiers => modifiers.isEmpty

def requireCheck (condition : Bool) (message : String) : Except ValidationError Unit :=
  if condition then pure () else .error ⟨message⟩

def checkCatalog (catalog : Catalog) : Except ValidationError Unit := do
  let _ ← checkSchema catalog.toSchema
  for table in catalog do
    for column in table.columns do
      requireCheck (validDataType column.type) s!"invalid type declaration for '{column.name}'"
    let names := table.columns.map Column.name
    for key in table.keys do
      requireCheck (!key.isEmpty && key.eraseDups.length == key.length && key.all names.contains)
        s!"invalid unique key on '{table.name}'"
    let named := table.namedKeys.map Prod.fst
    requireCheck (named.all (!·.isEmpty) && named.eraseDups.length == named.length)
      s!"invalid named keys on '{table.name}'"
    requireCheck ((table.columns.filter (·.primaryKey)).length ≤ 1)
      s!"multiple column primary keys on '{table.name}'"
    let primaryColumns := (table.columns.filter (·.primaryKey)).map Column.name
    requireCheck (primaryColumns.isEmpty || table.primaryKey.isEmpty || primaryColumns == table.primaryKey)
      s!"conflicting primary keys on '{table.name}'"

end SQLean.Advanced
