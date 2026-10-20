import SQLean.Validation
import SQLean.AdvancedDDL
import SQLean.AdvancedParser
import Lean.Data.Json.Parser

/-! JSON interchange for externally supplied schemas. Names are exact; unquoted
SQL names are lowercased by the lexer, so use lowercase names in ordinary schemas.
-/

namespace SQLean

private def decodeType (json : Lean.Json) : Except String SqlType := do
  match ← json.getStr? with
  | "int" => pure .int
  | "text" => pure .text
  | "bool" => pure .bool
  | "real" => pure .real
  | other => throw s!"unknown SQL type '{other}'; expected int, text, bool, or real"

private def decodeColumn (json : Lean.Json) : Except String ColumnDef := do
  let name ← (← json.getObjVal? "name").getStr?
  let type ← decodeType (← json.getObjVal? "type")
  let nullable ← match json.getObjVal? "nullable" with
    | .ok value => value.getBool?
    | .error _ => pure false
  pure ⟨name, if nullable then .nullable type else type⟩

private def decodeTable (json : Lean.Json) : Except String TableDef := do
  let name ← (← json.getObjVal? "name").getStr?
  let columns ← (← json.getObjVal? "columns").getArr?
  pure ⟨name, ← columns.toList.mapM decodeColumn⟩

/-- Decode `{"tables": [{"name": "t", "columns": [{"name": "id", "type": "int"}]}]}`
and reject malformed schemas, including duplicate table or column names.
-/
def parseSchemaJson (source : String) : Except String Schema := do
  let json ← Lean.Json.parse source
  let tables ← (← json.getObjVal? "tables").getArr?
  let schema ← tables.toList.mapM decodeTable
  let _ ← (checkSchema schema).mapError toString
  pure schema

end SQLean

namespace SQLean.Advanced

private def optionalJson (json : Lean.Json) (name : String) : Option Lean.Json :=
  (json.getObjVal? name).toOption

private def namesJson (json : Lean.Json) : Except String (List Name) := do
  (← json.getArr?).toList.mapM Lean.Json.getStr?

private def collationIdJson (json : Lean.Json) : Except String CollationId := do
  let label ← json.getStr?
  match label with
  | "default" => pure .databaseDefault
  | "C" => pure .c
  | "POSIX" => pure .posix
  | other =>
    if other.startsWith "custom:" then
      pure (.custom (other.drop 7).toString)
    else throw s!"unknown collation identity '{other}'"

private def collationEntryJson (json : Lean.Json) : Except String CollationEntry := do
  let id ← collationIdJson (← json.getObjVal? "id")
  let schema ← (← json.getObjVal? "schema").getStr?
  let name ← (← json.getObjVal? "name").getStr?
  let encoding ← match optionalJson json "encoding" with
    | none | some .null => pure none
    | some value => pure (some (← value.getStr?))
  let deterministic ← match optionalJson json "deterministic" with
    | none => pure true | some value => value.getBool?
  let exposeUnqualified ← match optionalJson json "exposeUnqualified" with
    | none => pure false | some value => value.getBool?
  pure {id, schema, name, encoding, deterministic, exposeUnqualified}

/-- Decode an explicit native collation snapshot without certifying its
well-formedness. Absence retains the documented built-in UTF8 environment. -/
def decodeCollationEnvJson (source : String) : Except String CollationEnv := do
  let json ← Lean.Json.parse source
  match optionalJson json "collations" with
  | none => pure .builtin
  | some snapshot =>
    let encoding ← (← snapshot.getObjVal? "encoding").getStr?
    let entries ← (← (← snapshot.getObjVal? "entries").getArr?).toList.mapM collationEntryJson
    pure {encoding, entries}

private def catalogColumn (json : Lean.Json) : Except String Column := do
  let name ← (← json.getObjVal? "name").getStr?
  let typeName ← (← json.getObjVal? "type").getStr?
  let typeName := match typeName with
    | "int32" => "INTEGER" | "int64" => "BIGINT"
    | "float32" => "REAL" | "float64" | "double" => "DOUBLE PRECISION"
    | name => name
  let type ← (parseDataType typeName).mapError toString
  let modifiers ← match optionalJson json "modifiers" with
    | none => pure type.modifiers
    | some value =>
      if !type.modifiers.isEmpty then throw "type modifiers must be supplied in the type name or modifiers field, not both"
      (← value.getArr?).toList.mapM Lean.Json.getNat?
  let type := { type with modifiers }
  let nullable ← match optionalJson json "nullable" with
    | none => pure false | some value => value.getBool?
  let defaultValue ← match optionalJson json "default" with
    | none => pure none
    | some value => do
      let expr ← (parseExpression (← value.getStr?)).mapError toString
      pure (some expr)
  pure { name, type, nullable := some nullable, defaultValue }

private def catalogTable (json : Lean.Json) : Except String CatalogTable := do
  let name ← (← json.getObjVal? "name").getStr?
  let schema ← match optionalJson json "schema" with
    | none | some .null => pure none
    | some value => pure (some (← value.getStr?))
  let exposeUnqualified ← match optionalJson json "exposeUnqualified" with
    | none => pure schema.isNone
    | some value => value.getBool?
  let columns ← (← (← json.getObjVal? "columns").getArr?).toList.mapM catalogColumn
  let uniqueKeys ← match optionalJson json "uniqueKeys" with
    | none => pure [] | some value => (← value.getArr?).toList.mapM namesJson
  let primaryKey ← match optionalJson json "primaryKey" with
    | none => pure [] | some value => namesJson value
  let namedKeys ← match optionalJson json "namedKeys" with
    | none => pure []
    | some value => (← value.getObj?).toList.mapM fun (key, names) => do
        pure (key, ← namesJson names)
  let columnCollations ← match optionalJson json "columnCollations" with
    | none => pure []
    | some value => (← value.getArr?).toList.mapM fun item => do
      let column ← (← item.getObjVal? "column").getStr?
      let collation ← collationIdJson (← item.getObjVal? "collation")
      pure (column, collation)
  pure { name, columns, uniqueKeys, primaryKey, namedKeys, schema, exposeUnqualified, columnCollations }

/-- Decode catalog structure without running a validity checker. This lets an
independent contract validator classify invalid environments itself. -/
def decodeCatalogJson (source : String) : Except String Catalog := do
  let json ← Lean.Json.parse source
  (← (← json.getObjVal? "tables").getArr?).toList.mapM catalogTable

/-- Extended schema JSON adds nullable columns, SQL default expressions and
unique/primary/named keys used for DDL transitions and ON CONFLICT checking. -/
def parseCatalogJson (source : String) : Except String Catalog := do
  let catalog ← decodeCatalogJson source
  let _ ← (checkCatalogDefaults catalog).mapError toString
  pure catalog

/-- Comma-separated parameter type families in positional order. A `?` suffix
permits NULL parameter values, for example `int,text?`. -/
def parseParameterTypes (source : String) : Except String ParameterEnv := do
  let declarations ← (parseParameterDeclarations source).mapError toString
  pure (declarations.zipIdx.map fun ((type, nullable), index) =>
    (index + 1, if nullable then type.sqlType.asNullable else type.sqlType))

end SQLean.Advanced
