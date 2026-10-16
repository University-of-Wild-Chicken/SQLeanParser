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

private def catalogColumn (json : Lean.Json) : Except String Column := do
  let name ← (← json.getObjVal? "name").getStr?
  let typeName ← (← json.getObjVal? "type").getStr?
  let type : DataType ← match typeName with
    | "int" => pure ⟨.int, []⟩ | "text" => pure ⟨.text, []⟩
    | "bool" => pure ⟨.bool, []⟩ | "real" => pure ⟨.real, []⟩
    | _ => throw s!"unknown SQL type '{typeName}'"
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
  let columns ← (← (← json.getObjVal? "columns").getArr?).toList.mapM catalogColumn
  let uniqueKeys ← match optionalJson json "uniqueKeys" with
    | none => pure [] | some value => (← value.getArr?).toList.mapM namesJson
  let primaryKey ← match optionalJson json "primaryKey" with
    | none => pure [] | some value => namesJson value
  let namedKeys ← match optionalJson json "namedKeys" with
    | none => pure []
    | some value => (← value.getObj?).toList.mapM fun (key, names) => do
        pure (key, ← namesJson names)
  pure { name, columns, uniqueKeys, primaryKey, namedKeys }

/-- Extended schema JSON adds nullable columns, SQL default expressions and
unique/primary/named keys used for DDL transitions and ON CONFLICT checking. -/
def parseCatalogJson (source : String) : Except String Catalog := do
  let json ← Lean.Json.parse source
  let catalog ← (← (← json.getObjVal? "tables").getArr?).toList.mapM catalogTable
  let _ ← (checkCatalogDefaults catalog).mapError toString
  pure catalog

/-- Comma-separated parameter type families in positional order. A `?` suffix
permits NULL parameter values, for example `int,text?`. -/
def parseParameterTypes (source : String) : Except String ParameterEnv := do
  if source.isEmpty then return []
  (source.splitOn ",").zipIdx.mapM fun (name, index) => do
    let name := name.trimAscii.toString
    let nullable := name.endsWith "?"
    let name := if nullable then name.dropEnd 1 |>.toString else name
    let type ← match name with
      | "int" => pure SqlType.int | "text" => pure SqlType.text
      | "bool" => pure SqlType.bool | "real" => pure SqlType.real
      | _ => throw s!"unknown parameter type '{name}'"
    pure (index + 1, if nullable then type.asNullable else type)

end SQLean.Advanced
