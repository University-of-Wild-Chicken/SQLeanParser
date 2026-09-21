import SQLean.Validation
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
  | other => throw s!"unknown SQL type '{other}'; expected int, text, or bool"

private def decodeColumn (json : Lean.Json) : Except String ColumnDef := do
  let name ← (← json.getObjVal? "name").getStr?
  let type ← decodeType (← json.getObjVal? "type")
  pure ⟨name, type⟩

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
