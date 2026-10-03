import Tests.RelationalCorpus

namespace SQLean.Tests

/-- The industrial examples add a cyclic graph and an acyclic parts assembly
schema to the existing relational corpus schema. -/
def industrialCorpusSchema : Schema := relationalCorpusSchema ++ [
  { name := "edges", columns := [⟨"source", .int⟩, ⟨"target", .int⟩] },
  { name := "parts", columns := [
      ⟨"parent_id", .int⟩, ⟨"child_id", .int⟩, ⟨"quantity", .int⟩] }
]

private def decodeIndustrialType (code : Char) : Except String SqlType :=
  match code with
  | 'i' => .ok .int
  | 't' => .ok .text
  | 'b' => .ok .bool
  | 'r' => .ok .real
  | 'I' => .ok (.nullable .int)
  | 'T' => .ok (.nullable .text)
  | 'B' => .ok (.nullable .bool)
  | 'R' => .ok (.nullable .real)
  | _ => .error s!"invalid industrial corpus type code: {code}"

private def industrialCategory (category : String) (query : RelQuery) : Bool :=
  match category with
  | "recursive_ctes" => query.recursive || query.source.derived.any (·.recursive)
  | "unions" => !query.unions.isEmpty ||
      query.ctes.any (fun cte => !cte.query.unions.isEmpty) ||
      query.source.derived.any (fun derived => !derived.unions.isEmpty)
  | "source_free" => query.source.name.isEmpty && query.source.alias.isNone &&
      query.source.derived.isNone && query.joins.isEmpty
  | _ => false

/-- Every example verifies its advertised feature, exact independently specified
output schema, successful static certification, and canonical AST round trip. -/
def industrialCorpusTests : IO Nat := do
  let schemaSource ← IO.FS.readFile "fixtures/industrial/schema.json"
  let schema ← expectOk "industrial corpus JSON schema" (parseSchemaJson schemaSource)
  SQLean.Tests.assert (schema == industrialCorpusSchema)
    "industrial corpus JSON and Lean schemas differ"
  let typeSource ← IO.FS.readFile "fixtures/industrial/expected_types.json"
  let typesJson ← expectOk "industrial expected types JSON" (Lean.Json.parse typeSource)
  let mut total := 0
  for category in ["recursive_ctes", "unions", "source_free"] do
    let source ← IO.FS.readFile s!"fixtures/industrial/{category}.sql"
    let queries := (source.splitOn "\n").filter (fun line => !line.trimAscii.toString.isEmpty)
    let expectedJson ← expectOk s!"{category} expected types" (typesJson.getObjVal? category)
    let expected ← expectOk s!"{category} expected types array" expectedJson.getArr?
    SQLean.Tests.assert (queries.length == 50)
      s!"expected exactly 50 {category} examples, found {queries.length}"
    SQLean.Tests.assert (decide queries.Nodup) s!"{category} examples must be distinct"
    SQLean.Tests.assert (expected.size == queries.length)
      s!"{category}: expected output types are missing"
    for ((querySource, typeJson), index) in (queries.zip expected.toList).zipIdx do
      let label := s!"industrial {category} example {index + 1}"
      let ast ← expectOk label (parseStatement querySource)
      match ast with
      | .relational query =>
          SQLean.Tests.assert (industrialCategory category query)
            s!"{label}: example does not exercise its advertised query class"
      | _ => throw (IO.userError s!"{label}: expected a relational SELECT AST")
      let codes ← expectOk s!"{label} type codes" typeJson.getStr?
      let expectedTypes ← expectOk s!"{label} decode types"
        (codes.toList.mapM decodeIndustrialType)
      let certified ← expectOk s!"{label} validation" (certifyStatement schema ast)
      SQLean.Tests.assert (certified.outputTypes == expectedTypes)
        s!"{label}: expected output types {reprStr expectedTypes}, got {reprStr certified.outputTypes}"
      let rendered := toSql ast
      let reparsed ← expectOk s!"{label} round trip: {rendered}" (parseStatement rendered)
      SQLean.Tests.assert (ast == reparsed) s!"{label}: SQL rendering changed the AST"
    total := total + queries.length
  pure total

end SQLean.Tests
