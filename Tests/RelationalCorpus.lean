import SQLean.Parser
import SQLean.Pretty
import SQLean.CRUDValidation
import SQLean.SchemaJson
import Tests.Support

namespace SQLean.Tests

/-- The complete, non-null input schema shared by the relational examples. -/
def relationalCorpusSchema : Schema := [
  { name := "users", columns := [
      ⟨"id", .int⟩, ⟨"age", .int⟩, ⟨"name", .text⟩, ⟨"city", .text⟩] },
  { name := "orders", columns := [
      ⟨"id", .int⟩, ⟨"user_id", .int⟩, ⟨"amount", .int⟩, ⟨"status", .text⟩] },
  { name := "departments", columns := [⟨"id", .int⟩, ⟨"name", .text⟩] },
  { name := "employees", columns := [
      ⟨"id", .int⟩, ⟨"department_id", .int⟩, ⟨"manager_id", .int⟩,
      ⟨"name", .text⟩, ⟨"salary", .int⟩] },
  { name := "flags", columns := [
      ⟨"id", .int⟩, ⟨"enabled", .bool⟩, ⟨"label", .text⟩] }
]

/-- Independently specified expected output types, in fixture order. Lowercase
letters mean non-null primitive types; uppercase letters mean nullable types.
Every example checks its entire ordered result schema, including wildcard
expansion, aggregate nullability, and null extension through nested queries. -/
private def expectedTypeCodes : String → List String
  | "joins" => [
      "ti", "ii", "ti", "tI", "iT", "Ti", "Ii", "II", "TT", "tt",
      "iittiiit", "iitti", "iIIIT", "IITTIIIT", "iittiiiti", "tT", "tt", "tt", "tT", "ttT",
      "tib", "i", "iI", "i", "II", "tb", "ti", "tI", "ti", "ii",
      "ti", "ti", "tt", "i", "ii", "tt", "tt", "tT", "ii", "iI",
      "tbb", "ti", "iittt", "tTT", "TtT", "TIt", "ti", "tt", "ii", "iiitiT"]
  | "grouping" => [
      "i", "i", "i", "I", "R", "II", "TT", "iIRII", "IR", "TT",
      "ti", "tR", "tiI", "itI", "t", "ii", "tii", "ti", "tI", "iR",
      "iII", "i", "I", "ti", "ti", "ti", "itI", "ii", "iIR", "tiR",
      "iTi", "ti", "TTi", "bi", "ti", "ti", "ii", "ti", "ti", "iIR",
      "iI", "ib", "ti", "tI", "tB", "tb", "bi", "ti", "tI", "ti"]
  | "subqueries" => [
      "i", "tt", "it", "iitt", "i", "i", "t", "t", "t", "t",
      "i", "i", "ii", "t", "ii", "ti", "iI", "i", "ti", "II",
      "i", "I", "R", "ti", "t", "tI", "i", "ti", "tI", "ti",
      "I", "I", "ti", "i", "t", "i", "i", "it", "ti", "t",
      "tt", "tR", "tb", "bi", "tt", "Ii", "t", "ti", "t", "I"]
  | "ctes" => [
      "i", "itt", "it", "i", "i", "t", "t", "i", "i", "ii",
      "i", "I", "R", "II", "ti", "t", "tI", "i", "I", "I",
      "ti", "t", "tI", "ti", "TI", "tt", "tt", "tR", "i", "ti",
      "ti", "i", "t", "iI", "i", "t", "tI", "tt", "ii", "t",
      "i", "ti", "t", "i", "i", "tI", "i", "t", "t", "i"]
  | _ => []

private def decodeType (code : Char) : SqlType :=
  match code with
  | 'i' => .int
  | 't' => .text
  | 'b' => .bool
  | 'r' => .real
  | 'I' => .nullable .int
  | 'T' => .nullable .text
  | 'B' => .nullable .bool
  | 'R' => .nullable .real
  | _ => .int

private def containsAggregate : RelExpr → Bool
  | .countAll | .aggregate _ _ _ => true
  | .binary _ left right => containsAggregate left || containsAggregate right
  | .unary _ arg | .isNull arg _ => containsAggregate arg
  | _ => false

private def exercisesCategory (category : String) (query : RelQuery) : Bool :=
  match category with
  | "joins" => !query.joins.isEmpty
  | "grouping" => !query.groupBy.isEmpty || query.having.isSome || query.selectList.any (fun item =>
      match item with
      | .expression expr _ => containsAggregate expr
      | .all _ => false)
  | "subqueries" => query.source.derived.isSome || query.joins.any (·.table.derived.isSome)
  | "ctes" => !query.ctes.isEmpty
  | _ => false

/-- Verify 50 distinct examples per new query class. Each example must exercise
its advertised feature, receive a static-validity certificate with the exact
expected result types, and retain its AST through canonical SQL rendering. -/
def relationalCorpusTests : IO Nat := do
  let schemaSource ← IO.FS.readFile "fixtures/relational/schema.json"
  let decoded ← expectOk "relational corpus JSON schema" (parseSchemaJson schemaSource)
  SQLean.Tests.assert (decoded == relationalCorpusSchema)
    "relational corpus JSON and Lean schemas differ"
  let mut total := 0
  for category in ["joins", "grouping", "subqueries", "ctes"] do
    let source ← IO.FS.readFile s!"fixtures/relational/{category}.sql"
    let queries := (source.splitOn "\n").filter (fun line => !line.trimAscii.toString.isEmpty)
    let expected := expectedTypeCodes category
    SQLean.Tests.assert (queries.length == 50)
      s!"expected exactly 50 {category} examples, found {queries.length}"
    SQLean.Tests.assert (decide queries.Nodup) s!"{category} examples must be distinct"
    SQLean.Tests.assert (expected.length == queries.length)
      s!"{category}: expected output types are missing"
    for ((querySource, typeCodes), index) in (queries.zip expected).zipIdx do
      let label := s!"relational {category} example {index + 1}"
      let ast ← expectOk label (parseStatement querySource)
      match ast with
      | .relational query =>
          SQLean.Tests.assert (exercisesCategory category query)
            s!"{label}: example does not exercise its advertised query class"
      | _ => throw (IO.userError s!"{label}: expected a relational SELECT AST")
      let certified ← expectOk s!"{label} validation" (certifyStatement relationalCorpusSchema ast)
      let expectedTypes := typeCodes.toList.map decodeType
      SQLean.Tests.assert (certified.outputTypes == expectedTypes)
        s!"{label}: expected output types {reprStr expectedTypes}, got {reprStr certified.outputTypes}"
      let rendered := toSql ast
      let reparsed ← expectOk s!"{label} round trip: {rendered}" (parseStatement rendered)
      SQLean.Tests.assert (ast == reparsed) s!"{label}: SQL rendering changed the AST"
    total := total + queries.length
  pure total

end SQLean.Tests
