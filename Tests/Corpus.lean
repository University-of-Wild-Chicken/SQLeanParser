import SQLean.Parser
import SQLean.Pretty
import SQLean.Validation
import Tests.Support

namespace SQLean.Tests

/-- Schema shared by the 100 checked-in parser examples. -/
def corpusSchema : Schema := [
  { name := "users", columns := [
      ⟨"id", .int⟩, ⟨"age", .int⟩, ⟨"name", .text⟩, ⟨"city", .text⟩] },
  { name := "inventory", columns := [
      ⟨"sku", .int⟩, ⟨"price", .int⟩, ⟨"quantity", .int⟩, ⟨"label", .text⟩] }
]

/-- Exercise exactly 100 distinct checked-in queries, including static validity
certificates and canonical round trips.
Run the test executable from the repository root so the fixture path resolves.
-/
def corpusTests : IO Nat := do
  let source ← IO.FS.readFile "fixtures/queries.sql"
  let queries := (source.splitOn "\n").filter (fun line => !line.trimAscii.toString.isEmpty)
  SQLean.Tests.assert (queries.length == 100) s!"expected exactly 100 corpus queries, found {queries.length}"
  SQLean.Tests.assert (decide queries.Nodup) "corpus queries must be distinct"
  for (querySource, index) in queries.zipIdx do
    let label := s!"corpus query {index + 1}"
    let ast ← expectOk label (parseQuery querySource)
    let certified ← expectOk s!"{label} validation" (certifyQuery corpusSchema ast)
    SQLean.Tests.assert (certified.outputTypes.length == ast.selectList.length)
      s!"{label}: output type arity differs from SELECT list"
    let rendered := toSql ast
    let reparsed ← expectOk s!"{label} round trip: {rendered}" (parseQuery rendered)
    SQLean.Tests.assert (ast == reparsed) s!"{label}: SQL rendering changed the AST"
  pure queries.length

end SQLean.Tests
