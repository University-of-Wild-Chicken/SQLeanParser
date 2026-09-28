import SQLean.Parser
import SQLean.Pretty
import SQLean.CRUDValidation
import SQLean.SchemaJson
import Tests.Support

namespace SQLean.Tests

/-- The JSON schema alongside the CRUD examples must match this definition. -/
def crudCorpusSchema : Schema := [
  { name := "users", columns := [
      ⟨"id", .int⟩, ⟨"age", .int⟩, ⟨"name", .text⟩, ⟨"city", .text⟩] },
  { name := "inventory", columns := [
      ⟨"sku", .int⟩, ⟨"price", .int⟩, ⟨"quantity", .int⟩, ⟨"label", .text⟩] },
  { name := "flags", columns := [
      ⟨"id", .int⟩, ⟨"enabled", .bool⟩, ⟨"label", .text⟩] }
]

private def statementCategory : Statement → String
  | .select _ => "select"
  | .insert _ => "insert"
  | .update _ => "update"
  | .delete _ => "delete"
  | .relational _ => "relational"

private def hasNewExprFeature : Expr → Bool
  | .literal (.bool _) => true
  | .literal _ | .column _ => false
  | .binary _ left right => hasNewExprFeature left || hasNewExprFeature right
  | .unary _ _ => true

private def hasNewSelectFeature (query : SelectQuery) : Bool :=
  query.distinct || !query.orderBy.isEmpty || query.limit.isSome || query.offset.isSome ||
  (match query.projection with
   | .all => true
   | .expressions items => items.any hasNewExprFeature) ||
  query.whereClause.any hasNewExprFeature

private def expectedOutputArity (statement : Statement) : Nat :=
  match statement with
  | .select query =>
    match query.projection with
    | .all => ((crudCorpusSchema.findTable query.table).map (·.columns.length)).getD 0
    | .expressions items => items.length
  | .insert _ | .update _ | .delete _ => 0
  -- Relational statements fail this corpus's category check before arity checks.
  | .relational _ => 0

/-- Verify exactly 50 distinct examples for each introduced CRUD category.
Every example receives a static-validity proof and survives a canonical SQL
round trip without changing its AST. SELECT examples all use a new feature.
-/
def crudCorpusTests : IO Nat := do
  let schemaSource ← IO.FS.readFile "fixtures/crud/schema.json"
  let decoded ← expectOk "CRUD corpus JSON schema" (parseSchemaJson schemaSource)
  SQLean.Tests.assert (decoded == crudCorpusSchema) "CRUD corpus JSON and Lean schemas differ"
  let mut total := 0
  for category in ["select", "insert", "update", "delete"] do
    let source ← IO.FS.readFile s!"fixtures/crud/{category}.sql"
    let queries := (source.splitOn "\n").filter (fun line => !line.trimAscii.toString.isEmpty)
    SQLean.Tests.assert (queries.length == 50)
      s!"expected exactly 50 CRUD {category} examples, found {queries.length}"
    SQLean.Tests.assert (decide queries.Nodup) s!"CRUD {category} examples must be distinct"
    for (querySource, index) in queries.zipIdx do
      let label := s!"CRUD {category} example {index + 1}"
      let ast ← expectOk label (parseStatement querySource)
      SQLean.Tests.assert (statementCategory ast == category)
        s!"{label}: expected {category}, got {statementCategory ast}"
      if let .select query := ast then
        SQLean.Tests.assert (hasNewSelectFeature query)
          s!"{label}: example does not exercise a newly introduced SELECT feature"
      let certified ← expectOk s!"{label} validation" (certifyStatement crudCorpusSchema ast)
      SQLean.Tests.assert (certified.outputTypes.length == expectedOutputArity ast)
        s!"{label}: certificate output type arity differs from the statement"
      let rendered := toSql ast
      let reparsed ← expectOk s!"{label} round trip: {rendered}" (parseStatement rendered)
      SQLean.Tests.assert (ast == reparsed) s!"{label}: SQL rendering changed the AST"
    total := total + queries.length
  pure total

end SQLean.Tests
