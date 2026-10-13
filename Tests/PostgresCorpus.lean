import Tests.RelationalCorpus

namespace SQLean.Tests

private def decodePostgresType (code : Char) : Except String SqlType :=
  match code with
  | 'i' => .ok .int
  | 't' => .ok .text
  | 'b' => .ok .bool
  | 'r' => .ok .real
  | 'I' => .ok (.nullable .int)
  | 'T' => .ok (.nullable .text)
  | 'B' => .ok (.nullable .bool)
  | 'R' => .ok (.nullable .real)
  | _ => .error s!"invalid PostgreSQL corpus type code: {code}"

private def hasPostgresExpr (category : String) : RelExpr → Bool
  | .filteredAggregate arg predicate => category == "aggregate_filter" ||
      hasPostgresExpr category arg || hasPostgresExpr category predicate
  | .cast arg _ => category == "casts" || hasPostgresExpr category arg
  | .pattern arg pat _ => category == "predicates" ||
      hasPostgresExpr category arg || hasPostgresExpr category pat
  | .binary _ left right => hasPostgresExpr category left || hasPostgresExpr category right
  | .unary _ arg | .aggregate _ arg _ | .isNull arg _ => hasPostgresExpr category arg
  | _ => false

private def postgresCategory (category source : String) (statement : Statement) : Bool :=
  match statement with
  | .returning _ items => category == "returning" && !items.isEmpty
  | .relational query =>
      match category with
      | "distinct_on" => !query.distinctOn.isEmpty
      | "null_ordering" => query.orderBy.any (·.nullsFirst.isSome)
      | "predicates" =>
          -- BETWEEN deliberately normalizes to comparison expressions.
          source.contains " IN (" || source.contains " BETWEEN " ||
          query.selectList.any (fun item => match item with
            | .expression expr _ => hasPostgresExpr category expr
            | _ => false) || query.whereClause.any (hasPostgresExpr category)
      | "casts" => source.contains "::" || source.contains "CAST("
      | "aggregate_filter" => query.selectList.any (fun item => match item with
          | .expression expr _ => hasPostgresExpr category expr
          | _ => false)
      | _ => false
  | _ => false

/-- Fifty independently typed examples per PostgreSQL class. Rich SELECTs are
reparsed through the relational API because normalization of BETWEEN can
produce a spelling also accepted by the legacy SELECT API. -/
def postgresCorpusTests : IO Nat := do
  let schemaSource ← IO.FS.readFile "fixtures/postgresql/schema.json"
  let schema ← expectOk "PostgreSQL corpus schema" (parseSchemaJson schemaSource)
  SQLean.Tests.assert (schema == relationalCorpusSchema)
    "PostgreSQL JSON and Lean corpus schemas differ"
  let typeSource ← IO.FS.readFile "fixtures/postgresql/expected_types.json"
  let typesJson ← expectOk "PostgreSQL expected types" (Lean.Json.parse typeSource)
  let mut total := 0
  for category in ["distinct_on", "aggregate_filter", "casts", "predicates", "null_ordering", "returning"] do
    let source ← IO.FS.readFile s!"fixtures/postgresql/{category}.sql"
    let queries := (source.splitOn "\n").filter (fun line => !line.trimAscii.toString.isEmpty)
    let expectedJson ← expectOk s!"{category} type expectations" (typesJson.getObjVal? category)
    let expected ← expectOk s!"{category} type array" expectedJson.getArr?
    SQLean.Tests.assert (queries.length == 50)
      s!"expected exactly 50 {category} examples, found {queries.length}"
    SQLean.Tests.assert (decide queries.Nodup) s!"{category} examples must be distinct"
    SQLean.Tests.assert (expected.size == queries.length) s!"{category}: missing type expectations"
    for ((querySource, typeJson), index) in (queries.zip expected.toList).zipIdx do
      let label := s!"PostgreSQL {category} example {index + 1}"
      let ast ← expectOk label (parseStatement querySource)
      SQLean.Tests.assert (postgresCategory category querySource ast)
        s!"{label}: example does not exercise its advertised feature"
      let codes ← expectOk s!"{label} type codes" typeJson.getStr?
      let expectedTypes ← expectOk s!"{label} decoded types" (codes.toList.mapM decodePostgresType)
      let certified ← expectOk s!"{label} validation" (certifyStatement schema ast)
      SQLean.Tests.assert (certified.outputTypes == expectedTypes)
        s!"{label}: expected {reprStr expectedTypes}, got {reprStr certified.outputTypes}"
      let rendered := toSql ast
      match ast with
      | .relational query =>
          let reparsed ← expectOk s!"{label} round trip" (parseRelQuery rendered)
          SQLean.Tests.assert (query == reparsed) s!"{label}: rendering changed the relational AST"
      | _ =>
          let reparsed ← expectOk s!"{label} round trip" (parseStatement rendered)
          SQLean.Tests.assert (ast == reparsed) s!"{label}: rendering changed the statement AST"
    total := total + queries.length
  pure total

end SQLean.Tests
