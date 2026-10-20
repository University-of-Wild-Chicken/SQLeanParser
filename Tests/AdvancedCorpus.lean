import SQLean.AdvancedParser
import SQLean.AdvancedPretty
import SQLean.AdvancedValidation
import SQLean.SchemaJson
import Tests.Support

namespace SQLean.Tests

private def advancedType (code : Char) : Except String SqlType :=
  match code with
  | 'i' => .ok .int | 't' => .ok .text | 'b' => .ok .bool | 'r' => .ok .real
  | 'I' => .ok (.nullable .int) | 'T' => .ok (.nullable .text)
  | 'B' => .ok (.nullable .bool) | 'R' => .ok (.nullable .real)
  | _ => .error s!"unknown advanced fixture type code: {code}"

mutual
  private def advancedExprFeature (category : String) : Nat → Advanced.Expr → Bool
    | 0, _ => false
    | fuel + 1, expr =>
      match expr with
      | .null => category == "nulls"
      | .decimal _ => category == "floating"
      | .parameter _ => category == "placeholders"
      | .inQuery arg query => category == "in_subqueries" ||
          advancedExprFeature category fuel arg || advancedQueryFeature category fuel query
      | .exists query => category == "exists" || advancedQueryFeature category fuel query
      | .scalarQuery query => advancedQueryFeature category fuel query
      | .binary _ lhs rhs | .pattern lhs rhs _ | .filteredAggregate lhs rhs =>
          advancedExprFeature category fuel lhs || advancedExprFeature category fuel rhs
      | .unary _ arg | .aggregate _ arg _ | .isNull arg _ | .cast arg _ =>
          advancedExprFeature category fuel arg
      | .between arg lower upper _ => advancedExprFeature category fuel arg ||
          advancedExprFeature category fuel lower || advancedExprFeature category fuel upper
      | .inList arg values => advancedExprFeature category fuel arg ||
          values.any (advancedExprFeature category fuel)
      | _ => false

  private def advancedQueryFeature (category : String) : Nat → Advanced.Query → Bool
    | 0, _ => false
    | fuel + 1, query =>
      query.ctes.any (fun cte => advancedQueryFeature category fuel cte.query) ||
      query.orderBy.any (fun order => advancedExprFeature category fuel order.expr) ||
      match query.body with
      | .set op _ left right =>
          (op == .intersect && category == "intersect") ||
          (op == .except && category == "except") ||
          advancedQueryFeature category fuel left || advancedQueryFeature category fuel right
      | .select select =>
          select.items.any (fun
            | .all .. => false
            | .expression expr _ => advancedExprFeature category fuel expr) ||
          select.source.any (advancedFromFeature category fuel) ||
          select.whereClause.any (advancedExprFeature category fuel) ||
          select.groupBy.any (advancedExprFeature category fuel) ||
          select.having.any (advancedExprFeature category fuel)

  private def advancedFromFeature (category : String) : Nat → Advanced.From → Bool
    | 0, _ => false
    | fuel + 1, source =>
      match source with
      | .table .. => false
      | .derived query _ _ lateral => (lateral && category == "lateral") ||
          advancedQueryFeature category fuel query
      | .join _ left right condition =>
          advancedFromFeature category fuel left || advancedFromFeature category fuel right ||
          match condition with
          | .using _ => category == "using_joins"
          | .natural => category == "natural_joins"
          | .on expr => advancedExprFeature category fuel expr
          | .none => false
end

private def advancedCategory (category source : String) (params : Advanced.ParameterEnv)
    (statement : Advanced.Statement) : Bool :=
  if category == "placeholders" then !params.isEmpty
  else if category == "nulls" && source.contains "scratch" then true
  else match statement with
  | .query query => advancedQueryFeature category (source.length + 1) query
  | .insert query => category == "upsert" && query.onConflict.isSome ||
      (category == "insert_select" && match query.source with | .query _ => true | _ => false)
  | .createTable _ => category == "create_table"
  | .alterTable .. => category == "alter_table"
  | .dropTable .. => category == "drop_table"
  | _ => false

/-- Fifteen classes, fifty distinct statements each. Every expected output type
is authored independently in the generator, and every successful static check
produces a Lean certificate. Canonical AST and catalog transitions are checked. -/
def advancedCorpusTests : IO Nat := do
  let schemaSource ← IO.FS.readFile "fixtures/advanced/schema.json"
  let catalog ← expectOk "advanced fixture catalog" (Advanced.parseCatalogJson schemaSource)
  let metadataSource ← IO.FS.readFile "fixtures/advanced/cases.json"
  let metadata ← expectOk "advanced fixture metadata" (Lean.Json.parse metadataSource)
  let mut total := 0
  for category in ["in_subqueries", "exists", "lateral", "using_joins", "natural_joins",
      "intersect", "except", "upsert", "insert_select", "nulls", "floating",
      "placeholders", "create_table", "alter_table", "drop_table"] do
    let source ← IO.FS.readFile s!"fixtures/advanced/{category}.sql"
    let queries := (source.splitOn "\n").filter (fun line => !line.trimAscii.toString.isEmpty)
    let casesJson ← expectOk s!"{category} metadata" (metadata.getObjVal? category)
    let cases ← expectOk s!"{category} cases" casesJson.getArr?
    SQLean.Tests.assert (queries.length == 50 && cases.size == 50)
      s!"expected exactly 50 {category} examples and expectations"
    SQLean.Tests.assert (decide queries.Nodup) s!"{category}: duplicate examples"
    for ((querySource, case), index) in (queries.zip cases.toList).zipIdx do
      let label := s!"advanced {category} example {index + 1}"
      let expectedSource ← expectOk label ((case.getObjVal? "sql") >>= Lean.Json.getStr?)
      SQLean.Tests.assert (expectedSource == querySource) s!"{label}: fixture metadata differs"
      let codes ← expectOk label ((case.getObjVal? "types") >>= Lean.Json.getStr?)
      let expectedTypes ← expectOk label (codes.toList.mapM advancedType)
      let paramCodes ← expectOk label ((case.getObjVal? "parameters") >>= Lean.Json.getStr?)
      let paramTypes ← expectOk label (paramCodes.toList.mapM advancedType)
      let params : Advanced.ParameterEnv := paramTypes.zipIdx.map (fun (type, index) => (index + 1, type))
      let ast ← expectOk s!"{label} parse" (Advanced.parse querySource)
      SQLean.Tests.assert (advancedCategory category querySource params ast)
        s!"{label}: example does not exercise the advertised syntax"
      let certified ← expectOk s!"{label} certificate" (Advanced.certifyStatement catalog params ast)
      SQLean.Tests.assert (certified.outputTypes == expectedTypes)
        s!"{label}: expected {reprStr expectedTypes}, got {reprStr certified.outputTypes}"
      let rendered := Advanced.render ast
      let reparsed ← expectOk s!"{label} canonical parse: {rendered}" (Advanced.parse rendered)
      SQLean.Tests.assert (ast == reparsed) s!"{label}: canonical rendering changed the AST"
      let original ← expectOk s!"{label} catalog transition" (Advanced.checkStatementDetailed catalog params ast)
      let roundtrip ← expectOk s!"{label} canonical transition" (Advanced.checkStatementDetailed catalog params reparsed)
      SQLean.Tests.assert (original == roundtrip) s!"{label}: canonical rendering changed the catalog transition"
    total := total + queries.length
  pure total

end SQLean.Tests
