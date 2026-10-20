import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

namespace SQLean.Tests

/-- The independent rule records the chosen scalar operator, rather than a
common type of the left scalar and the complete array. -/
example : SelectContract.ExprValid [] .empty
    (.quantifiedComparison .eq .any (.literal (.int 1)) (.array [.literal (.int 2)]))
    (some ⟨.bool, true⟩) [] :=
  .quantifiedComparison (selected := ⟨[.int32, .int32], .bool⟩)
    (.int (by decide)) (.array (.cons (.int (by decide)) .nil) rfl) rfl

/-- Unknown literal RHS input can acquire an array type from the operator. -/
example : SelectContract.ExprValid [] .empty
    (.quantifiedComparison .eq .some (.literal (.int 1)) (.literal (.text "{1,2}")))
    (some ⟨.bool, true⟩) [] :=
  .quantifiedComparison (selected := ⟨[.int32, .int32], .bool⟩)
    (.int (by decide)) .text rfl

/-- Concrete TEXT is not an unknown array literal. -/
example : SelectContract.quantifiedComparisonSignature .eq
    (.known ⟨.int32, false⟩) (.known ⟨.text, false⟩) = none := rfl

/-- JSON element comparison fails scalar operator resolution; this is distinct
from the deferred runtime element-operator gap of whole-array JSON[] equality. -/
example : SelectContract.quantifiedComparisonSignature .eq
    (.known ⟨.json, false⟩) (.known ⟨.array .json, false⟩) = none := rfl

private def quantifiedCertificate (query : Advanced.Query)
    (params : SelectContract.ParameterEnv := []) :
    IO (List SelectContract.OutputColumn) := do
  let certificate ← expectOk "quantified-array SELECT"
    ((SelectContract.checkQuery .basicV29 [] params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let identity ← expectOk "quantified-array identity renderer"
    ((RenderContract.check .identityV01 query).mapError reprStr)
  let postgres ← expectOk "quantified-array PostgreSQL renderer"
    ((RenderContract.check .postgres16V01 query).mapError reprStr)
  have _identity : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
  have _postgres : Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
    postgres.roundTrip
  pure certificate.output

private def quantifiedOutput (sql : String) (parameterTypes : String := "") :
    IO (List SelectContract.OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let params ← expectOk sql (Assurance.parseContractParameterTypes parameterTypes)
  quantifiedCertificate query params

private def quantifiedField (id : String) (record : Lean.Json) (name : String) : IO String :=
  expectOk s!"{id}: {name}" ((record.getObjVal? name) >>= Lean.Json.getStr?)

private def quantifiedOperatorInventoryTests : IO Nat := do
  let json ← expectOk "quantified operator inventory JSON"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/array_quantified/operator_signatures.json"))
  let records ← expectOk "quantified operator inventory records" json.getArr?
  SQLean.Tests.assert (records.size == 192) "expected exactly 192 scalar operator signatures"
  let mut observed : List (Advanced.ComparisonOp × SelectContract.FunctionOverload) := []
  for record in records do
    let operator ← quantifiedField "operator inventory" record "operator"
    let op ← match operator with
      | "=" => pure Advanced.ComparisonOp.eq
      | "<>" => pure .ne
      | "<" => pure .lt
      | "<=" => pure .le
      | ">" => pure .gt
      | ">=" => pure .ge
      | _ => throw (IO.userError s!"unexpected operator inventory spelling: {operator}")
    let parseType := fun field => do
      let name ← quantifiedField operator record field
      let declaration ← expectOk name (Advanced.parseDataType name)
      match SelectContract.concreteType declaration with
      | some type => pure type.unmodified
      | none => throw (IO.userError s!"unsupported scalar operator inventory type: {name}")
    let left ← parseType "left"
    let right ← parseType "right"
    let expected : SelectContract.FunctionOverload := ⟨[left, right], .bool⟩
    SQLean.Tests.assert
      (SelectContract.comparisonOverload op
        (.known ⟨left, false⟩) (.known ⟨right, false⟩) == some expected)
      s!"operator inventory selected a different scalar overload: {operator} {reprStr expected}"
    SQLean.Tests.assert
      (SelectContract.quantifiedComparisonSignature op
        (.known ⟨left, false⟩) (.known ⟨right.asArray, false⟩) == some expected)
      s!"operator inventory selected a different quantified overload: {operator} {reprStr expected}"
    observed := (op, expected) :: observed
  let expected := [Advanced.ComparisonOp.eq, .ne, .lt, .le, .gt, .ge] |>.flatMap fun op =>
    (SelectContract.equalityCatalog.filter (fun signature => !signature.inputs.contains .name)).map fun signature => (op, signature)
  SQLean.Tests.assert (decide observed.Nodup &&
      expected.all observed.contains && observed.all expected.contains)
    "operator fixture differs from the closed normative inventory"
  pure records.size

def arrayQuantifiedContractTests : IO Nat := do
  let operators : List Advanced.ComparisonOp := [.eq, .ne, .lt, .le, .gt, .ge]
  let mut count ← quantifiedOperatorInventoryTests
  -- Each of the independently native-audited 192 scalar signatures obtains a
  -- full query certificate with an array element of the declared right type.
  SQLean.Tests.assert (SelectContract.equalityCatalog.length == 35)
    "quantified scalar operator inventory must contain the original 32 and three exact NAME input pairs"
  for signature in SelectContract.equalityCatalog do
    let (leftType, rightType) ← match signature.inputs with
      | [left, right] => pure (left, right)
      | _ => throw (IO.userError "scalar comparison inventory must have two inputs")
    for op in operators do
      let left := Advanced.Expr.cast .null leftType.dataType
      let right := Advanced.Expr.array [.cast .null rightType.dataType]
      let query : Advanced.Query := { body := .select {
        items := [.expression (.quantifiedComparison op .any left right) (some "v")] } }
      let actual ← quantifiedCertificate query
      SQLean.Tests.assert (actual == [⟨"v", ⟨.bool, true⟩⟩])
        s!"quantified scalar signature {reprStr op}: {reprStr signature}"
      count := count + 1
  for quantifier in ["ANY", "SOME", "ALL"] do
    for op in ["=", "<>", "<", "<=", ">", ">="] do
      let sql := s!"SELECT 1 {op} {quantifier}(ARRAY[1,2,NULL])"
      let actual ← quantifiedOutput sql
      SQLean.Tests.assert (actual == [⟨"?column?", ⟨.bool, true⟩⟩])
        s!"quantifier/operator/default label: {sql}"
      count := count + 1
  let ordinary := [
    "SELECT 1 = ANY(NULL) AS v",
    "SELECT NULL = ANY(NULL) AS v",
    "SELECT NULL = ALL(ARRAY[]::INTEGER[]) AS v",
    "SELECT NULL = SOME(ARRAY[]::INTEGER[]) AS v",
    "SELECT '1' = ANY(ARRAY[1,2]) AS v",
    "SELECT 1 = ANY('{1,2}') AS v",
    "SELECT 'b' = ANY('{a,b}') AS v",
    "SELECT NULL = ALL('{}') AS v",
    "SELECT 1 = ANY(ARRAY[1::BIGINT]) AS v",
    "SELECT 1::INTEGER < ALL(ARRAY[1::REAL]) AS v",
    "SELECT DATE '2024-01-01' <= ALL(ARRAY[TIMESTAMP '2024-01-01 12:00']) AS v",
    "SELECT 'null'::JSONB = ANY(ARRAY['null'::JSONB]) AS v",
    "SELECT 2 = ANY(ARRAY[[1,2],[3,4]]) AS v",
    "SELECT NOT (2 = ANY(ARRAY[1,NULL])) AS v",
    "SELECT (2 = ANY(ARRAY[1,NULL])) AND TRUE AS v",
    "SELECT 1 = ALL(ARRAY[]::INTEGER[]) AS v WHERE 2 = SOME(ARRAY[2])",
    "SELECT d.v FROM (SELECT 2 = ANY(ARRAY[1,2]) AS v) d"]
  for sql in ordinary do
    let actual ← quantifiedOutput sql
    SQLean.Tests.assert (actual == [⟨"v", ⟨.bool, true⟩⟩]) s!"quantified output: {sql}"
    count := count + 1
  let invalid := [
    "SELECT 1 = ANY(1)",
    "SELECT 1 = ANY('{1,2}'::TEXT)",
    "SELECT 1 = ALL(NULL::INTEGER)",
    "SELECT ARRAY[1] = ANY(NULL)",
    "SELECT ARRAY[1] = ANY(ARRAY[ARRAY[1]])",
    "SELECT 'null'::JSON = ANY(ARRAY['null'::JSON])",
    "SELECT NULL = ANY(NULL::JSON[])",
    "SELECT TRUE = ANY(ARRAY[1,2])",
    "SELECT DATE '2024-01-01' = ANY(ARRAY[1])",
    "SELECT 1 = ANY(ARRAY[])"]
  for sql in invalid do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV29 [] [] query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError s!"expected Invalid quantified-array query: {sql}")
    count := count + 1
  for sql in [
      "SELECT 1 = ANY((SELECT ARRAY[1])::INTEGER[])",
      "SELECT 1 = ANY(unknown_array_function())",
      "SELECT 1 = ANY(ARRAY[COUNT(*)])"] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV29 [] [] query with
    | .error (.unsupported _) => pure ()
    | _ => throw (IO.userError s!"expected Unsupported quantified-array boundary: {sql}")
    count := count + 1
  let parameterCases := [
    ("SELECT $1 = ANY($2) AS v", "int,integer[]"),
    ("SELECT $1 = ALL($2) AS v", "numeric?,real[]?"),
    ("SELECT ? = SOME(ARRAY[?,?]) AS v", "int,int,int?"),
    ("SELECT $2 = ANY($1) AS v", "integer[],bigint")]
  for (sql, types) in parameterCases do
    let actual ← quantifiedOutput sql types
    SQLean.Tests.assert (actual == [⟨"v", ⟨.bool, true⟩⟩]) s!"quantified parameters: {sql}"
    count := count + 1
  let sql := "SELECT ? = SOME(ARRAY[?,?]) AS a, ? = ALL(?) AS b"
  let query ← expectOk sql (Advanced.parseQuery sql)
  let params ← expectOk sql (Assurance.parseContractParameterTypes "int,int,int,int,integer[]")
  let _ ← quantifiedCertificate query params
  SQLean.Tests.assert (Advanced.queryParameters 1024 query ==
      (List.range 5).map (fun n => .anonymous (n + 1)))
    "quantified array parameter traversal order changed"
  count := count + 1
  let bad : Advanced.Query := { body := .select { items := [
    .expression (.quantifiedComparison .eq .any
      (.parameter (.anonymous 2)) (.array [.parameter (.anonymous 1)]))] } }
  match SelectContract.checkQuery .basicV29 [] params bad with
  | .error (.invalid _) => pure ()
  | _ => throw (IO.userError "manual reordered quantified placeholders must be Invalid")
  count := count + 1
  match SelectContract.checkQuery .basicV29 [] params query 1 with
  | .error (.inconclusive _) => pure ()
  | _ => throw (IO.userError "quantified array exhaustion must be Inconclusive")
  count := count + 1
  pure count

def arrayQuantifiedCorpusTests : IO Nat := do
  let json ← expectOk "quantified array fixture JSON"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/array_quantified/synthetic.json"))
  let records ← expectOk "quantified array fixture records" json.getArr?
  SQLean.Tests.assert (records.size == 50) "expected exactly 50 quantified array synthetic queries"
  let mut ids : List String := []
  let mut statements : List String := []
  for record in records do
    let id ← quantifiedField "quantified array fixture" record "id"
    let sql ← quantifiedField id record "sql"
    SQLean.Tests.assert ((← quantifiedField id record "source_kind") == "synthetic") s!"{id}: population"
    let params ← quantifiedField id record "parameter_types"
    let expected ← expectOk id ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
    let expected ← expected.toList.mapM fun column => do
      let name ← quantifiedField id column "name"
      let type ← quantifiedField id column "type"
      let nullable ← expectOk id ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
      pure (name, type, nullable)
    let actual ← quantifiedOutput sql params
    let labels := actual.map fun column =>
      let type := match column.type.base with
        | .bool => "bool"
        | base => (base.dataType.toSql.toLower).replace ", " ","
      (column.name, type, column.type.nullable)
    SQLean.Tests.assert (labels == expected)
      s!"{id}: exact quantified output {reprStr labels}; expected {reprStr expected}"
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (decide ids.Nodup && decide statements.Nodup)
    "duplicate quantified array corpus identities or SQL"
  pure records.size

end SQLean.Tests
