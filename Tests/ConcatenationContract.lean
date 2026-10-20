import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

namespace SQLean.Tests

/-- The polymorphic text family retains the INTEGER input instead of claiming
that PostgreSQL applies a general implicit INTEGER-to-TEXT cast. -/
example : SelectContract.ExprValid [] .empty
    (.concat (.literal (.text "value: ")) (.literal (.int 42)))
    (some ⟨.text, false⟩) [] :=
  .concat (selected := ⟨.textOther, [.text, .int32], .text⟩)
    .text (.int (by decide)) rfl

example : SelectContract.ExprValid [] .empty (.concat .null .null)
    (some ⟨.text, true⟩) [] :=
  .concat (selected := ⟨.textText, [.text, .text], .text⟩) .null .null rfl

example : SelectContract.concatSignature
    (.known ⟨.array .int32, false⟩) (.unknown true) = none := rfl

private def concatCertificate (query : Advanced.Query)
    (params : SelectContract.ParameterEnv := []) :
    IO (List SelectContract.OutputColumn) := do
  let certificate ← expectOk "concatenation SELECT"
    ((SelectContract.checkQuery .basicV29 [] params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let identity ← expectOk "concatenation identity renderer"
    ((RenderContract.check .identityV01 query).mapError reprStr)
  let postgres ← expectOk "concatenation PostgreSQL renderer"
    ((RenderContract.check .postgres16V01 query).mapError reprStr)
  have _identity : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
  have _postgres : Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
    postgres.roundTrip
  pure certificate.output

private def concatOutput (sql : String) (parameterTypes : String := "") :
    IO (List SelectContract.OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let params ← expectOk sql (Assurance.parseContractParameterTypes parameterTypes)
  concatCertificate query params

private def concatField (id : String) (record : Lean.Json) (name : String) : IO String :=
  expectOk s!"{id}: {name}" ((record.getObjVal? name) >>= Lean.Json.getStr?)

private def concatOperatorInventoryTests : IO Nat := do
  let json ← expectOk "concatenation operator inventory JSON"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/concatenation/operator_signatures.json"))
  let records ← expectOk "concatenation operator inventory records" json.getArr?
  SQLean.Tests.assert (records.size == 5) "expected exactly five scalar concatenation signatures"
  let mut observed : List (List String × String × String) := []
  for record in records do
    SQLean.Tests.assert ((← concatField "concat inventory" record "operator") == "||")
      "unexpected concatenation operator spelling"
    let left ← concatField "concat inventory" record "left"
    let right ← concatField "concat inventory" record "right"
    let output ← concatField "concat inventory" record "output"
    let function ← concatField "concat inventory" record "function"
    observed := ([left, right], output, function) :: observed
  let expected := SelectContract.concatOperators.map fun operator =>
    (operator.catalogInputs, operator.output.dataType.toSql.toLower, operator.functionName)
  SQLean.Tests.assert (decide observed.Nodup && expected.all observed.contains &&
      observed.all expected.contains)
    "concatenation catalog fixture differs from the complete admitted inventory"
  pure records.size

def concatenationContractTests : IO Nat := do
  let mut count ← concatOperatorInventoryTests
  let declarations : List (String × SelectContract.ScalarType) := [
    ("smallint", .smallInt), ("integer", .int32), ("bigint", .int64),
    ("numeric(8,2)", .numeric []), ("real", .real), ("double precision", .doublePrecision),
    ("text", .text), ("varchar(5)", .varchar []), ("char(5)", .char []),
    ("boolean", .bool), ("date", .date), ("time(3)", .time []),
    ("time(3) with time zone", .timeTZ []), ("timestamp(3)", .timestamp []),
    ("timestamp(3) with time zone", .timestampTZ []), ("interval(3)", .interval []),
    ("uuid", .uuid), ("json", .json), ("jsonb", .jsonb), ("bytea", .bytea)]
  for (declaration, base) in declarations do
    let contextual := if base == .jsonb then SelectContract.ScalarType.jsonb
      else if base == .bytea then .bytea else .text
    for (sql, expected) in [
        ("SELECT CAST('x' AS TEXT) || $1 AS v", SelectContract.ScalarType.text),
        ("SELECT $1 || CAST('x' AS TEXT) AS v", .text),
        ("SELECT 'null' || $1 AS v", contextual),
        ("SELECT $1 || 'null' AS v", contextual)] do
      let actual ← concatOutput sql declaration
      SQLean.Tests.assert (actual == [⟨"v", ⟨expected, false⟩⟩])
        s!"concat exact parameter/context output: {declaration}; {sql}"
      count := count + 1
    let expectedLeft : SelectContract.ConcatSignature :=
      if base.isString then ⟨.textText, [.text, .text], .text⟩
      else ⟨.textOther, [.text, base], .text⟩
    let expectedRight : SelectContract.ConcatSignature :=
      if base.isString then ⟨.textText, [.text, .text], .text⟩
      else ⟨.otherText, [base, .text], .text⟩
    SQLean.Tests.assert
      (SelectContract.concatSignature (.known ⟨.text, false⟩) (.known ⟨base, false⟩) ==
        some expectedLeft &&
       SelectContract.concatSignature (.known ⟨base, false⟩) (.known ⟨.text, false⟩) ==
        some expectedRight) s!"exact polymorphic instantiation: {declaration}"
    count := count + 1
  for (left, right, expected) in [
      ("text", "text", SelectContract.ScalarType.text),
      ("text", "integer", .text), ("integer", "text", .text),
      ("jsonb", "jsonb", .jsonb), ("bytea", "bytea", .bytea)] do
    for nullableLeft in [false, true] do
      for nullableRight in [false, true] do
        let declarations := left ++ (if nullableLeft then "?" else "") ++ "," ++
          right ++ (if nullableRight then "?" else "")
        let actual ← concatOutput "SELECT $1 || $2 AS v" declarations
        SQLean.Tests.assert
          (actual == [⟨"v", ⟨expected, nullableLeft || nullableRight⟩⟩])
          s!"concat NULL propagation: {declarations}"
        count := count + 1
  let examples : List (String × SelectContract.ExactType) := [
    ("SELECT 'a' || 'b' AS v", ⟨.text, false⟩),
    ("SELECT NULL || NULL AS v", ⟨.text, true⟩),
    ("SELECT 'a' || NULL AS v", ⟨.text, true⟩),
    ("SELECT NULL || 1 AS v", ⟨.text, true⟩),
    ("SELECT 1 || NULL AS v", ⟨.text, true⟩),
    ("SELECT 'a'::CHAR(5) || 'b'::VARCHAR(3) AS v", ⟨.text, false⟩),
    ("SELECT 'a' || 1 + 2 AS v", ⟨.text, false⟩),
    ("SELECT 1 + 2 || 'a' AS v", ⟨.text, false⟩),
    ("SELECT 'a' || 'b' || 'c' AS v", ⟨.text, false⟩),
    ("SELECT 'a' || ('b' || 'c') AS v", ⟨.text, false⟩),
    ("SELECT CAST('a' AS BYTEA) || 'b' AS v", ⟨.bytea, false⟩),
    ("SELECT 'a' || CAST('b' AS BYTEA) AS v", ⟨.bytea, false⟩),
    ("SELECT CAST('a' AS BYTEA) || CAST('b' AS BYTEA) AS v", ⟨.bytea, false⟩),
    ("SELECT CAST('a' AS TEXT) || CAST('b' AS BYTEA) AS v", ⟨.text, false⟩),
    ("SELECT CAST('{}' AS JSONB) || '{}' AS v", ⟨.jsonb, false⟩),
    ("SELECT '{}' || CAST('{}' AS JSONB) AS v", ⟨.jsonb, false⟩),
    ("SELECT CAST('{}' AS JSONB) || CAST('{}' AS TEXT) AS v", ⟨.text, false⟩),
    ("SELECT CAST('{}' AS TEXT) || CAST('{}' AS JSONB) AS v", ⟨.text, false⟩),
    ("SELECT CAST('{}' AS JSONB) || NULL AS v", ⟨.jsonb, true⟩),
    ("SELECT CAST('null' AS JSONB) || CAST('{}' AS JSONB) AS v", ⟨.jsonb, false⟩),
    ("SELECT CAST('{}' AS JSON) || 'x' AS v", ⟨.text, false⟩),
    ("SELECT CAST('{}' AS JSON) || CAST('x' AS TEXT) AS v", ⟨.text, false⟩),
    ("SELECT CAST(ARRAY[1,2] AS TEXT) || 'x' AS v", ⟨.text, false⟩),
    ("SELECT CAST('{}' AS JSONB) || 'invalid JSON' AS v", ⟨.jsonb, false⟩),
    ("SELECT COALESCE(NULL::TEXT || 'x','fallback') AS v", ⟨.text, false⟩),
    ("SELECT CASE WHEN TRUE THEN 'x' || 1 ELSE 'y' END AS v", ⟨.text, false⟩),
    ("SELECT d.a || d.b AS v FROM (SELECT 1 AS a,'x' AS b) d", ⟨.text, false⟩),
    ("SELECT DISTINCT 'a' || 'b' AS v ORDER BY v", ⟨.text, false⟩),
    ("SELECT 'a' || 'b' = 'ab' AS v", ⟨.bool, false⟩),
    ("SELECT 'abc' LIKE 'a' || '%' AS v", ⟨.bool, false⟩)]
  for (sql, expected) in examples do
    SQLean.Tests.assert ((← concatOutput sql) == [⟨"v", expected⟩]) s!"concat expression: {sql}"
    count := count + 1
  SQLean.Tests.assert ((← concatOutput "SELECT 'a' || 'b'") ==
    [⟨"?column?", ⟨.text, false⟩⟩]) "concat default label must not inherit either operand"
  count := count + 1
  for sql in [
      "SELECT 1 || 2", "SELECT TRUE || FALSE", "SELECT 1 || TRUE",
      "SELECT '{}'::JSON || '{}'::JSON", "SELECT '{}'::JSONB || 1",
      "SELECT '{}'::JSON || '{}'::JSONB", "SELECT 'a'::BYTEA || 1",
      "SELECT 'a'::BYTEA || '{}'::JSONB", "SELECT DATE '2024-01-01' || DATE '2024-01-02'"] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV29 [] [] query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError s!"expected Invalid concat operands: {sql}")
    count := count + 1
  for (sql, element) in [
      ("SELECT ARRAY[1] || ARRAY[2]", SelectContract.ScalarType.int32),
      ("SELECT ARRAY[1] || 2", .int32), ("SELECT 1 || ARRAY[2]", .int32),
      ("SELECT ARRAY[1] || NULL", .int32), ("SELECT NULL || ARRAY[1]", .int32),
      ("SELECT ARRAY[1] || '{2}'", .int32), ("SELECT '{1}' || ARRAY[2]", .int32),
      ("SELECT 'x'::TEXT || ARRAY['y']", .text),
      ("SELECT ARRAY['x'] || 'y'::TEXT", .text)] do
    SQLean.Tests.assert ((← concatOutput sql) == [⟨"?column?", ⟨element.asArray, false⟩⟩])
      s!"promoted array concatenation exact output: {sql}"
    count := count + 1
  for sql in [
      "SELECT ROW(1,2) || 'x'", "SELECT 'x' || ROW(1,2)",
      "SELECT (SELECT 'x') || 'y'", "SELECT 'x' || unknown_function()"] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV29 [] [] query with
    | .error (.unsupported _) => pure ()
    | _ => throw (IO.userError s!"expected Unsupported concat context: {sql}")
    count := count + 1
  for (sql, declarations) in [
      ("SELECT ? || (? || ?) AS v", "text,int,text"),
      ("SELECT $2 || $1 || $2 AS v", "int,text"),
      ("SELECT ? || d.v AS v FROM (SELECT ? || ? AS v) d WHERE ? || ? = 'ab'",
        "text,text,text,text,text")] do
    SQLean.Tests.assert ((← concatOutput sql declarations) == [⟨"v", ⟨.text, false⟩⟩])
      s!"concat lexical parameter order: {sql}"
    count := count + 1
  let params ← expectOk "concat parameters" (Assurance.parseContractParameterTypes "text,text")
  let bad : Advanced.Query := { body := .select { items := [
    .expression (.concat (.parameter (.anonymous 2)) (.parameter (.anonymous 1)))] } }
  match SelectContract.checkQuery .basicV29 [] params bad with
  | .error (.invalid _) => pure ()
  | _ => throw (IO.userError "concat swapped anonymous ordinals must be Invalid")
  count := count + 1
  let query ← expectOk "concat exhaustion" (Advanced.parseQuery "SELECT 'a' || ('b' || 'c')")
  match SelectContract.checkQuery .basicV29 [] [] query 1 with
  | .error (.inconclusive _) => pure ()
  | _ => throw (IO.userError "concat exhaustion must be Inconclusive")
  count := count + 1
  pure count

def concatenationCorpusTests : IO Nat := do
  let json ← expectOk "concatenation fixture JSON"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/concatenation/synthetic.json"))
  let records ← expectOk "concatenation fixture records" json.getArr?
  SQLean.Tests.assert (records.size == 50) "expected exactly 50 concatenation synthetic queries"
  let mut ids : List String := []
  let mut statements : List String := []
  for record in records do
    let id ← concatField "concatenation fixture" record "id"
    let sql ← concatField id record "sql"
    SQLean.Tests.assert ((← concatField id record "source_kind") == "synthetic") s!"{id}: population"
    let params ← concatField id record "parameter_types"
    let expected ← expectOk id ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
    let expected ← expected.toList.mapM fun column => do
      let name ← concatField id column "name"
      let type ← concatField id column "type"
      let nullable ← expectOk id ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
      pure (name, type, nullable)
    let actual ← concatOutput sql params
    let labels := actual.map fun column =>
      let type := match column.type.base with
        | .bool => "bool"
        | .int32 => "int32"
        | .text => "text"
        | base => (base.dataType.toSql.toLower).replace ", " ","
      (column.name, type, column.type.nullable)
    SQLean.Tests.assert (labels == expected)
      s!"{id}: exact concatenation output {reprStr labels}; expected {reprStr expected}"
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (decide ids.Nodup && decide statements.Nodup)
    "duplicate concatenation corpus identities or SQL"
  pure records.size

end SQLean.Tests
