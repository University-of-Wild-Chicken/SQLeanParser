import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

/-! One hundred fixed source-free SELECTs with independently authored concrete type,
modifier, nullability, and parameter declarations. Each obtains a complete
basic SELECT derivation and exact identity/PostgreSQL render certificates.
Runtime values and PostgreSQL's native output types are checked separately by
the native corpus runner; these tests do not imply execution success. -/
namespace SQLean.Tests

private def scalarLabel : SelectContract.ScalarType → String
  | .int32 => "int32"
  | .text => "text"
  | .bool => "bool"
  | type => (type.dataType.toSql.toLower).replace ", " ","

private def field (label : String) (record : Lean.Json) (name : String) : IO String :=
  expectOk s!"{label}: {name}" ((record.getObjVal? name) >>= Lean.Json.getStr?)

private def signatureFixtureTests : IO Unit := do
  let source ← IO.FS.readFile "fixtures/functions/signatures.json"
  let json ← expectOk "function signature JSON" (Lean.Json.parse source)
  let records ← expectOk "function signature array" json.getArr?
  let actual ← records.toList.mapM fun record => do
    let name ← field "signature" record "name"
    let inputs ← expectOk "signature inputs" ((record.getObjVal? "inputs") >>= Lean.Json.getArr?)
    let inputs ← inputs.toList.mapM fun input => expectOk "signature input" input.getStr?
    let output ← field "signature" record "output"
    pure (name, inputs, output)
  let label := fun type : SelectContract.ScalarType => type.dataType.toSql.toLower
  let expected := SelectContract.functionNames.flatMap fun name =>
    (SelectContract.functionCatalog name).map fun signature =>
      (name, signature.inputs.map label, label signature.output)
  SQLean.Tests.assert (actual.length == 84 && actual == expected)
    "native signature fixture differs from the normative function inventory"

private def scalarFormCategoryTests (category : String) : IO Nat := do
  let source ← IO.FS.readFile s!"fixtures/{category}/synthetic.json"
  let json ← expectOk "scalar form fixture JSON" (Lean.Json.parse source)
  let records ← expectOk "scalar form fixture array" json.getArr?
  SQLean.Tests.assert (records.size == 50) "expected exactly 50 scalar form examples"
  let mut ids : List String := []
  let mut statements : List String := []
  for record in records do
    let id ← field "scalar form record" record "id"
    let kind ← field id record "source_kind"
    SQLean.Tests.assert (kind == "synthetic") s!"{id}: unexpected source population"
    let sql ← field id record "sql"
    let parameterTypes ← field id record "parameter_types"
    let expectedType ← field id record "contract_type"
    let expectedNullable ← expectOk s!"{id}: nullable"
      ((record.getObjVal? "nullable") >>= Lean.Json.getBool?)
    let params ← expectOk s!"{id}: exact declarations"
      (Assurance.parseContractParameterTypes parameterTypes)
    let query ← expectOk s!"{id}: parse" (Advanced.parseQuery sql)
    let certificate ← expectOk s!"{id}: complete SELECT certificate"
      ((SelectContract.checkQuery .basicV23 [] params query).mapError reprStr)
    have _valid : SelectContract.SelectValid .basicV23 [] params query certificate.output :=
      certificate.valid
    have _preserved : SelectContract.SelectValid .basicV23 [] params
        (RenderContract.translateParameters query) certificate.output :=
      RenderContract.translateParameters_valid certificate.valid
    match certificate.output with
    | [column] =>
        SQLean.Tests.assert
          (column.name == "v" && scalarLabel column.type.base == expectedType &&
            column.type.nullable == expectedNullable)
          s!"{id}: incorrect exact output: {reprStr certificate.output}; expected {expectedType}"
    | _ => throw (IO.userError s!"{id}: expected one named scalar output")
    let identity ← expectOk s!"{id}: identity render certificate"
      ((RenderContract.check .identityV01 query).mapError reprStr)
    let postgres ← expectOk s!"{id}: PostgreSQL render certificate"
      ((RenderContract.check .postgres16V01 query).mapError reprStr)
    have _identityRoundTrip : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
    have _postgresRoundTrip :
        Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
      postgres.roundTrip
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (decide ids.Nodup) "duplicate scalar form fixture identity"
  SQLean.Tests.assert (decide statements.Nodup) "duplicate scalar form SQL fixture"
  pure records.size

/-- Both fixed factors must receive all 50 complete static certificates. -/
def scalarFormCorpusTests : IO Nat := do
  signatureFixtureTests
  let functions ← scalarFormCategoryTests "functions"
  let conditional ← scalarFormCategoryTests "conditional"
  pure (functions + conditional)

/-- Closed witnesses are kernel-checked independently of executable checking. -/
example : SelectContract.ExprValid [] .empty
    (.coalesce [.null, .literal (.int 1)]) (some ⟨.int32, false⟩) [] :=
  .coalesce (.cons .null (.cons (.int (by decide)) .nil)) (by decide)

example : SelectContract.ExprValid [] .empty
    (.call ["lower"] [.literal (.text "A")]) (some ⟨.text, false⟩) [] :=
  .call (.cons .text .nil) (by decide)

def scalarFormBoundaryTests : IO Nat := do
  let rejected := [
    "SELECT CURRENT_DATE", "SELECT CURRENT_TIME", "SELECT CURRENT_TIMESTAMP",
    "SELECT LOCALTIME", "SELECT LOCALTIMESTAMP", "SELECT CURRENT_USER",
    "SELECT SESSION_USER", "SELECT SYSTEM_USER", "SELECT CURRENT_ROLE",
    "SELECT CURRENT_CATALOG", "SELECT CURRENT_SCHEMA", "SELECT USER",
    "SELECT 1 ISNULL", "SELECT 1 NOTNULL", "SELECT * FROM ONLY t",
    "UPDATE ONLY t SET x = 1", "DELETE FROM ONLY t",
    "SELECT CASE END", "SELECT CASE WHEN TRUE THEN END", "SELECT CASE WHEN TRUE THEN 1",
    "SELECT COALESCE()", "SELECT GREATEST()", "SELECT LEAST()", "SELECT NULLIF(1)",
    "SELECT NULLIF(1, 2, 3)", "SELECT lower(,1)", "SELECT lower(1,)" ]
  for sql in rejected do
    expectError sql (Advanced.parse sql)
  let quoted := [
    "SELECT \"CURRENT_DATE\"", "SELECT 1 AS \"ISNULL\"", "SELECT 1 AS \"NOTNULL\"",
    "SELECT * FROM \"ONLY\"", "SELECT \"APP\".\"MyFn\"(1)", "SELECT \"coalesce\"(1)" ]
  for sql in quoted do
    let query ← expectOk sql (Advanced.parseQuery sql)
    let _ ← expectOk sql ((RenderContract.check .identityV01 query).mapError reprStr)
  let typed : List (String × SelectContract.ScalarType × Bool) := [
    ("NULLIF(1::numeric(4,2), 2::numeric(4,2))", .numeric [4,2], true),
    ("NULLIF('a'::char(3), 'b'::char(3))", .char [3], true),
    ("NULLIF(TIME(2) '12:00', TIME(2) '13:00')", .time [2], true),
    ("NULLIF(1, 2::real)", .doublePrecision, true),
    ("NULLIF(1::real, 2)", .real, true),
    ("COALESCE(1::numeric(4,2), 2::numeric(4,2))", .numeric [4,2], false),
    ("COALESCE(NULL, 1::numeric(4,2))", .numeric [], false),
    ("CASE WHEN TRUE THEN 1::numeric(4,2) END", .numeric [], true),
    ("CASE WHEN TRUE THEN 1::numeric(4,2) ELSE 2::numeric(4,2) END", .numeric [4,2], false),
    ("COALESCE(1, 2::real)", .real, false),
    ("CASE 'a' WHEN 'a' THEN 1 ELSE 2 END", .int32, false)]
  for (expression, base, nullable) in typed do
    let query ← expectOk expression (Advanced.parseQuery s!"SELECT {expression} AS v")
    let certificate ← expectOk expression
      ((SelectContract.checkQuery .basicV23 [] [] query).mapError reprStr)
    SQLean.Tests.assert (certificate.output == [⟨"v", ⟨base, nullable⟩⟩])
      s!"wrong conditional exact result: {expression}: {reprStr certificate.output}"
  let invalid := [
    "SELECT CASE NULL WHEN 1 THEN 2 ELSE 3 END",
    "SELECT CASE WHEN 1 THEN 2 END", "SELECT COALESCE(TRUE, 1)",
    "SELECT GREATEST(JSON '{}', JSON '{}')", "SELECT NULLIF(JSON '{}', JSON '{}')",
    "SELECT lower(1)", "SELECT abs(TRUE)", "SELECT concat()", "SELECT concat_ws(',')" ]
  for sql in invalid do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV23 [] [] query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError s!"expected independently invalid scalar form: {sql}")
  let parameterSql := "SELECT CASE WHEN ? THEN ? WHEN ? THEN ? ELSE ? END AS v"
  let params ← expectOk "CASE parameter declarations" (Assurance.parseContractParameterTypes "bool,int,bool,int,int")
  let query ← expectOk "CASE parameter order" (Advanced.parseQuery parameterSql)
  let certificate ← expectOk "CASE full parameter certificate"
    ((SelectContract.checkQuery .basicV23 [] params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let rendered ← expectOk "CASE ordered parameter rendering"
    ((RenderContract.check .postgres16V01 query).mapError reprStr)
  SQLean.Tests.assert
    (rendered.sql == "SELECT (CASE WHEN $1 THEN $2 WHEN $3 THEN $4 ELSE $5 END) AS \"v\";")
    "CASE renderer reordered WHEN/THEN/ELSE parameter occurrences"
  pure (rejected.length + quoted.length + typed.length + invalid.length + 1)

end SQLean.Tests
