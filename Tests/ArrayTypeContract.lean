import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.ContractSupport
import Lean.Data.Json

/-! Exact array declaration/cast/parameter checks. These certify static types,
not successful array-input conversion or constraints on element values/shapes. -/
namespace SQLean.Tests

private def arrayProjection (expr : Advanced.Expr) : Advanced.Query :=
  { body := .select { items := [.expression expr (some "v")] } }

private def arrayCertificate (query : Advanced.Query)
    (catalog : Advanced.Catalog := []) (params : SelectContract.ParameterEnv := []) :
    IO (List SelectContract.OutputColumn) := do
  let certificate ← expectOk "array SELECT certificate"
    ((SelectContract.checkQuery .basicV32 catalog params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let identity ← expectOk "array identity renderer"
    ((RenderContract.check .identityV01 query).mapError reprStr)
  let postgres ← expectOk "array PostgreSQL renderer"
    ((RenderContract.check .postgres16V01 query).mapError reprStr)
  have _identity : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
  have _postgres : Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
    postgres.roundTrip
  pure certificate.output

private def arraySqlOutput (sql : String) (params : SelectContract.ParameterEnv := []) :
    IO (List SelectContract.OutputColumn) := do
  arrayCertificate (← expectOk sql (Advanced.parseQuery sql)) [] params

/-- This kernel derivation preserves the exact declared rank/modifiers in its
environment while the parameter result has the PostgreSQL array OID type. -/
example : SelectContract.ExprValid
    [⟨1, ⟨.array (.array .numeric), [8, 2]⟩, false⟩]
    .empty (.parameter (.numbered 1))
    (some ⟨.array (.numeric []), false⟩) [.numbered 1] := by
  exact .parameter
    (binding := ⟨1, ⟨.array (.array .numeric), [8, 2]⟩, false⟩)
    (base := .array (.numeric [8, 2])) (by simp) rfl rfl

def arrayTypeContractTests : IO Nat := do
  let declarations : List (Advanced.DataType × SelectContract.ScalarType) := [
    (⟨.smallInt, []⟩, .smallInt), (⟨.int, []⟩, .int32), (⟨.bigInt, []⟩, .int64),
    (⟨.numeric, [8, 2]⟩, .numeric [8, 2]), (⟨.real, []⟩, .real),
    (⟨.doublePrecision, []⟩, .doublePrecision), (⟨.text, []⟩, .text),
    (⟨.varchar, [8]⟩, .varchar [8]), (⟨.char, []⟩, .char [1]),
    (⟨.char, [3]⟩, .char [3]), (⟨.bool, []⟩, .bool), (⟨.date, []⟩, .date),
    (⟨.time, [3]⟩, .time [3]), (⟨.timeTZ, [2]⟩, .timeTZ [2]),
    (⟨.timestamp, [4]⟩, .timestamp [4]), (⟨.timestampTZ, [6]⟩, .timestampTZ [6]),
    (⟨.interval, [2]⟩, .interval [2]), (⟨.uuid, []⟩, .uuid),
    (⟨.json, []⟩, .json), (⟨.jsonb, []⟩, .jsonb), (⟨.bytea, []⟩, .bytea)]
  let mut count := 0
  for (element, scalar) in declarations do
    for rank in [1, 2, 4] do
      let declaration : Advanced.DataType :=
        ⟨(List.range rank).foldl (fun typeName _ => .array typeName) element.name, element.modifiers⟩
      let catalog : Advanced.Catalog := [{
        name := "arrays", columns := [{ name := "v", type := declaration, nullable := some false }]
      }]
      let query : Advanced.Query := {
        body := .select { items := [.all], source := some (.table "arrays") }
      }
      let actual ← arrayCertificate query catalog
      SQLean.Tests.assert (sameOutputTypes actual [{name := "v", type := ⟨scalar.asArray, false⟩}])
        s!"array catalog loses exact element/modifier or retains declared rank: {reprStr declaration}"
      let params : SelectContract.ParameterEnv := [⟨1, declaration, true⟩]
      let actual ← arrayCertificate (arrayProjection (.parameter (.anonymous 1))) [] params
      SQLean.Tests.assert (sameOutputTypes actual [{name := "v", type := ⟨scalar.unmodified.asArray, true⟩}])
        s!"array parameter must discard typmods: {reprStr declaration}"
      let actual ← arrayCertificate (arrayProjection (.cast .null declaration))
      SQLean.Tests.assert (sameOutputTypes actual [{name := "v", type := ⟨scalar.asArray, true⟩}])
        s!"array cast loses element modifiers: {reprStr declaration}"
      count := count + 3
  let exact : List (String × SelectContract.ExactType) := [
    ("SELECT '{1,NULL}'::INTEGER[] AS v", ⟨.array .int32, false⟩),
    ("SELECT CAST(NULL AS INTEGER[][]) AS v", ⟨.array .int32, true⟩),
    ("SELECT CAST('{null,1}'::JSONB[] AS INTEGER[]) AS v", ⟨.array .int32, false⟩),
    ("SELECT CAST('{1,2}'::INTEGER[] AS NUMERIC(8,2)[]) AS v", ⟨.array (.numeric [8,2]), false⟩),
    ("SELECT CAST('{1,2}'::TEXT[] AS INTEGER[]) AS v", ⟨.array .int32, false⟩),
    ("SELECT CAST('{1,2}'::INTEGER[] AS TEXT) AS v", ⟨.text, false⟩),
    ("SELECT CAST('{true,false}'::BOOLEAN[] AS INTEGER[]) AS v", ⟨.array .int32, false⟩),
    ("SELECT COALESCE(NULL::INTEGER[], '{1}'::BIGINT[]) AS v", ⟨.array .int64, false⟩),
    ("SELECT GREATEST(NULL::INTEGER[], '{1}'::BIGINT[]) AS v", ⟨.array .int64, false⟩),
    ("SELECT LEAST('{1}'::SMALLINT[], '{2}'::NUMERIC(8,2)[]) AS v", ⟨.array (.numeric []), false⟩),
    ("SELECT COALESCE(NULL::NUMERIC(8,2)[], '{1}'::NUMERIC(8,2)[]) AS v",
      ⟨.array (.numeric [8,2]), false⟩),
    ("SELECT COALESCE(NULL::JSON[], '{null}'::JSON[]) AS v", ⟨.array .json, false⟩),
    ("SELECT NULLIF('{1}'::NUMERIC(8,2)[], '{2}'::NUMERIC(8,2)[]) AS v",
      ⟨.array (.numeric [8,2]), true⟩),
    ("SELECT CASE '{1}'::INTEGER[] WHEN '{1}'::INTEGER[] THEN 1 ELSE 0 END AS v", ⟨.int32, false⟩),
    ("SELECT CASE WHEN TRUE THEN '{1}'::INTEGER[] ELSE '{2}'::BIGINT[] END AS v",
      ⟨.array .int64, false⟩),
    ("SELECT '{1,NULL}'::INTEGER[] = '{1,NULL}'::INTEGER[][] AS v", ⟨.bool, false⟩),
    ("SELECT NULL::INTEGER[] < '{1}'::INTEGER[] AS v", ⟨.bool, true⟩),
    ("SELECT '{1,NULL}'::INTEGER[] IS NULL AS v", ⟨.bool, false⟩),
    ("SELECT '{1}'::INTEGER[] IN ('{1}'::INTEGER[], '{2}'::INTEGER[]) AS v", ⟨.bool, false⟩),
    ("SELECT '{1}'::INTEGER[] BETWEEN '{0}'::INTEGER[] AND '{2}'::INTEGER[] AS v", ⟨.bool, false⟩),
    ("SELECT DISTINCT '{1}'::INTEGER[] AS v ORDER BY v", ⟨.array .int32, false⟩),
    ("SELECT '{1}'::JSONB[] AS v ORDER BY 1", ⟨.array .jsonb, false⟩)]
  for (sql, expected) in exact do
    let actual ← arraySqlOutput sql
    SQLean.Tests.assert (sameOutputTypes actual [{name := "v", type := expected}]) s!"array exact output: {sql}: {reprStr actual}"
    count := count + 1
  let invalid := [
    "SELECT '{1}'::INTEGER[] = '{1}'::BIGINT[]",
    "SELECT '{1}'::INTEGER[] < '{1}'::NUMERIC[]",
    "SELECT NULLIF('{1}'::INTEGER[], '{1}'::BIGINT[])",
    "SELECT '{a}'::TEXT[] = '{a}'::VARCHAR[]",
    "SELECT '{1}'::INTEGER[] + '{1}'::INTEGER[]",
    "SELECT CAST('{true}'::BOOLEAN[] AS BIGINT[])",
    "SELECT CAST('{1}'::INTEGER[] AS JSONB[])",
    "SELECT CAST('{1}'::INTEGER[] AS JSONB)",
    "SELECT CAST(1 AS INTEGER[])",
    "SELECT COALESCE('{1}'::INTEGER[], 1)",
    "SELECT '{1}'::INTEGER[] IN ('{1}'::BIGINT[])",
    "SELECT 1 LIMIT '{1}'::INTEGER[]",
    "SELECT 1 WHERE '{true}'::BOOLEAN[]",
    "SELECT '{null}'::JSON[] AND TRUE",
    "SELECT CASE WHEN '{null}'::JSON[] THEN 1 ELSE 0 END",
    "SELECT * FROM (SELECT '{1}'::INTEGER[] AS id) l JOIN (SELECT '{1}'::BIGINT[] AS id) r USING (id)"]
  for sql in invalid do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV32 [] [] query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError s!"expected Invalid array type use: {sql}")
    count := count + 1
  let unsupported := [
    "SELECT '{null}'::JSON[] = '{null}'::JSON[]",
    "SELECT DISTINCT '{null}'::JSON[]",
    "SELECT '{null}'::JSON[] AS v ORDER BY v",
    "SELECT '{null}'::JSON[] AS v ORDER BY 1",
    "SELECT 1 ORDER BY '{null}'::JSON[]",
    "SELECT GREATEST('{null}'::JSON[], '{null}'::JSON[])",
    "SELECT LEAST('{null}'::JSON[], '{null}'::JSON[])",
    "SELECT NULLIF('{null}'::JSON[], '{null}'::JSON[])",
    "SELECT '{null}'::JSON[] IN ('{null}'::JSON[])",
    "SELECT '{null}'::JSON[] BETWEEN '{null}'::JSON[] AND '{null}'::JSON[]",
    "SELECT CASE '{null}'::JSON[] WHEN '{null}'::JSON[] THEN 1 END",
    "SELECT * FROM (SELECT '{null}'::JSON[] AS id) l JOIN (SELECT '{null}'::JSON[] AS id) r USING (id)",
    "SELECT '{1}'::INTEGER[] = '{1}'",
    "SELECT array_length('{1}'::INTEGER[], 1)"]
  for sql in unsupported do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV32 [] [] query with
    | .error (.unsupported _) => pure ()
    | _ => throw (IO.userError s!"expected Unsupported array boundary: {sql}")
    count := count + 1
  let malformedTypes : List Advanced.DataType := [
      ⟨.array .int, [2]⟩, ⟨.array .numeric, [0]⟩, ⟨.array (.array .varchar), [0]⟩,
      ⟨.array .timestamp, [7]⟩, ⟨.array .jsonb, [1]⟩]
  for malformed in malformedTypes do
    let query := arrayProjection (.cast .null malformed)
    match SelectContract.checkQuery .basicV32 [] [] query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError s!"array element modifiers must be checked: {reprStr malformed}")
    count := count + 1
  pure count

private def arrayField (id : String) (record : Lean.Json) (name : String) : IO String :=
  expectOk s!"{id}: {name}" ((record.getObjVal? name) >>= Lean.Json.getStr?)

def arrayTypeCorpusTests : IO Nat := do
  let json ← expectOk "array type fixture JSON"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/array_types/synthetic.json"))
  let records ← expectOk "array type fixture records" json.getArr?
  SQLean.Tests.assert (records.size == 50) "expected exactly 50 array type synthetic queries"
  let mut ids : List String := []
  let mut statements : List String := []
  for record in records do
    let id ← arrayField "array type fixture" record "id"
    let sql ← arrayField id record "sql"
    SQLean.Tests.assert ((← arrayField id record "source_kind") == "synthetic") s!"{id}: population"
    let params ← expectOk id
      (Assurance.parseContractParameterTypes (← arrayField id record "parameter_types"))
    let expected ← expectOk id ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
    let expected ← expected.toList.mapM fun column => do
      let name ← arrayField id column "name"
      let type ← arrayField id column "type"
      let nullable ← expectOk id ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
      pure (name, type, nullable)
    let actual ← arraySqlOutput sql params
    let labels := actual.map fun column =>
      let type := match column.type.base with
        | .bool => "bool"
        | base => (base.dataType.toSql.toLower).replace ", " ","
      (column.name, type, column.type.nullable)
    SQLean.Tests.assert (labels == expected) s!"{id}: exact array output {reprStr labels}; expected {reprStr expected}"
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (decide ids.Nodup && decide statements.Nodup) "duplicate array corpus identities or SQL"
  pure records.size

end SQLean.Tests
