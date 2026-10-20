import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

namespace SQLean.Tests

/-- Empty arrays have no inferred type, independently of checker execution. -/
example (params : SelectContract.ParameterEnv) (scope : SelectContract.Scope)
    (type : SelectContract.ExprType) (uses : List Advanced.Parameter) :
    ¬ SelectContract.ExprValid params scope (.array []) type uses := by
  intro valid
  cases valid with
  | array args signature =>
    cases args
    simp [SelectContract.arraySignature, SelectContract.scalarInputs] at signature

/-- A direct declared target supplies an empty constructor's type. -/
example : SelectContract.ExprValid [] .empty
    (.cast (.array []) ⟨.array .int, []⟩)
    (some ⟨.array .int32, false⟩) [] :=
  .castArray (.targeted .nil rfl) rfl (by decide)

/-- NULL elements remain distinct from NULL array objects. -/
example : SelectContract.ExprValid [] .empty (.array [.null])
    (some ⟨.array .text, false⟩) [] :=
  .array (.cons .null .nil) rfl

/-- The generic cast rule cannot bypass direct constructor coercion. -/
example : ¬ SelectContract.OrdinaryCast (.array [.literal (.int 1)]) ⟨.array .int, []⟩ := by
  decide

private def constructorOutput (sql : String) (parameterTypes : String := "") :
    IO (List SelectContract.OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let params ← expectOk sql (Assurance.parseContractParameterTypes parameterTypes)
  let certificate ← expectOk sql
    ((SelectContract.checkQuery .basicV27 [] params query).mapError reprStr)
  have _valid := certificate.valid
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let identity ← expectOk sql ((RenderContract.check .identityV01 query).mapError reprStr)
  let postgres ← expectOk sql ((RenderContract.check .postgres16V01 query).mapError reprStr)
  have _identity : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
  have _postgres : Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
    postgres.roundTrip
  pure certificate.output

def arrayConstructorContractTests : IO Nat := do
  let exact : List (String × SelectContract.ScalarType) := [
    ("ARRAY[1,2,3]", .array .int32),
    ("ARRAY[NULL]", .array .text),
    ("ARRAY[NULL,NULL]", .array .text),
    ("ARRAY['a',NULL]", .array .text),
    ("ARRAY[1,2::BIGINT]", .array .int64),
    ("ARRAY[1,2.0]", .array (.numeric [])),
    ("ARRAY[1,2::REAL]", .array .real),
    ("ARRAY[1::REAL,2::DOUBLE PRECISION]", .array .doublePrecision),
    ("ARRAY[TRUE,NULL]", .array .bool),
    ("ARRAY['true',FALSE]", .array .bool),
    ("ARRAY[1::NUMERIC(8,2),2::NUMERIC(8,2)]", .array (.numeric [8,2])),
    ("ARRAY[1::NUMERIC(8,2),2::NUMERIC(9,3)]", .array (.numeric [])),
    ("ARRAY[1::NUMERIC(8,2),NULL]", .array (.numeric [])),
    ("ARRAY['a'::VARCHAR(5),'b'::VARCHAR(5)]", .array (.varchar [5])),
    ("ARRAY['a'::VARCHAR(5),'b']", .array (.varchar [])),
    ("ARRAY[DATE '2024-01-01',TIMESTAMP '2024-01-01 12:00']", .array (.timestamp [])),
    ("ARRAY[[1,2],[3,4]]", .array .int32),
    ("ARRAY[ARRAY[1],ARRAY[2]]", .array .int32),
    ("ARRAY[ARRAY[NULL]]", .array .text),
    ("ARRAY[ARRAY[1]::BIGINT[],ARRAY[2]]", .array .int64),
    ("ARRAY[ARRAY[1],'{2}']", .array .int32),
    ("ARRAY[]::INTEGER[]", .array .int32),
    ("ARRAY[[]]::INTEGER[]", .array .int32),
    ("ARRAY[[],[]]::INTEGER[]", .array .int32),
    ("ARRAY[[[[]]]]::NUMERIC(8,2)[]", .array (.numeric [8,2])),
    ("ARRAY[TRUE,2]::INTEGER[]", .array .int32),
    ("ARRAY[1,2.7]::INTEGER[]", .array .int32),
    ("ARRAY[['1'],['2']]::INTEGER[]", .array .int32),
    ("ARRAY[NULL]::JSON[]", .array .json),
    ("ARRAY[ARRAY[1],'{2}'::TEXT]::INTEGER[]", .array .int32),
    ("ARRAY[1::NUMERIC(8,2)]::NUMERIC[]", .array (.numeric [])),
    ("CAST(ARRAY[1] AS TEXT)", .text),
    ("CAST(CAST(ARRAY[] AS INTEGER[]) AS BIGINT[])", .array .int64),
    ("ARRAY[ARRAY[]::INTEGER[],ARRAY[]::INTEGER[]]", .array .int32),
    ("ARRAY[ARRAY[]::TEXT[]]::INTEGER[]", .array .int32),
    ("ARRAY[COALESCE(ARRAY[DATE '2024-01-01',TIMESTAMP '2024-01-01 12:00'])]::TIME[]",
      .array (.time []))]
  let mut count := 0
  for (expr, base) in exact do
    let actual ← constructorOutput s!"SELECT {expr}"
    SQLean.Tests.assert (actual == [⟨"array", ⟨base, false⟩⟩])
      s!"constructor exact type/default label: {expr}: {reprStr actual}"
    count := count + 1
  -- These have valid static typing; PostgreSQL can reject their runtime shape.
  for expr in [
      "ARRAY[[1],[2,3]]", "ARRAY[ARRAY[1],NULL]",
      "ARRAY[ARRAY[],ARRAY[1]]::INTEGER[]"] do
    let actual ← constructorOutput s!"SELECT {expr} AS v"
    SQLean.Tests.assert (actual == [⟨"v", ⟨.array .int32, false⟩⟩])
      s!"runtime shape must not be confused with static type validity: {expr}"
    count := count + 1
  let invalid := [
    "SELECT ARRAY[]",
    "SELECT ARRAY[[]]",
    "SELECT ARRAY[ARRAY[],ARRAY[1]]",
    "SELECT COALESCE(ARRAY[],ARRAY[1])",
    "SELECT ARRAY[COALESCE(ARRAY[],ARRAY[1])]::INTEGER[]",
    "SELECT ARRAY[ARRAY[],ARRAY[]::INTEGER[]]",
    "SELECT ARRAY[]::TEXT",
    "SELECT ARRAY[1,TRUE]",
    "SELECT ARRAY[1,'x'::TEXT]",
    "SELECT ARRAY[ARRAY[1],2]",
    "SELECT ARRAY[ARRAY[1],2]::INTEGER[]",
    "SELECT ARRAY[1::BIGINT]::BOOLEAN[]",
    "SELECT ARRAY[DATE '2024-01-01',TIMESTAMP '2024-01-01 12:00']::TIME[]",
    "SELECT ARRAY[ARRAY[DATE '2024-01-01'],ARRAY[TIMESTAMP '2024-01-01 12:00']]::TIME[]",
    "SELECT ARRAY[1] = ARRAY[1::BIGINT]",
    "SELECT ARRAY[1]::JSONB[]",
    "SELECT 1 WHERE ARRAY[TRUE]",
    "SELECT ARRAY[1] LIMIT ARRAY[1]",
    "SELECT ARRAY[COUNT(*)] FOR UPDATE"]
  for sql in invalid do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV27 [] [] query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError s!"expected Invalid constructor query: {sql}")
    count := count + 1
  let unsupported := [
    "SELECT ARRAY[NULL::JSON] = ARRAY[NULL::JSON]",
    "SELECT DISTINCT ARRAY[NULL::JSON]",
    "SELECT array_length(ARRAY[1],1)",
    "SELECT ARRAY[(SELECT 1)]",
    "SELECT ARRAY[COUNT(*)]"]
  for sql in unsupported do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV27 [] [] query with
    | .error (.unsupported _) => pure ()
    | _ => throw (IO.userError s!"expected Unsupported constructor boundary: {sql}")
    count := count + 1
  let paramsCases : List (String × String × SelectContract.ScalarType) := [
    ("SELECT ARRAY[?,NULL] AS v", "int?", .array .int32),
    ("SELECT ARRAY[[$1,$2],[$2,$1]] AS v", "int,bigint", .array .int64),
    ("SELECT ARRAY[ARRAY[?],ARRAY[?]]::BIGINT[] AS v", "int,int?", .array .int64),
    ("SELECT ARRAY[$1,NULL] AS v", "numeric(8,2)", .array (.numeric [])),
    ("SELECT ARRAY[$1,$2] AS v", "integer[],integer[]?", .array .int32)]
  for (sql, params, base) in paramsCases do
    let actual ← constructorOutput sql params
    SQLean.Tests.assert (actual == [⟨"v", ⟨base, false⟩⟩]) s!"constructor parameters: {sql}"
    count := count + 1
  let sql := "SELECT ARRAY[[?,?],[?,?]] AS v, ? AS trailing_value"
  let query ← expectOk sql (Advanced.parseQuery sql)
  let params ← expectOk sql (Assurance.parseContractParameterTypes "int,int,int,int,text")
  let certificate ← expectOk sql
    ((SelectContract.checkQuery .basicV27 [] params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  SQLean.Tests.assert (Advanced.queryParameters 1024 query ==
      (List.range 5).map (fun n => .anonymous (n + 1)))
    "nested constructors must retain lexical parameter order"
  count := count + 1
  let bad : Advanced.Query := { body := .select { items := [
    .expression (.array [.parameter (.anonymous 2), .parameter (.anonymous 1)])] } }
  match SelectContract.checkQuery .basicV27 [] params bad with
  | .error (.invalid _) => pure ()
  | _ => throw (IO.userError "manual reordered constructor parameters must be Invalid")
  count := count + 1
  match SelectContract.checkQuery .basicV27 [] params query 2 with
  | .error (.inconclusive _) => pure ()
  | _ => throw (IO.userError "constructor budget exhaustion must be Inconclusive")
  count := count + 1
  pure count

private def constructorField (id : String) (record : Lean.Json) (name : String) : IO String :=
  expectOk s!"{id}: {name}" ((record.getObjVal? name) >>= Lean.Json.getStr?)

def arrayConstructorCorpusTests : IO Nat := do
  let json ← expectOk "array constructor fixture JSON"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/array_constructors/synthetic.json"))
  let records ← expectOk "array constructor fixture records" json.getArr?
  SQLean.Tests.assert (records.size == 50) "expected exactly 50 array constructor synthetic queries"
  let mut ids : List String := []
  let mut statements : List String := []
  for record in records do
    let id ← constructorField "array constructor fixture" record "id"
    let sql ← constructorField id record "sql"
    SQLean.Tests.assert ((← constructorField id record "source_kind") == "synthetic") s!"{id}: population"
    let params ← constructorField id record "parameter_types"
    let expected ← expectOk id ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
    let expected ← expected.toList.mapM fun column => do
      let name ← constructorField id column "name"
      let type ← constructorField id column "type"
      let nullable ← expectOk id ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
      pure (name, type, nullable)
    let actual ← constructorOutput sql params
    let labels := actual.map fun column =>
      let type := match column.type.base with
        | .bool => "bool"
        | .int32 => "int32"
        | .text => "text"
        | base => (base.dataType.toSql.toLower).replace ", " ","
      (column.name, type, column.type.nullable)
    SQLean.Tests.assert (labels == expected)
      s!"{id}: exact constructor output {reprStr labels}; expected {reprStr expected}"
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (decide ids.Nodup && decide statements.Nodup)
    "duplicate array constructor corpus identities or SQL"
  pure records.size

end SQLean.Tests
