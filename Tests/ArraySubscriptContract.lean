import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

namespace SQLean.Tests

/-- Extraction is nullable even when the array and index are nonnullable. -/
example : SelectContract.ExprValid [] .empty
    (.subscript (.array [.literal (.int 7)]) [.index (.literal (.int 1))])
    (some ⟨.int32, true⟩) [] :=
  .subscript (.array (.cons (.int (by decide)) .nil) rfl)
    (.index (.int (by decide)) rfl .nil) (by decide) (by decide)

/-- Omitted slice endpoints need neither fabricated expressions nor uses. -/
example : SelectContract.ExprValid [] .empty
    (.subscript (.array [.literal (.int 7)]) [.slice none none])
    (some ⟨.array .int32, true⟩) [] :=
  .subscript (.array (.cons (.int (by decide)) .nil) rfl)
    (.slice .absent .absent rfl rfl .nil) (by decide) (by decide)

example : SelectContract.subscriptBoundSignature (.known ⟨.numeric [6, 2], false⟩) = true := rfl
example : SelectContract.subscriptBoundSignature (.known ⟨.text, false⟩) = false := rfl
example : SelectContract.subscriptBoundSignature (.unknown false) = true := rfl

/-- An empty raw group cannot acquire validity through the extraction rule. -/
example (params : SelectContract.ParameterEnv) (scope : SelectContract.Scope)
    (base : Advanced.Expr) (type : SelectContract.ExprType) (uses : List Advanced.Parameter) :
    ¬ SelectContract.ExprValid params scope (.subscript base []) type uses := by
  intro valid
  cases valid with
  | subscript _ _ nonempty _ => exact nonempty rfl

private def subscriptCertificate (query : Advanced.Query)
    (params : SelectContract.ParameterEnv := []) :
    IO (List SelectContract.OutputColumn) := do
  let certificate ← expectOk "array subscript SELECT"
    ((SelectContract.checkQuery .basicV19 [] params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let identity ← expectOk "array subscript identity renderer"
    ((RenderContract.check .identityV01 query).mapError reprStr)
  let postgres ← expectOk "array subscript PostgreSQL renderer"
    ((RenderContract.check .postgres16V01 query).mapError reprStr)
  have _identity : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
  have _postgres : Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
    postgres.roundTrip
  pure certificate.output

private def subscriptOutput (sql : String) (parameterTypes : String := "") :
    IO (List SelectContract.OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let params ← expectOk sql (Assurance.parseContractParameterTypes parameterTypes)
  subscriptCertificate query params

private def subscriptLabelTests : IO Nat := do
  -- Authored names independently observed through PostgreSQL result descriptors.
  -- FLOAT is an explicit pre-existing syntax exclusion; FLOAT4/FLOAT8 are covered.
  let types := [
    ("SMALLINT", "int2"), ("INT2", "int2"), ("INT", "int4"), ("INTEGER", "int4"),
    ("INT4", "int4"), ("BIGINT", "int8"), ("INT8", "int8"), ("TEXT", "text"),
    ("VARCHAR(5)", "varchar"), ("CHARACTER VARYING(5)", "varchar"),
    ("CHAR(5)", "bpchar"), ("CHARACTER(5)", "bpchar"), ("BOOL", "bool"), ("BOOLEAN", "bool"),
    ("REAL", "float4"), ("FLOAT4", "float4"), ("DOUBLE PRECISION", "float8"), ("FLOAT8", "float8"),
    ("NUMERIC(6,2)", "numeric"), ("DECIMAL(6,2)", "numeric"), ("DATE", "date"),
    ("TIME(2)", "time"), ("TIME(2) WITHOUT TIME ZONE", "time"), ("TIME(2) WITH TIME ZONE", "timetz"),
    ("TIMETZ(2)", "timetz"), ("TIMESTAMP(3)", "timestamp"),
    ("TIMESTAMP(3) WITHOUT TIME ZONE", "timestamp"), ("TIMESTAMP(3) WITH TIME ZONE", "timestamptz"),
    ("TIMESTAMPTZ(3)", "timestamptz"), ("INTERVAL(2)", "interval"),
    ("UUID", "uuid"), ("JSON", "json"), ("JSONB", "jsonb"), ("BYTEA", "bytea")]
  let mut count := 0
  for (type, name) in types do
    for sql in [s!"SELECT NULL::{type}", s!"SELECT (NULL::{type}[])[1]"] do
      let actual ← subscriptOutput sql
      SQLean.Tests.assert (actual.map (·.name) == [name]) s!"cast/subscript default name: {sql}"
      count := count + 1
  let inherited := [
    ("SELECT (CAST(NULL::INTEGER AS NUMERIC))", "numeric"),
    ("SELECT (CAST(ARRAY[1,2] AS BIGINT[]))[1]", "array"),
    ("SELECT (CAST(ARRAY[1,2] AS BIGINT[]))[1:2]", "array"),
    ("SELECT (COALESCE(ARRAY[1],ARRAY[2]))[1]", "coalesce"),
    ("SELECT a::BIGINT FROM (SELECT 1 AS a) d", "a"),
    ("SELECT (a::BIGINT[])[1] FROM (SELECT ARRAY[1] AS a) d", "a"),
    ("SELECT CASE WHEN TRUE THEN 1 ELSE 2 END", "case"),
    ("SELECT CASE WHEN TRUE THEN 1 ELSE a END FROM (SELECT 2 AS a) d", "a"),
    ("SELECT (CASE WHEN TRUE THEN ARRAY[1] ELSE a END)[1] FROM (SELECT ARRAY[2] AS a) d", "a"),
    ("SELECT CASE WHEN TRUE THEN 1 ELSE 2::BIGINT END", "case"),
    ("SELECT (CASE WHEN TRUE THEN 1 ELSE 2 END)::BIGINT", "int8"),
    ("SELECT (CASE WHEN TRUE THEN 1 ELSE a END)::BIGINT FROM (SELECT 2 AS a) d", "a"),
    ("SELECT CASE WHEN TRUE THEN ARRAY[1] ELSE ARRAY[2] END", "array"),
    ("SELECT (CASE WHEN TRUE THEN ARRAY[1] ELSE ARRAY[2] END)[1]", "array"),
    ("SELECT CASE WHEN TRUE THEN 1 ELSE COALESCE(2,3) END", "coalesce"),
    ("SELECT CASE WHEN TRUE THEN 1 ELSE CASE WHEN TRUE THEN 2 ELSE a END END FROM (SELECT 3 AS a) d", "a"),
    ("SELECT ((ARRAY[[1,2],[3,4]])[1:1])[1][2]", "array")]
  for (sql, name) in inherited do
    let actual ← subscriptOutput sql
    SQLean.Tests.assert (actual.map (·.name) == [name]) s!"inherited default name: {sql}"
    count := count + 1
  pure count

def arraySubscriptContractTests : IO Nat := do
  let mut count ← subscriptLabelTests
  let types := ["SMALLINT", "INTEGER", "BIGINT", "NUMERIC(6,2)", "REAL", "DOUBLE PRECISION",
    "TEXT", "VARCHAR(5)", "CHAR(5)", "BOOLEAN", "DATE", "TIME(2)", "TIME(2) WITH TIME ZONE",
    "TIMESTAMP(3)", "TIMESTAMP(3) WITH TIME ZONE", "INTERVAL(2)", "UUID", "JSON", "JSONB", "BYTEA"]
  for type in types do
    let declaration ← expectOk type (Advanced.parseDataType type)
    let base ← match SelectContract.concreteType declaration with
      | some type => pure type
      | none => throw (IO.userError s!"unsupported test declaration: {type}")
    for (suffix, expectedType) in [("[1]", base), ("[1:2]", base.asArray)] do
      let sql := s!"SELECT (NULL::{type}[]){suffix} AS v"
      let actual ← subscriptOutput sql
      SQLean.Tests.assert (actual == [⟨"v", ⟨expectedType, true⟩⟩])
        s!"subscript preserved exact element modifiers: {sql}: {reprStr actual}"
      count := count + 1
  let bounds := ["NULL", "'2'", "1::SMALLINT", "1::INTEGER", "1::BIGINT", "1.5::NUMERIC(6,2)",
    "1.5::REAL", "1.5::DOUBLE PRECISION", "-1", "0", "2147483648::BIGINT", "'bad'"]
  for bound in bounds do
    let sql := s!"SELECT (ARRAY[11,22,33])[{bound}] AS v"
    let actual ← subscriptOutput sql
    SQLean.Tests.assert (actual == [⟨"v", ⟨.int32, true⟩⟩]) s!"subscript bound conversion: {sql}"
    count := count + 1
  let shapes := [
    ("(ARRAY[1,2])[8]", false), ("(ARRAY[]::INTEGER[])[1]", false),
    ("(ARRAY[1,NULL])[2]", false), ("(ARRAY[[11,12],[21,22]])[1][2]", false),
    ("(ARRAY[[11,12],[21,22]])[1]", false), ("(ARRAY[[11,12],[21,22]])[1][1][1]", false),
    ("(ARRAY[[11,12],[21,22]])[1:1][2]", true), ("(ARRAY[[11,12],[21,22]])[2][1:1]", true),
    ("(ARRAY[[11,12],[21,22]])[:][2:]", true), ("(ARRAY[[11,12],[21,22]])[99][99:100]", true),
    ("(ARRAY[1,2])[:]", true), ("(ARRAY[1,2])[NULL:]", true), ("(ARRAY[1,2])[:NULL]", true),
    ("(ARRAY[1,2])[2:1]", true), ("(ARRAY[]::INTEGER[])[:]", true),
    ("((ARRAY[[11,12],[21,22]])[1:1])[1][2]", false),
    ("('[0:2]={11,22,33}'::INTEGER[])[0]", false),
    ("('[0:2]={11,22,33}'::INTEGER[])[0:1]", true)]
  for (expression, slice) in shapes do
    let actual ← subscriptOutput s!"SELECT {expression} AS v"
    let type := if slice then SelectContract.ScalarType.array .int32 else .int32
    SQLean.Tests.assert (actual == [⟨"v", ⟨type, true⟩⟩]) s!"grouped subscript type: {expression}"
    count := count + 1
  for dimensions in [1, 2, 3, 4, 5, 6] do
    let sql := "SELECT (ARRAY[1])" ++ String.join (List.replicate dimensions "[1]") ++ " AS v"
    let actual ← subscriptOutput sql
    SQLean.Tests.assert (actual == [⟨"v", ⟨.int32, true⟩⟩]) s!"admitted dimensions: {dimensions}"
    count := count + 1
  let invalid := [
    "SELECT (NULL)[1]", "SELECT ('{1,2}')[1]", "SELECT (1)[1]", "SELECT ('a'::TEXT)[1]",
    "SELECT ('a'::BYTEA)[1]", "SELECT ((ARRAY[[1,2],[3,4]])[1])[2]",
    "SELECT (ARRAY[1])[TRUE]", "SELECT (ARRAY[1])['1'::TEXT]",
    "SELECT (ARRAY[1])['1'::VARCHAR(5)]", "SELECT (ARRAY[1])['1'::CHAR(1)]",
    "SELECT (ARRAY[1])[DATE '2024-01-01']", "SELECT (ARRAY[1])['1'::JSONB]",
    "SELECT (ARRAY[1])[ARRAY[1]]", "SELECT (ARRAY[1])[TRUE:2]", "SELECT (ARRAY[1])[1:FALSE]"]
  for sql in invalid do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV19 [] [] query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError s!"expected Invalid subscript: {sql}")
    count := count + 1
  for sql in ["SELECT ('{}'::JSONB)[1]", "SELECT (ARRAY[1])[1][1][1][1][1][1][1]",
      "SELECT ((SELECT ARRAY[1]))[1]", "SELECT (unknown_array_function())[1]",
      "SELECT (ARRAY[1])[COUNT(*)]"] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV19 [] [] query with
    | .error (.unsupported _) => pure ()
    | _ => throw (IO.userError s!"expected Unsupported subscript: {sql}")
    count := count + 1
  let parameterCases := [
    ("SELECT ($1)[$2] AS v", "numeric(6,2)[],bigint", SelectContract.ScalarType.numeric []),
    ("SELECT ($1)[$2] AS v", "varchar(5)[],numeric", .varchar []),
    ("SELECT (CAST($1 AS NUMERIC(6,2)[]))[$2] AS v", "numeric[],integer", .numeric [6,2]),
    ("SELECT (CAST($1 AS VARCHAR(5)[]))[:$2] AS v", "varchar[],real", .array (.varchar [5])),
    ("SELECT (?)[?] AS v", "integer[],int", .int32)]
  for (sql, params, type) in parameterCases do
    let actual ← subscriptOutput sql params
    SQLean.Tests.assert (actual == [⟨"v", ⟨type, true⟩⟩]) s!"subscript parameter modifiers: {sql}"
    count := count + 1
  let sql := "SELECT (ARRAY[?,?])[?:?][?] AS v, (?)[?] AS w"
  let params ← expectOk sql (Assurance.parseContractParameterTypes "int,int,int,int,int,integer[],int")
  let query ← expectOk sql (Advanced.parseQuery sql)
  let _ ← subscriptCertificate query params
  SQLean.Tests.assert (Advanced.queryParameters 1024 query ==
    (List.range 7).map (fun n => .anonymous (n + 1))) "subscript lexical parameter order"
  count := count + 1
  let bad : Advanced.Query := { body := .select { items := [
    .expression (.subscript (.array [.parameter (.anonymous 2)])
      [.index (.parameter (.anonymous 1))])] } }
  match SelectContract.checkQuery .basicV19 [] params bad with
  | .error (.invalid _) => pure ()
  | _ => throw (IO.userError "manual reordered subscript parameters must be Invalid")
  count := count + 1
  let empty : Advanced.Query := { body := .select { items := [.expression (.subscript .null [])] } }
  match SelectContract.checkQuery .basicV19 [] [] empty with
  | .error (.invalid _) => pure ()
  | _ => throw (IO.userError "empty subscript group must be Invalid")
  count := count + 1
  match SelectContract.checkQuery .basicV19 [] params query 1 with
  | .error (.inconclusive _) => pure ()
  | _ => throw (IO.userError "subscript exhaustion must be Inconclusive")
  count := count + 1
  pure count

private def subscriptField (id : String) (record : Lean.Json) (name : String) : IO String :=
  expectOk s!"{id}: {name}" ((record.getObjVal? name) >>= Lean.Json.getStr?)

private def subscriptSqlTypeName : SelectContract.ScalarType → String
  | .char [] => "bpchar"
  | .array element => subscriptSqlTypeName element ++ "[]"
  | base => (base.dataType.toSql.toLower).replace ", " ","

def arraySubscriptCorpusTests : IO Nat := do
  let json ← expectOk "array subscript fixture JSON"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/array_subscripts/synthetic.json"))
  let records ← expectOk "array subscript fixture records" json.getArr?
  SQLean.Tests.assert (records.size == 50) "expected exactly 50 array subscript synthetic queries"
  let mut ids : List String := []
  let mut statements : List String := []
  for record in records do
    let id ← subscriptField "array subscript fixture" record "id"
    let sql ← subscriptField id record "sql"
    SQLean.Tests.assert ((← subscriptField id record "source_kind") == "synthetic") s!"{id}: population"
    let params ← subscriptField id record "parameter_types"
    let expected ← expectOk id ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
    let expected ← expected.toList.mapM fun column => do
      let name ← subscriptField id column "name"
      let type ← subscriptField id column "type"
      let nullable ← expectOk id ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
      pure (name, type, nullable)
    let actual ← subscriptOutput sql params
    let labels := actual.map fun column =>
      let type := match column.type.base with
        | .bool => "bool"
        | .int32 => "int32"
        | .text => "text"
        | base => subscriptSqlTypeName base
      (column.name, type, column.type.nullable)
    SQLean.Tests.assert (labels == expected)
      s!"{id}: exact subscript output {reprStr labels}; expected {reprStr expected}"
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (decide ids.Nodup && decide statements.Nodup)
    "duplicate array subscript corpus identities or SQL"
  pure records.size

end SQLean.Tests
