import SQLean.RenderContract.Checker
import Tests.Support

/-! Concrete type syntax and structural serialization witnesses. These tests
do not evaluate typed literal contents or assert database cast success. -/
namespace SQLean.Tests
open Advanced

private def castQuery (type : DataType) : Advanced.Query :=
  {body := .select {items := [.expression (.cast (.parameter (.anonymous 1)) type)]}}

private def exactTypes : List DataType :=
  ([TypeName.smallInt, .char, .date, .time, .timeTZ, .timestamp, .timestampTZ,
    .interval, .uuid, .json, .jsonb, .bytea].map fun name => ⟨name, []⟩) ++
  [⟨.char, [1]⟩, ⟨.char, [10485760]⟩] ++
  ([TypeName.time, .timeTZ, .timestamp, .timestampTZ, .interval].flatMap fun name =>
    [⟨name, [0]⟩, ⟨name, [3]⟩, ⟨name, [6]⟩])

private def aliases : List (String × DataType) := [
  ("INT2", ⟨.smallInt, []⟩), ("INT4", ⟨.int, []⟩), ("INT8", ⟨.bigInt, []⟩),
  ("FLOAT4", ⟨.real, []⟩), ("FLOAT8", ⟨.doublePrecision, []⟩),
  ("DECIMAL(12,4)", ⟨.numeric, [12, 4]⟩),
  ("CHARACTER", ⟨.char, []⟩), ("CHARACTER(7)", ⟨.char, [7]⟩),
  ("CHARACTER VARYING(7)", ⟨.varchar, [7]⟩), ("CHAR VARYING", ⟨.varchar, []⟩),
  ("TIME(3) WITHOUT TIME ZONE", ⟨.time, [3]⟩),
  ("TIME(3) WITH TIME ZONE", ⟨.timeTZ, [3]⟩), ("TIMETZ(3)", ⟨.timeTZ, [3]⟩),
  ("TIMESTAMP(6) WITHOUT TIME ZONE", ⟨.timestamp, [6]⟩),
  ("TIMESTAMP(6) WITH TIME ZONE", ⟨.timestampTZ, [6]⟩),
  ("TIMESTAMPTZ(6)", ⟨.timestampTZ, [6]⟩)
]

private def invalidTypes : List DataType := [
  ⟨.char, [0]⟩, ⟨.char, [10485761]⟩, ⟨.char, [1, 2]⟩,
  ⟨.date, [3]⟩, ⟨.time, [7]⟩, ⟨.timeTZ, [0, 1]⟩,
  ⟨.timestamp, [7]⟩, ⟨.timestampTZ, [0, 1]⟩, ⟨.interval, [7]⟩,
  ⟨.uuid, [1]⟩, ⟨.json, [1]⟩, ⟨.jsonb, [1]⟩, ⟨.bytea, [1]⟩
]

private def typedStrings : List (String × String) := [
  ("DATE '2000-02-29'", "CAST('2000-02-29' AS DATE)"),
  ("TIME(3) '12:34:56.123'", "CAST('12:34:56.123' AS TIME(3))"),
  ("TIME WITH TIME ZONE '12:34:56+02'", "CAST('12:34:56+02' AS TIME WITH TIME ZONE)"),
  ("TIMESTAMP '2000-02-29 12:34:56'", "CAST('2000-02-29 12:34:56' AS TIMESTAMP)"),
  ("TIMESTAMP(3) WITH TIME ZONE '2000-02-29 12:34:56.123+02'",
    "CAST('2000-02-29 12:34:56.123+02' AS TIMESTAMP(3) WITH TIME ZONE)"),
  ("INTERVAL(3) '1 day 2.123 seconds'", "CAST('1 day 2.123 seconds' AS INTERVAL(3))"),
  ("UUID '00000000-0000-0000-0000-000000000001'",
    "CAST('00000000-0000-0000-0000-000000000001' AS UUID)"),
  ("JSON '{\"a\":1}'", "CAST('{\"a\":1}' AS JSON)"),
  ("JSONB '{\"a\":1}'", "CAST('{\"a\":1}' AS JSONB)"),
  ("BYTEA '\\x00ff'", "CAST('\\x00ff' AS BYTEA)"),
  ("SMALLINT '7'", "CAST('7' AS SMALLINT)"),
  ("CHARACTER(3) 'abc'", "CAST('abc' AS CHAR(3))")
]

/-- The new admissibility cases compute in the kernel, without the parser or
compiled evaluation being used to justify the proposition. -/
example : RenderContract.checkDataType ⟨.timestampTZ, [6]⟩ = .ok () := rfl
example : RenderContract.checkDataType ⟨.char, [10485760]⟩ = .ok () := rfl
example : RenderContract.checkSQLiteDataType ⟨.smallInt, []⟩ = .ok () := rfl

def extendedTypeRenderingTests : IO Nat := do
  let mut count := 0
  for type in exactTypes do
    let reparsed ← expectOk type.toSql (Advanced.parseDataType type.toSql)
    SQLean.Tests.assert (reparsed == type) s!"concrete type roundtrip lost modifiers: {type.toSql}"
    for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
      let query := castQuery type
      let certificate ← expectOk type.toSql ((RenderContract.check profile query).mapError reprStr)
      let recovered ← expectOk type.toSql (RenderContract.parseRendered profile certificate.sql)
      SQLean.Tests.assert (decide (recovered = RenderContract.expectedQuery profile query))
        s!"cast target or parameter identity changed: {type.toSql}"
      SQLean.Tests.assert (certificate.footprint.parameters == [.anonymous 1])
        s!"cast erased its parameter: {type.toSql}"
      count := count + 1
    match type.name with
    | .smallInt | .char =>
        let _ ← expectOk type.toSql
          ((RenderContract.check .sqliteV01 (castQuery type)).mapError reprStr)
    | _ =>
        match RenderContract.check .sqliteV01 (castQuery type) with
        | .error (.unsupported _) => pure ()
        | .error failure => throw (IO.userError s!"SQLite misclassified PostgreSQL cast {type.toSql}: {reprStr failure}")
        | .ok _ => throw (IO.userError s!"SQLite must exclude PostgreSQL cast {type.toSql}")
    count := count + 2
  for (source, type) in aliases do
    let actual ← expectOk source (Advanced.parseDataType source)
    SQLean.Tests.assert (actual == type) s!"type alias changed target: {source}"
    count := count + 1
  for type in invalidTypes do
    expectError type.toSql (Advanced.parseDataType type.toSql)
    for profile in [RenderContract.Profile.identityV01, .postgres16V01, .sqliteV01] do
      match RenderContract.check profile (castQuery type) with
      | .error (.invalid _) => pure ()
      | .error failure => throw (IO.userError s!"malformed type misclassified: {type.toSql}: {reprStr failure}")
      | .ok _ => throw (IO.userError s!"malformed type accepted: {type.toSql}")
      count := count + 1
    count := count + 1
  for (source, canonical) in typedStrings do
    let actual ← expectOk source (Advanced.parseExpression source)
    let expected ← expectOk canonical (Advanced.parseExpression canonical)
    SQLean.Tests.assert (decide (actual = expected)) s!"typed string normalization changed cast: {source}"
    let query : Advanced.Query := {body := .select {items := [.expression actual]}}
    let _ ← expectOk source ((RenderContract.check .postgres16V01 query).mapError reprStr)
    count := count + 1
  for source in [
    "CHARACTER 'abc'", "CHAR 'abc'", "INTERVAL '1' YEAR TO SECOND",
    "INTERVAL '1 day' DAY TO MONTH", "CAST('1' AS INTERVAL YEAR(2))",
    "CAST('1' AS \"int4\")", "CAST('1' AS \"DATE\")", "CAST('1' AS \"char\")",
    "CAST('1' AS public.custom)", "CAST('1' AS INTEGER[3])"] do
    expectError source (Advanced.parseExpression source)
    count := count + 1
  let columns ← expectOk "type keywords remain identifiers"
    (Advanced.parseQuery "SELECT date, time, timestamp, interval, uuid, json, bytea FROM types")
  match columns.body with
  | .select select =>
      SQLean.Tests.assert (select.items == ["date", "time", "timestamp", "interval", "uuid", "json", "bytea"].map
        (fun name => Advanced.SelectItem.expression (.column none name)))
        "type keywords were consumed as typed constants without a string"
  | _ => throw (IO.userError "unexpected compound query")
  count := count + 1
  let declarations ← expectOk "precise parameter declarations"
    (Advanced.parseParameterDeclarations "NUMERIC(12,4)?, TIMESTAMP(3) WITH TIME ZONE?, int32, double, CHAR(5)")
  SQLean.Tests.assert (declarations ==
    [(⟨.numeric, [12, 4]⟩, true), (⟨.timestampTZ, [3]⟩, true), (⟨.int, []⟩, false),
     (⟨.doublePrecision, []⟩, false), (⟨.char, [5]⟩, false)])
    "parameter declarations lost comma-bearing modifiers or nullable suffix"
  count := count + 1
  for source in ["int32", "int64", "float32", "float64", "double"] do
    expectError s!"metadata alias is not an SQL type: {source}" (Advanced.parseDataType source)
    let _ ← expectOk source (Advanced.parseParameterDeclarations source)
    count := count + 1
  for source in ["NUMERIC(12,4),", "DATE??", "TIME(7)", "UUID(2)", "DATE $1"] do
    expectError source (Advanced.parseParameterDeclarations source)
    count := count + 1
  let empty ← expectOk "empty declarations" (Advanced.parseParameterDeclarations "  ")
  SQLean.Tests.assert empty.isEmpty "empty declaration list changed"
  pure (count + 1)

end SQLean.Tests
