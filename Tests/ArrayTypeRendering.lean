import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import Tests.Support

/-! Array declarations preserve their suffix count and scalar modifiers.
These are syntax, structural roundtrip and parameter-transport witnesses;
array contents, dimensions and casts are not executed here. -/
namespace SQLean.Tests
open Advanced

private def wrap : Nat → TypeName → TypeName
  | 0, element => element
  | n + 1, element => .array (wrap n element)

private def castQuery (type : DataType) : Advanced.Query :=
  {body := .select {items := [.expression (.cast (.parameter (.anonymous 1)) type)]}}

private def scalarTypes : List DataType :=
  ([TypeName.smallInt, .int, .bigInt, .real, .doublePrecision, .numeric, .text, .varchar,
    .char, .bool, .date, .time, .timeTZ, .timestamp, .timestampTZ, .interval, .uuid,
    .json, .jsonb, .bytea].map fun name => ⟨name, []⟩) ++
  [⟨.varchar, [3]⟩, ⟨.char, [1]⟩, ⟨.numeric, [8, 2]⟩,
   ⟨.time, [0]⟩, ⟨.timeTZ, [3]⟩, ⟨.timestamp, [6]⟩, ⟨.timestampTZ, [2]⟩, ⟨.interval, [4]⟩]

private def malformed : List DataType := [
  ⟨.array .int, [2]⟩,
  ⟨.array (.array .varchar), [0]⟩,
  ⟨.array (.array .char), [10485761]⟩,
  ⟨.array .numeric, [0, 2]⟩,
  ⟨.array (.array .numeric), [8, 1001]⟩,
  ⟨.array .timestampTZ, [7]⟩,
  ⟨.array (.array .uuid), [1]⟩]

/-- Universal scalar-suffix composition is a kernel equality. No placeholder
or renderer branch erases the declared array suffix count. -/
example (element : TypeName) (modifiers : List Nat) :
    (⟨.array element, modifiers⟩ : DataType).toSql =
      (⟨element, modifiers⟩ : DataType).toSql ++ "[]" := rfl
example (element : TypeName) (modifiers : List Nat) :
    RenderContract.checkDataType ⟨.array element, modifiers⟩ =
      RenderContract.checkDataType ⟨element, modifiers⟩ := rfl
example : (⟨.array (.array .varchar), [3]⟩ : DataType).toSql = "VARCHAR(3)[][]" := rfl
example : (⟨.array (.array .timestampTZ), [2]⟩ : DataType).toSql =
    "TIMESTAMP(2) WITH TIME ZONE[][]" := rfl
example : RenderContract.arrayTypeDepth (.array (.array .int)) = 2 := rfl
example : RenderContract.checkDataType ⟨.array (.array .varchar), [3]⟩ = .ok () := rfl
example : RenderContract.checkSQLiteDataType ⟨.array .int, []⟩ =
    .error (.unsupported ⟨"coverage.sqlite.array-type",
      "this SQLite rendering profile cannot preserve array-type without an AST rewrite"⟩) := rfl

/-- The independently defined array representation domain has a constructive
witness; parser acceptance is not a premise of its admissibility proof. -/
example : RenderContract.Admissible (castQuery ⟨.array .varchar, [3]⟩) := by
  refine ⟨{depth := 5, parameters := [.anonymous 1]}, ?_, ?_, ?_⟩
  · unfold castQuery RenderContract.inspectQuery
    dsimp
    unfold RenderContract.inspectSelect
    dsimp
    unfold RenderContract.inspectItem RenderContract.inspectExpr
    unfold RenderContract.inspectExpr
    rfl
  · decide
  · decide

private def rejected (profile : RenderContract.Profile) (query : Advanced.Query)
    (status code : String) (budget : Nat := 1024) : IO Unit := do
  match RenderContract.check profile query budget with
  | .ok _ => throw (IO.userError s!"array boundary unexpectedly accepted {status}/{code}")
  | .error failure =>
    SQLean.Tests.assert (failure.status == status && failure.diagnostic.code == code)
      s!"array boundary misclassified: {reprStr failure}"

private def checkCast (type : DataType) : IO Nat := do
  let parsed ← expectOk type.toSql (Advanced.parseDataType type.toSql)
  SQLean.Tests.assert (parsed == type) s!"array declaration roundtrip changed modifiers/rank: {type.toSql}"
  let query := castQuery type
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    let certificate ← expectOk type.toSql ((RenderContract.check profile query).mapError reprStr)
    SQLean.Tests.assert (certificate.footprint.parameters == [.anonymous 1])
      s!"array cast lost its parameter: {type.toSql}"
    let recovered ← expectOk type.toSql (RenderContract.parseRendered profile certificate.sql)
    SQLean.Tests.assert (decide (recovered = RenderContract.expectedQuery profile query))
      s!"array cast changed its declaration or binding: {type.toSql}"
    let again ← expectOk type.toSql ((RenderContract.check profile recovered).mapError reprStr)
    SQLean.Tests.assert (again.sql == certificate.sql) s!"array canonical SQL is unstable: {type.toSql}"
    let environment : Parameter → String
      | .anonymous n => s!"anonymous-{n}" | .numbered n => s!"numbered-{n}"
    SQLean.Tests.assert (certificate.transport environment 1 == "anonymous-1")
      s!"array cast changed a logical parameter value: {type.toSql}"
  rejected .sqliteV01 query "unsupported" "coverage.sqlite.array-type"
  pure 4

def arrayTypeRenderingTests : IO Nat := do
  let mut count := 0
  for type in scalarTypes do
    for depth in [1, 2, 4] do
      count := count + (← checkCast ⟨wrap depth type.name, type.modifiers⟩)
  for type in malformed do
    for profile in [RenderContract.Profile.identityV01, .postgres16V01, .sqliteV01] do
      rejected profile (castQuery type) "invalid" "representation.type-modifiers"
      count := count + 1
  let aliases : List (String × DataType) := [
    ("INT4[][]", ⟨.array (.array .int), []⟩),
    ("DECIMAL(8,2)[]", ⟨.array .numeric, [8, 2]⟩),
    ("CHARACTER VARYING(3)[][]", ⟨.array (.array .varchar), [3]⟩),
    ("TIMESTAMPTZ(2)[]", ⟨.array .timestampTZ, [2]⟩)]
  for (source, type) in aliases do
    let parsed ← expectOk source (Advanced.parseDataType source)
    SQLean.Tests.assert (parsed == type) s!"array alias lost its scalar declaration: {source}"
    count := count + 1
  let declarations ← expectOk "array parameters"
    (Advanced.parseParameterDeclarations "INTEGER[]?, NUMERIC(8,2)[][], VARCHAR(3)[]?")
  SQLean.Tests.assert (declarations ==
    [(⟨.array .int, []⟩, true), (⟨.array (.array .numeric), [8, 2]⟩, false),
      (⟨.array .varchar, [3]⟩, true)]) "array parameter declarations lost modifiers or nullable flags"
  count := count + 1
  for source in ["INTEGER[3]", "INTEGER ARRAY", "INTEGER[][2]", "INTEGER[", "INTEGER[]junk"] do
    expectError source (Advanced.parseDataType source)
    count := count + 1
  -- Array suffix depth must not evade the structural resource boundary.
  rejected .identityV01 (castQuery ⟨wrap 12 .int, []⟩) "inconclusive" "resource.depth" 8
  rejected .postgres16V01 (castQuery ⟨wrap 12 .int, []⟩) "inconclusive" "resource.depth" 8
  count := count + 2
  -- A hidden array target in a nested query still belongs to the SQLite boundary.
  let hidden : Advanced.Query := {
    body := .select {
      items := [.all none]
      source := some (.derived (castQuery ⟨.array .int, []⟩) "d" [] false) }}
  rejected .sqliteV01 hidden "unsupported" "coverage.sqlite.array-type"
  let certificate ← expectOk "nested array cast" ((RenderContract.check .postgres16V01 hidden).mapError reprStr)
  SQLean.Tests.assert (certificate.footprint.parameters == [.anonymous 1])
    "nested derived array cast lost its parameter"
  count := count + 2
  let mixed : Advanced.Query := {body := .select {items := [
    .expression (.cast (.parameter (.anonymous 1)) ⟨.array .int, []⟩),
    .expression (.parameter (.numbered 1))]}}
  rejected .postgres16V01 mixed "unsupported" "coverage.mixed-parameters"
  pure (count + 1)

end SQLean.Tests
