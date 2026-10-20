import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import SQLean.AdvancedQueryValidation
import Tests.Support

/-! CTE representation and binding transport are independent of CTE validity.
In particular, structural SQLite round trips do not assert PostgreSQL name
resolution, native alias arity, output naming, or evaluation behavior. Several
deliberately invalid or dialect-dependent queries below still have representable
syntax. No source query is executed by this test module.
-/
namespace SQLean.Tests
open Advanced RenderContract

private def scalar (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr]}}

private def anon (index : Nat) : Advanced.Expr := .parameter (.anonymous index)

private def numbered (index : Nat) : Advanced.Expr := .parameter (.numbered index)

private def occurrenceWitness : Advanced.Query := {
  body := .select {items := [.expression (anon 2)]}
  ctes := [⟨"c", scalar (anon 1), []⟩] }

private theorem inspectParameterQuery (index : Nat) :
    inspectQuery (scalar (anon index)) =
      .ok {depth := 4, parameters := [.anonymous index]} := by
  unfold scalar anon inspectQuery
  dsimp
  unfold inspectSelect
  dsimp
  unfold inspectItem inspectExpr
  rfl

/-- Even an unused definition contributes its original lexical occurrence.
This closed witness is reduced in the kernel, without evaluating a checker. -/
example : Admissible occurrenceWitness := by
  have nameValid : checkName "c" = .ok () := by
    have bytes : "c".utf8ByteSize = 1 := by decide
    simp [checkName, bytes]
    rfl
  refine ⟨{depth := 5, parameters := [.anonymous 1, .anonymous 2]}, ?_, ?_, ?_⟩
  · unfold occurrenceWitness inspectQuery
    simp only [List.attach_cons, List.attach_nil, List.map_cons, List.map_nil]
    rw [inspectParameterQuery]
    dsimp
    unfold inspectSelect
    dsimp
    unfold anon
    unfold inspectItem inspectExpr
    rw [nameValid]
    rfl
  · decide
  · decide

/-- Translation visits definitions once and does not inline their references. -/
example :
    translateParameters occurrenceWitness =
      {body := .select {items := [.expression (numbered 2)]},
       ctes := [⟨"c", scalar (numbered 1), []⟩]} := by
  unfold occurrenceWitness scalar anon numbered
  unfold translateParameters
  dsimp
  unfold translateQueryBody translateCTE
  unfold translateSelect
  dsimp
  unfold translateSelectItem translateExpr
  dsimp
  unfold translateParameters
  dsimp
  unfold translateQueryBody translateSelect
  dsimp
  unfold translateSelectItem translateExpr
  rfl

private def checkQuery (query : Advanced.Query) (parameters : List Parameter)
    (sqlite : Bool := true) : IO Nat := do
  let profiles := [RenderContract.Profile.identityV01, .postgres16V01] ++
    (if sqlite then [.sqliteV01] else [])
  for profile in profiles do
    let certificate ← expectOk "CTE rendering" ((RenderContract.check profile query).mapError reprStr)
    SQLean.Tests.assert (certificate.footprint.parameters == parameters)
      "CTE definitions/references changed lexical parameter occurrences"
    let reparsed ← expectOk certificate.sql (parseRendered profile certificate.sql)
    SQLean.Tests.assert (decide (reparsed = expectedQuery profile query))
      "CTE rendering changed a definition, alias, query boundary, or reference"
    let again ← expectOk certificate.sql ((RenderContract.check profile reparsed).mapError reprStr)
    SQLean.Tests.assert (again.sql == certificate.sql) "CTE canonical bytes changed"
    SQLean.Tests.assert
      (certificate.parameterMap.map (·.source) == parameters.eraseDups)
      "CTE binding map lost an unused binding or duplicated a repeated reference"
    for parameter in parameters do
      SQLean.Tests.assert
        (certificate.transport reprStr (parameterSlot parameter) == reprStr parameter)
        "CTE translation changed a driver binding"
  SQLean.Tests.assert (Advanced.queryParameters 256 query == parameters)
    "The expanded walker disagrees with complete CTE parameter traversal"
  pure profiles.length

private def checkSQL (sql : String) (parameters : List Parameter := [])
    (sqlite : Bool := true) : IO Nat := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  checkQuery query parameters sqlite

private def rejected (profile : RenderContract.Profile) (query : Advanced.Query)
    (status code : String) (budget : Nat := 1024) : IO Unit := do
  match RenderContract.check profile query budget with
  | .ok _ => throw (IO.userError s!"CTE unexpectedly passed {status}/{code}")
  | .error failure =>
      SQLean.Tests.assert (failure.status == status && failure.diagnostic.code == code)
        s!"CTE boundary differs: {reprStr failure}"

private def nested : Nat → Advanced.Query
  | 0 => scalar 1
  | n + 1 => {body := .select {items := [.expression 1]}, ctes := [⟨"unused", nested n, []⟩]}

def cteRenderingTests : IO Nat := do
  let mut count := 0
  -- Ordinary, inherited, shadowed, and schema-independent reference shapes.
  for sql in [
      "WITH c AS (SELECT 1 AS x) SELECT * FROM c",
      "WITH a AS (SELECT 1 AS x), b AS (SELECT x + 1 AS y FROM a) SELECT y FROM b",
      "WITH a AS (SELECT 1 AS x) SELECT l.x, r.x FROM a AS l CROSS JOIN a AS r",
      "WITH unused AS (SELECT 1 AS x) SELECT 2 AS y",
      "WITH a AS (SELECT 1 AS x) SELECT * FROM (SELECT x FROM a) AS d",
      "WITH a AS (SELECT 1 AS x) SELECT * FROM (WITH a AS (SELECT 2 AS x) SELECT * FROM a) AS d",
      "WITH a AS (SELECT 1 AS x) SELECT * FROM (WITH a AS (SELECT x + 1 AS x FROM a) SELECT * FROM a) AS d",
      "WITH a AS (SELECT 1 AS x) SELECT * FROM (WITH b AS (SELECT * FROM a), a AS (SELECT 2 AS x) SELECT * FROM b) AS d",
      "WITH outer_name AS (SELECT 1 AS x), a AS (WITH outer_name AS (SELECT 2 AS x) SELECT * FROM outer_name), b AS (SELECT * FROM outer_name) SELECT a.x, b.x FROM a CROSS JOIN b",
      "WITH \"a.b\"(\"x.y\") AS (SELECT 1) SELECT \"a.b\".\"x.y\" FROM \"a.b\"",
      "WITH \"a\"\"b\" AS (SELECT 1 AS \"x\"\"y\") SELECT \"x\"\"y\" FROM \"a\"\"b\"",
      "WITH \"A\" AS (SELECT 1 AS x), a AS (SELECT 2 AS x) SELECT \"A\".x, a.x FROM \"A\" CROSS JOIN a",
      "WITH c(first, second) AS (SELECT 1 AS x, 2 AS y) SELECT second, first FROM c",
      "WITH c AS (SELECT NULL AS x) SELECT x FROM c",
      "WITH c AS (SELECT 1 + 1) SELECT * FROM c",
      "WITH c AS (SELECT 1 AS x ORDER BY x LIMIT 1) SELECT x FROM c",
      "WITH c AS (SELECT 1 AS x) SELECT x FROM c WHERE x > 0 ORDER BY x LIMIT 1 OFFSET 0",
      "WITH c AS (SELECT 1 AS x) SELECT b.x, c.x FROM base_rows AS b LEFT JOIN c ON b.x = c.x",
      "WITH RECURSIVE c(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM c WHERE n < 3) SELECT n FROM c"] do
    count := count + (← checkSQL sql)
  -- These are representation checks only. Native PostgreSQL/SQLite differ on
  -- forward/self references, prefix aliases, duplicate labels, and unused bodies.
  for sql in [
      "WITH a AS (SELECT * FROM b), b AS (SELECT 2 AS x) SELECT * FROM a",
      "WITH t AS (SELECT x FROM t) SELECT * FROM t",
      "WITH c(first) AS (SELECT 1 AS x, 2 AS y) SELECT * FROM c",
      "WITH c(x, x) AS (SELECT 1, 2) SELECT * FROM c",
      "WITH c(x, x) AS (SELECT 1, 2) SELECT c.x FROM c",
      "WITH c AS (SELECT 1 AS x, 2 AS x) SELECT * FROM c",
      "WITH a AS (SELECT 1), a AS (SELECT 2) SELECT 3",
      "WITH unused AS (SELECT absent FROM missing_relation) SELECT 1",
      "WITH c(x, y, z) AS (SELECT 1, 2) SELECT * FROM c",
      "WITH a AS (WITH hidden AS (SELECT 1 AS x) SELECT * FROM hidden), b AS (SELECT * FROM hidden) SELECT * FROM b"] do
    count := count + (← checkSQL sql)
  -- PostgreSQL-only substructure remains supported inside definitions.
  for sql in [
      "WITH t AS (SELECT 1 AS id) SELECT a.id, b.id FROM t AS a CROSS JOIN public.t AS b",
      "WITH c AS (SELECT 1 AS x, 2 AS y) SELECT d.first, d.y FROM c AS d(first)",
      "WITH c AS (SELECT CAST(NULL AS NUMERIC(8, 2)) AS x) SELECT x FROM c",
      "WITH c AS (SELECT CAST(NULL AS VARCHAR(5)[]) AS x) SELECT x FROM c",
      "WITH c AS (SELECT id FROM users FOR UPDATE) SELECT id FROM c",
      "WITH c AS (SELECT id FROM users) SELECT id FROM c FOR UPDATE",
      "WITH c AS (SELECT id FROM users) SELECT id FROM c FOR UPDATE OF c",
      "WITH unused AS (SELECT l.id FROM users AS l LEFT JOIN users AS r ON FALSE FOR UPDATE OF r) SELECT 1"] do
    count := count + (← checkSQL sql [] false)
  let ordered ← expectOk "CTE AST boundaries" (Advanced.parseQuery
    "WITH first(a, a) AS (SELECT 1, 2), second AS (WITH first AS (SELECT 3 AS z) SELECT z FROM first) SELECT * FROM first")
  SQLean.Tests.assert (ordered.ctes.map (·.name) == ["first", "second"])
    "CTE declaration order was changed"
  SQLean.Tests.assert (ordered.ctes[0]!.columns == ["a", "a"])
    "CTE duplicate output aliases were deduplicated"
  SQLean.Tests.assert (ordered.ctes[1]!.query.ctes.map (·.name) == ["first"])
    "An inner WITH clause escaped its definition"
  count := count + 3
  for (sql, uses, sqlite) in [
      ("WITH a AS (SELECT ? AS x) SELECT ? AS v FROM a", [.anonymous 1, .anonymous 2], true),
      ("WITH unused AS (SELECT ? AS x) SELECT ?", [.anonymous 1, .anonymous 2], true),
      ("WITH a AS (SELECT ? AS x) SELECT ?, l.x, r.x FROM a AS l CROSS JOIN a AS r",
        [.anonymous 1, .anonymous 2], true),
      ("WITH a AS (SELECT $3 AS x), unused AS (SELECT $1 AS y) SELECT $3 FROM a",
        [.numbered 3, .numbered 1, .numbered 3], true),
      ("WITH a AS (WITH b AS (SELECT ? AS x) SELECT ? FROM b), c AS (SELECT ? AS y) SELECT ? FROM a",
        [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4], true),
      ("WITH unused AS (SELECT ? AS u), a AS (SELECT ? AS x) SELECT ? FROM (WITH b AS (SELECT ? AS y) SELECT ? FROM b) AS d WHERE ? ORDER BY ? OFFSET ? LIMIT ?",
        (List.range 9).map (fun n => Parameter.anonymous (n + 1)), false),
      ("WITH a AS (SELECT SUBSTRING(? FOR ? FROM ?) AS x) SELECT ? FROM a",
        [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4], false),
      ("WITH a AS (SELECT CAST(? AS JSONB) ? ? AS v) SELECT ? FROM a",
        [.anonymous 1, .anonymous 2, .anonymous 3], false),
      ("WITH a AS (SELECT make_interval(secs => ?, days := ?) AS v) SELECT ? FROM a",
        [.anonymous 1, .anonymous 2, .anonymous 3], false)] do
    count := count + (← checkSQL sql uses sqlite)
  for (sql, code) in [
      ("WITH c AS (SELECT * FROM public.users) SELECT * FROM c", "coverage.sqlite.schema-qualification"),
      ("WITH c AS (SELECT id FROM users FOR UPDATE) SELECT * FROM c", "coverage.sqlite.row-locking"),
      ("WITH c AS (SELECT ARRAY[1] AS v) SELECT * FROM c", "coverage.sqlite.array-constructor")] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    rejected .sqliteV01 query "unsupported" code
    count := count + 1
  for sql in [
      "WITH c AS SELECT 1 SELECT * FROM c",
      "WITH c AS (SELECT 1), SELECT * FROM c",
      "WITH c AS () SELECT 1",
      "WITH c AS (SELECT 1) SELECT * FROM c; SELECT 2"] do
    expectError sql (Advanced.parseQuery sql)
    count := count + 1
  for (query, code) in [
      ({body := .select {items := [.expression 1]}, ctes := [⟨"", scalar 1, []⟩]},
        "representation.empty-name"),
      ({body := .select {items := [.expression 1]}, ctes := [⟨"unused", scalar 1, [""]⟩]},
        "representation.empty-name"),
      ({body := .select {items := [.expression 1]}, ctes := [⟨"unused", scalar (.column none "x\x00y"), []⟩]},
        "representation.name-nul")] do
    rejected .identityV01 query "invalid" code
    count := count + 1
  rejected .identityV01 {occurrenceWitness with
    ctes := [⟨"unused", scalar (anon 2), []⟩], body := .select {items := [.expression (anon 1)]}}
    "invalid" "representation.parameters"
  rejected .identityV01 {occurrenceWitness with
    ctes := [⟨"unused", scalar (numbered 1), []⟩]}
    "unsupported" "coverage.mixed-parameters"
  count := count + 2
  for profile in [RenderContract.Profile.identityV01, .postgres16V01, .sqliteV01] do
    rejected profile (nested 12) "inconclusive" "resource.depth" 8
    count := count + 1
  pure count

end SQLean.Tests
