import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import SQLean.AdvancedQueryValidation
import Tests.Support

/-! Recursive syntax and lexical binding transport. These are representation
witnesses: they deliberately include PostgreSQL-invalid recursive shapes and
engine-dependent constructs, without claiming termination or value equality. -/
namespace SQLean.Tests
open Advanced RenderContract

private def scalar (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr]}}

private def occurrenceWitness : Advanced.Query := {
  body := .select {items := [.expression (.parameter (.anonymous 3))]}
  recursive := true
  ctes := [⟨"r", {body := .set .union true (scalar (.parameter (.anonymous 1))) (scalar (.parameter (.anonymous 2)))}, []⟩] }

/-- A recursive marker does not duplicate or unroll lexical occurrences. -/
example :
    translateParameters occurrenceWitness = {
      body := .select {items := [.expression (.parameter (.numbered 3))]}
      recursive := true
      ctes := [⟨"r", {body := .set .union true (scalar (.parameter (.numbered 1))) (scalar (.parameter (.numbered 2)))}, []⟩] } := by
  unfold occurrenceWitness scalar
  unfold translateParameters
  dsimp
  unfold translateQueryBody translateCTE translateSelect
  dsimp
  unfold translateSelectItem translateExpr
  dsimp
  unfold translateParameters
  dsimp
  unfold translateQueryBody
  unfold translateParameters
  dsimp
  unfold translateQueryBody translateSelect
  dsimp
  unfold translateSelectItem translateExpr
  rfl

private def checkSQL (sql : String) (uses : List Parameter := [])
    (sqlite : Bool := true) : IO Nat := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let profiles := [RenderContract.Profile.identityV01, .postgres16V01] ++
    (if sqlite then [.sqliteV01] else [])
  for profile in profiles do
    let certificate ← expectOk sql ((RenderContract.check profile query).mapError reprStr)
    SQLean.Tests.assert (certificate.footprint.parameters == uses)
      "recursive definitions must contribute each lexical occurrence once"
    SQLean.Tests.assert (certificate.parameterMap.map (·.source) == uses.eraseDups)
      "recursive references changed the binding map"
    let parsed ← expectOk certificate.sql (parseRendered profile certificate.sql)
    SQLean.Tests.assert (decide (parsed = expectedQuery profile query))
      "recursive rendering changed a marker, operation, alias or local clause"
    let again ← expectOk certificate.sql ((RenderContract.check profile parsed).mapError reprStr)
    SQLean.Tests.assert (again.sql == certificate.sql) "recursive canonical bytes changed"
    for parameter in uses do
      SQLean.Tests.assert
        (certificate.transport reprStr (parameterSlot parameter) == reprStr parameter)
        "recursive rendering changed a bound value"
  SQLean.Tests.assert (Advanced.queryParameters 512 query == uses)
    "expanded recursive walker disagrees with lexical parameter order"
  pure profiles.length

private def boundary (profile : RenderContract.Profile) (query : Advanced.Query)
    (status code : String) (fuel : Nat := 1024) : IO Unit := do
  match RenderContract.check profile query fuel with
  | .ok _ => throw (IO.userError s!"recursive representation unexpectedly passed {code}")
  | .error failure =>
    SQLean.Tests.assert (failure.status == status && failure.diagnostic.code == code)
      s!"recursive boundary changed: {reprStr failure}"

private def nested : Nat → Advanced.Query
  | 0 => scalar 1
  | n + 1 => {
      body := .select {items := [.expression 1]}
      recursive := true
      ctes := [⟨"r", nested n, []⟩]}

def recursiveContractRenderingTests : IO Nat := do
  let mut count := 0
  for sql in [
      "WITH RECURSIVE r(n) AS (SELECT 1 UNION ALL SELECT n+1 FROM r WHERE n<3) SELECT n FROM r",
      "WITH RECURSIVE r(n) AS (SELECT 1 UNION SELECT n FROM r) SELECT n FROM r",
      "WITH RECURSIVE r(n) AS (SELECT 1 UNION ALL SELECT r.n+1 FROM r AS r WHERE r.n<3) SELECT n FROM r ORDER BY n LIMIT 3",
      "WITH RECURSIVE \"r.dot\"(\"n.dot\") AS (SELECT 1 UNION ALL SELECT \"n.dot\"+1 FROM \"r.dot\" WHERE \"n.dot\"<3) SELECT \"n.dot\" FROM \"r.dot\"",
      "WITH RECURSIVE \"r\"\"q\"(n) AS (SELECT 1 UNION ALL SELECT n FROM \"r\"\"q\") SELECT n FROM \"r\"\"q\"",
      "WITH RECURSIVE base AS (SELECT 1 AS x), r(x) AS (SELECT x FROM base UNION ALL SELECT x+1 FROM r WHERE x<3) SELECT * FROM r",
      "WITH RECURSIVE r(x) AS (SELECT 1 UNION ALL SELECT x+1 FROM r WHERE x<3), result AS (SELECT x FROM r) SELECT x FROM result",
      "WITH RECURSIVE r(x) AS (SELECT 1 UNION ALL SELECT x+1 FROM r WHERE x<3) SELECT l.x,r.x FROM r AS l CROSS JOIN r AS r",
      "WITH RECURSIVE unused(x) AS (SELECT 1 UNION ALL SELECT x FROM unused) SELECT 2",
      "WITH RECURSIVE r(x) AS (SELECT NULL UNION ALL SELECT 1) SELECT x FROM r",
      "WITH RECURSIVE r(x) AS (SELECT 1 AS a,2 AS b UNION ALL SELECT x+1,b FROM r WHERE x<3) SELECT * FROM r",
      "WITH RECURSIVE r(x,x) AS (SELECT 1,2 UNION ALL SELECT 3,4 FROM r WHERE FALSE) SELECT * FROM r",
      "WITH RECURSIVE a(x) AS (SELECT x FROM b),b(x) AS (SELECT 1) SELECT * FROM a",
      "WITH RECURSIVE a(x) AS (SELECT 1 UNION ALL SELECT x FROM b),b(x) AS (SELECT x FROM a) SELECT * FROM a",
      "WITH RECURSIVE r(x) AS (SELECT x FROM r UNION ALL SELECT 1) SELECT x FROM r",
      "WITH RECURSIVE r(x) AS (SELECT 1 UNION ALL SELECT a.x FROM r AS a CROSS JOIN r AS b) SELECT x FROM r",
      "WITH RECURSIVE r(x) AS (SELECT 1 INTERSECT SELECT x FROM r) SELECT x FROM r",
      "WITH RECURSIVE r(x) AS (SELECT 1 EXCEPT SELECT x FROM r) SELECT x FROM r",
      "WITH RECURSIVE r(x) AS (SELECT 1 UNION ALL SELECT x FROM r ORDER BY 1 LIMIT 2) SELECT x FROM r",
      "WITH RECURSIVE r(x) AS (SELECT 1 UNION ALL SELECT (SELECT x FROM r)) SELECT x FROM r",
      "WITH RECURSIVE r(x) AS (SELECT 1 UNION ALL SELECT x FROM (SELECT x FROM r) AS d) SELECT x FROM r",
      "WITH RECURSIVE r(x) AS (SELECT 1 UNION ALL SELECT r.x FROM r LEFT JOIN (SELECT 1 AS y) AS d ON TRUE) SELECT x FROM r",
      "WITH RECURSIVE r(x) AS (SELECT 1 UNION ALL SELECT r.x FROM (SELECT 1 AS y) AS d LEFT JOIN r ON TRUE) SELECT x FROM r"] do
    count := count + (← checkSQL sql)
  -- Nested term clauses and typed expressions are represented even where the
  -- target engine or independent static profile imposes further restrictions.
  for sql in [
      "WITH RECURSIVE r(x) AS (SELECT 1 UNION ALL (SELECT x FROM r ORDER BY x LIMIT 1)) SELECT x FROM r",
      "WITH RECURSIVE r(x) AS (SELECT 1 UNION ALL (WITH d AS (SELECT x FROM r) SELECT x FROM d)) SELECT x FROM r",
      "WITH RECURSIVE r(x) AS (SELECT 1 UNION ALL (WITH r AS (SELECT 2 AS x) SELECT x FROM r)) SELECT x FROM r",
      "WITH RECURSIVE r(x) AS (SELECT 1 UNION ALL (SELECT x FROM r INTERSECT ALL SELECT 2)) SELECT x FROM r",
      "WITH RECURSIVE r(x) AS (SELECT CAST(NULL AS NUMERIC(8,2)) UNION ALL SELECT CAST(NULL AS NUMERIC(8,2)) FROM r WHERE FALSE) SELECT x FROM r",
      "WITH RECURSIVE r(x) AS (SELECT ARRAY[1] UNION ALL SELECT ARRAY[2] FROM r WHERE FALSE) SELECT x FROM r",
      "WITH RECURSIVE r(x) AS (SELECT CAST('a' AS TEXT) UNION ALL SELECT CAST(CURRENT_USER AS TEXT) FROM r WHERE FALSE) SELECT x FROM r",
      "WITH RECURSIVE r(x) AS (SELECT 1 UNION ALL SELECT x FROM r FOR UPDATE) SELECT x FROM r"] do
    count := count + (← checkSQL sql [] false)
  for (sql, uses, sqlite) in [
      ("WITH RECURSIVE r(n) AS (SELECT ? UNION ALL SELECT n+? FROM r WHERE n<?) SELECT ? FROM r LIMIT ?",
        (List.range 5).map (fun n => Parameter.anonymous (n+1)), true),
      ("WITH RECURSIVE r(n) AS (SELECT $3 UNION ALL SELECT n+$1 FROM r WHERE n<$3) SELECT $2 FROM r",
        [.numbered 3,.numbered 1,.numbered 3,.numbered 2], true),
      ("WITH RECURSIVE unused AS (SELECT ?),r(n) AS (SELECT ? UNION ALL SELECT n+? FROM r WHERE n<?) SELECT ?,a.n,b.n FROM r AS a CROSS JOIN r AS b",
        (List.range 5).map (fun n => Parameter.anonymous (n+1)), true),
      ("WITH RECURSIVE r(n) AS ((SELECT ? LIMIT ?) UNION ALL (SELECT n+? FROM r WHERE n<? OFFSET ? LIMIT ?)) SELECT ? FROM r OFFSET ? LIMIT ?",
        (List.range 9).map (fun n => Parameter.anonymous (n+1)), false),
      ("WITH RECURSIVE r(n) AS (SELECT ? UNION ALL (WITH d AS (SELECT ? FROM r) SELECT ? FROM d)) SELECT ? FROM r",
        (List.range 4).map (fun n => Parameter.anonymous (n+1)), false)] do
    count := count + (← checkSQL sql uses sqlite)
  let malformed := {occurrenceWitness with ctes := []}
  boundary .identityV01 malformed "invalid" "representation.recursive"
  boundary .identityV01 {occurrenceWitness with ctes := [
    ⟨"", scalar (.parameter (.anonymous 1)), []⟩]} "invalid" "representation.empty-name"
  boundary .identityV01 {occurrenceWitness with ctes := [
    ⟨"r", scalar (.parameter (.anonymous 2)), []⟩]} "invalid" "representation.parameters"
  boundary .postgres16V01 {occurrenceWitness with ctes := [
    ⟨"r", scalar (.parameter (.numbered 1)), []⟩]} "unsupported" "coverage.mixed-parameters"
  count := count + 4
  for profile in [RenderContract.Profile.identityV01,.postgres16V01,.sqliteV01] do
    boundary profile (nested 12) "inconclusive" "resource.depth" 8
    count := count + 1
  pure count

end SQLean.Tests
