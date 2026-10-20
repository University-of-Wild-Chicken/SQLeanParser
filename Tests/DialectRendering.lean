import SQLean.RenderContract
import Tests.Support

namespace SQLean.Tests
open Advanced

private def integer (n : Nat) : Advanced.Expr := .literal (.int n)
private def simple (n : Nat) : Advanced.Query :=
  {body := .select {items := [.expression (integer n)]}}
private def sourceQuery (source : Advanced.From) : Advanced.Query :=
  {body := .select {items := [.all], source := some source}}

private def reconstruct (profile : RenderContract.Profile) (source : String) : IO Advanced.Query := do
  let parsed ← expectOk "dialect input" (if profile == .sqliteV01 then
    Advanced.parseSQLiteQuery source else Advanced.parseQuery source)
  let certificate ← match RenderContract.check profile parsed with
    | .ok certificate => pure certificate
    | .error failure => throw (IO.userError s!"dialect render failed: {source}: {reprStr failure}")
  let actual ← expectOk "dialect full reparse" (RenderContract.parseRendered profile certificate.sql)
  SQLean.Tests.assert (decide (actual = RenderContract.expectedQuery profile parsed))
    s!"dialect rendering changed an AST field: {source}"
  let again ← match RenderContract.check profile actual with
    | .ok certificate => pure certificate
    | .error failure => throw (IO.userError s!"dialect canonical rerender failed: {reprStr failure}")
  SQLean.Tests.assert (certificate.sql == again.sql) s!"dialect canonical bytes changed: {source}"
  expectError "dialect parser consumes full input"
    (RenderContract.parseRendered profile (certificate.sql ++ " SELECT 99;"))
  pure parsed

private def sqliteUnsupported : List (String × Advanced.Query) :=
  let q := simple 1
  let table : Advanced.From := .table "t"
  [
    ("ILIKE", {body := .select {items := [.expression (.pattern (.literal (.text "a")) (.literal (.text "A")) true)]}}),
    ("DISTINCT ON", {body := .select {items := [.expression (integer 1)], distinctOn := [integer 1]}}),
    ("LATERAL", sourceQuery (.derived q "d" [] true)),
    ("table alias columns", sourceQuery (.table "t" (some "a") ["renamed"])),
    ("derived alias columns", sourceQuery (.derived q "a" ["renamed"])),
    ("nested table alias columns", sourceQuery (.join .inner table
      (.table "u" (some "b") ["renamed"]) (.on (.literal (.bool true))))),
    ("INTERSECT ALL", {body := .set .intersect true q q}),
    ("EXCEPT ALL", {body := .set .except true q q}),
    ("OFFSET without LIMIT", {q with offset := some 1}),
    ("right-nested UNION", {body := .set .union false q {body := .set .union false q q}}),
    ("right-nested EXCEPT", {body := .set .except false q {body := .set .except false q q}}),
    ("left operand LIMIT", {body := .set .union true {q with limit := some 1} q}),
    ("right operand LIMIT", {body := .set .union true q {q with limit := some 1}}),
    ("left operand ORDER BY", {body := .set .union true {q with orderBy := [⟨integer 1, false, none⟩]} q}),
    ("right operand ORDER BY", {body := .set .union true q {q with orderBy := [⟨integer 1, false, none⟩]}}),
    ("left operand CTE", {body := .set .union true {q with ctes := [⟨"c", q, []⟩]} q}),
    ("right operand CTE", {body := .set .union true q {q with ctes := [⟨"c", q, []⟩]}}),
    ("nested unsupported predicate", {q with ctes := [⟨"c", {body := .select {
      items := [.expression (.pattern (.literal (.text "a")) (.literal (.text "A")) true)]}}, []⟩]}),
    ("nested unsupported set", sourceQuery (.derived {body := .set .intersect true q q} "d"))
  ]

/-- Concrete dialect-specific parser, exact reconstruction and explicit coverage
checks. Execution oracles live in scripts/check_dialect_cli.py. -/
def dialectRenderingTests : IO Nat := do
  let mut count := 0
  for category in ["sqlite_numbered_parameters", "sqlite_compound_queries", "sqlite_limit_comma",
      "postgres_numeric_scale"] do
    let profile := if category == "postgres_numeric_scale" then
      RenderContract.Profile.postgres16V01 else .sqliteV01
    let text ← IO.FS.readFile s!"fixtures/dialects/{category}.sql"
    let sources := (text.splitOn "\n").filter (!·.trimAscii.toString.isEmpty)
    SQLean.Tests.assert (sources.length == 50) s!"expected 50 examples: {category}"
    for source in sources do
      let _ ← reconstruct profile source
      count := count + 1
  let numbered ← reconstruct .sqliteV01 "SELECT ?2, ?1, ?2"
  match numbered.body with
  | .select {items := [.expression (.parameter (.numbered 2)) none,
      .expression (.parameter (.numbered 1)) none, .expression (.parameter (.numbered 2)) none], ..} => pure ()
  | _ => throw (IO.userError "SQLite numbered slots were changed into occurrence positions")
  let comma ← reconstruct .sqliteV01 "SELECT 1 LIMIT 2, 3"
  SQLean.Tests.assert (comma.limit == some 3 && comma.offset == some 2)
    "SQLite comma LIMIT reversed offset and count"
  let mixed ← reconstruct .sqliteV01 "SELECT 1 UNION SELECT 2 INTERSECT SELECT 2"
  match mixed.body with
  | .set .intersect false {body := .set .union false _ _, ..} _ => pure ()
  | _ => throw (IO.userError "SQLite set operations must associate left with equal precedence")
  let postgres ← reconstruct .postgres16V01 "SELECT 1 UNION SELECT 2 INTERSECT SELECT 2"
  match postgres.body with
  | .set .union false _ {body := .set .intersect false _ _, ..} => pure ()
  | _ => throw (IO.userError "PostgreSQL INTERSECT precedence regressed")
  -- SQLite gives comma and explicit JOIN the same left-associative precedence.
  -- Empty-table execution witnesses in the CLI suite distinguish these trees.
  for (kind, keyword) in ([(.right, "RIGHT"), (.full, "FULL"), (.left, "LEFT")] :
      List (JoinKind × String)) do
    let t : Advanced.From := .table "t"
    let u : Advanced.From := .table "u"
    let v : Advanced.From := .table "v"
    let condition : Advanced.JoinCondition := .on (.literal (.bool true))
    let leftGrouped := Advanced.From.join kind (.join .cross t u .none) v condition
    let rightGrouped := Advanced.From.join .cross t (.join kind u v condition) .none
    for (profile, sql, expected) in [
        (RenderContract.Profile.sqliteV01, s!"SELECT v.c FROM t, u {keyword} JOIN v ON TRUE", leftGrouped),
        (.postgres16V01, s!"SELECT v.c FROM t, u {keyword} JOIN v ON TRUE", rightGrouped),
        (.sqliteV01, s!"SELECT v.c FROM t, (u {keyword} JOIN v ON TRUE)", rightGrouped),
        (.sqliteV01, s!"SELECT v.c FROM (t, u) {keyword} JOIN v ON TRUE", leftGrouped)] do
      let parsed ← reconstruct profile sql
      match parsed.body with
      | .select select =>
          SQLean.Tests.assert (decide (select.source = some expected))
            s!"comma/JOIN association changed: {profile.name}: {sql}"
      | _ => throw (IO.userError "expected join SELECT")
      count := count + 1
  let mixedCase ← reconstruct .sqliteV01 "SeLeCt 1 AS MixedCase"
  match mixedCase.body with
  | .select {items := [.expression _ (some "MixedCase")], ..} => pure ()
  | _ => throw (IO.userError "SQLite must preserve unquoted alias spelling")
  let folded ← reconstruct .postgres16V01 "SeLeCt 1 AS MixedCase"
  match folded.body with
  | .select {items := [.expression _ (some "mixedcase")], ..} => pure ()
  | _ => throw (IO.userError "PostgreSQL must fold unquoted aliases")
  let mixedCte ← reconstruct .sqliteV01
    "WiTh Camel(ColName) AS (sElEcT 1) SeLeCt ColName FROM Camel"
  match mixedCte.ctes, mixedCte.body with
  | [⟨"Camel", _, ["ColName"]⟩], .select {
      items := [.expression (.column none "ColName") none],
      source := some (.table "Camel" none []), ..} => pure ()
  | _, _ => throw (IO.userError "SQLite must preserve CTE and column spelling")
  let qualified ← reconstruct .sqliteV01 "SELECT X.* FROM T AS X"
  match qualified.body with
  | .select {items := [.all (some "X")], source := some (.table "T" (some "X") []), ..} => pure ()
  | _ => throw (IO.userError "SQLite must preserve relation and qualifier spelling")
  let _ ← reconstruct .sqliteV01
    "SELECT CAST(1 AS NuMeRiC(2,4)), SuM(1) FILTER (WHERE TrUe), 1 NoT In (2)"
  count := count + 5
  -- SQLite block comments stop at the first terminator. PostgreSQL nests them.
  let sqliteComment ← reconstruct .sqliteV01 "SELECT 1 /* /* */ + 2 -- */"
  SQLean.Tests.assert (decide (sqliteComment = {body := .select {
    items := [.expression (.binary .add (integer 1) (integer 2))]}}))
    "SQLite incorrectly nested block comments"
  let postgresComment ← reconstruct .postgres16V01 "SELECT 1 /* /* */ + 2 -- */"
  SQLean.Tests.assert (decide (postgresComment = simple 1))
    "PostgreSQL nested block comments regressed"
  let sqliteParameters ← reconstruct .sqliteV01 "SELECT ?1 /* /* */ + ?2 -- */"
  SQLean.Tests.assert (decide (sqliteParameters = {body := .select {
    items := [.expression (.binary .add (.parameter (.numbered 1)) (.parameter (.numbered 2)))]}}))
    "SQLite comment handling changed logical parameter slots"
  let postgresParameters ← reconstruct .postgres16V01 "SELECT $1 /* /* */ + $2 -- */"
  SQLean.Tests.assert (decide (postgresParameters = {body := .select {
    items := [.expression (.parameter (.numbered 1))]}}))
    "PostgreSQL comment handling exposed a commented parameter"
  count := count + 4
  let anonymous ← reconstruct .sqliteV01 "WITH c(x) AS (SELECT ?) SELECT ?, x FROM c"
  match RenderContract.check .sqliteV01 anonymous with
  | .ok certificate =>
      SQLean.Tests.assert (certificate.sql.contains '?') "SQLite parameters lost their native marker"
      SQLean.Tests.assert (!certificate.sql.contains '$') "SQLite renderer emitted PostgreSQL markers"
      SQLean.Tests.assert (certificate.parameterMap == [
        ⟨.anonymous 1, 1⟩, ⟨.anonymous 2, 2⟩]) "SQLite anonymous transport map changed"
  | .error failure => throw (IO.userError s!"anonymous SQLite render failed: {reprStr failure}")
  for source in ["SELECT ?0", "SELECT $1", "SELECT ?, ?1", "SELECT ?1, ?",
      "SELECT 1 LIMIT 1,", "SELECT 1 LIMIT ,1", "SELECT 1 LIMIT 1,2 OFFSET 3"] do
    expectError source (Advanced.parseSQLiteQuery source)
    count := count + 1
  for (label, query) in sqliteUnsupported do
    match RenderContract.check .sqliteV01 query with
    | .error (.unsupported _) => pure ()
    | .error failure => throw (IO.userError s!"SQLite restriction misclassified: {label}: {reprStr failure}")
    | .ok _ => throw (IO.userError s!"SQLite unsupported syntax accepted: {label}")
    count := count + 1
  -- Profile limits are explicit even on a SQLite build configured for more slots.
  let _ ← reconstruct .sqliteV01 "SELECT ?32766"
  match RenderContract.check .sqliteV01
      {body := .select {items := [.expression (.parameter (.numbered 32767))]}} with
  | .error (.unsupported _) => pure ()
  | _ => throw (IO.userError "SQLite oversized parameter slot must be unsupported")
  pure (count + 7)

end SQLean.Tests
