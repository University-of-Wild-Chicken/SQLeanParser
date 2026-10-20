import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import Tests.Support

/-! COLLATE syntax and parameter transport. Object lookup, coercion, and
collation provenance are separate from these representation witnesses.
Precedence and restricted BETWEEN cases follow the pinned PostgreSQL16 grammar. -/
namespace SQLean.Tests
open Advanced RenderContract

private def scalar (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr]}}
private def col (name : Name) : Advanced.Expr := .column none name
private def text (value : String) : Advanced.Expr := .literal (.text value)
private def anon (n : Nat) : Advanced.Expr := .parameter (.anonymous n)
private def num (n : Nat) : Advanced.Expr := .parameter (.numbered n)
private def annotated (expr : Advanced.Expr) : Advanced.Expr := .collate expr ["C"]

example (expr : Advanced.Expr) (name : List Name) :
    translateExpr (.collate expr name) = .collate (translateExpr expr) name := by
  simp only [translateExpr]

example (expr : Advanced.Expr) (name : List Name) :
    translateExpr (translateExpr (.collate expr name)) = translateExpr (.collate expr name) :=
  translateExpr_idempotent _

example (expr : Advanced.Expr) (name : List Name) :
    renderSql .postgres16V01 (translateParameters (scalar (.collate expr name))) =
      renderSql .postgres16V01 (scalar (.collate expr name)) :=
  renderPostgres_translateParameters _

private def parsed (source : String) (expected : Advanced.Expr) : IO Unit := do
  let result ← expectOk source (Advanced.parseExpression source)
  SQLean.Tests.assert (decide (result = expected)) s!"COLLATE AST mismatch: {source}"

private def roundTripQuery (query : Advanced.Query) (uses : List Parameter := []) : IO Nat := do
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    let cert ← expectOk "COLLATE rendering" ((RenderContract.check profile query).mapError reprStr)
    SQLean.Tests.assert (cert.footprint.parameters == uses) "COLLATE changed lexical parameter order"
    let result ← expectOk cert.sql (parseRendered profile cert.sql)
    SQLean.Tests.assert (decide (result = expectedQuery profile query))
      "COLLATE changed the operand or identifier components"
    let again ← expectOk cert.sql ((RenderContract.check profile result).mapError reprStr)
    SQLean.Tests.assert (again.sql == cert.sql) "COLLATE canonical bytes changed"
    for parameter in uses do
      SQLean.Tests.assert (cert.transport reprStr (parameterSlot parameter) == reprStr parameter)
        "COLLATE changed a binding value"
  pure 2

private def roundTrip (expr : Advanced.Expr) (uses : List Parameter := []) : IO Nat :=
  roundTripQuery (scalar expr) uses

private def boundary (profile : RenderContract.Profile) (expr : Advanced.Expr)
    (status code : String) (fuel : Nat := 1024) : IO Unit := do
  match RenderContract.check profile (scalar expr) fuel with
  | .error failure =>
      SQLean.Tests.assert (failure.status == status && failure.diagnostic.code == code)
        s!"wrong COLLATE boundary: {reprStr failure}"
  | .ok cert => throw (IO.userError s!"unexpected COLLATE representation acceptance: {cert.sql}")

private def nested : Nat → Advanced.Expr
  | 0 => text "x"
  | n + 1 => annotated (nested n)

def collationRenderingTests : IO Nat := do
  let mut count := 0
  for (source, expected) in [
      ("a COLLATE \"C\"", annotated (col "a")),
      ("a COLLATE c", .collate (col "a") ["c"]),
      ("a COLLATE pg_catalog.\"C\"", .collate (col "a") ["pg_catalog", "C"]),
      ("a COLLATE postgres.pg_catalog.\"C\"", .collate (col "a") ["postgres", "pg_catalog", "C"]),
      ("a COLLATE a.b.c.d", .collate (col "a") ["a", "b", "c", "d"]),
      ("a COLLATE \"a.b\"", .collate (col "a") ["a.b"]),
      ("a COLLATE \"a\"\"b\".\"where\"", .collate (col "a") ["a\"b", "where"]),
      ("a COLLATE a.select", .collate (col "a") ["a", "select"]),
      ("a COLLATE between", .collate (col "a") ["between"]),
      ("a+b COLLATE \"C\"", .binary .add (col "a") (annotated (col "b"))),
      ("a COLLATE \"C\"+b", .binary .add (annotated (col "a")) (col "b")),
      ("-a COLLATE \"C\"", annotated (.unary .neg (col "a"))),
      ("-(a COLLATE \"C\")", .unary .neg (annotated (col "a"))),
      ("a::text COLLATE \"C\"", annotated (.cast (col "a") ⟨.text, []⟩)),
      ("a COLLATE \"C\"::text", .cast (annotated (col "a")) ⟨.text, []⟩),
      ("a[1] COLLATE \"C\"", annotated (.subscript (col "a") [.index 1])),
      ("(a COLLATE \"C\")[1]", .subscript (annotated (col "a")) [.index 1]),
      ("a COLLATE \"C\" COLLATE \"POSIX\"", .collate (annotated (col "a")) ["POSIX"]),
      ("NOT a COLLATE \"C\"", .unary .not (annotated (col "a"))),
      ("a=b COLLATE \"C\"", .binary .eq (col "a") (annotated (col "b"))),
      ("a||b COLLATE \"C\"", .concat (col "a") (annotated (col "b"))),
      ("a COLLATE \"C\"||b", .concat (annotated (col "a")) (col "b")),
      ("NULL COLLATE \"C\"", annotated .null),
      ("NULL COLLATE \"C\" IS DISTINCT FROM a", .distinctFrom (annotated .null) (col "a")),
      ("a COLLATE \"C\" IS DISTINCT FROM NULL", .distinctFrom (annotated (col "a")) .null),
      ("a BETWEEN (b COLLATE \"C\") AND c", .between (col "a") (annotated (col "b")) (col "c")),
      ("a BETWEEN b AND c COLLATE \"C\"", .between (col "a") (col "b") (annotated (col "c"))),
      ("a BETWEEN f(b COLLATE \"C\") AND c", .between (col "a") (.call ["f"] [annotated (col "b")]) (col "c")),
      ("SUBSTRING(a FOR b COLLATE \"C\" FROM c COLLATE \"C\")",
        .substring .forFrom [col "a", annotated (col "b"), annotated (col "c")]),
      ("? COLLATE between ? ?", .jsonExistence .key (.collate (anon 1) ["between"]) (anon 2))
      ] do
    parsed source expected
    count := count + 1
    count := count + (← roundTrip expected (if source == "? COLLATE between ? ?" then
      [.anonymous 1, .anonymous 2] else []))
  for source in ["a COLLATE", "a COLLATE \"\"", "a COLLATE 'C'", "a COLLATE select",
      "a COLLATE .c", "a COLLATE c.", "a COLLATE c..d", "a COLLATE ?",
      "a COLLATE \"C\"[1]", "a BETWEEN b COLLATE \"C\" AND c",
      "a BETWEEN b+c COLLATE \"C\" AND d", "a BETWEEN -(b) COLLATE \"C\" AND c"] do
    expectError source (Advanced.parseExpression source)
    count := count + 1
  for (expr, uses) in [
      (annotated (anon 1), [Parameter.anonymous 1]),
      (.concat (annotated (anon 1)) (annotated (anon 2)), [.anonymous 1, .anonymous 2]),
      (.substring .forFrom [annotated (anon 1), anon 2, anon 3],
        [.anonymous 1, .anonymous 2, .anonymous 3]),
      (.subscript (annotated (anon 1)) [.slice (some (anon 2)) (some (anon 3))],
        [.anonymous 1, .anonymous 2, .anonymous 3]),
      (.caseExpr (some (annotated (anon 1))) [(annotated (anon 2), annotated (anon 3))]
        (some (annotated (anon 4))), [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4]),
      (.concat (annotated (num 2)) (annotated (num 1)), [.numbered 2, .numbered 1]),
      (.concat (annotated (num 3)) (annotated (num 3)), [.numbered 3, .numbered 3])] do
    count := count + (← roundTrip expr uses)
  for name in [["a.b"], ["a", "b"], ["a\"b"], ["? $1 -- ;"], ["a", "b", "c", "d"]] do
    count := count + (← roundTrip (.collate (text "x") name))
  for (source, total) in [
      ("WITH c AS (SELECT ? COLLATE \"C\" AS x) SELECT ? COLLATE \"C\" FROM c ORDER BY ? COLLATE \"C\"", 3),
      ("SELECT ? COLLATE \"C\" FROM (SELECT ? COLLATE \"C\" AS x) AS d WHERE (? COLLATE \"C\")=(? COLLATE \"C\")", 4),
      ("SELECT ? COLLATE \"C\" UNION ALL SELECT ? COLLATE \"POSIX\"", 2),
      ("WITH RECURSIVE r(x) AS (SELECT ? COLLATE \"C\" UNION ALL SELECT ? COLLATE \"C\" FROM r WHERE FALSE) SELECT ? COLLATE \"C\" FROM r", 3)] do
    let query ← expectOk source (Advanced.parseQuery source)
    count := count + (← roundTripQuery query ((List.range total).map (fun n => .anonymous (n+1))))
  boundary .identityV01 (.collate (text "x") []) "invalid" "representation.collation-name"
  boundary .identityV01 (.collate (text "x") [""]) "invalid" "representation.empty-name"
  boundary .identityV01 (.collate (text "x") ["a\x00b"]) "invalid" "representation.name-nul"
  boundary .identityV01 (.collate (text "x") [String.ofList (List.replicate 64 'a')])
    "invalid" "representation.name-length"
  boundary .identityV01 (annotated (anon 2)) "invalid" "representation.parameters"
  boundary .postgres16V01 (.concat (annotated (anon 1)) (annotated (num 1)))
    "unsupported" "coverage.mixed-parameters"
  boundary .identityV01 (nested 10) "inconclusive" "resource.depth" 5
  count := count + 7
  for source in ["SELECT 'x' COLLATE \"C\"", "SELECT ? COLLATE \"C\"",
      "SELECT ('x'||'y') COLLATE \"C\"", "SELECT 'a' BETWEEN 'a' COLLATE \"C\" AND 'z'"] do
    let query ← expectOk source (Advanced.parseSQLiteQuery source)
    match RenderContract.check .sqliteV01 query with
    | .error (.unsupported diagnostic) =>
        SQLean.Tests.assert (diagnostic.code == "coverage.sqlite.collation")
          "SQLite COLLATE profile diagnostic changed"
    | other => throw (IO.userError s!"SQLite COLLATE was not explicitly excluded: {reprStr (other.map (·.sql))}")
    count := count + 1
  -- SQLite has a different concatenation precedence. Parsing retains that
  -- distinction even though its checked COLLATE renderer remains excluded.
  for (source, expr) in [
      ("SELECT a||b COLLATE c*d", Advanced.Expr.binary .mul
        (.concat (col "a") (.collate (col "b") ["c"])) (col "d")),
      ("SELECT -a COLLATE c", .collate (.unary .neg (col "a")) ["c"]),
      ("SELECT a COLLATE c||b", .concat (.collate (col "a") ["c"]) (col "b")),
      ("SELECT a BETWEEN b COLLATE c AND d", .between (col "a") (.collate (col "b") ["c"]) (col "d"))] do
    let query ← expectOk source (Advanced.parseSQLiteQuery source)
    SQLean.Tests.assert (decide (query = scalar expr)) s!"SQLite COLLATE precedence changed: {source}"
    count := count + 1
  pure count

end SQLean.Tests
