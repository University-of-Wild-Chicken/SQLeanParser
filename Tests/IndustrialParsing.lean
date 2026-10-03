import SQLean.Parser
import SQLean.Pretty
import Tests.Support

namespace SQLean.Tests

private def accepted : List String := [
  "SELECT 1",
  "SELECT 1 + 2 * 3 AS total;",
  "SELECT 'portable SQL', TRUE, -7",
  "SELECT 1 WHERE TRUE",
  "SELECT DISTINCT 1 ORDER BY 1 DESC LIMIT 2 OFFSET 1",
  "SELECT COUNT(*) HAVING COUNT(*) > 0",
  "SELECT 1 UNION SELECT 2",
  "SELECT 1 UNION ALL SELECT 2",
  "SELECT 1 UNION SELECT 2 UNION ALL SELECT 3 UNION SELECT 4",
  "SELECT 1 AS n UNION ALL SELECT 2 AS other ORDER BY n DESC LIMIT 3 OFFSET 1",
  "SELECT id FROM users UNION SELECT user_id FROM orders",
  "SELECT id FROM users WHERE age >= 18 UNION ALL SELECT user_id FROM orders WHERE amount > 100 ORDER BY 1",
  "SELECT age AS value, COUNT(*) AS n FROM users GROUP BY age HAVING COUNT(*) > 1 UNION ALL SELECT amount, COUNT(*) FROM orders GROUP BY amount HAVING COUNT(*) > 2 ORDER BY value, n DESC",
  "SELECT 1 AS n UNION ALL SELECT id FROM users UNION SELECT 3",
  "SELECT q.n FROM (SELECT 1 AS n UNION ALL SELECT 2 ORDER BY n LIMIT 1) q",
  "WITH a(n) AS (SELECT 1 UNION ALL SELECT 2) SELECT n FROM a",
  "WITH a(n) AS (SELECT 1) SELECT n FROM a UNION SELECT 2 ORDER BY n",
  "WITH a AS (SELECT 1 AS n), b AS (SELECT n FROM a UNION SELECT 2) SELECT n FROM b",
  "WITH RECURSIVE a AS (SELECT id FROM users) SELECT id FROM a",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM seq WHERE n < 10) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION SELECT n + 1 FROM seq WHERE n < 10) SELECT n FROM seq ORDER BY n DESC LIMIT 5 OFFSET 1",
  "WITH RECURSIVE tree(id, depth) AS (SELECT id, 0 FROM employees WHERE manager_id = 0 UNION ALL SELECT e.id, t.depth + 1 FROM employees e JOIN tree t ON e.manager_id = t.id) SELECT id, depth FROM tree",
  "WITH RECURSIVE edges AS (SELECT id, manager_id FROM employees), tree(id) AS (SELECT id FROM edges WHERE manager_id = 0 UNION SELECT e.id FROM edges e JOIN tree t ON e.manager_id = t.id) SELECT id FROM tree",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM seq WHERE n < 5), filtered AS (SELECT n FROM seq WHERE n > 2) SELECT n FROM filtered",
  "SELECT s.n FROM (WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM seq WHERE n < 5) SELECT n FROM seq) s",
  "WITH outer_cte(n) AS (WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM seq WHERE n < 5) SELECT n FROM seq) SELECT n FROM outer_cte",
  "WITH RECURSIVE \"recursive\" (\"union\") AS (SELECT 1 UNION ALL SELECT \"union\" + 1 FROM \"recursive\" WHERE \"union\" < 3) SELECT \"union\" FROM \"recursive\"",
  "select 1 as n union /* duplicate preserving */ all select 2 order by n;",
  "WITH /* mode */ RECURSIVE seq(n) AS (SELECT 1 -- anchor\nUNION ALL SELECT n + 1 FROM seq WHERE n < 3) SELECT n FROM seq"
]

private def rejected : List String := [
  "SELECT", "SELECT FROM users", "SELECT 1,", "SELECT 1 FROM",
  "SELECT 1 JOIN users ON TRUE", "SELECT 1 WHERE", "SELECT 1 OFFSET 2",
  "SELECT 1 UNION", "SELECT 1 UNION ALL", "SELECT 1 UNION DISTINCT",
  "SELECT 1 UNION DISTINCT SELECT 2", "SELECT 1 UNION ALL DISTINCT SELECT 2", "SELECT 1 UNION DISTINCT ALL SELECT 2",
  "SELECT 1 UNION UNION SELECT 2", "SELECT 1 UNION SELECT",
  "SELECT 1 UNION (SELECT 2)", "(SELECT 1) UNION SELECT 2",
  "SELECT 1 ORDER BY 1 UNION SELECT 2", "SELECT 1 LIMIT 1 UNION ALL SELECT 2",
  "SELECT 1 UNION SELECT 2 ORDER BY 1 UNION SELECT 3",
  "SELECT 1 UNION WITH a AS (SELECT 2) SELECT 2",
  "SELECT 1 INTERSECT SELECT 2", "SELECT 1 EXCEPT SELECT 2",
  "SELECT 1 UNION ALL SELECT 2;;", "SELECT 1; UNION SELECT 2",
  "WITH RECURSIVE", "WITH RECURSIVE SELECT 1",
  "WITH RECURSIVE RECURSIVE a AS (SELECT 1) SELECT 1",
  "WITH RECURSIVE a(n) AS SELECT 1 SELECT 1",
  "WITH RECURSIVE a(n) AS (SELECT 1 UNION ALL) SELECT n FROM a",
  "WITH RECURSIVE a(n) AS (SELECT 1)"
]

private def int (n : Nat) : RelExpr := .literal (.int n)

def industrialParsingTests : IO Nat := do
  for source in accepted do
    let query ← expectOk source (parseRelQuery source)
    let _ ← expectOk source (parseStatement source)
    let rendered := toSql query
    let reparsed ← expectOk s!"industrial round trip: {rendered}" (parseRelQuery rendered)
    SQLean.Tests.assert (query == reparsed) s!"industrial rendering changed AST: {source}"
  for source in rejected do
    expectError source (parseRelQuery source)
    expectError source (parseStatement source)

  let constant ← expectOk "SELECT without FROM AST" (parseRelQuery "SELECT 1 + 2 * 3 AS n")
  SQLean.Tests.assert (constant == {
    source := { name := "" },
    selectList := [.expression (.binary .add (int 1) (.binary .mul (int 2) (int 3))) (some "n")] })
    "SELECT without FROM must have an empty source and retain expression precedence"

  let compound ← expectOk "compound AST" (parseRelQuery
    "SELECT 1 AS n UNION ALL SELECT 2 UNION SELECT 3 ORDER BY n DESC LIMIT 2 OFFSET 1")
  SQLean.Tests.assert (compound == {
    source := { name := "" }, selectList := [.expression (int 1) (some "n")],
    unions := [
      { all := true, query := { source := { name := "" }, selectList := [.expression (int 2)] } },
      { all := false, query := { source := { name := "" }, selectList := [.expression (int 3)] } }],
    orderBy := [{ expr := .column none "n", descending := true }],
    limit := some 2, offset := some 1 })
    "UNION flags/order or global sorting/pagination changed"

  let recursive ← expectOk "recursive CTE AST" (parseRelQuery
    "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM seq WHERE n < 10) SELECT n FROM seq")
  SQLean.Tests.assert (recursive == {
    source := { name := "seq" }, selectList := [.expression (.column none "n")], recursive := true,
    ctes := [{ name := "seq", columns := ["n"], query := {
      source := { name := "" }, selectList := [.expression (int 1)],
      unions := [{ all := true, query := {
        source := { name := "seq" },
        selectList := [.expression (.binary .add (.column none "n") (int 1))],
        whereClause := some (.binary .lt (.column none "n") (int 10)) } }] } }] })
    "WITH RECURSIVE must mark the enclosing CTE list and preserve anchor/step shape"

  let unionDefault ← expectOk "deduplicating UNION" (parseRelQuery "SELECT 1 UNION SELECT 2")
  SQLean.Tests.assert (unionDefault.unions.map (·.all) == [false]) "bare UNION must preserve deduplication mode"

  for source in ["SELECT 1", "SELECT 1 UNION SELECT 2",
      "WITH RECURSIVE seq(n) AS (SELECT 1) SELECT n FROM seq"] do
    let statement ← expectOk "industrial dispatch" (parseStatement source)
    match statement with
    | .relational _ => pure ()
    | _ => throw (IO.userError s!"industrial query must use relational AST: {source}")
  expectError "MVP still requires FROM" (parseQuery "SELECT 1")
  expectError "MVP does not support UNION" (parseQuery "SELECT id FROM users UNION SELECT id FROM users")

  let arms := String.intercalate " UNION ALL " ((List.range 100).map fun n => s!"SELECT {n}")
  let long ← expectOk "100 compound arms" (parseRelQuery arms)
  SQLean.Tests.assert (long.unions.length == 99) "lost compound arms"
  let longAgain ← expectOk "100 compound arms round trip" (parseRelQuery (toSql long))
  SQLean.Tests.assert (long == longAgain) "long compound rendering changed AST"

  let nested := (List.range 30).foldl
    (fun sql _ => s!"SELECT q.n FROM ({sql}) q UNION ALL SELECT 0") "SELECT 1 AS n"
  let deep ← expectOk "30 nested compounds" (parseRelQuery nested)
  let deepAgain ← expectOk "30 nested compounds round trip" (parseRelQuery (toSql deep))
  SQLean.Tests.assert (deep == deepAgain) "nested compound rendering changed AST"

  match parseRelQuery "SELECT 1 UNION ALL\n" with
  | .error error =>
    SQLean.Tests.assert (error.position.line == 2 && error.position.column == 1)
      s!"missing UNION arm error position differs: {error}"
  | .ok _ => throw (IO.userError "accepted missing UNION arm")
  pure (3 * accepted.length + 2 * rejected.length + 13)

end SQLean.Tests
