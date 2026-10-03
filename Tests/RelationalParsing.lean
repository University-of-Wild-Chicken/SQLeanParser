import SQLean.Parser
import SQLean.Pretty
import Tests.Support

namespace SQLean.Tests

private def accepted : List String := [
  "SELECT * FROM users",
  "SELECT u.id, u.name FROM users AS u",
  "SELECT id label, name AS display_name FROM users u",
  "SELECT u.*, u.id + 1 AS next_id FROM users u",
  "SELECT *, id FROM users",
  "SELECT id, * FROM users",
  "SELECT \"u\".\"ID\" AS \"User ID\" FROM \"Users\" \"u\"",
  "SELECT \"u\".* FROM \"Users\" AS \"u\"",
  "SELECT u.id, o.id FROM users u JOIN orders o ON u.id = o.user_id",
  "SELECT u.id FROM users u INNER JOIN orders o ON u.id = o.user_id",
  "SELECT u.id FROM users u LEFT JOIN orders o ON u.id = o.user_id",
  "SELECT u.id FROM users u LEFT OUTER JOIN orders o ON u.id = o.user_id",
  "SELECT u.id FROM users u RIGHT JOIN orders o ON u.id = o.user_id",
  "SELECT u.id FROM users u RIGHT OUTER JOIN orders o ON u.id = o.user_id",
  "SELECT u.id FROM users u FULL JOIN orders o ON u.id = o.user_id",
  "SELECT u.id FROM users u FULL OUTER JOIN orders o ON u.id = o.user_id",
  "SELECT u.id FROM users u CROSS JOIN orders o",
  "SELECT a.id FROM users a JOIN orders b ON a.id = b.user_id LEFT JOIN lines c ON b.id = c.order_id",
  "SELECT COUNT(*), COUNT(id), COUNT(DISTINCT name) FROM users",
  "SELECT SUM(age), AVG(age), MIN(age), MAX(age) FROM users",
  "SELECT SUM(DISTINCT age + 1), AVG(DISTINCT age), MIN(DISTINCT age), MAX(DISTINCT age) FROM users",
  "SELECT age, COUNT(*) AS total FROM users GROUP BY age HAVING COUNT(*) > 1 ORDER BY total DESC",
  "SELECT age + 1, name FROM users GROUP BY age + 1, name ORDER BY age + 1 ASC, name DESC LIMIT 2 OFFSET 1",
  "SELECT COUNT(*) FROM users HAVING COUNT(*) > 0",
  "SELECT DISTINCT u.name FROM users u LEFT JOIN orders o ON u.id = o.user_id WHERE o.id IS NULL",
  "SELECT u.id FROM users u WHERE NOT u.id IS NULL AND u.name IS NOT NULL",
  "SELECT (id IS NULL) = FALSE, (id = 1) IS NOT NULL FROM users",
  "SELECT -u.age * +2 + 1, NOT u.age >= 18 FROM users u",
  "SELECT count, sum, avg, min, max FROM users",
  "SELECT \"group\", \"join\", \"is\" FROM \"from\"",
  "SELECT /* alias */ u.id -- selected\nFROM users AS u;",
  "SELECT u.id FROM users u JOIN orders o ON (u.id = o.user_id AND o.id > 1) OR FALSE",
  "SELECT COUNT ( * ) FROM users",
  "SELECT COUNT(DISTINCT (age + 1)) FROM users",
  "SELECT q.id FROM (SELECT id FROM users) AS q",
  "SELECT q.* FROM (SELECT id, name FROM users WHERE active) q",
  "SELECT u.id FROM users u JOIN (SELECT user_id FROM orders) o ON u.id = o.user_id",
  "SELECT q.id FROM (SELECT r.id FROM (SELECT id FROM users) r) q",
  "SELECT q.total FROM (SELECT SUM(age) AS total FROM users) q",
  "WITH active_users AS (SELECT id FROM users WHERE active) SELECT id FROM active_users",
  "WITH active_users (user_id) AS (SELECT id FROM users WHERE active) SELECT user_id FROM active_users",
  "WITH a AS (SELECT id FROM users), b AS (SELECT id FROM a) SELECT b.id FROM b",
  "WITH a AS (WITH b AS (SELECT id FROM users) SELECT id FROM b) SELECT id FROM a",
  "SELECT q.id FROM (WITH a AS (SELECT id FROM users) SELECT id FROM a) q",
  "WITH a AS (SELECT id FROM users) SELECT q.id FROM (SELECT id FROM a) q",
  "WITH \"group\" (\"ID\") AS (SELECT id FROM users) SELECT \"ID\" FROM \"group\";",
  "WITH a AS (SELECT id FROM users ORDER BY id LIMIT 2) SELECT id FROM a ORDER BY id",
  "WITH RECURSIVE a AS (SELECT id FROM users) SELECT id FROM a"
]

private def rejected : List String := [
  "SELECT * AS all_users FROM users", "SELECT u.* alias FROM users u",
  "SELECT u.* + 1 FROM users u", "SELECT u. FROM users u",
  "SELECT u..id FROM users u", "SELECT a.b.c FROM users",
  "SELECT .id FROM users", "SELECT id AS FROM users", "SELECT id AS where FROM users",
  "SELECT id FROM users AS", "SELECT id FROM users AS where",
  "SELECT id FROM users JOIN orders", "SELECT id FROM users JOIN orders ON",
  "SELECT id FROM users INNER orders ON TRUE",
  "SELECT id FROM users LEFT OUTER orders ON TRUE",
  "SELECT id FROM users OUTER JOIN orders ON TRUE",
  "SELECT id FROM users CROSS JOIN orders ON TRUE",
  "SELECT id FROM users NATURAL JOIN orders",
  "SELECT id FROM users JOIN orders USING (id)",
  "SELECT id FROM users, orders",
  "SELECT id FROM users GROUP age", "SELECT id FROM users GROUP BY",
  "SELECT id FROM users GROUP BY age,", "SELECT id FROM users GROUP BY age DESC",
  "SELECT id FROM users HAVING", "SELECT id FROM users HAVING TRUE GROUP BY id",
  "SELECT id FROM users ORDER BY id GROUP BY id",
  "SELECT id FROM users GROUP BY id WHERE TRUE",
  "SELECT COUNT() FROM users", "SELECT COUNT(id, age) FROM users",
  "SELECT COUNT(DISTINCT *) FROM users", "SELECT SUM(*) FROM users",
  "SELECT AVG(*) FROM users", "SELECT COUNT(ALL id) FROM users",
  "SELECT COUNT(DISTINCT) FROM users", "SELECT unknown(id) FROM users",
  "SELECT \"COUNT\"(id) FROM users", "SELECT u.count(id) FROM users u",
  "SELECT id IS TRUE FROM users", "SELECT id IS NOT FALSE FROM users",
  "SELECT id IS FROM users", "SELECT id IS NULL IS NULL FROM users",
  "SELECT id = 1 IS NULL FROM users", "SELECT id IS NULL = TRUE FROM users",
  "SELECT -NOT TRUE FROM users", "SELECT id = NOT TRUE FROM users",
  "SELECT id < age < 100 FROM users", "SELECT NULL FROM users",
  "SELECT * FROM users;;", "SELECT * FROM users; SELECT * FROM orders",
  "SELECT u.id FROM users u LIMIT 1.5", "SELECT u.id FROM users u OFFSET 1",
  "SELECT id FROM (SELECT id FROM users)",
  "SELECT id FROM (SELECT id FROM users) AS",
  "SELECT q.id FROM (SELECT id FROM users;) q",
  "SELECT q.id FROM (SELECT id FROM users; SELECT id FROM users) q",
  "SELECT q.id FROM (SELECT id FROM users q",
  "SELECT q.id FROM () q", "SELECT q.id FROM (users) q",
  "SELECT q.id FROM ((SELECT id FROM users)) q",
  "WITH", "WITH SELECT id FROM users",
  "WITH a SELECT id FROM users", "WITH a AS SELECT id FROM users",
  "WITH a AS () SELECT id FROM a",
  "WITH a AS (SELECT id FROM users;) SELECT id FROM a",
  "WITH a AS (SELECT id FROM users)",
  "WITH a AS (SELECT id FROM users), SELECT id FROM a",
  "WITH a () AS (SELECT id FROM users) SELECT id FROM a",
  "WITH a (id,) AS (SELECT id FROM users) SELECT id FROM a",
  "WITH a AS (DELETE FROM users) SELECT * FROM a"
]

private def col (qualifier name : String) : RelExpr := .column (some qualifier) name
private def int (n : Nat) : RelExpr := .literal (.int n)

def relationalParsingTests : IO Nat := do
  for source in accepted do
    let query ← expectOk source (parseRelQuery source)
    let _ ← expectOk source (parseStatement source)
    let rendered := toSql query
    let reparsed ← expectOk s!"relational round trip: {rendered}" (parseRelQuery rendered)
    SQLean.Tests.assert (query == reparsed) s!"relational SQL rendering changed AST: {source}"
  for source in rejected do
    expectError source (parseRelQuery source)
    expectError source (parseStatement source)

  let joined ← expectOk "JOIN AST" (parseRelQuery
    "SELECT u.*, o.id AS order_id FROM users u LEFT OUTER JOIN orders o ON u.id = o.user_id CROSS JOIN flags f")
  SQLean.Tests.assert (joined == {
    source := { name := "users", alias := some "u" },
    selectList := [.all (some "u"), .expression (col "o" "id") (some "order_id")],
    joins := [
      { kind := .left, table := { name := "orders", alias := some "o" },
        on := some (.binary .eq (col "u" "id") (col "o" "user_id")) },
      { kind := .cross, table := { name := "flags", alias := some "f" } }] })
    "JOIN kinds, aliases, qualification, or order changed"

  let grouped ← expectOk "aggregation AST" (parseRelQuery
    "SELECT DISTINCT u.age, COUNT(*) AS n, SUM(DISTINCT u.id) total FROM users u WHERE u.id > 0 GROUP BY u.age HAVING COUNT(*) >= 2 ORDER BY n DESC LIMIT 5 OFFSET 1")
  SQLean.Tests.assert (grouped == {
    source := { name := "users", alias := some "u" },
    selectList := [.expression (col "u" "age"), .expression .countAll (some "n"),
      .expression (.aggregate .sum (col "u" "id") true) (some "total")],
    whereClause := some (.binary .gt (col "u" "id") (int 0)),
    groupBy := [col "u" "age"], having := some (.binary .ge .countAll (int 2)),
    distinct := true, orderBy := [{ expr := .column none "n", descending := true }],
    limit := some 5, offset := some 1 })
    "grouping, aggregate, alias, or clause AST changed"

  let nulls ← expectOk "IS NULL precedence" (parseRelQuery
    "SELECT NOT u.id IS NULL AND u.id + 1 IS NOT NULL FROM users u")
  SQLean.Tests.assert (nulls.selectList == [.expression
    (.binary .and (.unary .not (.isNull (col "u" "id")))
      (.isNull (.binary .add (col "u" "id") (int 1)) true))])
    "IS NULL must bind with comparisons, below arithmetic and above NOT"

  let old ← expectOk "legacy statement compatibility" (parseStatement
    "SELECT count, join, group, as, having, is FROM inner")
  match old with
  | .select _ => pure ()
  | _ => throw (IO.userError "previously accepted SELECT must retain the legacy AST")
  expectError "MVP remains strict" (parseQuery "SELECT u.id FROM users u")

  let tokens ← expectOk "relational tokens" (lex "SELECT u.id FROM users u")
  let tokenQuery ← expectOk "relational token API" (Parser.parseRelQueryTokens tokens)
  let stringQuery ← expectOk "relational string API" (parseRelQuery "SELECT u.id FROM users u")
  SQLean.Tests.assert (tokenQuery == stringQuery) "relational token and string APIs differ"
  expectError "relational missing EOF" (Parser.parseRelQueryTokens [])
  expectError "relational duplicate EOF" (Parser.parseRelQueryTokens [⟨.eof, {}⟩, ⟨.eof, {}⟩])

  match parseRelQuery "SELECT u.id FROM users u\nJOIN orders o ON\n" with
  | .error error =>
    SQLean.Tests.assert (error.position.line == 3 && error.position.column == 1)
      s!"JOIN expression error position differs: {error}"
  | .ok _ => throw (IO.userError "accepted missing JOIN predicate")

  let joins := String.intercalate " " ((List.range 100).map fun n => s!"JOIN t t{n} ON TRUE")
  let long ← expectOk "100 JOIN clauses" (parseRelQuery s!"SELECT root.id FROM t root {joins}")
  SQLean.Tests.assert (long.joins.length == 100) "lost JOIN clauses"
  let groups := String.intercalate ", " ((List.range 100).map fun n => s!"t.c{n}")
  let grouped ← expectOk "100 GROUP BY items" (parseRelQuery s!"SELECT COUNT(*) FROM t GROUP BY {groups}")
  SQLean.Tests.assert (grouped.groupBy.length == 100) "lost GROUP BY items"

  let derived ← expectOk "derived table AST" (parseRelQuery
    "SELECT q.id FROM (SELECT id FROM users) AS q")
  SQLean.Tests.assert (derived.source == {
    name := "", alias := some "q", derived := some {
      source := { name := "users" }, selectList := [.expression (.column none "id")] } })
    "derived query or its alias changed"
  let ctes ← expectOk "CTE AST" (parseRelQuery
    "WITH a (user_id) AS (SELECT id FROM users), b AS (SELECT user_id FROM a) SELECT user_id FROM b")
  SQLean.Tests.assert (ctes.ctes == [
    { name := "a", columns := ["user_id"], query := {
        source := { name := "users" }, selectList := [.expression (.column none "id")] } },
    { name := "b", query := {
        source := { name := "a" }, selectList := [.expression (.column none "user_id")] } }])
    "CTE order, output columns, or query changed"
  let cteStatement ← expectOk "WITH statement dispatch" (parseStatement
    "WITH a AS (SELECT id FROM users) SELECT id FROM a")
  match cteStatement with
  | .relational _ => pure ()
  | _ => throw (IO.userError "WITH returned wrong statement kind")
  let nested := (List.range 40).foldl
    (fun sql _ => s!"SELECT q.id FROM ({sql}) q") "SELECT id FROM users"
  let _ ← expectOk "40 nested derived tables" (parseRelQuery nested)
  let cteDefs := String.intercalate ", " ((List.range 100).map fun n => s!"t{n} AS (SELECT id FROM t)")
  let manyCtes ← expectOk "100 CTE definitions" (parseRelQuery s!"WITH {cteDefs} SELECT id FROM t99")
  SQLean.Tests.assert (manyCtes.ctes.length == 100) "lost CTE definitions"
  pure (3 * accepted.length + 2 * rejected.length + 16)

end SQLean.Tests
