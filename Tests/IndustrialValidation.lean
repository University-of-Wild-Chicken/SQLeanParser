import SQLean.Parser
import SQLean.NestedValidation
import SQLean.CRUDValidation
import Tests.Support

namespace SQLean.Tests

private def industrialSchema : Schema := [
  ⟨"users", [⟨"id", .int⟩, ⟨"age", .int⟩, ⟨"name", .text⟩]⟩,
  ⟨"orders", [⟨"id", .int⟩, ⟨"user_id", .int⟩, ⟨"amount", .int⟩]⟩,
  ⟨"employees", [⟨"id", .int⟩, ⟨"manager_id", .int⟩, ⟨"name", .text⟩]⟩,
  ⟨"a", [⟨"n", .int⟩]⟩,
  ⟨"b", [⟨"n", .int⟩]⟩]

private def acceptedIndustrial : List (String × List SqlType) := [
  ("SELECT 1", [.int]),
  ("SELECT 1 + 2 AS n, 'ready' AS status, TRUE AS ok", [.int, .text, .bool]),
  ("SELECT COUNT(*)", [.int]),
  ("SELECT SUM(1), AVG(1), MIN(1), MAX(1)", [.nullable .int, .nullable .real, .nullable .int, .nullable .int]),
  ("SELECT 1 WHERE FALSE", [.int]),
  ("SELECT 1 AS n ORDER BY n LIMIT 3 OFFSET 1", [.int]),
  ("SELECT 1 AS n GROUP BY n HAVING COUNT(*) > 0", [.int]),
  ("SELECT 1 AS n UNION SELECT 2 ORDER BY n", [.int]),
  ("SELECT 1 UNION ALL SELECT 2 UNION SELECT 3 ORDER BY 1 DESC LIMIT 2 OFFSET 1", [.int]),
  ("SELECT id AS n FROM users UNION SELECT user_id FROM orders ORDER BY n", [.int]),
  ("SELECT name, age FROM users UNION ALL SELECT 'unknown', 0 ORDER BY 1, 2 DESC", [.text, .int]),
  ("SELECT SUM(age) AS n FROM users UNION SELECT SUM(amount) FROM orders ORDER BY n", [.nullable .int]),
  ("SELECT COUNT(*) AS n FROM users UNION ALL SELECT 0 ORDER BY n", [.int]),
  ("SELECT d.n FROM (SELECT 1 AS n UNION ALL SELECT 2) d", [.int]),
  ("WITH x(n) AS (SELECT 1 UNION SELECT 2) SELECT n FROM x", [.int]),
  ("WITH x(n) AS (SELECT 1) SELECT n FROM x UNION SELECT n + 1 FROM x ORDER BY n", [.int]),
  ("WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM seq WHERE n < 5) SELECT n FROM seq ORDER BY n", [.int]),
  ("WITH RECURSIVE seq(n) AS (SELECT 1 UNION SELECT n + 1 FROM seq WHERE n < 5) SELECT SUM(n) FROM seq", [.nullable .int]),
  ("WITH RECURSIVE seq AS (SELECT 1 AS n UNION ALL SELECT n + 1 FROM seq WHERE n < 5) SELECT * FROM seq", [.int]),
  ("WITH RECURSIVE seq(n, label) AS (SELECT 1, 'level' UNION ALL SELECT n + 1, label FROM seq WHERE n < 5) SELECT label, n FROM seq", [.text, .int]),
  ("WITH RECURSIVE tree(id, depth) AS (SELECT id, 0 FROM employees WHERE manager_id = 0 UNION ALL SELECT e.id, t.depth + 1 FROM employees e JOIN tree t ON e.manager_id = t.id) SELECT id, depth FROM tree", [.int, .int]),
  ("WITH RECURSIVE tree(id) AS (SELECT id FROM employees WHERE manager_id = 0 UNION SELECT e.id FROM tree t JOIN employees e ON e.manager_id = t.id) SELECT id FROM tree", [.int]),
  ("WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT seq.n + 1 FROM seq CROSS JOIN users u WHERE seq.n < 3 AND u.id = 1) SELECT n FROM seq", [.int]),
  ("WITH RECURSIVE seed(n) AS (SELECT 1), seq(n) AS (SELECT n FROM seed UNION ALL SELECT n + 1 FROM seq WHERE n < 3), result(n) AS (SELECT n FROM seq) SELECT n FROM result", [.int]),
  ("WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM seq WHERE n < 3) SELECT n FROM seq UNION ALL SELECT 99 ORDER BY n", [.int]),
  ("WITH RECURSIVE seq(n) AS (SELECT SUM(id) FROM users UNION ALL SELECT n + 1 FROM seq WHERE n < 10) SELECT n FROM seq", [.nullable .int]),
  ("WITH RECURSIVE x AS (SELECT id FROM users) SELECT id FROM x", [.int]),
  ("WITH RECURSIVE x(n) AS (SELECT 1 UNION ALL SELECT 2) SELECT n FROM x", [.int]),
  ("SELECT d.n FROM (WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM seq WHERE n < 3) SELECT n FROM seq) d", [.int]),
  ("WITH RECURSIVE a(n) AS (WITH a(n) AS (SELECT 1) SELECT n FROM a) SELECT n FROM a", [.int]),
  ("WITH RECURSIVE a(n) AS (WITH RECURSIVE a(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM a WHERE n < 3) SELECT n FROM a) SELECT n FROM a", [.int]),
  ("WITH RECURSIVE seq(n) AS (SELECT d.n FROM (WITH seq(n) AS (SELECT 1) SELECT n FROM seq) d UNION ALL SELECT n + 1 FROM seq WHERE n < 3) SELECT n FROM seq", [.int]),
  ("WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT n FROM seq) SELECT n FROM seq", [.int])
]

private def rejectedIndustrial : List String := [
  "SELECT *",
  "SELECT users.*",
  "SELECT id",
  "SELECT users.id",
  "SELECT 1 WHERE 7",
  "SELECT 1 ORDER BY missing",
  "SELECT 1 UNION SELECT 1, 2",
  "SELECT 1 UNION SELECT 'x'",
  "SELECT TRUE UNION SELECT 1",
  "SELECT SUM(age) FROM users UNION SELECT age FROM users",
  "SELECT SUM(age) FROM users UNION SELECT AVG(age) FROM users",
  "SELECT id FROM users UNION SELECT missing FROM users",
  "SELECT id FROM users UNION SELECT id FROM missing",
  "SELECT id FROM users UNION SELECT users.id FROM orders",
  "SELECT id AS n FROM users UNION SELECT age AS m FROM users ORDER BY m",
  "SELECT id AS n FROM users UNION SELECT age FROM users ORDER BY age",
  "SELECT id AS n FROM users UNION SELECT age FROM users ORDER BY users.id",
  "SELECT 1 AS n UNION SELECT 2 ORDER BY n + 1",
  "SELECT 1 AS n UNION SELECT 2 ORDER BY COUNT(*)",
  "SELECT 1 AS n UNION SELECT 2 ORDER BY 0",
  "SELECT 1 AS n UNION SELECT 2 ORDER BY -1",
  "SELECT 1 AS n UNION SELECT 2 ORDER BY +1",
  "SELECT 1 AS n UNION SELECT 2 ORDER BY 2",
  "SELECT 1 AS n, 2 AS n UNION SELECT 3, 4 ORDER BY n",
  "WITH seq(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM seq) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT n FROM seq) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT n FROM seq UNION ALL SELECT n + 1 FROM seq) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT d.n FROM (SELECT n FROM seq) d UNION ALL SELECT n + 1 FROM seq) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT 'x' FROM seq) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT n, n + 1 FROM seq) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT SUM(id) FROM users UNION ALL SELECT 1 FROM seq) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT a.n FROM seq a JOIN seq b ON a.n = b.n) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT d.n FROM (SELECT n FROM seq) d) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT DISTINCT n FROM seq) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT COUNT(*) FROM seq) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT n FROM seq GROUP BY n) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT n FROM seq HAVING COUNT(*) > 0) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT n FROM seq WHERE COUNT(*) > 0) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT seq.n FROM seq LEFT JOIN users u ON seq.n = u.id) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT seq.n FROM users u RIGHT JOIN seq ON seq.n = u.id) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT seq.n FROM seq FULL JOIN users u ON seq.n = u.id) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT seq.n FROM seq CROSS JOIN (SELECT 1 AS n) d) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT n FROM seq ORDER BY n) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT n FROM seq LIMIT 5) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT n FROM seq UNION ALL SELECT n FROM seq) SELECT n FROM seq",
  "WITH RECURSIVE a(n) AS (SELECT n FROM a UNION ALL SELECT n + 1 FROM a) SELECT n FROM a",
  "WITH RECURSIVE a(n) AS (SELECT n FROM b), b(n) AS (SELECT 1) SELECT n FROM a",
  "WITH RECURSIVE a(n) AS (SELECT 1 UNION ALL SELECT n FROM b), b(n) AS (SELECT 1 UNION ALL SELECT n FROM a) SELECT n FROM a",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM seq), seq(n) AS (SELECT 2) SELECT n FROM seq",
  "WITH RECURSIVE seq(n, n) AS (SELECT 1, 2 UNION ALL SELECT n, n FROM seq) SELECT n FROM seq",
  "WITH RECURSIVE seq(n, m) AS (SELECT 1 UNION ALL SELECT n + 1 FROM seq) SELECT n FROM seq",
  "WITH RECURSIVE seq AS (SELECT 1 UNION ALL SELECT n + 1 FROM seq) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT missing FROM seq) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT n FROM seq) SELECT missing FROM seq"
]

def industrialValidationTests : IO Nat := do
  for (source, types) in acceptedIndustrial do
    let query ← expectOk source (parseRelQuery source)
    let checked ← expectOk source (certifyRelQuery industrialSchema query)
    SQLean.Tests.assert (checked.outputTypes == types) s!"wrong industrial types: {source}"
    SQLean.Tests.assert (checked.outputNames.length == types.length) s!"wrong industrial named arity: {source}"
    let statement ← expectOk source (parseStatement source)
    let statementTypes ← expectOk source (checkStatement industrialSchema statement)
    SQLean.Tests.assert (statementTypes == types) s!"wrong industrial statement types: {source}"
  for source in rejectedIndustrial do
    let query ← expectOk source (parseRelQuery source)
    expectError source (certifyRelQuery industrialSchema query)
  let one : RelQuery := { source := { name := "" }, selectList := [.expression (.literal (.int 1)) (some "n")] }
  let table : RelQuery := { source := { name := "users" }, selectList := [.expression (.column none "id")] }
  let compound : RelQuery := { one with unions := [⟨false, one⟩] }
  expectError "core must reject UNION metadata" (certifyRelQueryCore industrialSchema compound)
  expectError "core must reject recursive metadata" (certifyRelQueryCore industrialSchema { one with recursive := true })
  let malformed : List RelQuery := [
    { one with recursive := true },
    { one with source := { name := "", alias := some "absent" } },
    { one with joins := [⟨.cross, { name := "users" }, none⟩] },
    { compound with offset := some 1 },
    { compound with unions := [⟨false, { one with orderBy := [⟨.column none "n", false⟩] }⟩] },
    { compound with unions := [⟨false, { one with limit := some 1 }⟩] },
    { compound with unions := [⟨false, { one with offset := some 1 }⟩] },
    { compound with unions := [⟨false, { one with ctes := [⟨"x", table, []⟩] }⟩] },
    { compound with unions := [⟨false, { one with recursive := true }⟩] },
    { compound with unions := [⟨false, compound⟩] }]
  for query in malformed do
    expectError "malformed industrial AST" (certifyRelQuery industrialSchema query)
  pure (acceptedIndustrial.length + rejectedIndustrial.length + malformed.length + 2)

example (schema : Schema) (query : RelQuery) (types : List SqlType) :
    checkRelQuery schema query = .ok types ↔ ValidRelQuery schema query types := checkRelQuery_iff

end SQLean.Tests
