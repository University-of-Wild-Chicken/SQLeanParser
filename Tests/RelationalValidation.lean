import SQLean.RelationalValidation
import SQLean.Parser
import Tests.Support

namespace SQLean.Tests

private def schema : Schema := [
  ⟨"users", [⟨"id", .int⟩, ⟨"name", .text⟩, ⟨"age", .int⟩, ⟨"active", .bool⟩]⟩,
  ⟨"orders", [⟨"id", .int⟩, ⟨"user_id", .int⟩, ⟨"amount", .int⟩, ⟨"status", .text⟩]⟩,
  ⟨"metrics", [⟨"id", .int⟩, ⟨"rate", .real⟩, ⟨"optional", .nullable .int⟩]⟩]

private def validCases : List (String × List SqlType) := [
  ("SELECT u.id, u.name FROM users u", [.int, .text]),
  ("SELECT id, users.name FROM users", [.int, .text]),
  ("SELECT id AS same, name AS same FROM users", [.int, .text]),
  ("SELECT u.*, u.id AS another_id FROM users u", [.int, .text, .int, .bool, .int]),
  ("SELECT u.id, o.amount FROM users u JOIN orders o ON u.id = o.user_id", [.int, .int]),
  ("SELECT name, amount FROM users JOIN orders ON users.id = user_id", [.text, .int]),
  ("SELECT a.id, b.id FROM users a JOIN users b ON a.id = b.id", [.int, .int]),
  ("SELECT u.id, o.amount FROM users u CROSS JOIN orders o", [.int, .int]),
  ("SELECT u.id, o.amount FROM users u LEFT JOIN orders o ON u.id = o.user_id", [.int, .nullable .int]),
  ("SELECT u.id, o.amount FROM users u RIGHT JOIN orders o ON u.id = o.user_id", [.nullable .int, .int]),
  ("SELECT u.id, o.amount FROM users u FULL JOIN orders o ON u.id = o.user_id", [.nullable .int, .nullable .int]),
  ("SELECT o.amount + 1, o.amount > 0 FROM users u LEFT JOIN orders o ON u.id = o.user_id",
    [.nullable .int, .nullable .bool]),
  ("SELECT NOT (o.amount > 0), o.amount IS NULL, o.amount IS NOT NULL FROM users u LEFT JOIN orders o ON u.id = o.user_id",
    [.nullable .bool, .bool, .bool]),
  ("SELECT o.amount FROM users u LEFT JOIN orders o ON u.id = o.user_id WHERE o.amount > 0", [.nullable .int]),
  ("SELECT u.id FROM users u LEFT JOIN orders o ON u.id = o.user_id WHERE o.id IS NULL", [.int]),
  ("SELECT u.id, o.id, m.id FROM users u LEFT JOIN orders o ON u.id = o.user_id RIGHT JOIN metrics m ON o.id = m.id",
    [.nullable .int, .nullable .int, .int]),
  ("SELECT COUNT(*), COUNT(id), COUNT(DISTINCT name) FROM users", [.int, .int, .int]),
  ("SELECT SUM(age), AVG(age), MIN(age), MAX(age) FROM users",
    [.nullable .int, .nullable .real, .nullable .int, .nullable .int]),
  ("SELECT MIN(name), MAX(name), COUNT(active) FROM users", [.nullable .text, .nullable .text, .int]),
  ("SELECT SUM(DISTINCT age + 1), AVG(DISTINCT age), MAX(DISTINCT age) FROM users",
    [.nullable .int, .nullable .real, .nullable .int]),
  ("SELECT COUNT(*) + 1, SUM(age) / COUNT(*) FROM users", [.int, .nullable .int]),
  ("SELECT COUNT(*) > 0, SUM(age) IS NULL FROM users", [.bool, .bool]),
  ("SELECT name, COUNT(*) FROM users GROUP BY name", [.text, .int]),
  ("SELECT u.name, COUNT(*) FROM users u GROUP BY name", [.text, .int]),
  ("SELECT name, COUNT(*) FROM users u GROUP BY u.name", [.text, .int]),
  ("SELECT age + 1, COUNT(*) FROM users GROUP BY age", [.int, .int]),
  ("SELECT age + 1, COUNT(*) FROM users GROUP BY age + 1", [.int, .int]),
  ("SELECT (age + 1) * 2, COUNT(*) FROM users GROUP BY age + 1", [.int, .int]),
  ("SELECT name, age FROM users GROUP BY name, age ORDER BY name, age", [.text, .int]),
  ("SELECT name AS label, COUNT(*) AS n FROM users GROUP BY label ORDER BY n DESC", [.text, .int]),
  ("SELECT name AS age, COUNT(*) FROM users GROUP BY name, age ORDER BY age", [.text, .int]),
  ("SELECT name AS age, COUNT(*) FROM users GROUP BY name ORDER BY age", [.text, .int]),
  ("SELECT u.name AS id FROM users u JOIN orders o ON u.id = o.user_id ORDER BY id", [.text]),
  ("SELECT name, COUNT(*) FROM users GROUP BY 1 ORDER BY 2", [.text, .int]),
  ("SELECT name, COUNT(*) FROM users GROUP BY +1 ORDER BY - -2", [.text, .int]),
  ("SELECT age AS bucket, COUNT(*) AS n FROM users GROUP BY bucket HAVING COUNT(*) > 1 ORDER BY n DESC LIMIT 5 OFFSET 1", [.int, .int]),
  ("SELECT COUNT(*) FROM users HAVING SUM(age) > 1", [.int]),
  ("SELECT 1 FROM users HAVING TRUE", [.int]),
  ("SELECT COUNT(*) FROM users ORDER BY SUM(age)", [.int]),
  ("SELECT 1 FROM users ORDER BY COUNT(*)", [.int]),
  ("SELECT name FROM users GROUP BY name ORDER BY COUNT(*)", [.text]),
  ("SELECT u.id, COUNT(o.id), SUM(o.amount) FROM users u LEFT JOIN orders o ON u.id = o.user_id GROUP BY u.id HAVING SUM(o.amount) > 0",
    [.int, .int, .nullable .int]),
  ("SELECT DISTINCT name AS n FROM users ORDER BY n", [.text]),
  ("SELECT DISTINCT u.name FROM users u ORDER BY name", [.text]),
  ("SELECT DISTINCT name, COUNT(*) AS n FROM users GROUP BY name ORDER BY 2", [.text, .int]),
  ("SELECT DISTINCT * FROM users ORDER BY age", [.int, .text, .int, .bool]),
  ("SELECT u.* FROM users u GROUP BY u.id, u.name, u.age, u.active", [.int, .text, .int, .bool]),
  ("SELECT rate + 1, rate > 1, -rate FROM metrics", [.real, .bool, .real]),
  ("SELECT SUM(rate), AVG(rate), MIN(rate), MAX(rate) FROM metrics",
    [.nullable .real, .nullable .real, .nullable .real, .nullable .real]),
  ("SELECT optional + rate, optional = 1, optional IS NULL FROM metrics",
    [.nullable .real, .nullable .bool, .bool]),
  ("SELECT name < 'z' FROM users", [.bool]),
  ("SELECT active FROM users WHERE active", [.bool])
]

private def invalidCases : List String := [
  "SELECT id FROM missing",
  "SELECT missing FROM users",
  "SELECT users.id FROM users u",
  "SELECT u.id FROM users",
  "SELECT id FROM users u JOIN orders o ON u.id = o.user_id",
  "SELECT id FROM users u JOIN users v ON u.id = v.id",
  "SELECT u.id FROM users u JOIN orders u ON TRUE",
  "SELECT users.id FROM users JOIN users ON TRUE",
  "SELECT u.id FROM users u JOIN orders o ON m.id = o.id JOIN metrics m ON m.id = o.id",
  "SELECT u.id FROM users u JOIN orders o ON o.amount",
  "SELECT u.id FROM users u JOIN orders o ON COUNT(*) > 0",
  "SELECT u.id FROM users u JOIN missing o ON TRUE",
  "SELECT u.id FROM users u LEFT JOIN orders o ON u.name = o.amount",
  "SELECT q.* FROM users u",
  "SELECT age FROM users WHERE age",
  "SELECT age FROM users WHERE COUNT(*) > 0",
  "SELECT age FROM users WHERE SUM(age) > 0",
  "SELECT SUM(name) FROM users",
  "SELECT AVG(name) FROM users",
  "SELECT SUM(active) FROM users",
  "SELECT MIN(active) FROM users",
  "SELECT MAX(active) FROM users",
  "SELECT COUNT(COUNT(*)) FROM users",
  "SELECT SUM(AVG(age)) FROM users",
  "SELECT COUNT(SUM(age) + 1) FROM users",
  "SELECT SUM(COUNT(*) IS NULL) FROM users",
  "SELECT age, COUNT(*) FROM users",
  "SELECT name, age FROM users GROUP BY name",
  "SELECT age FROM users GROUP BY age + 1",
  "SELECT * FROM users GROUP BY id",
  "SELECT name FROM users GROUP BY COUNT(*)",
  "SELECT COUNT(*) AS n FROM users GROUP BY n",
  "SELECT name, COUNT(*) FROM users GROUP BY 2",
  "SELECT name, COUNT(*) FROM users GROUP BY 0",
  "SELECT name, COUNT(*) FROM users GROUP BY 3",
  "SELECT name, COUNT(*) FROM users GROUP BY -1",
  "SELECT name FROM users GROUP BY name HAVING age > 1",
  "SELECT name FROM users GROUP BY name HAVING name",
  "SELECT name FROM users HAVING TRUE",
  "SELECT name FROM users ORDER BY COUNT(*)",
  "SELECT name FROM users GROUP BY name ORDER BY age",
  "SELECT age, COUNT(*) FROM users GROUP BY name ORDER BY age",
  "SELECT name AS age, COUNT(*) FROM users GROUP BY age",
  "SELECT u.name AS id, COUNT(*) FROM users u JOIN orders o ON u.id = o.user_id GROUP BY id",
  "SELECT name AS n, age AS n FROM users ORDER BY n",
  "SELECT name AS n, age AS n, COUNT(*) FROM users GROUP BY n",
  "SELECT name AS n FROM users ORDER BY n + 1",
  "SELECT name AS n, COUNT(*) FROM users GROUP BY name HAVING n = 'x'",
  "SELECT name FROM users ORDER BY 0",
  "SELECT name FROM users ORDER BY 2",
  "SELECT name FROM users ORDER BY -1",
  "SELECT DISTINCT name FROM users ORDER BY age",
  "SELECT DISTINCT age FROM users ORDER BY age + 1",
  "SELECT DISTINCT name, COUNT(*) FROM users GROUP BY name ORDER BY SUM(age)",
  "SELECT rate AND TRUE FROM metrics",
  "SELECT name + 1 FROM users",
  "SELECT active < FALSE FROM users"
]

private def baseQuery : RelQuery :=
  { source := { name := "users" }, selectList := [.expression (.column none "id")] }

private def invalidManual : List RelQuery := [
  { baseQuery with selectList := [] },
  { baseQuery with offset := some 1 },
  { baseQuery with source := { name := "users", alias := some "" } },
  { baseQuery with selectList := [.expression (.column none "id") (some "")] },
  { baseQuery with joins := [{ kind := .inner, table := { name := "orders" } }] },
  { baseQuery with joins := [{ kind := .left, table := { name := "orders" } }] },
  { baseQuery with joins := [{ kind := .right, table := { name := "orders" } }] },
  { baseQuery with joins := [{ kind := .full, table := { name := "orders" } }] },
  { baseQuery with joins := [{ kind := .cross, table := { name := "orders" }, on := some (.literal (.bool true)) }] },
  { baseQuery with source := { name := "users", derived := some baseQuery } },
  { baseQuery with joins := [{ kind := .cross, table := { name := "orders", derived := some baseQuery } }] },
  { baseQuery with ctes := [{ name := "x", query := baseQuery }] }
]

def relationalValidationTests : IO Nat := do
  for (source, expected) in validCases do
    let query ← expectOk source (parseRelQuery source)
    let certified ← expectOk source (certifyRelQueryCore schema query)
    SQLean.Tests.assert (certified.outputTypes == expected) s!"wrong relational output types: {source}"
    let types ← expectOk source (checkRelQueryCore schema query)
    SQLean.Tests.assert (types == expected) s!"relational convenience check differs: {source}"
  for source in invalidCases do
    let query ← expectOk s!"must parse before semantic rejection: {source}" (parseRelQuery source)
    expectError source (certifyRelQueryCore schema query)
  for query in invalidManual do
    expectError "invalid manually constructed relational query" (certifyRelQueryCore schema query)
  let duplicateSchema : Schema := [⟨"users", [⟨"id", .int⟩, ⟨"id", .int⟩]⟩]
  expectError "relational check rejects malformed schemas" (certifyRelQueryCore duplicateSchema baseQuery)
  pure (validCases.length + invalidCases.length + invalidManual.length + 1)

private def countExample : RelQuery :=
  { source := { name := "users" }, selectList := [.expression .countAll] }

example : ValidRelQueryCore schema countExample [.int] :=
  checkRelQueryCore_sound rfl

private def groupedExample : RelQuery :=
  { source := { name := "users", alias := some "u" },
    selectList := [.expression (.column (some "u") "name"), .expression (.aggregate .sum (.column none "age"))],
    groupBy := [.column none "name"] }

example : ValidRelQueryCore schema groupedExample [.text, .nullable .int] :=
  checkRelQueryCore_sound rfl

example (schema : Schema) (query : RelQuery) (types : List SqlType) :
    checkRelQueryCore schema query = .ok types ↔ ValidRelQueryCore schema query types :=
  checkRelQueryCore_iff

end SQLean.Tests
