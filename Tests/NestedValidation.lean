import SQLean.Parser
import SQLean.NestedValidation
import SQLean.Pretty
import Tests.Support

namespace SQLean.Tests

private def nestedSchema : Schema := [
  ⟨"users", [⟨"id", .int⟩, ⟨"age", .int⟩, ⟨"name", .text⟩]⟩,
  ⟨"orders", [⟨"id", .int⟩, ⟨"user_id", .int⟩, ⟨"amount", .int⟩]⟩]

private def acceptedNested : List (String × List SqlType) := [
  ("SELECT d.id FROM (SELECT id FROM users) AS d", [.int]),
  ("SELECT d.* FROM (SELECT id, name FROM users) d", [.int, .text]),
  ("SELECT d.total FROM (SELECT SUM(amount) AS total FROM orders) d", [.nullable .int]),
  ("SELECT AVG(d.total) FROM (SELECT SUM(amount) AS total FROM orders) d", [.nullable .real]),
  ("SELECT u.id, d.amount FROM users u LEFT JOIN (SELECT user_id, amount FROM orders) d ON u.id = d.user_id", [.int, .nullable .int]),
  ("SELECT x.id FROM (SELECT d.id FROM (SELECT id FROM users) d) x", [.int]),
  ("WITH x AS (SELECT id, name FROM users) SELECT name FROM x", [.text]),
  ("WITH x(n) AS (SELECT COUNT(*) FROM users) SELECT n FROM x", [.int]),
  ("WITH x(total) AS (SELECT SUM(amount) FROM orders) SELECT total FROM x", [.nullable .int]),
  ("WITH x AS (SELECT id FROM users), y AS (SELECT id FROM x) SELECT id FROM y", [.int]),
  ("WITH users AS (SELECT id FROM users) SELECT * FROM users", [.int]),
  ("WITH x AS (SELECT id FROM users) SELECT d.id FROM (SELECT id FROM x) d", [.int]),
  ("WITH x AS (SELECT id FROM users) SELECT d.amount FROM (WITH x AS (SELECT amount FROM orders) SELECT amount FROM x) d", [.int]),
  ("WITH x AS (WITH y AS (SELECT id FROM users) SELECT id FROM y) SELECT id FROM x", [.int]),
  ("SELECT d.id, o.amount FROM (SELECT id FROM users) d JOIN (SELECT user_id, amount FROM orders) o ON d.id = o.user_id", [.int, .int]),
  ("WITH x(a, b) AS (SELECT id, id FROM users) SELECT a, b FROM x", [.int, .int]),
  ("WITH x AS (SELECT id FROM users) SELECT a.id, b.id FROM x a JOIN x b ON a.id = b.id", [.int, .int]),
  ("SELECT d.ok FROM (SELECT COUNT(*) > 0 AS ok FROM orders) d WHERE d.ok", [.bool])
]

private def rejectedNested : List String := [
  "SELECT d.id FROM (SELECT missing FROM users) d",
  "SELECT d.id FROM (SELECT id FROM missing) d",
  "SELECT d.missing FROM (SELECT id FROM users) d",
  "SELECT d.total FROM (SELECT SUM(amount) FROM orders) d",
  "SELECT d.id FROM (SELECT id, id FROM users) d",
  "SELECT d.id FROM (SELECT id AS x, age AS x FROM users) d",
  "SELECT d.id FROM users u JOIN (SELECT u.id FROM orders) d ON u.id = d.id",
  "SELECT d.id FROM (SELECT o.id FROM users) d JOIN orders o ON d.id = o.user_id",
  "SELECT d.id FROM (SELECT id FROM users) d JOIN orders d ON d.id = d.user_id",
  "SELECT users.id FROM (SELECT id FROM users) d",
  "WITH x AS (SELECT id FROM missing) SELECT id FROM x",
  "WITH x AS (SELECT id FROM x) SELECT id FROM x",
  "WITH x AS (SELECT id FROM y), y AS (SELECT id FROM users) SELECT id FROM x",
  "WITH x AS (SELECT id FROM users), x AS (SELECT id FROM orders) SELECT id FROM x",
  "WITH x(a, b) AS (SELECT id FROM users) SELECT a FROM x",
  "WITH x(a) AS (SELECT id, name FROM users) SELECT a FROM x",
  "WITH x(a, a) AS (SELECT id, name FROM users) SELECT a FROM x",
  "WITH x AS (SELECT SUM(amount) FROM orders) SELECT * FROM x",
  "WITH x AS (SELECT id FROM users) SELECT missing FROM x",
  "WITH x AS (SELECT id FROM users) SELECT name FROM x",
  "WITH users AS (SELECT id FROM orders) SELECT age FROM users",
  "SELECT d.id FROM (WITH x AS (SELECT id FROM users) SELECT id FROM x) d JOIN x ON d.id = x.id",
  "SELECT d.name FROM (SELECT name, COUNT(*) AS n FROM users) d",
  "WITH x AS (SELECT id FROM users WHERE COUNT(*) > 0) SELECT id FROM x",
  "WITH x AS (SELECT id FROM users) SELECT d.id FROM (SELECT id FROM orders WHERE id = x.id) d"
]

def nestedValidationTests : IO Nat := do
  for (source, types) in acceptedNested do
    let query ← expectOk source (parseRelQuery source)
    let checked ← expectOk source (certifyRelQuery nestedSchema query)
    SQLean.Tests.assert (checked.outputTypes == types) s!"wrong nested types: {source}"
    SQLean.Tests.assert (checked.outputNames.length == types.length) s!"wrong named arity: {source}"
    let roundTrip ← expectOk source (parseRelQuery (toSql query))
    SQLean.Tests.assert (roundTrip == query) s!"nested round trip changed AST: {source}"
  for source in rejectedNested do
    let query ← expectOk source (parseRelQuery source)
    expectError source (certifyRelQuery nestedSchema query)
  let child : RelQuery := { source := { name := "users" }, selectList := [.all] }
  for ref in [
    ({ name := "", derived := some child } : TableRef),
    { name := "", alias := some "", derived := some child },
    { name := "users", alias := some "d", derived := some child }] do
    expectError "malformed manual derived source" (certifyRelQuery nestedSchema
      { source := ref, selectList := [.all] })
  pure (acceptedNested.length + rejectedNested.length + 3)

example (schema : Schema) (query : RelQuery) (checked : CertifiedRelQuery schema query) :
    ValidRelQuery schema query checked.outputTypes := checked.valid

end SQLean.Tests
