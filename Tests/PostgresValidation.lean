import SQLean.Parser
import SQLean.NestedValidation
import Tests.Support

namespace SQLean.Tests

private def postgresSchema : Schema := [
  ⟨"users", [⟨"id", .int⟩, ⟨"age", .int⟩, ⟨"name", .text⟩, ⟨"city", .text⟩, ⟨"enabled", .bool⟩]⟩,
  ⟨"orders", [⟨"id", .int⟩, ⟨"user_id", .int⟩, ⟨"amount", .int⟩, ⟨"status", .text⟩]⟩]

private def acceptedPostgres : List (String × List SqlType) := [
  ("SELECT DISTINCT ON (id) id, id FROM users ORDER BY id", [.int, .int]),
  ("SELECT DISTINCT ON (id) id, id AS id FROM users ORDER BY id", [.int, .int]),
  ("SELECT DISTINCT ON (id) id AS id, users.id FROM users ORDER BY id", [.int, .int]),
  ("SELECT DISTINCT ON (k) id AS k, users.id AS k FROM users ORDER BY k", [.int, .int]),
  ("SELECT id, id FROM users ORDER BY id", [.int, .int]),
  ("SELECT age + 1 AS k, users.age + 1 AS k FROM users ORDER BY k", [.int, .int]),
  ("SELECT DISTINCT ON (id) u.id FROM users u JOIN orders o ON u.id = o.user_id", [.int]),
  ("SELECT u.id FROM users u JOIN orders o ON u.id = o.user_id ORDER BY id", [.int]),
  ("SELECT DISTINCT ON (id) u.id, o.id AS other FROM users u JOIN orders o ON u.id = o.user_id ORDER BY id", [.int, .int]),
  ("SELECT DISTINCT ON (+1) name FROM users", [.text]),
  ("SELECT DISTINCT ON (+1) name FROM users ORDER BY +1", [.text]),
  ("SELECT DISTINCT ON (TRUE::BOOLEAN) name FROM users", [.text]),
  ("SELECT DISTINCT ON ('x'::TEXT) name FROM users", [.text]),
  ("SELECT DISTINCT ON (1::INT) name FROM users ORDER BY 1::INT", [.text]),
  ("SELECT name FROM users ORDER BY +0", [.text]),
  ("SELECT COUNT(*) FROM users GROUP BY +1", [.int]),
  ("SELECT 16777216 IN (0::REAL, 16777217), 1 IN (1::REAL, 2::DOUBLE PRECISION)", [.bool, .bool]),
  ("SELECT name IN (city, 'x'), enabled IN (TRUE, FALSE) FROM users", [.bool, .bool]),
  ("SELECT city IN ('x', 'y'), COUNT(*) FROM users GROUP BY city", [.bool, .int]),
  ("SELECT COUNT(*) IN (1, 2) FROM users", [.bool]),
  ("SELECT DISTINCT ON (city) name, age FROM users ORDER BY city, age DESC", [.text, .int]),
  ("SELECT DISTINCT ON (city) name FROM users", [.text]),
  ("SELECT DISTINCT ON (city, age) name FROM users ORDER BY age, city, id", [.text]),
  ("SELECT DISTINCT ON (city, age) name FROM users ORDER BY city", [.text]),
  ("SELECT DISTINCT ON (city, city) name FROM users ORDER BY city, age", [.text]),
  ("SELECT DISTINCT ON (city, age) name FROM users ORDER BY city, city, age, id", [.text]),
  ("SELECT DISTINCT ON (1) city, name FROM users ORDER BY 1, name DESC", [.text, .text]),
  ("SELECT DISTINCT ON (place) city AS place, name FROM users ORDER BY place, name", [.text, .text]),
  ("SELECT DISTINCT ON (age) city AS age, name FROM users ORDER BY age, name", [.text, .text]),
  ("SELECT DISTINCT ON (u.city) u.name FROM users u ORDER BY city, u.name", [.text]),
  ("SELECT DISTINCT ON (age + 1) name FROM users ORDER BY age + 1, id", [.text]),
  ("SELECT DISTINCT ON (city) city, COUNT(*) FROM users GROUP BY city ORDER BY city", [.text, .int]),
  ("SELECT DISTINCT ON (COUNT(*)) COUNT(*) FROM users ORDER BY COUNT(*)", [.int]),
  ("SELECT DISTINCT ON (n) COUNT(*) AS n FROM users ORDER BY n", [.int]),
  ("SELECT DISTINCT ON (city) city FROM users UNION SELECT status FROM orders ORDER BY 1", [.text]),
  ("WITH x AS (SELECT DISTINCT ON (city) city, name FROM users ORDER BY city, id) SELECT name FROM x", [.text]),
  ("SELECT d.name FROM (SELECT DISTINCT ON (city) name FROM users ORDER BY city, id) d", [.text]),
  ("SELECT COUNT(*) FILTER (WHERE age > 18) FROM users", [.int]),
  ("SELECT SUM(age) FILTER (WHERE enabled), AVG(age) FILTER (WHERE enabled) FROM users", [.nullable .int, .nullable .real]),
  ("SELECT COUNT(DISTINCT city) FILTER (WHERE age > 18) FROM users", [.int]),
  ("SELECT MIN(name) FILTER (WHERE enabled), MAX(age) FILTER (WHERE TRUE) FROM users", [.nullable .text, .nullable .int]),
  ("SELECT city, COUNT(*) FILTER (WHERE age > 18) FROM users GROUP BY city", [.text, .int]),
  ("SELECT COUNT(*) FROM users HAVING COUNT(*) FILTER (WHERE enabled) > 1", [.int]),
  ("SELECT COUNT(*) FROM users ORDER BY COUNT(*) FILTER (WHERE name LIKE 'A%')", [.int]),
  ("SELECT COUNT(*) FILTER (WHERE o.amount > 1) FROM users u LEFT JOIN orders o ON u.id = o.user_id", [.int]),
  ("SELECT SUM(CAST(age AS REAL)) FILTER (WHERE name ILIKE 'a%') FROM users", [.nullable .real]),
  ("SELECT COUNT(*) FILTER (WHERE TRUE) + COUNT(*) FILTER (WHERE FALSE)", [.int]),
  ("SELECT CAST(1 AS TEXT), CAST('2' AS INTEGER), CAST(TRUE AS INT), CAST(0 AS BOOLEAN)", [.text, .int, .int, .bool]),
  ("SELECT 1::REAL, 'true'::BOOLEAN, FALSE::TEXT, CAST(1::REAL AS INT)", [.real, .bool, .text, .int]),
  ("SELECT age::TEXT, name::INT, enabled::INTEGER FROM users", [.text, .int, .int]),
  ("SELECT 1::DOUBLE PRECISION, CAST(2 AS DOUBLE PRECISION)", [.real, .real]),
  ("SELECT o.amount::TEXT FROM users u LEFT JOIN orders o ON u.id = o.user_id", [.nullable .text]),
  ("SELECT SUM(age)::REAL, COUNT(*)::TEXT FROM users", [.nullable .real, .text]),
  ("SELECT city::TEXT, COUNT(*) FROM users GROUP BY city", [.text, .int]),
  ("SELECT name LIKE 'A%', name NOT ILIKE '%z', city ILIKE name FROM users", [.bool, .bool, .bool]),
  ("SELECT o.status LIKE 'open' FROM users u LEFT JOIN orders o ON u.id = o.user_id", [.nullable .bool]),
  ("SELECT 'open' ILIKE o.status FROM users u LEFT JOIN orders o ON u.id = o.user_id", [.nullable .bool]),
  ("SELECT city LIKE 'A%', COUNT(*) FROM users GROUP BY city", [.bool, .int]),
  ("SELECT MIN(name) LIKE 'A%' FROM users", [.nullable .bool]),
  ("SELECT id FROM users WHERE name LIKE 'A%' AND enabled", [.int]),
  ("SELECT id FROM users WHERE age BETWEEN 18 AND 65 AND id IN (1, 2, 3)", [.int]),
  ("SELECT id FROM users WHERE age NOT BETWEEN 18 AND 65 OR city NOT IN ('A', 'B')", [.int]),
  ("SELECT o.amount IN (1, 2), o.amount BETWEEN 0 AND 5 FROM users u LEFT JOIN orders o ON u.id = o.user_id", [.nullable .bool, .nullable .bool]),
  ("SELECT u.id FROM users u LEFT JOIN orders o ON u.id = o.user_id ORDER BY o.amount DESC NULLS FIRST", [.int]),
  ("SELECT city, COUNT(*) FROM users GROUP BY city ORDER BY city NULLS LAST", [.text, .int]),
  ("SELECT 1 AS n UNION SELECT 2 ORDER BY n NULLS FIRST", [.int]),
  ("SELECT DISTINCT ON (city) name FROM users ORDER BY city DESC NULLS LAST, age NULLS FIRST", [.text]),
  ("SELECT DISTINCT city FROM users ORDER BY city NULLS FIRST", [.text]),
  ("WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT (n + 1)::INT FROM seq WHERE n BETWEEN 1 AND 3) SELECT n::TEXT FROM seq ORDER BY n NULLS LAST", [.text]),
  ("SELECT DISTINCT ON (COUNT(*) FILTER (WHERE enabled)) COUNT(*) FROM users", [.int]),
  ("SELECT DISTINCT ON (city) city FROM users GROUP BY city HAVING COUNT(*) FILTER (WHERE age IN (1, 2)) > 0 ORDER BY city NULLS FIRST", [.text])
]

private def rejectedPostgres : List String := [
  "SELECT DISTINCT ON (id) id, age AS id FROM users ORDER BY id",
  "SELECT DISTINCT ON (id) id, age AS id FROM users",
  "SELECT DISTINCT ON (id) age AS id, id FROM users",
  "SELECT id, age AS id FROM users ORDER BY id",
  "SELECT *, age AS id FROM users ORDER BY id",
  "SELECT DISTINCT ON (id) u.id, o.id FROM users u JOIN orders o ON u.id = o.user_id",
  "SELECT DISTINCT ON (id) u.id, o.id AS id FROM users u JOIN orders o ON u.id = o.user_id",
  "SELECT id AS k, age AS k FROM users ORDER BY k",
  "SELECT u.id FROM users u JOIN orders o ON u.id = o.user_id GROUP BY id",
  "SELECT DISTINCT ON (TRUE) name FROM users",
  "SELECT DISTINCT ON (FALSE) name FROM users",
  "SELECT DISTINCT ON ('x') name FROM users",
  "SELECT DISTINCT ON (+1) name FROM users ORDER BY name",
  "SELECT DISTINCT ON (1::INT) name FROM users ORDER BY +1",
  "SELECT name, COUNT(*) FROM users GROUP BY +1",
  "SELECT city IN (name, 'x'), COUNT(*) FROM users GROUP BY city",
  "SELECT age IN (COUNT(*), 1) FROM users",
  "SELECT COUNT(*) FROM users WHERE age IN (COUNT(*), 1)",
  "SELECT age IN (TRUE, 1) FROM users",
  "SELECT DISTINCT ON (city) name FROM users ORDER BY age, city",
  "SELECT DISTINCT ON (city, age) name FROM users ORDER BY city, id, age",
  "SELECT DISTINCT ON (city, age) name FROM users ORDER BY city, id",
  "SELECT DISTINCT ON (missing) name FROM users",
  "SELECT DISTINCT ON (age + 1) name FROM users ORDER BY age",
  "SELECT DISTINCT ON (0) name FROM users",
  "SELECT DISTINCT ON (-1) name FROM users",
  "SELECT DISTINCT ON (2) name FROM users",
  "SELECT DISTINCT ON (same) city AS same, name AS same FROM users",
  "SELECT DISTINCT ON (city) city, COUNT(*) FROM users",
  "SELECT DISTINCT ON (name) city, COUNT(*) FROM users GROUP BY city",
  "SELECT DISTINCT ON (COUNT(*)) name FROM users",
  "SELECT DISTINCT ON (age + city) name FROM users",
  "SELECT DISTINCT ON (u.id) u.id FROM users u JOIN orders o ON u.id = o.user_id ORDER BY o.id",
  "SELECT COUNT(*) FILTER (WHERE age) FROM users",
  "SELECT COUNT(*) FILTER (WHERE COUNT(*) > 1) FROM users",
  "SELECT SUM(age) FILTER (WHERE SUM(age) > 1) FROM users",
  "SELECT COUNT(*) FILTER (WHERE missing > 1) FROM users",
  "SELECT SUM(name) FILTER (WHERE enabled) FROM users",
  "SELECT AVG(enabled) FILTER (WHERE TRUE) FROM users",
  "SELECT SUM(COUNT(*)) FILTER (WHERE TRUE) FROM users",
  "SELECT SUM(COUNT(*) FILTER (WHERE TRUE)) FROM users",
  "SELECT age FROM users WHERE COUNT(*) FILTER (WHERE TRUE) > 0",
  "SELECT COUNT(*) FROM users GROUP BY COUNT(*) FILTER (WHERE TRUE)",
  "SELECT u.id FROM users u JOIN orders o ON COUNT(*) FILTER (WHERE TRUE) > 0",
  "SELECT age, COUNT(*) FILTER (WHERE enabled) FROM users",
  "SELECT city, COUNT(*) FROM users GROUP BY city ORDER BY age::TEXT",
  "SELECT COUNT(*) FROM users ORDER BY city LIKE 'A%'",
  "SELECT TRUE::REAL",
  "SELECT (1::REAL)::BOOLEAN",
  "SELECT missing::TEXT FROM users",
  "SELECT age::TEXT + 1 FROM users",
  "SELECT name::BOOLEAN + 1 FROM users",
  "SELECT name FROM users WHERE age::INT",
  "SELECT 1 LIKE 'A%'",
  "SELECT 'A' ILIKE 1",
  "SELECT TRUE LIKE FALSE",
  "SELECT name LIKE missing FROM users",
  "SELECT age FROM users WHERE city BETWEEN 1 AND 3",
  "SELECT age FROM users WHERE age IN (1, 'two')",
  "SELECT age FROM users WHERE age NOT IN (TRUE, FALSE)",
  "SELECT age FROM users WHERE name NOT BETWEEN 1 AND 2",
  "SELECT city LIKE 'A%', COUNT(*) FROM users",
  "SELECT id FROM users ORDER BY missing NULLS FIRST",
  "SELECT DISTINCT city FROM users ORDER BY age NULLS LAST",
  "SELECT 1 AS n UNION SELECT 2 ORDER BY n::TEXT NULLS FIRST",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT DISTINCT ON (n) n FROM seq) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT COUNT(*) FILTER (WHERE TRUE) FROM seq) SELECT n FROM seq",
  "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT n::TEXT FROM seq) SELECT n FROM seq"
]

private def castMatrixTests : IO Nat := do
  let bases : List SqlType := [.int, .text, .bool, .real]
  let targets : List CastType := [.int, .text, .bool, .real, .doublePrecision]
  let allowedPairs : List (SqlType × SqlType) := [
    (.int, .int), (.int, .text), (.int, .bool), (.int, .real),
    (.text, .int), (.text, .text), (.text, .bool), (.text, .real),
    (.bool, .int), (.bool, .text), (.bool, .bool),
    (.real, .int), (.real, .text), (.real, .real)]
  for source in bases do
    for target in targets do
      for nullable in [false, true] do
        let input := if nullable then source.asNullable else source
        let output := if nullable then target.resultType.asNullable else target.resultType
        let scope : RelScope := [⟨"t", "x", input⟩]
        let expr := RelExpr.cast (.column none "x") target
        if allowedPairs.contains (source, target.resultType) then
          let actual ← expectOk "cast matrix" (inferRelType scope false expr)
          SQLean.Tests.assert (actual == output) s!"cast matrix nullability mismatch: {repr input} -> {repr target}"
        else expectError "cast matrix invalid pair" (inferRelType scope false expr)
  pure 40

def postgresValidationTests : IO Nat := do
  for (source, types) in acceptedPostgres do
    let query ← expectOk source (parseRelQuery source)
    let checked ← expectOk source (certifyRelQuery postgresSchema query)
    SQLean.Tests.assert (checked.outputTypes == types) s!"wrong PostgreSQL result types: {source}"
  for source in rejectedPostgres do
    let query ← expectOk source (parseRelQuery source)
    expectError source (certifyRelQuery postgresSchema query)
  let scope : RelScope := [⟨"u", "age", .int⟩, ⟨"u", "name", .nullable .text⟩]
  let int := RelExpr.literal (.int 1)
  let yes := RelExpr.literal (.bool true)
  let malformed : List RelExpr := [
    .inList int [],
    .inList int [.literal (.text "x")],
    .filteredAggregate int yes,
    .filteredAggregate (.binary .add .countAll int) yes,
    .filteredAggregate (.cast .countAll .int) yes,
    .filteredAggregate (.filteredAggregate .countAll yes) yes,
    .filteredAggregate .countAll (.filteredAggregate .countAll yes),
    .filteredAggregate .countAll int,
    .pattern (.column none "name") int true]
  for expr in malformed do
    expectError "malformed PostgreSQL expression AST" (inferRelType scope true expr)
  expectError "FILTER forbidden in scalar context" (inferRelType scope false (.filteredAggregate .countAll yes))
  let filtered : RelExpr := .filteredAggregate .countAll (.pattern (.column none "name") (.literal (.text "A%")) true)
  let filteredType ← expectOk "nullable FILTER predicate" (inferRelType scope true filtered)
  SQLean.Tests.assert (filteredType == .int) "filtered COUNT must stay nonnullable"
  let query : RelQuery := {
    source := {name := "users"}, selectList := [.expression (.column none "id")],
    distinct := true, distinctOn := [.column none "id"] }
  expectError "DISTINCT and DISTINCT ON conflict" (certifyRelQuery postgresSchema query)
  let castTests ← castMatrixTests
  pure (acceptedPostgres.length + rejectedPostgres.length + malformed.length + castTests + 3)

example (scope : RelScope) (expr : RelExpr) (type : SqlType) :
    inferRelType scope true expr = .ok type ↔ RelHasType scope true expr type := inferRelType_iff

example (schema : Schema) (query : RelQuery) (types : List SqlType) :
    checkRelQueryCore schema query = .ok types ↔ ValidRelQueryCore schema query types := checkRelQueryCore_iff

example (schema : Schema) (query : RelQuery) (types : List SqlType) :
    checkRelQuery schema query = .ok types ↔ ValidRelQuery schema query types := checkRelQuery_iff

end SQLean.Tests
