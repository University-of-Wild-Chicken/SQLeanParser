import SQLean.Parser
import SQLean.Pretty
import Tests.Support

namespace SQLean.Tests

private def accepted : List String := [
  "SELECT DISTINCT ON (city) city, name FROM users ORDER BY city, age DESC",
  "SELECT DISTINCT ON (city, age) * FROM users ORDER BY city, age, id",
  "SELECT DISTINCT ON (u.age + 1) u.age + 1 AS next FROM users u ORDER BY next",
  "SELECT DISTINCT ON (1) 1",
  "SELECT DISTINCT ON (city) city FROM users",
  "SELECT COUNT(*) FILTER (WHERE age >= 18) FROM users",
  "SELECT COUNT(DISTINCT city) FILTER (WHERE age IN (18, 21)) FROM users",
  "SELECT SUM(age) FILTER (WHERE name ILIKE 'a%'), AVG(age) FILTER (WHERE age BETWEEN 1 AND 9) FROM users",
  "SELECT MIN(age) FILTER (WHERE TRUE), MAX(age) FILTER (WHERE NOT FALSE) FROM users",
  "SELECT city, COUNT(*) FILTER (WHERE age > 20) AS adults FROM users GROUP BY city HAVING COUNT(*) FILTER (WHERE age > 20) > 0 ORDER BY adults DESC NULLS LAST",
  "SELECT COUNT(*) FILTER (WHERE age > 20)::REAL FROM users",
  "SELECT (COUNT(*) FILTER (WHERE TRUE)) + 1 FROM users",
  "SELECT 1::INT, 2::INTEGER, TRUE::BOOL, FALSE::BOOLEAN, 3::REAL, 4::DOUBLE PRECISION, 5::TEXT",
  "SELECT CAST(1 AS INTEGER), CAST(TRUE AS BOOL), CAST(1 AS DOUBLE PRECISION)",
  "SELECT CAST(CAST(id AS TEXT) AS INTEGER) FROM users",
  "SELECT id::TEXT::INTEGER FROM users",
  "SELECT -id::REAL + 1 FROM users",
  "SELECT (-id)::REAL, (id + 1)::TEXT FROM users",
  "SELECT CAST(id + 1 AS TEXT) AS label FROM users",
  "SELECT u.id::INTEGER FROM users u JOIN orders o ON u.id::TEXT = o.user_id::TEXT",
  "SELECT name LIKE 'a%', name ILIKE 'A%', name NOT LIKE '%z', name NOT ILIKE '%Z' FROM users",
  "SELECT NOT name LIKE 'a%' AND age > 1 OR name ILIKE 'b%' FROM users",
  "SELECT id IN (1), id IN (1, 2, 3), id NOT IN (4, 5) FROM users",
  "SELECT id IN (1 + 2, age, (3 * 4)) FROM users",
  "SELECT 16777216 IN (0::REAL, 16777217)",
  "SELECT age BETWEEN 18 AND 65, age NOT BETWEEN 1 AND 9 FROM users",
  "SELECT age BETWEEN 1 + 2 AND 3 * 4 AND id IN (1, 2) OR FALSE FROM users",
  "SELECT NOT age BETWEEN 1 AND 9, NOT id NOT IN (1, 2) FROM users",
  "SELECT (age BETWEEN 1 AND 9) = TRUE, (name ILIKE 'a%') IS NOT NULL FROM users",
  "SELECT (name LIKE 'a%') = TRUE, (id IN (1, 2)) IS NULL, (age = 1) IS NOT NULL FROM users",
  "SELECT id FROM users ORDER BY id NULLS FIRST",
  "SELECT id FROM users ORDER BY id DESC NULLS FIRST, name ASC NULLS LAST",
  "SELECT 1 AS first, 2 AS last ORDER BY first NULLS FIRST, last NULLS LAST",
  "SELECT 1 first, 2 last UNION ALL SELECT 3, 4 ORDER BY last DESC NULLS FIRST",
  "SELECT first.id AS last FROM users first ORDER BY last NULLS LAST",
  "SELECT first, last FROM first ORDER BY first NULLS FIRST, last NULLS LAST",
  "SELECT id AS n FROM users UNION ALL SELECT user_id FROM orders ORDER BY n NULLS LAST",
  "WITH a AS (SELECT DISTINCT ON (city) city, age FROM users ORDER BY city, age DESC) SELECT age::REAL FROM a ORDER BY age NULLS LAST",
  "WITH RECURSIVE seq(n) AS (SELECT 1::INTEGER UNION ALL SELECT n + 1 FROM seq WHERE n BETWEEN 1 AND 4) SELECT n::TEXT FROM seq",
  "SELECT q.total FROM (SELECT COUNT(*) FILTER (WHERE age IN (1, 2)) AS total FROM users) q",
  "SELECT \"filter\", \"returning\", \"between\", \"cast\" FROM \"nulls\"",
  "SELECT /* portable cast */ 1 :: /* type */ INTEGER;",
  "select count(*) filter (where age not between 1 and 9) from users;"
]

private def returningAccepted : List String := [
  "INSERT INTO users VALUES (1, 'Ada', 30, TRUE) RETURNING *",
  "INSERT INTO users (id, name) VALUES (1, 'Ada'), (2, 'Bea') RETURNING id, name",
  "INSERT INTO users (id) VALUES (1) RETURNING users.id, id + 1 AS next_id",
  "INSERT INTO users (id) VALUES (1) RETURNING id::TEXT AS label",
  "UPDATE users SET age = age + 1 RETURNING *",
  "UPDATE users SET age = 1, name = 'Ada' WHERE id = 2 RETURNING users.*, id AS updated_id",
  "UPDATE users SET age = 1 RETURNING name ILIKE 'a%' AS matches, age BETWEEN 1 AND 3 AS small",
  "UPDATE users SET age = 1 RETURNING CAST(age AS REAL), id NOT IN (2, 3)",
  "DELETE FROM users RETURNING *",
  "DELETE FROM users WHERE id = 1 RETURNING id, name AS removed_name",
  "DELETE FROM users RETURNING users.id::TEXT, users.*;",
  "DELETE FROM \"Returning\" RETURNING \"Returning\".\"ID\" AS \"Deleted ID\"",
  "UPDATE users SET \"returning\" = 1 RETURNING \"returning\""
]

private def rejected : List String := [
  "SELECT DISTINCT ON", "SELECT DISTINCT ON () id FROM users",
  "SELECT DISTINCT ON (id,) id FROM users", "SELECT DISTINCT ON id FROM users",
  "SELECT DISTINCT ON (id) FROM users", "SELECT DISTINCT DISTINCT ON (id) id FROM users",
  "SELECT COUNT(*) FILTER FROM users", "SELECT COUNT(*) FILTER () FROM users",
  "SELECT COUNT(*) FILTER (age > 1) FROM users", "SELECT COUNT(*) FILTER (WHERE) FROM users",
  "SELECT COUNT(*) FILTER (WHERE TRUE FROM users",
  "SELECT COUNT(*) FILTER (WHERE TRUE) FILTER (WHERE TRUE) FROM users",
  "SELECT id FILTER (WHERE TRUE) FROM users", "SELECT 1 FILTER (WHERE TRUE)",
  "SELECT (COUNT(*)) FILTER (WHERE TRUE) FROM users",
  "SELECT COUNT(*)::INTEGER FILTER (WHERE TRUE) FROM users",
  "SELECT CAST(1)", "SELECT CAST(1 INTEGER)", "SELECT CAST(1 AS)", "SELECT CAST(AS INTEGER)",
  "SELECT CAST(1 AS INTEGER, TEXT)", "SELECT CAST(1 AS NUMERIC)", "SELECT CAST(1 AS INTEGER(3))",
  "SELECT 1::", "SELECT ::INTEGER", "SELECT 1:INTEGER", "SELECT 1:::INTEGER",
  "SELECT 1::DOUBLE", "SELECT 1::BIGINT", "SELECT 1::TEXT[]",
  "SELECT id IN () FROM users", "SELECT id IN (1,) FROM users", "SELECT id IN 1 FROM users",
  "SELECT id IN (SELECT id FROM users) FROM users", "SELECT id NOT IN () FROM users",
  "SELECT id NOT LIKE FROM users", "SELECT id NOT ILIKE FROM users",
  "SELECT id LIKE 'x' ESCAPE '!' FROM users", "SELECT id NOT = 1 FROM users",
  "SELECT id BETWEEN 1 FROM users", "SELECT id BETWEEN AND 2 FROM users",
  "SELECT id BETWEEN 1 AND FROM users", "SELECT id BETWEEN SYMMETRIC 1 AND 2 FROM users",
  "SELECT id BETWEEN 1 OR 2 FROM users", "SELECT id BETWEEN 1 AND 2 AND FROM users",
  "SELECT id IN (1) IN (2) FROM users", "SELECT id LIKE 'x' = TRUE FROM users",
  "SELECT id BETWEEN 1 AND 2 = TRUE FROM users", "SELECT id = 1 IN (1) FROM users",
  "SELECT id FROM users ORDER BY id NULLS", "SELECT id FROM users ORDER BY id NULLS MIDDLE",
  "SELECT id FROM users ORDER BY id NULLS FIRST DESC",
  "SELECT id FROM users ORDER BY id NULLS FIRST NULLS LAST",
  "SELECT id FROM users NULLS FIRST", "SELECT id FROM users RETURNING id",
  "SELECT 1::INTEGER;;"
]

private def returningRejected : List String := [
  "INSERT INTO users VALUES (1) RETURNING", "UPDATE users SET id = 1 RETURNING",
  "DELETE FROM users RETURNING", "DELETE FROM users RETURNING id,",
  "DELETE FROM users RETURNING * AS all_columns", "DELETE FROM users RETURNING id RETURNING name",
  "DELETE FROM users RETURNING id WHERE id = 1", "DELETE FROM users RETURNING id ORDER BY id",
  "UPDATE users SET id = 1 RETURNING id LIMIT 1",
  "INSERT INTO users VALUES (1) RETURNING id; SELECT 1",
  "INSERT INTO users VALUES (1::INTEGER) RETURNING id",
  "UPDATE users SET id = id::INTEGER RETURNING id",
  "DELETE FROM users WHERE id IN (1) RETURNING id",
  "DELETE FROM returning RETURNING *", "UPDATE users SET returning = 1 RETURNING *",
  "INSERT INTO users (returning) VALUES (1) RETURNING *",
  "DELETE FROM users WHERE RETURNING id", "UPDATE users SET id = RETURNING id"
]

private def int (n : Nat) : RelExpr := .literal (.int n)
private def col (name : String) : RelExpr := .column none name

private def projectionIs (source : String) (expected : RelExpr) : IO Unit := do
  let query ← expectOk source (parseRelQuery source)
  SQLean.Tests.assert (query.selectList == [.expression expected]) s!"precedence/AST differs: {source}"

def postgresParsingTests : IO Nat := do
  for source in accepted do
    let query ← expectOk source (parseRelQuery source)
    let _ ← expectOk source (parseStatement source)
    let reparsed ← expectOk "PostgreSQL relational roundtrip" (parseRelQuery (toSql query))
    SQLean.Tests.assert (query == reparsed) s!"PostgreSQL rendering changed AST: {source}"
  for source in returningAccepted do
    let statement ← expectOk source (parseStatement source)
    match statement with
    | .returning _ _ => pure ()
    | _ => throw (IO.userError s!"RETURNING variant lost: {source}")
    let reparsed ← expectOk "PostgreSQL RETURNING roundtrip" (parseStatement (toSql statement))
    SQLean.Tests.assert (statement == reparsed) s!"RETURNING rendering changed AST: {source}"
  for source in rejected do
    expectError source (parseRelQuery source)
    expectError source (parseStatement source)
  for source in returningRejected do
    expectError source (parseStatement source)

  projectionIs "SELECT -id::REAL + 1 FROM users"
    (.binary .add (.unary .neg (.cast (col "id") .real)) (int 1))
  projectionIs "SELECT (-id)::REAL FROM users" (.cast (.unary .neg (col "id")) .real)
  projectionIs "SELECT id::TEXT::INTEGER FROM users" (.cast (.cast (col "id") .text) .int)
  projectionIs "SELECT 1 + 2::INTEGER * 3" (.binary .add (int 1) (.binary .mul (.cast (int 2) .int) (int 3)))
  projectionIs "SELECT id IN (1, 2, 3) FROM users"
    (.inList (col "id") [int 1, int 2, int 3])
  projectionIs "SELECT 16777216 IN (0::REAL, 16777217)"
    (.inList (int 16777216) [.cast (int 0) .real, int 16777217])
  projectionIs "SELECT age BETWEEN 1 + 2 AND 3 * 4 AND TRUE FROM users"
    (.binary .and ((col "age").between (.binary .add (int 1) (int 2)) (.binary .mul (int 3) (int 4)))
      (.literal (.bool true)))
  projectionIs "SELECT NOT age BETWEEN 1 AND 9 OR FALSE FROM users"
    (.binary .or (.unary .not ((col "age").between (int 1) (int 9))) (.literal (.bool false)))
  projectionIs "SELECT id NOT IN (1, 2) FROM users" (.unary .not ((col "id").inValues [int 1, int 2]))
  projectionIs "SELECT NOT name ILIKE 'a%' AND TRUE FROM users"
    (.binary .and (.unary .not (.pattern (col "name") (.literal (.text "a%")) true)) (.literal (.bool true)))
  projectionIs "SELECT COUNT(*) FILTER (WHERE id > 1)::TEXT FROM users"
    (.cast (.filteredAggregate .countAll (.binary .gt (col "id") (int 1))) .text)
  projectionIs "SELECT '1.23456789012345'::DOUBLE PRECISION::TEXT"
    (.cast (.cast (.literal (.text "1.23456789012345")) .doublePrecision) .text)

  let distinct ← expectOk "DISTINCT ON AST" (parseRelQuery
    "SELECT DISTINCT ON (city, age) city, age FROM users ORDER BY city NULLS FIRST, age DESC NULLS LAST")
  SQLean.Tests.assert (!distinct.distinct && distinct.distinctOn == [col "city", col "age"] &&
    distinct.orderBy == [{ expr := col "city", nullsFirst := some true },
      { expr := col "age", descending := true, nullsFirst := some false }])
    "DISTINCT ON keys or explicit null ordering lost"
  let returning ← expectOk "RETURNING AST" (parseStatement
    "UPDATE users SET id = 2 WHERE id = 1 RETURNING id::TEXT AS changed")
  SQLean.Tests.assert (returning == .returning (.update {
    table := "users", assignments := [{ column := "id", value := .literal (.int 2) }],
    whereClause := some (.binary .eq (.column "id") (.literal (.int 1))) })
    [.expression (.cast (col "id") .text) (some "changed")]) "RETURNING mutation or projection changed"

  let tokens ← expectOk "cast lexer position" (lex "SELECT 1\n::INTEGER")
  let castToken := tokens[2]!
  SQLean.Tests.assert (castToken.kind == .symbol "::" && castToken.position.line == 2 &&
    castToken.position.column == 1) ":: must be a single position-aware token"
  for source in ["SELECT id::TEXT FROM users", "SELECT id IN (1, 2) FROM users",
      "SELECT COUNT(*) FILTER (WHERE TRUE) FROM users", "SELECT DISTINCT ON (id) id FROM users"] do
    expectError "MVP grammar remains unchanged" (parseQuery source)

  let list := String.intercalate ", " ((List.range 100).map toString)
  let long ← expectOk "100-element IN list" (parseRelQuery s!"SELECT id IN ({list}) FROM users")
  let longAgain ← expectOk "100-element IN list roundtrip" (parseRelQuery (toSql long))
  SQLean.Tests.assert (long == longAgain) "long IN list AST did not roundtrip"
  let casts := (List.range 30).foldl (fun sql _ => sql ++ "::INTEGER") "1"
  let deep ← expectOk "30 chained casts" (parseRelQuery s!"SELECT {casts}")
  let deepAgain ← expectOk "30 nested CAST renderings" (parseRelQuery (toSql deep))
  SQLean.Tests.assert (deep == deepAgain) "deep cast AST did not roundtrip"

  pure (3 * accepted.length + 2 * returningAccepted.length + 2 * rejected.length +
    returningRejected.length + 21)

end SQLean.Tests
