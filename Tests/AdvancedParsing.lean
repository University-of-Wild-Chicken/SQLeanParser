import SQLean.AdvancedParser
import SQLean.AdvancedPretty
import Tests.Support

namespace SQLean.Tests
open Advanced

private def accepted : List String := [
  "SELECT id IN (SELECT user_id FROM orders) FROM users",
  "SELECT id NOT IN (SELECT user_id FROM orders WHERE amount > 1.25) FROM users",
  "SELECT id IN ((SELECT user_id FROM orders) INTERSECT (SELECT id FROM users)) FROM users",
  "SELECT EXISTS (SELECT 1 FROM orders o WHERE o.user_id = u.id) FROM users u",
  "SELECT NOT EXISTS (SELECT 1 FROM orders o WHERE o.user_id = u.id AND EXISTS (SELECT 1 FROM users v WHERE v.id = o.user_id)) FROM users u",
  "SELECT (SELECT MAX(amount) FROM orders o WHERE o.user_id = u.id) FROM users u",
  "SELECT u.id, q.n FROM users u CROSS JOIN LATERAL (SELECT u.id + 1 AS n) q",
  "SELECT u.id, q.n FROM users u LEFT OUTER JOIN LATERAL (SELECT COUNT(*) AS n FROM orders o WHERE o.user_id = u.id) q ON TRUE",
  "SELECT * FROM users u, LATERAL (SELECT u.id) q",
  "SELECT * FROM users u, orders o JOIN users v ON v.id = o.user_id",
  "SELECT * FROM a INNER JOIN b USING (id)",
  "SELECT a.*, b.* FROM a FULL OUTER JOIN b USING (id, city)",
  "SELECT * FROM a NATURAL JOIN b",
  "SELECT * FROM a NATURAL LEFT OUTER JOIN b NATURAL RIGHT JOIN c",
  "SELECT * FROM (a JOIN b USING (id)) JOIN c ON c.id = a.id",
  "SELECT 1 UNION SELECT 2 INTERSECT SELECT 3 EXCEPT ALL SELECT 4",
  "(SELECT 1 UNION ALL SELECT 2) INTERSECT (SELECT 2 EXCEPT SELECT 3)",
  "SELECT 1 INTERSECT ALL SELECT 1 INTERSECT DISTINCT SELECT 1 ORDER BY 1 DESC LIMIT 1 OFFSET 0",
  "WITH q(n) AS (SELECT 1 UNION SELECT 2) SELECT n FROM q EXCEPT SELECT 2",
  "WITH RECURSIVE q(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM q WHERE n < 4) SELECT n FROM q",
  "SELECT DISTINCT ON (id) id, COUNT(*) FILTER (WHERE amount > 1.5) FROM orders GROUP BY id HAVING COUNT(*) > 0 ORDER BY id NULLS LAST",
  "SELECT NULL, NULL::INTEGER, CAST(NULL AS NUMERIC(10,2)), 1.25, .5, 2., 3e2, 4E-3, 5e+2",
  "SELECT -1.5::DOUBLE PRECISION, (+1.25)::NUMERIC, 1.2e-30 / 2.0",
  "SELECT $1, $2::TEXT, $1 + 1, $123::BOOLEAN",
  "SELECT ?, ?::TEXT, ? + 1",
  "SELECT ? BETWEEN ? AND ?, ? NOT BETWEEN 1 AND 2",
  "SELECT $1 IN ($2, $3), $1 IS NULL, $2 NOT LIKE $3",
  "SELECT '?' AS \"$1\", /* $2 ? */ 1 -- ?\n",
  "SELECT /* nested /* comment */ done */ 1",
  "SELECT \"select\".\"null\", 'O''Neil' FROM \"from\" AS \"select\"",
  "INSERT INTO users(id,name) SELECT id, name FROM archived_users RETURNING id",
  "INSERT INTO users(id) (SELECT id FROM a UNION SELECT id FROM b) RETURNING *",
  "INSERT INTO users(id) VALUES (1) ON CONFLICT DO NOTHING RETURNING *",
  "INSERT INTO users AS u(id,name) VALUES (1,'A') ON CONFLICT (id) DO UPDATE SET name = excluded.name WHERE u.id > 0 RETURNING u.id",
  "INSERT INTO users(id) VALUES (1) ON CONFLICT ON CONSTRAINT users_pkey DO NOTHING",
  "INSERT INTO users DEFAULT VALUES RETURNING *",
  "UPDATE users AS u SET name = $1, age = age + 1.0 WHERE EXISTS (SELECT 1 FROM orders o WHERE o.user_id = u.id) RETURNING id",
  "DELETE FROM users u WHERE id IN (SELECT user_id FROM orders) RETURNING id",
  "CREATE TABLE t (id BIGINT PRIMARY KEY, label VARCHAR(30) NOT NULL DEFAULT 'a', price NUMERIC(12,2), score DOUBLE PRECISION, valid BOOLEAN DEFAULT TRUE, UNIQUE(label))",
  "CREATE TABLE IF NOT EXISTS t (id INT NULL, value TEXT UNIQUE, PRIMARY KEY(id))",
  "CREATE TABLE t (id INTEGER, x REAL DEFAULT 1.25, y TEXT DEFAULT NULL, PRIMARY KEY (id), UNIQUE (x, y))",
  "ALTER TABLE t ADD COLUMN IF NOT EXISTS x INTEGER NOT NULL DEFAULT 0, ADD y TEXT",
  "ALTER TABLE t DROP COLUMN IF EXISTS x CASCADE, DROP y RESTRICT",
  "ALTER TABLE t RENAME COLUMN x TO y",
  "ALTER TABLE t RENAME TO new_t",
  "ALTER TABLE t ALTER COLUMN x TYPE NUMERIC(20,4), ALTER y SET DATA TYPE VARCHAR(10)",
  "ALTER TABLE t ALTER COLUMN x SET NOT NULL, ALTER COLUMN y DROP NOT NULL",
  "ALTER TABLE t ALTER COLUMN x SET DEFAULT 1.0, ALTER COLUMN y DROP DEFAULT",
  "DROP TABLE IF EXISTS t CASCADE",
  "DROP TABLE t RESTRICT"
]

private def rejected : List String := [
  "", "SELECT", "SELECT FROM t", "SELECT 1; SELECT 2", "SELECT 1;;",
  "SELECT 1 IN ()", "SELECT 1 IN (1,)", "SELECT 1 IN (SELECT)", "SELECT 1 IN SELECT 1",
  "SELECT EXISTS ()", "SELECT EXISTS SELECT 1", "SELECT EXISTS (1)", "SELECT NOT EXISTS",
  "SELECT * FROM LATERAL t", "SELECT * FROM LATERAL (SELECT 1)",
  "SELECT * FROM a LEFT JOIN b", "SELECT * FROM a JOIN b USING ()",
  "SELECT * FROM a JOIN b USING (id,)", "SELECT * FROM a JOIN b USING id",
  "SELECT * FROM a CROSS JOIN b ON TRUE", "SELECT * FROM a NATURAL CROSS JOIN b",
  "SELECT * FROM a NATURAL JOIN b USING (id)", "SELECT * FROM a NATURAL JOIN b ON TRUE",
  "SELECT 1 INTERSECT", "SELECT 1 EXCEPT ALL", "SELECT 1 UNION INTERSECT SELECT 2",
  "SELECT 1 INTERSECT ALL ALL SELECT 2", "SELECT 1 ORDER BY 1 UNION SELECT 2",
  "(SELECT id FROM users LIMIT 1) ORDER BY id DESC",
  "(SELECT id FROM users ORDER BY id) LIMIT 1",
  "SELECT 1 LIMIT $1", "SELECT 1 LIMIT ?", "SELECT 1 OFFSET 1.5", "SELECT 1 LIMIT -1",
  "SELECT .", "SELECT 1e", "SELECT 1e+", "SELECT 1e-", "SELECT 1.2.3",
  "SELECT 1abc", "SELECT 1e2x", "SELECT .e2", "SELECT 1..2", "SELECT 1e2.0",
  "SELECT $0", "SELECT $", "SELECT $-1", "SELECT $1name", "SELECT ?, $1", "SELECT $1, ?",
  "SELECT 1 IN (1) IN (2)", "SELECT 1 BETWEEN 0 AND", "SELECT 1 BETWEEN AND 2",
  "SELECT 1 NOT = 2", "SELECT 1 = 2 = 3", "SELECT 1 FILTER (WHERE TRUE)",
  "SELECT (COUNT(*)) FILTER (WHERE TRUE)", "SELECT COUNT(DISTINCT *)",
  "SELECT CAST(1 AS INTEGER(2))", "SELECT 1::DOUBLE", "SELECT 1::VARCHAR(0)",
  "SELECT 1::NUMERIC(0)", "SELECT 1::NUMERIC(1001)", "SELECT 1::NUMERIC(2,1001)",
  "SELECT 1::NUMERIC(2,1,1)", "SELECT 1::VARCHAR(2,1)",
  "INSERT INTO t VALUES ()", "INSERT INTO t VALUES (1) ON CONFLICT",
  "INSERT INTO t VALUES (1) ON CONFLICT () DO NOTHING",
  "INSERT INTO t VALUES (1) ON CONFLICT DO UPDATE SET id = 1",
  "INSERT INTO t VALUES (1) ON CONFLICT (id) DO UPDATE",
  "INSERT INTO t VALUES (1) ON CONFLICT (id) DO UPDATE SET",
  "INSERT INTO t SELECT", "INSERT INTO t VALUES (1) RETURNING",
  "CREATE TABLE t ()", "CREATE TABLE t (id)", "CREATE TABLE t (id UNKNOWN)",
  "CREATE TABLE t (id INT,)", "CREATE TABLE t (id INT NULL NOT NULL)",
  "CREATE TABLE t (id INT DEFAULT 1 DEFAULT 2)", "CREATE TABLE t (id INT UNIQUE UNIQUE)",
  "CREATE TABLE t (id INT PRIMARY KEY PRIMARY KEY)", "CREATE TABLE t (PRIMARY KEY(id))",
  "CREATE TABLE t (id INT, UNIQUE())", "CREATE TABLE t (id INT REFERENCES other(id))",
  "ALTER TABLE t", "ALTER TABLE t ADD", "ALTER TABLE t DROP COLUMN",
  "ALTER TABLE t ALTER COLUMN x SET", "ALTER TABLE t ALTER COLUMN x DROP",
  "ALTER TABLE t RENAME COLUMN x", "ALTER TABLE t RENAME TO x, ADD y INT",
  "ALTER TABLE t ADD x INT, RENAME COLUMN y TO z", "DROP TABLE", "DROP TABLE IF t",
  "DROP TABLE t CASCADE RESTRICT", "SELECT 'unterminated", "SELECT \"unterminated",
  "SELECT /* unterminated", "SELECT \"\"", "SELECT 1 --done\n +"
]

private def exprShape (sql : String) (expected : Advanced.Expr) : IO Unit := do
  let expr ← expectOk sql (Advanced.parseExpression sql)
  SQLean.Tests.assert (expr == expected) s!"unexpected expression tree: {sql}"

private def queryBody (sql : String) : IO Advanced.QueryBody := do
  return (← expectOk sql (Advanced.parseQuery sql)).body

/-- Focused syntax, binding identity, precedence, diagnostic and roundtrip regressions. -/
def advancedParsingTests : IO Nat := do
  for sql in accepted do
    let ast ← expectOk sql (Advanced.parse sql)
    let again ← expectOk "advanced canonical SQL" (Advanced.parse (Advanced.render ast))
    SQLean.Tests.assert (ast == again) s!"canonical SQL changed AST: {sql}\n{Advanced.render ast}"
  for sql in rejected do
    expectError sql (Advanced.parse sql)
  let int (n : Nat) : Advanced.Expr := .literal (.int n)
  exprShape "1 + 2 * 3" (.binary .add (int 1) (.binary .mul (int 2) (int 3)))
  exprShape "-1.25::REAL" (.unary .neg (.cast (.decimal "1.25") {name := .real}))
  exprShape "NOT 1 IN (2,3) AND TRUE" (.binary .and (.unary .not (.inList (int 1) [int 2, int 3])) (.literal (.bool true)))
  exprShape "? BETWEEN ? AND ?" (.between (.parameter (.anonymous 1)) (.parameter (.anonymous 2)) (.parameter (.anonymous 3)))
  exprShape "? NOT BETWEEN 1 AND 2" (.between (.parameter (.anonymous 1)) (int 1) (int 2) true)
  exprShape "$2 + $2" (.binary .add (.parameter (.numbered 2)) (.parameter (.numbered 2)))
  for raw in [".5", "1.", "1.2500", "3e+2", "3E-2", "12345678901234567890.00000000001"] do
    exprShape raw (.decimal raw)
  match ← queryBody "SELECT 1 UNION SELECT 2 INTERSECT SELECT 3 EXCEPT SELECT 4" with
  | .set .except false {body := .set .union false _ {body := .set .intersect false _ _, ..}, ..} _ => pure ()
  | _ => throw (IO.userError "INTERSECT must bind above left-associated UNION/EXCEPT")
  match ← queryBody "(SELECT 1 UNION SELECT 2) INTERSECT SELECT 3" with
  | .set .intersect false {body := .set .union false _ _, ..} _ => pure ()
  | _ => throw (IO.userError "parenthesized set operand was flattened")
  match ← queryBody "SELECT 1 EXCEPT SELECT 2 EXCEPT SELECT 3" with
  | .set .except false {body := .set .except false _ _, ..} _ => pure ()
  | _ => throw (IO.userError "EXCEPT must associate left")
  let question ← expectOk "anonymous placeholders" (Advanced.parse "SELECT ?, '?' AS label, ? BETWEEN 1 AND 2")
  SQLean.Tests.assert ((Advanced.renderPostgres question).contains '$') "PostgreSQL renderer must number parameters"
  let pg ← expectOk "numbered PostgreSQL SQL" (Advanced.parse (Advanced.renderPostgres question))
  match pg with
  | .query {body := .select {items := [.expression (.parameter (.numbered 1)) _, _, .expression (.between (.parameter (.numbered 2)) _ _ _) _], ..}, ..} => pure ()
  | _ => throw (IO.userError "anonymous parameter identity was not preserved")
  match Advanced.parse "SELECT 1;\n$0" with
  | .error e => SQLean.Tests.assert (e.position.line == 2 && e.position.column == 1) "parameter diagnostic lost source position"
  | .ok _ => throw (IO.userError "invalid zero parameter accepted")
  match Advanced.parse "SELECT 1;\n  1e+" with
  | .error e => SQLean.Tests.assert (e.position.line == 2 && e.position.column == 3) "numeric diagnostic lost source position"
  | .ok _ => throw (IO.userError "malformed numeric exponent accepted")
  pure (accepted.length * 2 + rejected.length + 19)

end SQLean.Tests
