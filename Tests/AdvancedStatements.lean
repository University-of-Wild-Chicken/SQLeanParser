import SQLean
import SQLean.SchemaJson
import Tests.Support

namespace SQLean.Tests

private def statementCatalog : Advanced.Catalog := [{
  name := "users"
  columns := [
    { name := "id", type := ⟨.int, []⟩, nullable := some false },
    { name := "name", type := ⟨.text, []⟩, nullable := some false },
    { name := "balance", type := ⟨.real, []⟩ },
    { name := "active", type := ⟨.bool, []⟩, nullable := some false,
      defaultValue := some (.literal (.bool true)) }]
  uniqueKeys := [["id"]]
  namedKeys := [("users_id_key", ["id"])] }]

def advancedStatementTests : IO Nat := do
  let accepted : List (String × List SqlType) := [
    ("INSERT INTO users VALUES (1, 'Ada', NULL, TRUE) RETURNING *", [.int, .text, .nullable .real, .bool]),
    ("INSERT INTO users (id, name) VALUES (1, 'Ada') RETURNING balance, active", [.nullable .real, .bool]),
    ("INSERT INTO users (id, name, balance) SELECT 1, 'Ada', NULL RETURNING balance", [.nullable .real]),
    ("INSERT INTO users VALUES (1, 'Ada', 1.25e2, TRUE) ON CONFLICT (id) DO NOTHING", []),
    ("INSERT INTO users VALUES (1, 'Ada', NULL, TRUE) ON CONFLICT DO NOTHING RETURNING id", [.int]),
    ("INSERT INTO users (id, name) VALUES (1, 'Ada') ON CONFLICT (id) DO UPDATE SET name = excluded.name RETURNING id", [.int]),
    ("INSERT INTO users (id, name) VALUES (1, 'Ada') ON CONFLICT ON CONSTRAINT users_id_key DO UPDATE SET name = excluded.name WHERE users.id = excluded.id", []),
    ("INSERT INTO users AS u (id, name) VALUES (1, 'Ada') ON CONFLICT (id) DO UPDATE SET name = excluded.name WHERE u.id > 0 RETURNING u.id", [.int]),
    ("UPDATE users SET balance = NULL RETURNING balance", [.nullable .real]),
    ("UPDATE users AS u SET balance = 1.25 WHERE EXISTS (SELECT 1 WHERE u.id > 0) RETURNING u.id", [.int]),
    ("DELETE FROM users AS u WHERE u.id IN (SELECT id FROM users) RETURNING NULL", [.nullable .text]),
    ("DELETE FROM users RETURNING (SELECT COUNT(*) FROM users)", [.nullable .int]),
    ("CREATE TABLE items (id INT PRIMARY KEY, title TEXT NOT NULL DEFAULT 'new', price NUMERIC(8,2))", []),
    ("CREATE TABLE pairs (a INT, b INT, PRIMARY KEY (a,b), UNIQUE (b))", []),
    ("CREATE TABLE IF NOT EXISTS users (id INT)", []),
    ("ALTER TABLE users ADD COLUMN score REAL DEFAULT 1.5", []),
    ("ALTER TABLE users ADD COLUMN IF NOT EXISTS id TEXT", []),
    ("ALTER TABLE users ALTER COLUMN balance TYPE DOUBLE PRECISION", []),
    ("ALTER TABLE users ALTER COLUMN active DROP DEFAULT", []),
    ("ALTER TABLE users DROP COLUMN balance", []),
    ("ALTER TABLE users DROP COLUMN IF EXISTS absent", []),
    ("DROP TABLE IF EXISTS absent CASCADE", []),
    ("DROP TABLE users", [])]
  for (source, types) in accepted do
    let checked ← expectOk source (parseAndValidateAdvanced statementCatalog [] source)
    SQLean.Tests.assert (checked.result.outputTypes == types) s!"advanced statement types differ: {source}"
    let rendered := Advanced.render checked.statement
    let reparsed ← expectOk rendered (parseAndValidateAdvanced statementCatalog [] rendered)
    SQLean.Tests.assert (checked.statement == reparsed.statement && checked.result == reparsed.result)
      s!"advanced statement/catalog roundtrip: {source}"
  let rejected := [
    "INSERT INTO missing VALUES (1)", "INSERT INTO users (id) VALUES (1)",
    "INSERT INTO users (id, name) VALUES (NULL, 'Ada')",
    "INSERT INTO users (id, name) VALUES (1, NULL)",
    "INSERT INTO users (id, id) VALUES (1, 2)",
    "INSERT INTO users (id, missing) VALUES (1, 'Ada')",
    "INSERT INTO users (id, name) VALUES (1)",
    "INSERT INTO users (id, name) SELECT 1", "INSERT INTO users (id, name) SELECT NULL, 'Ada'",
    "INSERT INTO users (id, name) SELECT TRUE, 'Ada'", "INSERT INTO users DEFAULT VALUES",
    "INSERT INTO users (id, name) VALUES (1, 'Ada') ON CONFLICT (name) DO NOTHING",
    "INSERT INTO users (id, name) VALUES (1, 'Ada') ON CONFLICT (id, id) DO NOTHING",
    "INSERT INTO users (id, name) VALUES (1, 'Ada') ON CONFLICT ON CONSTRAINT missing DO NOTHING",
    "INSERT INTO users (id, name) VALUES (1, 'Ada') ON CONFLICT (id) DO UPDATE SET id = NULL",
    "INSERT INTO users (id, name) VALUES (1, 'Ada') ON CONFLICT (id) DO UPDATE SET name = excluded.missing",
    "INSERT INTO users (id, name) VALUES (1, 'Ada') ON CONFLICT (id) DO UPDATE SET name = 'x' WHERE id",
    "INSERT INTO users (id, name) VALUES (1, 'Ada') ON CONFLICT (id) DO UPDATE SET name = name",
    "INSERT INTO users (id, name) VALUES (1, 'Ada') ON CONFLICT (id) DO UPDATE SET name = excluded.name WHERE id = 1",
    "UPDATE users SET missing = 1", "UPDATE users SET name = NULL", "UPDATE users SET id = TRUE",
    "UPDATE users SET id = 1, id = 2", "UPDATE users SET id = 1 WHERE name",
    "UPDATE users AS u SET id = users.id", "DELETE FROM users WHERE name",
    "DELETE FROM users RETURNING COUNT(*)", "DELETE FROM users RETURNING other.*",
    "CREATE TABLE users (id INT)", "CREATE TABLE invalid (id INT, id TEXT)",
    "CREATE TABLE invalid (id INT, UNIQUE (missing))",
    "CREATE TABLE invalid (a INT PRIMARY KEY, b INT PRIMARY KEY)",
    "CREATE TABLE invalid (id INT DEFAULT missing)",
    "CREATE TABLE invalid (id INT DEFAULT (SELECT 1))",
    "CREATE TABLE invalid (id INT DEFAULT $1)",
    "CREATE TABLE invalid (id INT DEFAULT TRUE)",
    "CREATE TABLE invalid (id INT NOT NULL DEFAULT NULL)",
    "CREATE TABLE invalid (name VARCHAR(10485761))",
    "ALTER TABLE missing ADD COLUMN id INT", "ALTER TABLE users ADD COLUMN id TEXT",
    "ALTER TABLE users DROP COLUMN missing", "ALTER TABLE users RENAME COLUMN id TO name",
    "ALTER TABLE users RENAME TO users", "ALTER TABLE users ALTER COLUMN balance TYPE BOOLEAN",
    "ALTER TABLE users ALTER COLUMN active SET DEFAULT 1", "DROP TABLE missing",
    "ALTER TABLE users ADD COLUMN fresh INT, DROP COLUMN fresh",
    "ALTER TABLE users ALTER COLUMN balance TYPE INT, ALTER COLUMN balance TYPE REAL"]
  for source in rejected do
    let statement ← expectOk s!"semantic rejection must parse: {source}" (Advanced.parse source)
    expectError source (Advanced.checkStatementDetailed statementCatalog [] statement)
  expectError "DO UPDATE needs a conflict target"
    (Advanced.parse "INSERT INTO users (id, name) VALUES (1, 'Ada') ON CONFLICT DO UPDATE SET name = 'x'")
  expectError "VARCHAR length must be positive" (Advanced.parse "CREATE TABLE invalid (name VARCHAR(0))")
  let parameterCases : List (String × Advanced.ParameterEnv × List SqlType) := [
    ("SELECT ? BETWEEN ? AND ?", [(1,.int),(2,.int),(3,.int)], [.bool]),
    ("SELECT $2, $1, $2", [(1,.int),(2,.text)], [.text,.int,.text]),
    ("UPDATE users SET balance = ? WHERE id = ? RETURNING id", [(1,.real),(2,.int)], [.int]),
    ("INSERT INTO users (id, name) SELECT $1, $2 RETURNING id", [(1,.int),(2,.text)], [.int])]
  for (source, params, types) in parameterCases do
    let checked ← expectOk source (parseAndValidateAdvanced statementCatalog params source)
    SQLean.Tests.assert (checked.result.outputTypes == types) source
  for params in [[], [(1, .text)], [(1,.int),(1,.text)], [(0,.int)], [(1,.nullable .int)]] do
    expectError "parameter type declaration rejected"
      (parseAndValidateAdvanced statementCatalog params "UPDATE users SET id = $1")
  let sequence := [
    "CREATE TABLE books (id INT PRIMARY KEY, title TEXT NOT NULL DEFAULT 'untitled', rating REAL)",
    "INSERT INTO books (id) VALUES (1) RETURNING *",
    "ALTER TABLE books RENAME COLUMN id TO book_id",
    "ALTER TABLE books ADD COLUMN enabled BOOLEAN NOT NULL DEFAULT TRUE",
    "DROP TABLE books"]
  let statements ← expectOk "DDL sequence parse" (sequence.mapM Advanced.parse)
  let results ← expectOk "DDL sequence" (Advanced.checkStatements statementCatalog [] statements)
  SQLean.Tests.assert (results.length == 5) "catalog sequence result count"
  let some inserted := results[1]? | throw (IO.userError "missing INSERT transition")
  SQLean.Tests.assert (inserted.outputTypes == [.int,.text,.nullable .real]) "DDL drives INSERT typing"
  let some renamed := results[2]? | throw (IO.userError "missing RENAME transition")
  let some books := renamed.catalog.findTable "books" | throw (IO.userError "renamed catalog table lost")
  SQLean.Tests.assert (books.primaryKey == ["book_id"]) "RENAME must update primary key metadata"
  expectError "primary-key NOT NULL cannot be removed" (parseAndValidateAdvanced renamed.catalog []
    "ALTER TABLE books ALTER COLUMN book_id DROP NOT NULL")
  let some final := results[4]? | throw (IO.userError "missing DROP transition")
  SQLean.Tests.assert (final.catalog == statementCatalog) "DROP restores original catalog"
  let empty : Advanced.Statement := .insert { table := "users", source := .values [] }
  expectError "manual empty values" (Advanced.checkStatement statementCatalog [] empty)
  let mixed : Advanced.Statement := .update { table := "users", assignments := [
    ⟨"id", .binary .add (.parameter (.numbered 1)) (.parameter (.anonymous 1))⟩] }
  expectError "manual mixed parameters" (Advanced.checkStatement statementCatalog [(1,.int)] mixed)
  for source in ["SELECT NULL", "SELECT EXISTS (SELECT 1)", "CREATE TABLE next (id INT)"] do
    let _ ← expectOk "public statement integration" (parseAndValidateStatement statementCatalog.toSchema source)
  let decoded ← expectOk "nullable/real schema"
    (parseSchemaJson "{\"tables\":[{\"name\":\"t\",\"columns\":[{\"name\":\"v\",\"type\":\"real\",\"nullable\":true}]}]}")
  SQLean.Tests.assert (decoded == [⟨"t", [⟨"v", .nullable .real⟩]⟩]) "nullable JSON type"
  pure (accepted.length + rejected.length + parameterCases.length + 5 + 6 + 2 + 3 + 3)

end SQLean.Tests
