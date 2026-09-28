import SQLean.Parser
import Tests.Support

namespace SQLean.Tests

private def accepted : List String := [
  "SELECT * FROM users",
  "SELECT DISTINCT * FROM users;",
  "SELECT DISTINCT id, name FROM users WHERE active ORDER BY age DESC, id ASC LIMIT 10 OFFSET 2",
  "SELECT id FROM users ORDER BY id",
  "SELECT id FROM users LIMIT 0",
  "SELECT id FROM users LIMIT 20 OFFSET 0",
  "SELECT TRUE, FALSE, -1, +2 FROM users",
  "SELECT NOT age = 1 AND active OR FALSE FROM users",
  "SELECT NOT NOT TRUE, - -1, + +2 FROM users",
  "SELECT (age != 1) = active FROM users",
  "SELECT \"order\", \"limit\" FROM \"select\" ORDER BY \"order\" DESC",
  "INSERT INTO users VALUES (1, 'Ada', 30, TRUE)",
  "INSERT INTO users (id, name) VALUES (1, 'Ada'), (2, 'O''Brien');",
  "INSERT INTO \"Users\" (\"ID\") VALUES (-1), (+2), ((3 + 4) * 2)",
  "INSERT INTO flags VALUES (NOT FALSE), (TRUE AND NOT FALSE)",
  "UPDATE users SET age = age + 1",
  "UPDATE users SET name = 'Ada', active = NOT active WHERE id != 2;",
  "UPDATE \"Order\" SET \"set\" = -(1 + 2), \"where\" = TRUE",
  "DELETE FROM users",
  "DELETE FROM users WHERE NOT (active = FALSE) AND age >= 18;",
  "/* start */ delete /* keyword */ FROM users -- comment\n WHERE id = 1 /* end */;",
  "insert INTO users (id, name) VALUES (1, '--; /* SQL */'), (2, 'λ🙂') -- end",
  "UPDATE users SET age = -age * +2, active = NOT age > 21 AND active",
  "SELECT *, id FROM users", "SELECT id, * FROM users",
  "SELECT id IS NULL FROM users", "SELECT id AS label FROM users",
  "SELECT users.id FROM users", "SELECT id FROM users JOIN other ON id = id",
  "SELECT COUNT(id) FROM users"
]

private def rejected : List String := [
  "", ";", "-- only comment", "SELECT", "INSERT", "UPDATE", "DELETE",
  "SELECT FROM users", "SELECT DISTINCT FROM users", "SELECT DISTINCT DISTINCT id FROM users",
  "SELECT * + 1 FROM users",
  "SELECT id FROM users ORDER id", "SELECT id FROM users ORDER BY",
  "SELECT id FROM users ORDER BY id,", "SELECT id FROM users ORDER BY id ASC DESC",
  "SELECT id FROM users ORDER BY id WHERE active",
  "SELECT id FROM users LIMIT", "SELECT id FROM users LIMIT -1",
  "SELECT id FROM users LIMIT +1", "SELECT id FROM users LIMIT 1 + 2",
  "SELECT id FROM users LIMIT '1'", "SELECT id FROM users LIMIT 1.5",
  "SELECT id FROM users OFFSET 1", "SELECT id FROM users LIMIT 1 OFFSET",
  "SELECT id FROM users LIMIT 1 OFFSET -1", "SELECT id FROM users LIMIT 1 OFFSET +1",
  "SELECT id FROM users LIMIT 1 LIMIT 2", "SELECT id FROM users LIMIT 1 ORDER BY id",
  "SELECT id FROM users LIMIT 1 OFFSET 2 OFFSET 3",
  "SELECT id FROM users WHERE id = 1 = 2", "SELECT id FROM users WHERE NOT id < 1 < 2",
  "SELECT id = NOT active FROM users", "SELECT -NOT active FROM users",
  "SELECT TRUE FALSE FROM users", "SELECT NOT FROM users", "SELECT + FROM users",
  "SELECT NULL FROM users", "SELECT id IN (1, 2) FROM users",
  "SELECT order FROM users", "SELECT id FROM limit",
  "INSERT users VALUES (1)", "INSERT INTO VALUES (1)", "INSERT INTO users",
  "INSERT INTO users () VALUES (1)", "INSERT INTO users (id,) VALUES (1)",
  "INSERT INTO users (id name) VALUES (1)", "INSERT INTO users VALUES",
  "INSERT INTO users VALUES ()", "INSERT INTO users VALUES (1,)",
  "INSERT INTO users VALUES (1),", "INSERT INTO users VALUES (1), ()",
  "INSERT INTO users VALUES 1", "INSERT INTO users VALUES ((1)",
  "INSERT INTO users VALUES (DEFAULT)", "INSERT INTO users DEFAULT VALUES",
  "INSERT INTO users SELECT id FROM users", "INSERT INTO users VALUES (1) RETURNING id",
  "INSERT INTO users VALUES (1) ON CONFLICT (id) DO NOTHING",
  "UPDATE users", "UPDATE users SET", "UPDATE users SET = 1",
  "UPDATE users SET id", "UPDATE users SET id =", "UPDATE users SET id == 1",
  "UPDATE users SET id = 1,", "UPDATE users SET id = 1 name = 'Ada'",
  "UPDATE users SET id = 1 WHERE", "UPDATE users SET id = 1 ORDER BY id",
  "UPDATE users SET id = 1 LIMIT 1", "UPDATE users SET id = 1 RETURNING id",
  "DELETE users", "DELETE FROM", "DELETE FROM users WHERE",
  "DELETE * FROM users", "DELETE FROM users LIMIT 1", "DELETE FROM users RETURNING id",
  "CREATE TABLE users (id INT)", "DROP TABLE users", "BEGIN", "COMMIT", "ROLLBACK",
  "SELECT * FROM users;;", "INSERT INTO users VALUES (1);;",
  "UPDATE users SET id = 1;;", "DELETE FROM users;;",
  "SELECT * FROM users; DELETE FROM users",
  "INSERT INTO users VALUES (1); SELECT * FROM users",
  "UPDATE users SET id = 1; DELETE FROM users",
  "DELETE FROM users; INSERT INTO users VALUES (1)"
]

private def int (n : Nat) : Expr := .literal (.int n)
private def bool (b : Bool) : Expr := .literal (.bool b)

def crudParsingTests : IO Nat := do
  for source in accepted do
    let _ ← expectOk source (parseStatement source)
  for source in rejected do
    expectError source (parseStatement source)

  let selected ← expectOk "SELECT AST" (parseStatement
    "SELECT DISTINCT id FROM users WHERE active ORDER BY age + 1 DESC, id ASC LIMIT 0 OFFSET 2")
  SQLean.Tests.assert (selected == .select {
    table := "users", projection := .expressions [.column "id"],
    whereClause := some (.column "active"), distinct := true,
    orderBy := [{ expr := .binary .add (.column "age") (int 1), descending := true },
      { expr := .column "id" }], limit := some 0, offset := some 2 })
    "SELECT clauses changed AST"

  let star ← expectOk "wildcard AST" (parseStatement "SELECT * FROM users")
  SQLean.Tests.assert (star == .select { table := "users", projection := .all })
    "wildcard must be represented explicitly"

  let logical ← expectOk "NOT precedence" (parseStatement
    "SELECT NOT a = b AND c OR NOT NOT TRUE FROM t")
  SQLean.Tests.assert (logical == .select {
    table := "t", projection := .expressions [
      .binary .or (.binary .and (.unary .not (.binary .eq (.column "a") (.column "b")))
        (.column "c")) (.unary .not (.unary .not (bool true)))] })
    "NOT must bind below comparison and above AND; nested NOT must associate right"

  let arithmetic ← expectOk "unary arithmetic precedence" (parseStatement
    "SELECT -a * +b + -(1 + 2) / -3 FROM t")
  SQLean.Tests.assert (arithmetic == .select {
    table := "t", projection := .expressions [
      .binary .add (.binary .mul (.unary .neg (.column "a")) (.unary .pos (.column "b")))
        (.binary .div (.unary .neg (.binary .add (int 1) (int 2))) (.unary .neg (int 3)))] })
    "unary arithmetic must bind above multiplication"

  let comparison ← expectOk "inequality synonym" (parseStatement "SELECT a != 1 FROM t")
  let canonical ← expectOk "canonical inequality" (parseStatement "SELECT a <> 1 FROM t")
  SQLean.Tests.assert (comparison == canonical) "!= must have the same AST as <>"

  let inserted ← expectOk "INSERT AST" (parseStatement
    "INSERT INTO t (\"ID\", name) VALUES (1, 'Ada'), (2, 'O''Brien')")
  SQLean.Tests.assert (inserted == .insert {
    table := "t", columns := some ["ID", "name"],
    rows := [[int 1, .literal (.text "Ada")], [int 2, .literal (.text "O'Brien")]] })
    "INSERT must preserve column and row order and escaping"

  let positional ← expectOk "positional INSERT AST" (parseStatement "INSERT INTO t VALUES (1)")
  SQLean.Tests.assert (positional == .insert { table := "t", rows := [[int 1]] })
    "omitted INSERT column list must remain none"

  let updated ← expectOk "UPDATE AST" (parseStatement
    "UPDATE t SET a = a + 1, b = NOT FALSE WHERE a != 0")
  SQLean.Tests.assert (updated == .update {
    table := "t", assignments := [
      { column := "a", value := .binary .add (.column "a") (int 1) },
      { column := "b", value := .unary .not (bool false) }],
    whereClause := some (.binary .ne (.column "a") (int 0)) })
    "UPDATE assignments or predicate changed AST"

  let deleted ← expectOk "DELETE AST" (parseStatement "DELETE FROM t WHERE NOT a = 0")
  SQLean.Tests.assert (deleted == .delete {
    table := "t", whereClause := some (.unary .not (.binary .eq (.column "a") (int 0))) })
    "DELETE predicate changed AST"

  let noPredicate ← expectOk "unconditional DELETE" (parseStatement "DELETE FROM t")
  SQLean.Tests.assert (noPredicate == .delete { table := "t" })
    "omitted DELETE predicate must remain none"

  let oldKeywords := "SELECT order, distinct, limit, offset, asc, desc, by FROM order"
  let _ ← expectOk "MVP identifier compatibility" (parseQuery oldKeywords)
  expectError "CRUD reserved keywords" (parseStatement oldKeywords)

  expectError "missing final EOF" (Parser.parseStatementTokens [])
  expectError "non-EOF final token" (Parser.parseStatementTokens [⟨.word "delete", {}⟩])
  expectError "multiple EOF tokens" (Parser.parseStatementTokens [⟨.eof, {}⟩, ⟨.eof, {}⟩])
  let tokens ← expectOk "token API lexer" (lex "DELETE FROM t")
  let tokenAst ← expectOk "token API parser" (Parser.parseStatementTokens tokens)
  SQLean.Tests.assert (tokenAst == noPredicate) "token API and string API differ"

  match parseStatement "UPDATE t\nSET a = 1,\n" with
  | .error error =>
    SQLean.Tests.assert (error.position.line == 3 && error.position.column == 1)
      s!"missing assignment source location differs: {error}"
  | .ok _ => throw (IO.userError "accepted missing UPDATE assignment")

  let rows := String.intercalate ", " ((List.range 120).map fun n => s!"({n})")
  let longInsert ← expectOk "120 INSERT rows" (parseStatement s!"INSERT INTO t VALUES {rows}")
  match longInsert with
  | .insert query => SQLean.Tests.assert (query.rows.length == 120) "lost INSERT rows"
  | _ => throw (IO.userError "INSERT returned wrong statement kind")

  let assignments := String.intercalate ", " ((List.range 120).map fun n => s!"c{n} = {n}")
  let longUpdate ← expectOk "120 UPDATE assignments" (parseStatement s!"UPDATE t SET {assignments}")
  match longUpdate with
  | .update query => SQLean.Tests.assert (query.assignments.length == 120) "lost assignments"
  | _ => throw (IO.userError "UPDATE returned wrong statement kind")

  let ordering := String.intercalate ", " ((List.range 120).map fun n => s!"c{n} DESC")
  let longSelect ← expectOk "120 ORDER BY items" (parseStatement s!"SELECT * FROM t ORDER BY {ordering}")
  match longSelect with
  | .select query => SQLean.Tests.assert (query.orderBy.length == 120) "lost ORDER BY items"
  | _ => throw (IO.userError "SELECT returned wrong statement kind")

  let nested := (List.range 40).foldl (fun text _ => s!"NOT ({text})") "TRUE"
  let _ ← expectOk "nested NOT expression" (parseStatement s!"DELETE FROM t WHERE {nested}")
  pure (accepted.length + rejected.length + 21)

end SQLean.Tests
