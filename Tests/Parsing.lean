import SQLean.Parser
import SQLean.Pretty
import Tests.Support

namespace SQLean.Tests

private def accepted : List String := [
  "SELECT id FROM users;",
  "select ID, NAME from USERS",
  "SELECT id, name FROM users WHERE id = 1;",
  "SELECT 1 + 2 * 3, id / 2 FROM users WHERE id >= 3 AND id <> 10 OR id < 0",
  "SELECT (id + 1) * 2 FROM users WHERE (id <= 10 OR id > 12)",
  "SELECT id = 1 FROM users",
  "SELECT 'O''Brien', \"a\"\"b\" FROM \"Mixed Case\"",
  "SELECT \"select\" FROM \"Table\"",
  "SELECT '-- /* text */' FROM users -- comment\n;",
  "/* leading */ SELECT id /* between */ FROM users /* trailing */",
  "SELECT 'λ🙂' FROM users",
  "SELECT 123456789012345678901234567890 FROM users",
  "SELECT ((id)) FROM users",
  "SELECT (id = 1) = (id = 2) FROM users",
  "SELECT id / 2 * 3 FROM users",
  "SELECT id FROM users WHERE id = 1 AND id = 2 AND id = 3"
]

private def rejected : List String := [
  "", ";", "-- only a comment", "SELECT", "SELECT FROM users",
  "SELECT * FROM users", "SELECT id users", "SELECT id FROM",
  "SELECT id FROM users trailing", "SELECT id FROM users SELECT id FROM users",
  "SELECT id FROM users; SELECT id FROM users", "SELECT id FROM users;;",
  "SELECT id FROM users WHERE", "SELECT id, FROM users",
  "SELECT (id + 1 FROM users", "SELECT id + FROM users",
  "SELECT id = 1 = 2 FROM users", "SELECT id < 1 < 2 FROM users",
  "SELECT id >= 1 <> 2 FROM users", "SELECT id / FROM users",
  "SELECT -1 FROM users", "SELECT +1 FROM users", "SELECT NOT id FROM users",
  "SELECT TRUE FROM users", "SELECT FALSE FROM users", "SELECT NULL FROM users",
  "SELECT id != 1 FROM users", "SELECT id == 1 FROM users",
  "SELECT id FROM users WHERE id = 1 AND",
  "SELECT 'unterminated FROM users", "SELECT \"unterminated FROM users",
  "SELECT id FROM users /* unterminated", "SELECT @ FROM users",
  "SELECT ! FROM users", "SELECT 1.2 FROM users", "SELECT 1e3 FROM users",
  "SELECT id FROM users LIMIT 1", "SELECT id FROM users JOIN other ON id = id",
  "SELECT id AS alias FROM users", "SELECT users.id FROM users",
  "SELECT id FROM users ORDER BY id", "SELECT id FROM users GROUP BY id",
  "SELECT count(id) FROM users", "SELECT DISTINCT id FROM users",
  "SELECT () FROM users", "SELECT \"\" FROM users",
  "CREATE TABLE users (id INT)", "INSERT INTO users VALUES (1)",
  "UPDATE users SET id = 1", "DELETE FROM users", "BEGIN", "COMMIT", "ROLLBACK"
]

def parsingTests : IO Nat := do
  for source in accepted do
    let _ ← expectOk source (parseQuery source)
  for source in rejected do
    expectError source (parseQuery source)
  let query ← expectOk "precedence" (parseQuery
    "SELECT a + 2 * 3 FROM t WHERE a = 1 AND b = 2 OR c = 3")
  SQLean.Tests.assert (query == (⟨"t", [
    .binary .add (.column "a") (.binary .mul (.literal (.int 2)) (.literal (.int 3)))],
    some (.binary .or
      (.binary .and (.binary .eq (.column "a") (.literal (.int 1)))
        (.binary .eq (.column "b") (.literal (.int 2))))
      (.binary .eq (.column "c") (.literal (.int 3))))⟩ : Query))
    "expression precedence AST differs"
  let assoc ← expectOk "associativity" (parseQuery "SELECT 10 - 3 - 2, 12 / 3 / 2 FROM t")
  SQLean.Tests.assert (assoc.selectList == [
    .binary .sub (.binary .sub (.literal (.int 10)) (.literal (.int 3))) (.literal (.int 2)),
    .binary .div (.binary .div (.literal (.int 12)) (.literal (.int 3))) (.literal (.int 2))])
    "subtraction and division must associate left"
  let escaped ← expectOk "escaping" (parseQuery "SELECT 'O''Brien', \"a\"\"b\" FROM \"T\"")
  SQLean.Tests.assert (escaped == { table := "T", selectList := [.literal (.text "O'Brien"), .column "a\"b"] })
    "quoted names or escaped strings changed"
  let normalized ← expectOk "case normalization" (parseQuery "SeLeCt ID FrOm USERS")
  SQLean.Tests.assert (normalized == { table := "users", selectList := [.column "id"] })
    "unquoted identifiers must normalize to lowercase"
  for source in accepted do
    let ast ← expectOk "round trip parse" (parseQuery source)
    let rendered := toSql ast
    let reparsed ← expectOk s!"round trip: {rendered}" (parseQuery rendered)
    SQLean.Tests.assert (ast == reparsed) s!"SQL rendering changed AST: {source}"
  match lex "-- comment\nSELECT @" with
  | .error e =>
    SQLean.Tests.assert (e.position.line == 2 && e.position.column == 8 && e.position.offset == 18)
      s!"unexpected error location: {e}"
  | .ok _ => throw (IO.userError "lexer accepted unsupported character")
  match lex "'λ🙂' @" with
  | .error e =>
    SQLean.Tests.assert (e.position.column == 6 && e.position.offset == 5)
      "lexer positions must count characters, not UTF-8 bytes"
  | .ok _ => throw (IO.userError "lexer accepted unsupported character after Unicode string")
  match parseQuery "SELECT id\nFROM users\nWHERE" with
  | .error e =>
    SQLean.Tests.assert (e.position.line == 3 && e.position.column == 6)
      s!"unexpected EOF location: {e}"
  | .ok _ => throw (IO.userError "parser accepted missing WHERE expression")
  pure (accepted.length * 2 + rejected.length + 7)

end SQLean.Tests
