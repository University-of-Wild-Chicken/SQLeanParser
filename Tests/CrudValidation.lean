import SQLean.CRUDValidation
import SQLean.Parser
import Tests.Support

namespace SQLean.Tests

private def schema : Schema :=
  [⟨"users", [⟨"id", .int⟩, ⟨"name", .text⟩, ⟨"active", .bool⟩]⟩]

private def validCases : List (String × List SqlType) := [
  ("SELECT * FROM users", [.int, .text, .bool]),
  ("SELECT DISTINCT name FROM users ORDER BY name DESC LIMIT 10 OFFSET 2", [.text]),
  ("SELECT DISTINCT name FROM users ORDER BY 1", [.text]),
  ("SELECT DISTINCT * FROM users ORDER BY active", [.int, .text, .bool]),
  ("SELECT id, name FROM users ORDER BY +2, - -1", [.int, .text]),
  ("SELECT id FROM users ORDER BY + +1", [.int]),
  ("SELECT -id, +id, NOT active, TRUE, FALSE FROM users WHERE NOT active",
    [.int, .int, .bool, .bool, .bool]),
  ("SELECT id FROM users ORDER BY name, active, id + 1 LIMIT 0", [.int]),
  ("INSERT INTO users VALUES (1, 'Ada', TRUE), (2, 'Grace', FALSE)", []),
  ("INSERT INTO users (active, name, id) VALUES (NOT FALSE, 'Ada', -5 + 6)", []),
  ("INSERT INTO users VALUES (1 / 0, 'Static validity only', TRUE)", []),
  ("UPDATE users SET id = id + 1, name = 'new', active = NOT active WHERE id > 0", []),
  ("UPDATE users SET id = -1", []),
  ("UPDATE users SET active = TRUE WHERE active = FALSE", []),
  ("DELETE FROM users WHERE NOT active OR id = 0", []),
  ("DELETE FROM users", [])
]

private def invalidCases : List String := [
  "INSERT INTO missing VALUES (1)",
  "INSERT INTO users VALUES (1, 'Ada')",
  "INSERT INTO users VALUES (1, 'Ada', TRUE, 4)",
  "INSERT INTO users VALUES ('wrong', 'Ada', TRUE)",
  "INSERT INTO users VALUES (1, 2, TRUE)",
  "INSERT INTO users VALUES (1, 'Ada', 1)",
  "INSERT INTO users VALUES (1, 'Ada', TRUE), (2, 'Grace')",
  "INSERT INTO users VALUES (1, 'Ada', TRUE), (2, 'Grace', 'wrong')",
  "INSERT INTO users VALUES (id, 'Ada', TRUE)",
  "INSERT INTO users VALUES (1, name, TRUE)",
  "INSERT INTO users VALUES (1, 'Ada', active)",
  "INSERT INTO users VALUES (1, 'Ada', NOT 1)",
  "INSERT INTO users (id, name) VALUES (1, 'Ada')",
  "INSERT INTO users (id, name, active, id) VALUES (1, 'Ada', TRUE, 2)",
  "INSERT INTO users (id, name, missing) VALUES (1, 'Ada', TRUE)",
  "INSERT INTO users (active, name, id) VALUES (1, 'Ada', TRUE)",
  "UPDATE missing SET id = 1",
  "UPDATE users SET missing = 1",
  "UPDATE users SET id = missing",
  "UPDATE users SET id = 'wrong'",
  "UPDATE users SET name = id",
  "UPDATE users SET active = 1",
  "UPDATE users SET id = 1, id = 2",
  "UPDATE users SET id = 1 WHERE id",
  "UPDATE users SET id = 1 WHERE missing = 2",
  "UPDATE users SET active = -active",
  "DELETE FROM missing",
  "DELETE FROM users WHERE id",
  "DELETE FROM users WHERE 'text'",
  "DELETE FROM users WHERE missing = 1",
  "SELECT * FROM missing",
  "SELECT -name FROM users",
  "SELECT +active FROM users",
  "SELECT NOT id FROM users",
  "SELECT id FROM users ORDER BY missing",
  "SELECT id FROM users ORDER BY name + 1",
  "SELECT DISTINCT id FROM users ORDER BY name",
  "SELECT DISTINCT id FROM users ORDER BY id + 1",
  "SELECT DISTINCT * FROM users ORDER BY id + 1",
  "SELECT id FROM users ORDER BY 0",
  "SELECT id FROM users ORDER BY 2",
  "SELECT id FROM users ORDER BY -1",
  "SELECT id FROM users ORDER BY +0",
  "SELECT id FROM users ORDER BY + +0",
  "SELECT id FROM users ORDER BY + +2",
  "SELECT id FROM users ORDER BY - -2",
  "SELECT DISTINCT id FROM users ORDER BY - -999"
]

private def invalidManual : List Statement := [
  .select { table := "users", projection := .expressions [] },
  .select { table := "users", projection := .all, offset := some 1 },
  .insert { table := "users", rows := [] },
  .insert { table := "users", rows := [[]] },
  .insert { table := "users", columns := some [], rows := [[]] },
  .update { table := "users", assignments := [] }
]

def crudValidationTests : IO Nat := do
  for (source, expected) in validCases do
    let statement ← expectOk source (parseStatement source)
    let certified ← expectOk source (certifyStatement schema statement)
    SQLean.Tests.assert (certified.outputTypes == expected) s!"wrong CRUD output types: {source}"
    let types ← expectOk source (checkStatement schema statement)
    SQLean.Tests.assert (types == expected) s!"checkStatement differs: {source}"
  for source in invalidCases do
    let statement ← expectOk s!"must parse before type rejection: {source}" (parseStatement source)
    expectError source (certifyStatement schema statement)
  for statement in invalidManual do
    expectError s!"invalid manually constructed CRUD AST: {repr statement}"
      (certifyStatement schema statement)
  let malformedSchema : Schema := [⟨"users", [⟨"id", .int⟩, ⟨"id", .int⟩]⟩]
  for source in ["SELECT id FROM users", "INSERT INTO users VALUES (1, 2)",
    "UPDATE users SET id = 1", "DELETE FROM users"] do
    let statement ← expectOk source (parseStatement source)
    expectError "every CRUD kind rejects malformed schemas" (certifyStatement malformedSchema statement)
  pure (validCases.length + invalidCases.length + invalidManual.length + 4)

/-- Kernel-reduced examples exercise each statement constructor without native_decide. -/
private def selectExample : Statement :=
  .select { table := "users", projection := .all }

private def insertExample : Statement :=
  .insert { table := "users", columns := some ["active", "id", "name"],
            rows := [[.literal (.bool true), .unary .neg (.literal (.int 1)), .literal (.text "Ada")]] }

private def updateExample : Statement :=
  .update { table := "users", assignments := [⟨"active", .unary .not (.column "active")⟩],
            whereClause := some (.binary .eq (.column "id") (.literal (.int 1))) }

private def deleteExample : Statement :=
  .delete { table := "users", whereClause := some (.column "active") }

example : ValidStatement schema selectExample [.int, .text, .bool] :=
  checkStatement_sound schema selectExample [.int, .text, .bool] rfl

example : ValidStatement schema insertExample [] :=
  checkStatement_sound schema insertExample [] rfl

example : ValidStatement schema updateExample [] :=
  checkStatement_sound schema updateExample [] rfl

example : ValidStatement schema deleteExample [] :=
  checkStatement_sound schema deleteExample [] rfl

example (schema : Schema) (statement : Statement) (types : List SqlType) :
    checkStatement schema statement = .ok types ↔ ValidStatement schema statement types :=
  checkStatement_iff schema statement types

end SQLean.Tests
