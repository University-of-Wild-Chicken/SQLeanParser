import SQLean
import Tests.Support

namespace SQLean.Tests

private def returningSchema : Schema := [
  ⟨"users", [⟨"id", .int⟩, ⟨"name", .text⟩, ⟨"active", .bool⟩]⟩]

def postgresReturningTests : IO Nat := do
  let accepted : List (String × List SqlType) := [
    ("INSERT INTO users VALUES (1, 'Ada', TRUE) RETURNING *", [.int, .text, .bool]),
    ("INSERT INTO users (name, id, active) VALUES ('Ada', 1, TRUE), ('Ben', 2, FALSE) RETURNING id, name", [.int, .text]),
    ("INSERT INTO users VALUES (1, 'Ada', TRUE) RETURNING users.*, id + 1 AS next_id", [.int, .text, .bool, .int]),
    ("INSERT INTO users VALUES (1, 'Ada', TRUE) RETURNING CAST(id AS TEXT) AS key", [.text]),
    ("UPDATE users SET name = 'Updated' WHERE id = 1 RETURNING id, name", [.int, .text]),
    ("UPDATE users SET id = id + 1 RETURNING id::TEXT, active", [.text, .bool]),
    ("UPDATE users SET active = FALSE RETURNING name ILIKE 'a%' AS matched", [.bool]),
    ("UPDATE users SET active = NOT active RETURNING id BETWEEN 1 AND 5", [.bool]),
    ("DELETE FROM users WHERE id = 1 RETURNING *", [.int, .text, .bool]),
    ("DELETE FROM users RETURNING users.name AS removed_name, NOT active AS disabled", [.text, .bool]),
    ("DELETE FROM users RETURNING id IN (1, 2, 3), 'deleted' AS event", [.bool, .text]),
    ("DELETE FROM users RETURNING 1 AS count_per_row", [.int])]
  for (source, types) in accepted do
    let checked ← expectOk source (parseAndValidateStatement returningSchema source)
    SQLean.Tests.assert (checked.certificate.outputTypes == types) s!"wrong RETURNING types: {source}"
    match checked.statement with
    | .returning mutation items =>
        let base ← expectOk "underlying mutation" (certifyStatement returningSchema mutation.toStatement)
        SQLean.Tests.assert base.outputTypes.isEmpty "bare mutation unexpectedly returned columns"
        let projection ← expectOk "RETURNING row projection"
          (checkRelQueryCore returningSchema (returningQuery mutation items))
        SQLean.Tests.assert (projection == types) "RETURNING row projection differs"
    | _ => throw (IO.userError s!"RETURNING constructor missing: {source}")
    let roundTrip ← expectOk source (parseAndValidateStatement returningSchema (toSql checked.statement))
    SQLean.Tests.assert (roundTrip.statement == checked.statement) s!"RETURNING AST round trip: {source}"
  let rejected : List String := [
    "INSERT INTO users VALUES (1) RETURNING id",
    "INSERT INTO users VALUES ('bad', 'Ada', TRUE) RETURNING id",
    "INSERT INTO users (id, name, active) VALUES (1, 'Ada', TRUE) RETURNING missing",
    "UPDATE users SET missing = 1 RETURNING id",
    "UPDATE users SET id = 'bad' RETURNING id",
    "UPDATE users SET id = 1 WHERE name RETURNING id",
    "UPDATE users SET id = 1, id = 2 RETURNING id",
    "DELETE FROM missing RETURNING 1",
    "DELETE FROM users WHERE id RETURNING id",
    "DELETE FROM users RETURNING other.id",
    "DELETE FROM users RETURNING other.*",
    "DELETE FROM users RETURNING COUNT(*)",
    "DELETE FROM users RETURNING SUM(id)",
    "DELETE FROM users RETURNING COUNT(*) FILTER (WHERE active)",
    "DELETE FROM users RETURNING CAST(COUNT(*) AS TEXT)",
    "DELETE FROM users RETURNING name ILIKE id",
    "DELETE FROM users RETURNING active::REAL"]
  for source in rejected do
    let statement ← expectOk source (parseStatement source)
    expectError source (certifyStatement returningSchema statement)
    match parseAndValidateStatement returningSchema source with
    | .error (.validation _) => pure ()
    | _ => throw (IO.userError s!"wrong RETURNING API failure category: {source}")
  let malformed := ["DELETE FROM users RETURNING", "UPDATE users SET id = 1 RETURNING , id",
    "INSERT INTO users VALUES (1, 'Ada', TRUE) RETURNING id,", "DELETE FROM users RETURNING id RETURNING name"]
  for source in malformed do
    match parseAndValidateStatement returningSchema source with
    | .error (.parse _) => pure ()
    | _ => throw (IO.userError s!"wrong RETURNING syntax failure category: {source}")
  let mutation : Mutation := .delete { table := "users" }
  expectError "empty manual RETURNING projection" (certifyStatement returningSchema (.returning mutation []))
  expectError "empty manual RETURNING alias" (certifyStatement returningSchema
    (.returning mutation [.expression (.column none "id") (some "")]))
  pure (accepted.length + rejected.length + malformed.length + 2)

example (schema : Schema) (mutation : Mutation) (items : List SelectItem)
    (certificate : CertifiedStatement schema (.returning mutation items)) :
    ValidStatement schema (.returning mutation items) certificate.outputTypes := certificate.valid

end SQLean.Tests
