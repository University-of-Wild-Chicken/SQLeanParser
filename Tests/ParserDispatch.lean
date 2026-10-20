import SQLean.Parser
import Tests.Support

namespace SQLean.Tests

/-- The public compatibility dispatcher must not turn unsupported PostgreSQL
expressions into ordinary names, even when the legacy parser accepts them. -/
def parserDispatchTests : IO Nat := do
  let special := ["CURRENT_DATE", "CURRENT_TIME", "CURRENT_TIMESTAMP", "LOCALTIME",
    "LOCALTIMESTAMP", "CURRENT_USER", "SESSION_USER", "SYSTEM_USER", "CURRENT_ROLE",
    "CURRENT_CATALOG", "CURRENT_SCHEMA", "USER"]
  for name in special do
    expectError name (parseStatement s!"SELECT {name} FROM users")
    let _ ← expectOk s!"quoted {name}" (parseStatement s!"SELECT \"{name}\" FROM users")
    let _ ← expectOk s!"literal {name}" (parseStatement s!"SELECT '{name}' FROM users")
  let predicates := ["SELECT id ISNULL FROM users", "SELECT id NOTNULL FROM users",
    "SELECT * FROM ONLY users", "UPDATE ONLY users SET age = 1", "DELETE FROM ONLY users"]
  for sql in predicates do
    expectError sql (parseStatement sql)
  let quoted := ["SELECT id AS \"ISNULL\" FROM users", "SELECT id AS \"NOTNULL\" FROM users",
    "SELECT id FROM \"ONLY\"", "SELECT id FROM users /* CURRENT_DATE ISNULL ONLY */"]
  for sql in quoted do
    let _ ← expectOk sql (parseStatement sql)
  pure (3 * special.length + predicates.length + quoted.length)

end SQLean.Tests
