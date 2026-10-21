import SQLean.Parser
import SQLean.AdvancedEquality
import Tests.Support

namespace SQLean.Tests

/-- The public compatibility dispatcher must not turn unsupported PostgreSQL
expressions into ordinary names, even when the legacy parser accepts them. -/
def parserDispatchTests : IO Nat := do
  let special := ["CURRENT_DATE", "CURRENT_TIME", "CURRENT_TIMESTAMP", "LOCALTIME",
    "LOCALTIMESTAMP"]
  for name in special do
    expectError name (parseStatement s!"SELECT {name} FROM users")
    let _ ← expectOk s!"quoted {name}" (parseStatement s!"SELECT \"{name}\" FROM users")
    let _ ← expectOk s!"literal {name}" (parseStatement s!"SELECT '{name}' FROM users")
  let contextValues := [("CURRENT_USER", Advanced.ContextValue.currentUser),
    ("SESSION_USER", .sessionUser), ("SYSTEM_USER", .systemUser), ("CURRENT_ROLE", .currentRole),
    ("CURRENT_CATALOG", .currentCatalog), ("CURRENT_SCHEMA", .currentSchema), ("USER", .user)]
  for (name, value) in contextValues do
    match ← expectOk name (parseStatement s!"SELECT {name} FROM users") with
    | .extended (.query {body := .select select, ..}) =>
        SQLean.Tests.assert (select.items == [.expression (.contextValue value)])
          "context keyword was interpreted as a compatibility column"
    | _ => throw (IO.userError "context value lost its advanced AST")
    let _ ← expectOk s!"quoted {name}" (parseStatement s!"SELECT \"{name}\" FROM users")
    let _ ← expectOk s!"literal {name}" (parseStatement s!"SELECT '{name}' FROM users")
  for (spelling, negated) in [("ISNULL", false), ("NOTNULL", true)] do
    match ← expectOk spelling (parseStatement s!"SELECT id {spelling} FROM users") with
    | .extended (.query {body := .select select, ..}) =>
        SQLean.Tests.assert (select.items == [.expression (.isNull (.column none "id") negated)])
          "postfix null-test spelling was interpreted as a compatibility alias"
    | _ => throw (IO.userError "postfix null test lost its advanced AST")
  let predicates := ["SELECT * FROM ONLY users", "UPDATE ONLY users SET age = 1", "DELETE FROM ONLY users"]
  for sql in predicates do
    expectError sql (parseStatement sql)
  let quoted := ["SELECT id AS \"ISNULL\" FROM users", "SELECT id AS \"NOTNULL\" FROM users",
    "SELECT id FROM \"ONLY\"", "SELECT id FROM users /* CURRENT_DATE ISNULL ONLY */"]
  for sql in quoted do
    let _ ← expectOk sql (parseStatement sql)
  let rows := ["SELECT ROW(1) = ROW(1)", "SELECT (1,2) < (1,3)",
    "SELECT ROW() = ROW()"]
  for sql in rows do
    match ← expectOk sql (parseStatement sql) with
    | .extended (.query _) => pure ()
    | _ => throw (IO.userError "row comparison lost the advanced AST")
  match ← expectOk "ordinary row column" (parseStatement "SELECT row FROM users") with
  | .select _ => pure ()
  | _ => throw (IO.userError "ROW lookahead changed an ordinary compatibility column")
  match ← expectOk "COLLATE dispatch" (parseStatement "SELECT id COLLATE \"C\" FROM users") with
  | .extended (.query {body := .select select, ..}) =>
      SQLean.Tests.assert
        (select.items == [.expression (.collate (.column none "id") ["C"])])
        "COLLATE lost the operand or identifier components"
  | _ => throw (IO.userError "COLLATE lost its advanced AST")
  for sql in ["SELECT id COLLATE FROM users", "SELECT collate FROM users"] do
    expectError sql (parseStatement sql)
  for sql in ["SELECT \"collate\" FROM users", "SELECT id AS \"collate\" FROM users",
      "SELECT id AS collate FROM users", "SELECT id FROM users /* COLLATE */"] do
    let _ ← expectOk sql (parseStatement sql)
  -- KEY is UNRESERVED_KEYWORD in the pinned PostgreSQL grammar. A legacy
  -- clause list must not reject genuine projection/source references.
  let keyQuery : Advanced.Query := {body := .select {
    items := [.expression (.column none "key")], source := some (.table "key")}}
  for (source, expected) in [
      ("key", Advanced.Expr.column none "key"),
      ("KEY", .column none "key"),
      ("key.value", .column (some "key") "value"),
      ("s.key.key", .column (some "key") "key" (some "s")),
      ("key IN(SELECT key FROM key)", .inQuery (.column none "key") keyQuery)] do
    let parsed ← expectOk source (Advanced.parseExpression source)
    SQLean.Tests.assert (decide (parsed = expected)) s!"unreserved identifier AST changed: {source}"
  for (source, expected) in [
      ("SELECT key FROM key", keyQuery),
      ("SELECT key.* FROM key", {body := .select {
        items := [.all (some "key")], source := some (.table "key")}})] do
    let parsed ← expectOk source (Advanced.parseQuery source)
    SQLean.Tests.assert (decide (parsed = expected)) s!"unreserved query AST changed: {source}"
  for source in ["SELECT FROM t", "SELECT key FROM WHERE", "SELECT left FROM t", "SELECT cross FROM t"] do
    expectError source (Advanced.parseQuery source)
  expectError "SQLite KEY boundary" (Advanced.parseSQLiteQuery "SELECT key FROM t")
  pure (3 * (special.length + contextValues.length) + predicates.length + quoted.length + rows.length + 22)

end SQLean.Tests
