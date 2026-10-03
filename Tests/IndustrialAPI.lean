import SQLean
import Tests.Support

namespace SQLean.Tests

/-- Exercise the new query classes through both public parse-and-certify APIs. -/
def industrialAPITests : IO Nat := do
  for (source, types, names) in [
    ("SELECT 1 AS n, 'ready' AS status", [SqlType.int, .text], [some "n", some "status"]),
    ("SELECT 1 AS n UNION ALL SELECT 2 ORDER BY n", [.int], [some "n"]),
    ("WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM seq WHERE n < 5) SELECT n FROM seq ORDER BY n",
      [.int], [some "n"])] do
    let checked ← expectOk source (parseAndValidateRelQuery [] source)
    SQLean.Tests.assert (checked.certificate.outputTypes == types)
      s!"unexpected relational API types: {source}"
    SQLean.Tests.assert (checked.certificate.outputNames == names)
      s!"unexpected relational API output names: {source}"
    let statement ← expectOk source (parseAndValidateStatement [] source)
    SQLean.Tests.assert (statement.certificate.outputTypes == types)
      s!"statement API disagrees with relational API: {source}"
    SQLean.Tests.assert (statement.statement == .relational checked.query)
      s!"new syntax did not use the relational AST: {source}"
    let reparsed ← expectOk source (parseAndValidateRelQuery [] (toSql checked.query))
    SQLean.Tests.assert (reparsed.query == checked.query)
      s!"relational API round trip changed AST: {source}"
  match parseAndValidateRelQuery [] "SELECT 1 UNION ALL" with
  | .error (.parse _) => pure ()
  | _ => throw (IO.userError "relational API lost parse-error category")
  match parseAndValidateRelQuery [] "SELECT 1 UNION SELECT 'bad'" with
  | .error (.validation _) => pure ()
  | _ => throw (IO.userError "relational API lost validation-error category")
  match parseAndValidateRelQuery []
      "WITH RECURSIVE seq(n) AS (SELECT 1 UNION ALL SELECT missing FROM seq) SELECT n FROM seq" with
  | .error (.validation _) => pure ()
  | _ => throw (IO.userError "relational API accepted an unbound recursive column")
  expectError "MVP API still requires FROM" (parseAndValidate [] "SELECT 1")
  pure 7

example (schema : Schema) (checked : CheckedRelQuery schema) :
    ValidRelQuery schema checked.query checked.certificate.outputTypes :=
  checked.certificate.valid

example (schema : Schema) (query : RelQuery) (types : List SqlType) :
    checkRelQuery schema query = .ok types ↔ ValidRelQuery schema query types :=
  checkRelQuery_iff

end SQLean.Tests
