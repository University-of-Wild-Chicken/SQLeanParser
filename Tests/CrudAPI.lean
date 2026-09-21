import SQLean
import Tests.CrudCorpus

namespace SQLean.Tests

/-- End-to-end API behavior, including the two distinct failure categories. -/
def crudAPITests : IO Nat := do
  for (source, outputTypes) in [
    ("SELECT * FROM flags ORDER BY id", [SqlType.int, .bool, .text]),
    ("INSERT INTO flags VALUES (1, TRUE, 'live')", []),
    ("UPDATE flags SET enabled = NOT enabled WHERE id = 1", []),
    ("DELETE FROM flags WHERE NOT enabled", [])] do
    let checked ← expectOk source (parseAndValidateStatement crudCorpusSchema source)
    SQLean.Tests.assert (checked.certificate.outputTypes == outputTypes)
      s!"unexpected end-to-end output types: {source}"
    let reparsed ← expectOk "public AST rendering" (parseStatement (toSql checked.statement))
    SQLean.Tests.assert (reparsed == checked.statement) "checked AST round trip differs"
  match parseAndValidateStatement crudCorpusSchema "UPDATE users SET age =" with
  | .error (.parse _) => pure ()
  | _ => throw (IO.userError "CRUD API lost parse-error category")
  match parseAndValidateStatement crudCorpusSchema "UPDATE users SET age = 'old'" with
  | .error (.validation _) => pure ()
  | _ => throw (IO.userError "CRUD API lost validation-error category")
  expectError "old API remains strict SELECT" (parseAndValidate crudCorpusSchema
    "UPDATE users SET age = 1")
  pure 7

example (schema : Schema) (checked : CheckedStatement schema) :
    ValidStatement schema checked.statement checked.certificate.outputTypes :=
  checked.certificate.valid

end SQLean.Tests
