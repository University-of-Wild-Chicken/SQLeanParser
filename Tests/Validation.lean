import SQLean
import SQLean.SchemaJson
import Tests.Corpus

namespace SQLean.Tests

private def validSources : List (String × List SqlType) := [
  ("SELECT id, name FROM users", [.int, .text]),
  ("SELECT id + age, id - age, id * age, id / age FROM users", [.int, .int, .int, .int]),
  ("SELECT id = age, id <> age, id < age, id <= age, id > age, id >= age FROM users",
    [.bool, .bool, .bool, .bool, .bool, .bool]),
  ("SELECT name = city, name <> city FROM users", [.bool, .bool]),
  ("SELECT (id = age) = (name = city) FROM users", [.bool]),
  ("SELECT id FROM users WHERE id > 0 AND age < 100 OR name = 'Alice'", [.int]),
  ("SELECT 'literal', 42 FROM users WHERE 1 = 1", [.text, .int]),
  -- This deliberately records the boundary: typing does not prove division safety.
  ("SELECT 1 / 0 FROM users", [.int])
]

private def invalidSources : List String := [
  "SELECT id FROM missing",
  "SELECT missing FROM users",
  "SELECT id FROM users WHERE missing = 1",
  "SELECT id FROM users WHERE age",
  "SELECT id FROM users WHERE 'text'",
  "SELECT id + name FROM users",
  "SELECT name - id FROM users",
  "SELECT name * city FROM users",
  "SELECT name / 2 FROM users",
  "SELECT id = name FROM users",
  "SELECT id <> city FROM users",
  "SELECT name < city FROM users",
  "SELECT name <= city FROM users",
  "SELECT name > city FROM users",
  "SELECT name >= city FROM users",
  "SELECT id AND age FROM users",
  "SELECT id OR age FROM users",
  "SELECT (id = age) + 1 FROM users",
  "SELECT (id = age) < (name = city) FROM users",
  "SELECT id FROM \"USERS\""
]

private def invalidSchemas : List Schema := [
  [⟨"", [⟨"id", .int⟩]⟩],
  [⟨"users", []⟩],
  [⟨"users", [⟨"", .int⟩]⟩],
  [⟨"users", [⟨"id", .int⟩, ⟨"id", .text⟩]⟩],
  [⟨"users", [⟨"id", .int⟩]⟩, ⟨"users", [⟨"name", .text⟩]⟩]
]

def validationTests : IO Nat := do
  for (source, types) in validSources do
    let checked ← expectOk source (parseAndValidate corpusSchema source)
    SQLean.Tests.assert (checked.certificate.outputTypes == types) s!"wrong output types: {source}"
    let typesOnly ← expectOk source (checkQuery corpusSchema checked.query)
    SQLean.Tests.assert (typesOnly == types) s!"checkQuery differs: {source}"
  for source in invalidSources do
    let query ← expectOk s!"invalid typing but valid syntax: {source}" (parseQuery source)
    expectError source (certifyQuery corpusSchema query)
  for schema in invalidSchemas do
    expectError "invalid schema" (checkSchema schema)
    expectError "certification rejects invalid schema" (certifyQuery schema ⟨"users", [.column "id"], none⟩)
  expectError "empty projection in manual AST" (certifyQuery corpusSchema ⟨"users", [], none⟩)
  expectError "empty schema has no tables" (parseAndValidate [] "SELECT 1 FROM users")
  let boolSchema : Schema := [⟨"flags", [⟨"enabled", .bool⟩]⟩]
  let boolQuery ← expectOk "bool column" (parseAndValidate boolSchema
    "SELECT enabled, enabled AND enabled FROM flags WHERE enabled")
  SQLean.Tests.assert (boolQuery.certificate.outputTypes == [.bool, .bool]) "boolean columns not inferred"
  match parseAndValidate corpusSchema "SELECT * FROM users" with
  | .error (.parse _) => pure ()
  | _ => throw (IO.userError "parseAndValidate did not preserve syntax error category")
  match parseAndValidate corpusSchema "SELECT missing FROM users" with
  | .error (.validation _) => pure ()
  | _ => throw (IO.userError "parseAndValidate did not preserve validation error category")
  let schemaText ← IO.FS.readFile "fixtures/schema.json"
  let decoded ← expectOk "schema JSON" (parseSchemaJson schemaText)
  SQLean.Tests.assert (decoded == corpusSchema) "JSON fixture differs from Lean corpus schema"
  for source in ["{", "[]", "{}", "{\"tables\": 1}",
    "{\"tables\":[{\"name\":\"t\",\"columns\":[]}]}",
    "{\"tables\":[{\"name\":\"t\",\"columns\":[{\"name\":\"c\",\"type\":\"float\"}]}]}"] do
    expectError "bad schema JSON" (parseSchemaJson source)
  pure (validSources.length + invalidSources.length + invalidSchemas.length + 12)

end SQLean.Tests
