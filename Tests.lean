import Tests.Parsing
import Tests.Validation
import Tests.Corpus
import Tests.Proofs
import Tests.CrudParsing
import Tests.CrudValidation
import Tests.CrudCorpus
import Tests.CrudAPI

namespace SQLean.Tests

def run : IO Unit := do
  let parsing ← parsingTests
  IO.println s!"PASS: {parsing} parser acceptance/rejection, AST, round-trip, and position cases"
  let validation ← validationTests
  IO.println s!"PASS: {validation} schema/type/API cases"
  let corpus ← corpusTests
  IO.println s!"PASS: {corpus} distinct generated queries parsed, certified, and round-tripped"
  let crudParsing ← crudParsingTests
  IO.println s!"PASS: {crudParsing} CRUD parser and compatibility cases"
  let crudValidation ← crudValidationTests
  IO.println s!"PASS: {crudValidation} CRUD schema/type and certificate cases"
  let crudAPI ← crudAPITests
  IO.println s!"PASS: {crudAPI} CRUD public API cases"
  let crudCorpus ← crudCorpusTests
  IO.println s!"PASS: {crudCorpus} new CRUD examples (50 per category) parsed, certified, and round-tripped"
  IO.println "All tests passed. Lean proof examples compiled successfully."

end SQLean.Tests
