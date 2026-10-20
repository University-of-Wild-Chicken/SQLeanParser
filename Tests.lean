import Tests.Parsing
import Tests.Validation
import Tests.Corpus
import Tests.Proofs
import Tests.CrudParsing
import Tests.CrudValidation
import Tests.CrudCorpus
import Tests.CrudAPI
import Tests.RelationalParsing
import Tests.RelationalValidation
import Tests.NestedValidation
import Tests.RelationalCorpus
import Tests.IndustrialParsing
import Tests.IndustrialValidation
import Tests.IndustrialCorpus
import Tests.IndustrialAPI
import Tests.PostgresParsing
import Tests.PostgresValidation
import Tests.PostgresReturning
import Tests.PostgresCorpus
import Tests.AdvancedParsing
import Tests.AdvancedValidation
import Tests.AdvancedStatements
import Tests.AdvancedCorpus
import Tests.SelectContract
import Tests.SelectContractTrust
import Tests.ScopeContract
import Tests.ScopeContractTrust
import Tests.RenderContract
import Tests.DialectRendering

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
  let relationalParsing ← relationalParsingTests
  IO.println s!"PASS: {relationalParsing} relational parser and round-trip cases"
  let relationalValidation ← relationalValidationTests
  IO.println s!"PASS: {relationalValidation} join/group/type validity cases"
  let nested ← nestedValidationTests
  IO.println s!"PASS: {nested} nested query scope and certificate cases"
  let relationalCorpus ← relationalCorpusTests
  IO.println s!"PASS: {relationalCorpus} relational examples (50 per query class) certified and round-tripped"
  let industrialParsing ← industrialParsingTests
  IO.println s!"PASS: {industrialParsing} recursive CTE, UNION, and source-free parsing cases"
  let industrialValidation ← industrialValidationTests
  IO.println s!"PASS: {industrialValidation} recursive scope, compound type, and certificate cases"
  let industrialCorpus ← industrialCorpusTests
  IO.println s!"PASS: {industrialCorpus} industrial examples (50 per query class) certified and round-tripped"
  let industrialAPI ← industrialAPITests
  IO.println s!"PASS: {industrialAPI} industrial public API cases"
  let postgresParsing ← postgresParsingTests
  IO.println s!"PASS: {postgresParsing} PostgreSQL syntax, precedence, and AST round-trip checks"
  let postgresValidation ← postgresValidationTests
  IO.println s!"PASS: {postgresValidation} PostgreSQL type, grouping, and option validity checks"
  let postgresReturning ← postgresReturningTests
  IO.println s!"PASS: {postgresReturning} RETURNING mutation, projection, and API checks"
  let postgresCorpus ← postgresCorpusTests
  IO.println s!"PASS: {postgresCorpus} PostgreSQL examples (50 per feature class) certified and round-tripped"
  let advancedParsing ← advancedParsingTests
  IO.println s!"PASS: {advancedParsing} advanced parser, parameter identity, and round-trip checks"
  let advancedValidation ← advancedValidationTests
  IO.println s!"PASS: {advancedValidation} advanced query scope, type, and parameter checks"
  let advancedStatements ← advancedStatementTests
  IO.println s!"PASS: {advancedStatements} advanced mutation, DDL, catalog, and API checks"
  let advancedCorpus ← advancedCorpusTests
  IO.println s!"PASS: {advancedCorpus} advanced examples (50 per query class) certified and round-tripped"
  let contract ← selectContractTests
  IO.println s!"PASS: {contract} independent SELECT contract and assurance API checks"
  let render ← renderContractTests
  IO.println s!"PASS: {render} SELECT rendering, exact round-trip, binding-map, and corpus checks"
  let dialect ← dialectRenderingTests
  IO.println s!"PASS: {dialect} SQLite and PostgreSQL dialect rendering checks"
  ScopeContract.run
  IO.println "All tests passed. Lean proof examples compiled successfully."

end SQLean.Tests
