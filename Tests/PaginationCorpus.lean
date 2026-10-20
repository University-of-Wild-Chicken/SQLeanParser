import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

/-! The synthetic population has a declared catalog and exact parameter types,
so every record receives a complete independent basic SELECT certificate.

The collected application/compiler queries have no production catalog here.
For those records, INT32 declarations for referenced parameter indices are
explicit test assumptions, and only the outer pagination expressions receive
validity evidence. This does not certify the body, infer production parameter
types, or establish runtime nonnegativity. Both populations receive checked
identity and PostgreSQL rendering certificates. -/
namespace SQLean.Tests

private def paginationCatalog : Advanced.Catalog := [{
  name := "page_rows"
  columns := [{ name := "id", type := ⟨.int, []⟩, nullable := some false }]
}]

private def stringField (label : String) (record : Lean.Json) (field : String) : IO String :=
  expectOk s!"{label}: {field}" ((record.getObjVal? field) >>= Lean.Json.getStr?)

private def renderPagination (label : String) (query : Advanced.Query) :
    IO (RenderContract.Certificate .identityV01 query ×
      RenderContract.Certificate .postgres16V01 query) := do
  let identity ← expectOk s!"{label}: identity renderer certificate"
    ((RenderContract.check .identityV01 query).mapError reprStr)
  let postgres ← expectOk s!"{label}: PostgreSQL renderer certificate"
    ((RenderContract.check .postgres16V01 query).mapError reprStr)
  -- These propositions concern the exact original AST and its explicit
  -- translation, rather than Boolean AST comparisons or unchecked SQL text.
  have _identityRoundTrip : Advanced.parseQuery identity.sql = .ok query :=
    identity.roundTrip
  have _postgresRoundTrip :
      Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
    postgres.roundTrip
  pure (identity, postgres)

private def checkSyntheticPagination (record : Lean.Json) : IO (String × String) := do
  let label ← stringField "synthetic pagination record" record "id"
  let sourceKind ← stringField label record "source_kind"
  SQLean.Tests.assert (sourceKind == "synthetic") s!"{label}: incorrect population classification"
  let sql ← stringField label record "sql"
  let parameterTypes ← stringField label record "parameter_types"
  let params ← expectOk s!"{label}: exact parameter declarations"
    (Assurance.parseContractParameterTypes parameterTypes)
  let query ← expectOk s!"{label}: parse" (Advanced.parseQuery sql)
  SQLean.Tests.assert (query.limit.isSome || query.offset.isSome)
    s!"{label}: no outer pagination clause"
  let certificate ← expectOk s!"{label}: complete SELECT validity"
    ((SelectContract.checkQuery .basicV09 paginationCatalog params query).mapError reprStr)
  have _completeDerivation :
      SelectContract.SelectValid .basicV09 paginationCatalog params query certificate.output :=
    certificate.valid
  have _translatedDerivation :
      SelectContract.SelectValid .basicV09 paginationCatalog params
        (RenderContract.translateParameters query) certificate.output :=
    RenderContract.translateParameters_valid certificate.valid
  SQLean.Tests.assert (certificate.output == [⟨"id", ⟨.int32, false⟩⟩])
    s!"{label}: unexpected ordered output schema"
  SQLean.Tests.assert (certificate.outputCatalog == paginationCatalog)
    s!"{label}: SELECT changed the catalog"
  let _ ← renderPagination label query
  pure (label, sql)

private def checkConcretePagination (record : Lean.Json) : IO (String × String) := do
  let label ← stringField "concrete pagination record" record "id"
  let sourceKind ← stringField label record "source_kind"
  SQLean.Tests.assert
    (sourceKind == "application-constant" || sourceKind == "compiler-regression")
    s!"{label}: incorrect concrete population classification"
  let sql ← stringField label record "sql"
  let original ← stringField label record "raw_sql"
  let transformations ← expectOk s!"{label}: transformations"
    ((record.getObjVal? "transformations") >>= Lean.Json.getArr?)
  SQLean.Tests.assert (sql == original && transformations.isEmpty)
    s!"{label}: concrete source SQL was transformed"
  let query ← expectOk s!"{label}: parse" (Advanced.parseQuery sql)
  SQLean.Tests.assert (query.limit.isSome || query.offset.isSome)
    s!"{label}: no outer pagination clause"
  let (identity, _postgres) ← renderPagination label query
  -- The total renderer inspection supplies all referenced indices. These
  -- declarations are test assumptions, not inferred production type metadata.
  let indices := (identity.footprint.parameters.map SelectContract.parameterIndex).eraseDups
  let assumedParams : SelectContract.ParameterEnv :=
    indices.map (fun index => ⟨index, ⟨.int, []⟩, false⟩)
  let certificate ← expectOk s!"{label}: pagination-only validity under test INT32 assumptions"
    ((SelectContract.checkPaginationBounds .basicV09 assumedParams query).mapError reprStr)
  have _boundsDerivation :
      SelectContract.PaginationBoundsValid .basicV09 assumedParams query
        certificate.limitUses certificate.offsetUses := certificate.valid
  have _translatedBounds :
      SelectContract.PaginationBoundsValid .basicV09 assumedParams
        (RenderContract.translateParameters query)
        (certificate.limitUses.map RenderContract.translateParameter)
        (certificate.offsetUses.map RenderContract.translateParameter) :=
    RenderContract.pagination_bounds_valid_translated certificate.valid
  SQLean.Tests.assert (!(certificate.limitUses ++ certificate.offsetUses).isEmpty)
    s!"{label}: selected parameterized pagination factor is absent"
  SQLean.Tests.assert
    ((certificate.limitUses ++ certificate.offsetUses).all
      (fun parameter => indices.contains (SelectContract.parameterIndex parameter)))
    s!"{label}: pagination references an undeclared test index"
  pure (label, sql)

/-- Exactly fifty complete synthetic SELECT certificates and fifty collected
pagination-only certificates, with no success-dependent exclusions. Fixture
source hashes and extraction provenance are independently replayed by the
Python extraction tests; this test checks the resulting exact SQL records. -/
def paginationCorpusTests : IO Nat := do
  let syntheticSource ← IO.FS.readFile "fixtures/pagination/synthetic.json"
  let syntheticJson ← expectOk "synthetic pagination JSON" (Lean.Json.parse syntheticSource)
  let synthetic ← expectOk "synthetic pagination array" syntheticJson.getArr?
  SQLean.Tests.assert (synthetic.size == 50) "expected exactly 50 synthetic pagination records"
  let mut observed : List (String × String) := []
  for record in synthetic do
    observed := (← checkSyntheticPagination record) :: observed

  let concreteSource ← IO.FS.readFile "fixtures/pagination/concrete.jsonl"
  let concreteLines := (concreteSource.splitOn "\n").filter
    (fun line => !line.trimAscii.toString.isEmpty)
  SQLean.Tests.assert (concreteLines.length == 50) "expected exactly 50 concrete pagination records"
  for line in concreteLines do
    let record ← expectOk "concrete pagination JSON" (Lean.Json.parse line)
    observed := (← checkConcretePagination record) :: observed

  SQLean.Tests.assert (decide (observed.map Prod.fst).Nodup)
    "duplicate pagination record identities"
  SQLean.Tests.assert (decide (observed.map Prod.snd).Nodup)
    "duplicate pagination SQL records"
  pure observed.length

end SQLean.Tests
