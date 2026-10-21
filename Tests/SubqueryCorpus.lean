import SQLean.Assurance
import SQLean.SchemaJson
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

/-! Fixed expression-subquery corpus certificates. Downloaded queries and source DDL are
never executed. Source eligibility and exact ordered output metadata are
registered independently of checker outcomes; the two environment origins
remain distinct. -/
namespace SQLean.Tests
open SelectContract

private def subqueryField (record : Lean.Json) (field : String) : IO String :=
  expectOk field ((record.getObjVal? field) >>= Lean.Json.getStr?)

private def subqueryJsonArray (path : String) : IO (Array Lean.Json) := do
  expectOk path ((Lean.Json.parse (← IO.FS.readFile path)) >>= Lean.Json.getArr?)

private def subqueryType (label : String) : IO ScalarType := do
  match label with
  | "int32" => pure .int32
  | "int64" => pure .int64
  | "bool" => pure .bool
  | "bpchar" => pure (.char [])
  | other =>
    let spelling := if other.startsWith "bpchar(" then other.replace "bpchar" "CHAR" else other
    let declaration ← expectOk spelling (Advanced.parseDataType spelling)
    match concreteType declaration with
    | some type => pure type
    | none => throw (IO.userError s!"unregistered subquery output type {other}")

private def subqueryIdentity (label : String) : IO CollationId := do
  match label with
  | "default" => pure .databaseDefault
  | "C" => pure .c
  | "POSIX" => pure .posix
  | other =>
    if other.startsWith "custom:" && !(other.drop 7).isEmpty then
      pure (.custom (other.drop 7).toString)
    else throw (IO.userError s!"unregistered collation identity {other}")

private def subqueryExpected (record : Lean.Json) : IO (List OutputColumn) := do
  let columns ← expectOk "subquery output columns"
    ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
  columns.toList.mapM fun column => do
    let name ← subqueryField column "name"
    let type ← subqueryType (← subqueryField column "type")
    let nullable ← expectOk name ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
    let raw ← expectOk name (column.getObjVal? "collation")
    let collation ← match raw with
      | .null => pure none
      | value => pure (some (← subqueryIdentity (← expectOk name value.getStr?)))
    pure ⟨name, ⟨type, nullable⟩, collation⟩

private def subqueryEnvironment (path : String) : IO (Profile × Advanced.Catalog) := do
  let text ← IO.FS.readFile path
  let catalog ← expectOk path (Advanced.decodeCatalogJson text)
  let collations ← expectOk path (Advanced.decodeCollationEnvJson text)
  pure (Profile.basicV33.withCollations collations, catalog)

private def subqueryCertificate (id : String) (profile : Profile) (catalog : Advanced.Catalog)
    (params : ParameterEnv) (query : Advanced.Query) (expected : List OutputColumn) : IO Unit := do
  let certificate ← expectOk id
    ((SelectContract.checkQuery profile catalog params query).mapError reprStr)
  SQLean.Tests.assert (certificate.output == expected)
    s!"{id}: exact output types/nullability/identities {reprStr certificate.output}"
  have _catalog := certificate.catalog_unchanged
  have _transport := RenderContract.translateParameters_valid certificate.valid
  for rendering in [RenderContract.Profile.identityV01, .postgres16V01] do
    let rendered ← expectOk id ((RenderContract.check rendering query).mapError reprStr)
    have _roundTrip := rendered.roundTrip
    have _canonical := rendered.canonical
    let parsed ← expectOk id (RenderContract.parseRendered rendering rendered.sql)
    let checked ← expectOk id
      ((SelectContract.checkQuery profile catalog params parsed).mapError reprStr)
    SQLean.Tests.assert (checked.output == expected) s!"{id}: rendered exact output metadata"
    let again ← expectOk id ((RenderContract.check rendering parsed).mapError reprStr)
    SQLean.Tests.assert (again.sql == rendered.sql) s!"{id}: canonical rendering stability"

def subqueryCorpusTests : IO Nat := do
  let records ← subqueryJsonArray "fixtures/subqueries/synthetic.json"
  let (profile, catalog) ← subqueryEnvironment "fixtures/subqueries/schema.json"
  SQLean.Tests.assert (records.size == 150) "150 authored expression subqueries"
  let mut ids : List String := []
  let mut sqls : List String := []
  let mut factors : List String := []
  for record in records do
    let id ← subqueryField record "id"
    let sql ← subqueryField record "sql"
    SQLean.Tests.assert ((← subqueryField record "source_kind") == "synthetic" &&
      (← subqueryField record "catalogFile") == "fixtures/subqueries/schema.json")
      s!"{id}: authored environment identity"
    let params ← expectOk id (Assurance.parseContractParameterTypes
      (← subqueryField record "parameter_types"))
    let query ← expectOk id (Advanced.parseQuery sql)
    subqueryCertificate id profile catalog params query (← subqueryExpected record)
    ids := id :: ids
    sqls := sql :: sqls
    factors := (← subqueryField record "factor") :: factors
  SQLean.Tests.assert (decide ids.Nodup && decide sqls.Nodup) "distinct authored subqueries"
  for factor in ["scalar_subquery", "exists_subquery", "in_subquery"] do
    SQLean.Tests.assert ((factors.filter (· == factor)).length == 50) s!"fifty {factor} examples"
  pure records.size

def subquerySourceCorpusTests : IO Nat := do
  let registry ← expectOk "subquery source registry"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/subqueries/source_contracts.json"))
  let mut allIds : List String := []
  let mut registeredIds : List String := []
  let mut certified := 0
  let mut outputPositions := 0
  for factor in ["scalar", "exists", "in"] do
    let contracts ← expectOk factor ((registry.getObjVal? factor) >>= Lean.Json.getArr?)
    let lines := (← IO.FS.readFile s!"fixtures/subqueries/{factor}_concrete.jsonl").splitOn "\n"
    let mut records : List Lean.Json := []
    for line in lines do
      if !line.trimAscii.toString.isEmpty then
        records := (← expectOk factor (Lean.Json.parse line)) :: records
    SQLean.Tests.assert (records.length == 50) s!"fifty unchanged source {factor} examples"
    for record in records do
      let id ← subqueryField record "id"
      let sql ← subqueryField record "sql"
      SQLean.Tests.assert ((← subqueryField record "factor") == factor &&
        sql == (← subqueryField record "raw_sql")) s!"{id}: unchanged source and factor"
      allIds := id :: allIds
      let query ← expectOk id (Advanced.parseQuery sql)
      for rendering in [RenderContract.Profile.identityV01, .postgres16V01] do
        let rendered ← expectOk id ((RenderContract.check rendering query).mapError reprStr)
        have _roundTrip := rendered.roundTrip
        have _canonical := rendered.canonical
        let parsed ← expectOk id (RenderContract.parseRendered rendering rendered.sql)
        let again ← expectOk id ((RenderContract.check rendering parsed).mapError reprStr)
        SQLean.Tests.assert (again.sql == rendered.sql) s!"{id}: source rendering canonicality"
    for contract in contracts do
      let id ← subqueryField contract "id"
      let some record := records.find? (fun record =>
        (record.getObjVal? "id" >>= Lean.Json.getStr?).toOption == some id)
        | throw (IO.userError s!"{id}: registered source missing")
      let (profile, catalog) ← match ← expectOk id (contract.getObjVal? "catalogFile") with
        | .null => pure (Profile.basicV33, [])
        | value => subqueryEnvironment (← expectOk id value.getStr?)
      let query ← expectOk id (Advanced.parseQuery (← subqueryField record "sql"))
      let expected ← subqueryExpected contract
      subqueryCertificate id profile catalog [] query expected
      registeredIds := id :: registeredIds
      certified := certified + 1
      outputPositions := outputPositions + expected.length
  SQLean.Tests.assert (allIds.length == 150 && decide allIds.Nodup)
    "distinct complete source subquery population"
  SQLean.Tests.assert (certified == 78 && outputPositions == 84 && decide registeredIds.Nodup)
    "fixed independently reviewed source contract population"
  pure certified

end SQLean.Tests
