import SQLean.Assurance
import SQLean.SchemaJson
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

/-! Fixed COLLATE corpus certificates. Downloaded queries and source DDL are
never executed. Source eligibility and exact ordered output metadata are
registered independently of checker outcomes; the two environment origins
remain distinct. -/
namespace SQLean.Tests
open SelectContract

private def collationField (record : Lean.Json) (field : String) : IO String :=
  expectOk field ((record.getObjVal? field) >>= Lean.Json.getStr?)

private def collationJsonArray (path : String) : IO (Array Lean.Json) := do
  expectOk path ((Lean.Json.parse (← IO.FS.readFile path)) >>= Lean.Json.getArr?)

private def collationType (label : String) : IO ScalarType := do
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
    | none => throw (IO.userError s!"unregistered collation output type {other}")

private def collationIdentity (label : String) : IO CollationId := do
  match label with
  | "default" => pure .databaseDefault
  | "C" => pure .c
  | "POSIX" => pure .posix
  | other =>
    if other.startsWith "custom:" && !(other.drop 7).isEmpty then
      pure (.custom (other.drop 7).toString)
    else throw (IO.userError s!"unregistered collation identity {other}")

private def collationExpected (record : Lean.Json) : IO (List OutputColumn) := do
  let columns ← expectOk "collation output columns"
    ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
  columns.toList.mapM fun column => do
    let name ← collationField column "name"
    let type ← collationType (← collationField column "type")
    let nullable ← expectOk name ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
    let raw ← expectOk name (column.getObjVal? "collation")
    let collation ← match raw with
      | .null => pure none
      | value => pure (some (← collationIdentity (← expectOk name value.getStr?)))
    pure ⟨name, ⟨type, nullable⟩, collation⟩

private def collationEnvironment (path : String) : IO (Profile × Advanced.Catalog) := do
  let text ← IO.FS.readFile path
  let catalog ← expectOk path (Advanced.decodeCatalogJson text)
  let collations ← expectOk path (Advanced.decodeCollationEnvJson text)
  pure (Profile.basicV32.withCollations collations, catalog)

private def collationCertificate (id : String) (profile : Profile) (catalog : Advanced.Catalog)
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
    SQLean.Tests.assert (checked.output == expected) s!"{id}: rendered exact collation output"
    let again ← expectOk id ((RenderContract.check rendering parsed).mapError reprStr)
    SQLean.Tests.assert (again.sql == rendered.sql) s!"{id}: canonical rendering stability"

def collationCorpusTests : IO Nat := do
  let records ← collationJsonArray "fixtures/collations/synthetic.json"
  let (profile, catalog) ← collationEnvironment "fixtures/collations/schema.json"
  SQLean.Tests.assert (records.size == 50) "fifty authored COLLATE queries"
  let mut ids : List String := []
  let mut sqls : List String := []
  for record in records do
    let id ← collationField record "id"
    let sql ← collationField record "sql"
    SQLean.Tests.assert ((← collationField record "source_kind") == "synthetic" &&
      (← collationField record "catalogFile") == "fixtures/collations/schema.json")
      s!"{id}: authored environment identity"
    let params ← expectOk id (Assurance.parseContractParameterTypes
      (← collationField record "parameter_types"))
    let query ← expectOk id (Advanced.parseQuery sql)
    collationCertificate id profile catalog params query (← collationExpected record)
    ids := id :: ids
    sqls := sql :: sqls
  SQLean.Tests.assert (decide ids.Nodup && decide sqls.Nodup) "distinct authored collation population"
  pure records.size

private def collationSourceId (file : String) (statement : Nat) : String :=
  s!"collations:postgres:src/test/regress/sql/{file}:statement-{statement}"

private def icuId := collationSourceId "collate.icu.utf8.sql"
private def linuxId := collationSourceId "collate.linux.utf8.sql"
private def portableId := collationSourceId "collate.sql"

private def booleanColumn (name : String := "?column?") : OutputColumn :=
  ⟨name, ⟨.bool, false⟩, none⟩

private def integerColumn (name : String := "a") : OutputColumn :=
  ⟨name, ⟨.int32, true⟩, none⟩

private def textColumn (name : String) (nullable : Bool)
    (collation : CollationId := .databaseDefault) : OutputColumn :=
  ⟨name, ⟨.text, nullable⟩, some collation⟩

private def caseSensitive : CollationId :=
  .custom "collations:postgres:src/test/regress/sql/collate.icu.utf8.sql:context-statement-246"

private def observedEnglish : CollationId :=
  .custom "fixture-observed:pg_catalog:en-x-icu:all-encodings"

private def observedSwedish : CollationId :=
  .custom "fixture-observed:pg_catalog:sv-x-icu:all-encodings"

/-- Declared before checker execution, directly from the inspected SQL/DDL.
These are the 18 cases that do not need an imported-locale observation. -/
private def declaredSourceRegistry : List (String × List OutputColumn) :=
  [(icuId 215, [booleanColumn, booleanColumn]),
   (icuId 248, [booleanColumn, booleanColumn]),
   (icuId 249, [booleanColumn, booleanColumn]),
   (icuId 251, [booleanColumn]),
   (icuId 253, [booleanColumn]),
   (icuId 377, [booleanColumn]),
   (icuId 378, [booleanColumn]),
   (portableId 25, [booleanColumn "true"]),
   (portableId 26, [booleanColumn "false"]),
   (icuId 229, [textColumn "a" true]),
   (icuId 238, [integerColumn, textColumn "b" true]),
   (icuId 239, [integerColumn, textColumn "b" true]),
   (icuId 244, [integerColumn, ⟨"b", ⟨.array .text, true⟩, some .databaseDefault⟩]),
   (icuId 245, [integerColumn, ⟨"b", ⟨.array .text, true⟩, some .databaseDefault⟩]),
   (icuId 282, [textColumn "x" true caseSensitive, textColumn "x" true caseSensitive]),
   (icuId 284, [textColumn "x" true caseSensitive]),
   (icuId 286, [textColumn "x" true caseSensitive, textColumn "x" true caseSensitive]),
   (portableId 8, [integerColumn, textColumn "b" false .c])]

/-- Additional fixed metadata under the separately observed fixture catalog.
Native OIDs/provider/encoding are provenance of the asserted environment,
not inferred from successful checks or from regression expected values. -/
private def observedSourceRegistry : List (String × List OutputColumn) :=
  [(icuId 36, [booleanColumn "true"]),
   (icuId 37, [booleanColumn "false"]),
   (icuId 49, [booleanColumn "true"]),
   (icuId 50, [booleanColumn "false"]),
   (icuId 51, [booleanColumn "false"]),
   (icuId 52, [booleanColumn "true"]),
   (icuId 63, [booleanColumn "true"]),
   (icuId 64, [booleanColumn "true"]),
   (icuId 65, [booleanColumn "false"]),
   (icuId 66, [booleanColumn "false"]),
   (icuId 208, [booleanColumn, booleanColumn]),
   (icuId 212, [booleanColumn, booleanColumn]),
   (icuId 217, [booleanColumn, booleanColumn]),
   (icuId 221, [booleanColumn, booleanColumn]),
   (icuId 224, [booleanColumn, booleanColumn]),
   (linuxId 36, [booleanColumn "true"]),
   (linuxId 37, [booleanColumn "false"]),
   (linuxId 49, [booleanColumn "true"]),
   (linuxId 50, [booleanColumn "false"]),
   (linuxId 51, [booleanColumn "false"]),
   (linuxId 52, [booleanColumn "true"]),
   (linuxId 63, [booleanColumn "true"]),
   (linuxId 64, [booleanColumn "false"]),
   (linuxId 65, [booleanColumn "false"]),
   (linuxId 66, [booleanColumn "true"]),
   (icuId 17, [integerColumn, textColumn "b" false observedEnglish]),
   (icuId 18, [integerColumn, textColumn "b" false observedEnglish]),
   (icuId 19, [integerColumn, textColumn "b" false observedEnglish]),
   (icuId 32, [integerColumn, textColumn "b" false observedEnglish]),
   (icuId 203, [integerColumn, textColumn "b" true observedSwedish]),
   (icuId 204, [integerColumn, textColumn "b" true observedSwedish]),
   (icuId 228, [textColumn "a" true])]

private def checkedSourceRegistries : IO (List (String × String × List OutputColumn)) := do
  let declared ← collationJsonArray "fixtures/collations/source_contracts.json"
  let observed ← collationJsonArray "fixtures/collations/source_observed_contracts.json"
  SQLean.Tests.assert (declared.size == 50 && observed.size == 32)
    "complete declaration baseline and additional observed population"
  let mut metadata : List (String × List OutputColumn) := []
  let mut deferred : List String := []
  let mut result : List (String × String × List OutputColumn) := []
  for record in declared do
    let id ← collationField record "id"
    match ← collationField record "status" with
    | "valid" =>
      SQLean.Tests.assert ((← collationField record "eligibility") == "checker") s!"{id}: checker eligibility"
      let expected ← collationExpected record
      let path ← collationField record "catalogFile"
      let wanted := if id == portableId 25 || id == portableId 26 then "source_builtin.json"
        else if id == portableId 8 then "source_portable_declarations.json" else "source_icu_declarations.json"
      SQLean.Tests.assert (path == "fixtures/collations/" ++ wanted) s!"{id}: declaration environment"
      metadata := metadata ++ [(id, expected)]
      result := result ++ [(id, path, expected)]
    | "deferred" =>
      SQLean.Tests.assert ((← collationField record "eligibility") == "catalog_prerequisite" &&
        (← collationField record "diagnostic") == "source.collation_snapshot_unresolved")
        s!"{id}: source prerequisite is not a checker Unsupported outcome"
      for field in ["output_columns", "catalogFile"] do
        match ← expectOk field (record.getObjVal? field) with
        | .null => pure ()
        | _ => throw (IO.userError s!"{id}: missing source facts must stay null")
      deferred := deferred ++ [id]
    | other => throw (IO.userError s!"{id}: unknown baseline status {other}")
  SQLean.Tests.assert (metadata == declaredSourceRegistry && deferred == observedSourceRegistry.map Prod.fst)
    "independently preregistered 18/28 metadata and 32 prerequisite identities"
  let mut observedMetadata : List (String × List OutputColumn) := []
  for record in observed do
    let id ← collationField record "id"
    let path ← collationField record "catalogFile"
    SQLean.Tests.assert ((← collationField record "status") == "valid" &&
      (← collationField record "eligibility") == "checker" &&
      path == "fixtures/collations/source_observed_catalog.json") s!"{id}: observed environment"
    let expected ← collationExpected record
    observedMetadata := observedMetadata ++ [(id, expected)]
    result := result ++ [(id, path, expected)]
  SQLean.Tests.assert (observedMetadata == observedSourceRegistry && result.length == 50 &&
    decide (result.map (fun row => row.1)).Nodup &&
    (declaredSourceRegistry.map (fun row => row.2.length)).sum == 28 &&
    (observedSourceRegistry.map (fun row => row.2.length)).sum == 43)
    "all 50 fixed source identities and 71 ordered output positions"
  pure result

def collationConcreteContractTests : IO Nat := do
  let registry ← checkedSourceRegistries
  let text ← IO.FS.readFile "fixtures/collations/concrete.jsonl"
  let lines := (text.splitOn "\n").filter (fun line => !line.trimAscii.toString.isEmpty)
  SQLean.Tests.assert (lines.length == 50) "fifty unchanged COLLATE source statements"
  let mut ids : List String := []
  let mut sqls : List String := []
  for line in lines do
    let record ← expectOk "collation concrete record" (Lean.Json.parse line)
    let id ← collationField record "id"
    let sql ← collationField record "sql"
    SQLean.Tests.assert (sql == (← collationField record "raw_sql")) s!"{id}: exact original SQL"
    let transformations ← expectOk id ((record.getObjVal? "transformations") >>= Lean.Json.getArr?)
    SQLean.Tests.assert transformations.isEmpty s!"{id}: no source rewrites"
    match ← expectOk id (record.getObjVal? "parameter_types") with
    | .null => pure ()
    | _ => throw (IO.userError s!"{id}: no invented source bindings")
    let some (_, path, expected) := registry.find? (fun row => row.1 == id)
      | throw (IO.userError s!"unregistered COLLATE source {id}")
    let query ← expectOk id (Advanced.parseQuery sql)
    SQLean.Tests.assert (Advanced.queryParameters 1024 query).isEmpty s!"{id}: no source parameter occurrences"
    let (profile, catalog) ← collationEnvironment path
    collationCertificate id profile catalog [] query expected
    ids := id :: ids
    sqls := sql :: sqls
  SQLean.Tests.assert (decide ids.Nodup && decide sqls.Nodup &&
    (registry.map (fun row => row.1)).all ids.contains) "exact source coverage without skips"
  pure lines.length

end SQLean.Tests
