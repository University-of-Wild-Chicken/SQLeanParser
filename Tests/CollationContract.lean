import SQLean.Assurance
import SQLean.SchemaJson
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

namespace SQLean.Tests
open SelectContract

/-- Independent constructors witness explicit annotation and outer override.
These proofs do not invoke the executable checker. -/
private theorem literalC : ExprCollationValid .basicV32 [] .empty
    (.collate (.literal (.text "a")) ["C"])
    (some ⟨.text, false⟩) (.explicit .c) :=
  .collate (.collate .text) (.atom .text .text)
    (entry := ⟨.c, "pg_catalog", "C", none, true, true⟩) rfl rfl

example : ExprCollationValid .basicV32 [] .empty
    (.collate (.collate (.literal (.text "a")) ["C"]) ["POSIX"])
    (some ⟨.text, false⟩) (.explicit .posix) :=
  .collate (.collate (.collate .text)) literalC
    (entry := ⟨.posix, "pg_catalog", "POSIX", none, true, true⟩) rfl rfl

example : CollationDerivation.merge (.implicit .c) (.implicit .posix) =
    some (.conflict .c .posix) := rfl
example : CollationDerivation.merge (.explicit .c) (.explicit .posix) = none := rfl
example : CollationDerivation.merge (.conflict .c .posix) (.explicit .c) =
    some (.explicit .c) := rfl
example : CollationDerivation.stored (CollationDerivation.conflict .c .posix).identity =
    .none := rfl

private def boundaryField (record : Lean.Json) (field : String) : IO String :=
  expectOk field ((record.getObjVal? field) >>= Lean.Json.getStr?)

private def boundaryType (label : String) : IO ScalarType := do
  match label with
  | "int32" => pure .int32
  | "int64" => pure .int64
  | "bool" => pure .bool
  | "bpchar" => pure (.char [])
  | other =>
    let declared ← expectOk other (Advanced.parseDataType other)
    match concreteType declared with
    | some type => pure type
    | none => throw (IO.userError s!"unregistered boundary output type: {other}")

private def boundaryIdentity (value : Lean.Json) : IO (Option CollationId) := do
  match value with
  | .null => pure none
  | value =>
    match ← expectOk "collation identity" value.getStr? with
    | "default" => pure (some .databaseDefault)
    | "C" => pure (some .c)
    | "POSIX" => pure (some .posix)
    | other =>
      if other.startsWith "custom:" && !(other.drop 7).isEmpty then
        pure (some (.custom (other.drop 7).toString))
      else throw (IO.userError s!"unregistered collation identity: {other}")

private def boundaryOutput (record : Lean.Json) : IO (List OutputColumn) := do
  let columns ← expectOk "output_columns" ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
  columns.toList.mapM fun column => do
    let name ← boundaryField column "name"
    let base ← boundaryType (← boundaryField column "type")
    let nullable ← expectOk name ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
    let collation ← boundaryIdentity (← expectOk name (column.getObjVal? "collation"))
    pure ⟨name, ⟨base, nullable⟩, collation⟩

/-- Replay the independently registered native-analysis boundaries and snapshot
controls. The database observations are external evidence; each accepted case
still constructs the independent Lean type and collation judgments. -/
def collationContractTests : IO Nat := do
  let fixture ← expectOk "collation boundaries"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/collations/boundaries.json"))
  let environments ← expectOk "environments" (fixture.getObjVal? "environments")
  let nativeCases ← expectOk "cases" ((fixture.getObjVal? "cases") >>= Lean.Json.getArr?)
  let snapshots ← expectOk "snapshot_cases" ((fixture.getObjVal? "snapshot_cases") >>= Lean.Json.getArr?)
  SQLean.Tests.assert (nativeCases.size == 121 && snapshots.size == 10)
    "registered collation analysis and snapshot populations"
  let mut ids : List String := []
  let mut accepted := 0
  for record in nativeCases ++ snapshots do
    let id ← boundaryField record "id"
    let sql ← boundaryField record "sql"
    let environment ← boundaryField record "environment"
    let context ← expectOk environment (environments.getObjVal? environment)
    let catalog ← expectOk id (Advanced.decodeCatalogJson context.compress)
    let collations ← expectOk id (Advanced.decodeCollationEnvJson context.compress)
    let profile := Profile.basicV32.withCollations collations
    let query ← expectOk id (Advanced.parseQuery sql)
    let status ← boundaryField record "expected_status"
    match SelectContract.checkQuery profile catalog [] query with
    | .ok certificate =>
      SQLean.Tests.assert (status == "valid") s!"{id}: unexpected certificate"
      let expected ← boundaryOutput record
      SQLean.Tests.assert (certificate.output == expected)
        s!"{id}: exact type, nullability and collation: {reprStr certificate.output}"
      have _preserved := RenderContract.translateParameters_valid certificate.valid
      for rendering in [RenderContract.Profile.identityV01, .postgres16V01] do
        let rendered ← expectOk id ((RenderContract.check rendering query).mapError reprStr)
        have _roundTrip := rendered.roundTrip
        let parsed ← expectOk id (RenderContract.parseRendered rendering rendered.sql)
        let checked ← expectOk id ((SelectContract.checkQuery profile catalog [] parsed).mapError reprStr)
        SQLean.Tests.assert (checked.output == expected) s!"{id}: rendered metadata"
      accepted := accepted + 1
    | .error (.invalid diagnostic) =>
      SQLean.Tests.assert (status == "invalid" && diagnostic.code == (← boundaryField record "diagnostic"))
        s!"{id}: invalid diagnostic {reprStr diagnostic}"
    | .error (.unsupported diagnostic) =>
      SQLean.Tests.assert (status == "unsupported" && diagnostic.code == (← boundaryField record "diagnostic"))
        s!"{id}: unsupported diagnostic {reprStr diagnostic}"
    | .error (.inconclusive diagnostic) =>
      throw (IO.userError s!"{id}: unexpected resource boundary {reprStr diagnostic}")
    ids := id :: ids
  SQLean.Tests.assert (decide ids.Nodup && accepted == 77)
    "all 131 collation boundaries, including 77 exact certificates, must be replayed"
  let expression ← expectOk "collation fuel" (Advanced.parseQuery "SELECT 'a' COLLATE \"C\"")
  match SelectContract.checkQuery .basicV32 [] [] expression 1 with
  | .error (.inconclusive _) => pure ()
  | _ => throw (IO.userError "collation fuel exhaustion must remain Inconclusive")
  let malformed := Profile.basicV32.withCollations {entries := []}
  match checkPaginationBounds malformed [] expression with
  | .error (.invalid diagnostic) =>
    SQLean.Tests.assert (diagnostic.code == "invalid_collation_environment")
      "standalone pagination validates its collation environment"
  | _ => throw (IO.userError "standalone pagination accepted an incomplete collation snapshot")
  let diagnosticCases := [
    ("SELECT (SELECT 1)", "subquery"),
    ("SELECT EXISTS (SELECT 1)", "subquery"),
    ("SELECT 1 IN (SELECT 1)", "subquery"),
    ("SELECT COUNT(*)", "aggregate"),
    ("SELECT SUM(1) FILTER (WHERE TRUE)", "aggregate"),
    ("SELECT ROW(1)", "record_value")]
  for (sql, expectedCode) in diagnosticCases do
    let query ← expectOk sql (Advanced.parseQuery sql)
    let expr ← match query.body with
      | .select select => match select.items with
        | [.expression expr _] => pure expr
        | _ => throw (IO.userError s!"expected one diagnostic projection: {sql}")
      | _ => throw (IO.userError s!"expected diagnostic SELECT: {sql}")
    match checkExpr 1024 [] .empty expr,
        SelectContract.checkQuery .basicV32 [] [] query with
    | .error (.unsupported original), .error (.unsupported complete) =>
      SQLean.Tests.assert (original.code == expectedCode && complete == original)
        s!"collation checking must preserve the original unsupported diagnostic: {sql}"
    | _, _ => throw (IO.userError s!"expected unsupported diagnostic parity: {sql}")
  pure (ids.length + 2 + diagnosticCases.length)

end SQLean.Tests
