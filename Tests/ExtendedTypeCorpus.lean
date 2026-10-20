import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

/-! Fifty fixed source-free SELECTs with independently authored concrete type,
modifier, nullability, and parameter declarations. Each obtains a complete
basic SELECT derivation and exact identity/PostgreSQL render certificates.
Runtime values and PostgreSQL's native output types are checked separately by
the native corpus runner; these tests do not imply execution success. -/
namespace SQLean.Tests

private def scalarLabel : SelectContract.ScalarType → String
  | .int32 => "int32"
  | .text => "text"
  | .bool => "bool"
  | type => (type.dataType.toSql.toLower).replace ", " ","

private def field (label : String) (record : Lean.Json) (name : String) : IO String :=
  expectOk s!"{label}: {name}" ((record.getObjVal? name) >>= Lean.Json.getStr?)

def extendedTypeCorpusTests : IO Nat := do
  let source ← IO.FS.readFile "fixtures/extended_types/synthetic.json"
  let json ← expectOk "extended type fixture JSON" (Lean.Json.parse source)
  let records ← expectOk "extended type fixture array" json.getArr?
  SQLean.Tests.assert (records.size == 50) "expected exactly 50 extended scalar examples"
  let mut ids : List String := []
  let mut statements : List String := []
  for record in records do
    let id ← field "extended type record" record "id"
    let kind ← field id record "source_kind"
    SQLean.Tests.assert (kind == "synthetic") s!"{id}: unexpected source population"
    let sql ← field id record "sql"
    let parameterTypes ← field id record "parameter_types"
    let expectedType ← field id record "contract_type"
    let expectedNullable ← expectOk s!"{id}: nullable"
      ((record.getObjVal? "nullable") >>= Lean.Json.getBool?)
    let params ← expectOk s!"{id}: exact declarations"
      (Assurance.parseContractParameterTypes parameterTypes)
    let query ← expectOk s!"{id}: parse" (Advanced.parseQuery sql)
    let certificate ← expectOk s!"{id}: complete SELECT certificate"
      ((SelectContract.checkQuery .basicV22 [] params query).mapError reprStr)
    have _valid : SelectContract.SelectValid .basicV22 [] params query certificate.output :=
      certificate.valid
    have _preserved : SelectContract.SelectValid .basicV22 [] params
        (RenderContract.translateParameters query) certificate.output :=
      RenderContract.translateParameters_valid certificate.valid
    match certificate.output with
    | [column] =>
        SQLean.Tests.assert
          (column.name == "v" && scalarLabel column.type.base == expectedType &&
            column.type.nullable == expectedNullable)
          s!"{id}: incorrect exact output: {reprStr certificate.output}; expected {expectedType}"
    | _ => throw (IO.userError s!"{id}: expected one named scalar output")
    let identity ← expectOk s!"{id}: identity render certificate"
      ((RenderContract.check .identityV01 query).mapError reprStr)
    let postgres ← expectOk s!"{id}: PostgreSQL render certificate"
      ((RenderContract.check .postgres16V01 query).mapError reprStr)
    have _identityRoundTrip : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
    have _postgresRoundTrip :
        Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
      postgres.roundTrip
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (decide ids.Nodup) "duplicate extended type fixture identity"
  SQLean.Tests.assert (decide statements.Nodup) "duplicate extended type SQL fixture"
  pure records.size

end SQLean.Tests
