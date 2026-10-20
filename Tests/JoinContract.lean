import SQLean.Assurance
import SQLean.SchemaJson
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

namespace SQLean.Tests

private def joinCatalog : Advanced.Catalog := [
  { name := "t", columns := [
      { name := "id", type := ⟨.int, []⟩, nullable := some false },
      { name := "label", type := ⟨.text, []⟩, nullable := some true }] },
  { name := "u", columns := [
      { name := "id", type := ⟨.int, []⟩, nullable := some false },
      { name := "enabled", type := ⟨.bool, []⟩, nullable := some false }] },
  { name := "v", columns := [{ name := "id", type := ⟨.int, []⟩, nullable := some false }] },
  { name := "typed", columns := [
      { name := "amount", type := ⟨.numeric, [8, 2]⟩, nullable := some false },
      { name := "label", type := ⟨.varchar, [20]⟩, nullable := some false },
      { name := "at", type := ⟨.timestamp, [3]⟩, nullable := some false }] }]

private def queryOutput (sql : String) (params : SelectContract.ParameterEnv := []) :
    IO (List SelectContract.OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let certificate ← expectOk sql
    ((SelectContract.checkQuery .basicV26 joinCatalog params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let _ ← expectOk sql ((RenderContract.check .identityV01 query).mapError reprStr)
  let _ ← expectOk sql ((RenderContract.check .postgres16V01 query).mapError reprStr)
  pure certificate.output

def joinContractTests : IO Nat := do
  let nullableCases : List (String × List Bool) := [
    ("SELECT t.id, u.id FROM t CROSS JOIN u", [false, false]),
    ("SELECT t.id, u.id FROM t INNER JOIN u ON t.id = u.id", [false, false]),
    ("SELECT t.id, u.id FROM t LEFT JOIN u ON t.id = u.id", [false, true]),
    ("SELECT t.id, u.id FROM t RIGHT JOIN u ON t.id = u.id", [true, false]),
    ("SELECT t.id, u.id FROM t FULL JOIN u ON t.id = u.id", [true, true]),
    ("SELECT t.id, u.id FROM t LEFT JOIN u ON t.id = u.id WHERE u.id IS NOT NULL", [false, true]),
    ("SELECT t.id, u.id, v.id FROM (t LEFT JOIN u ON t.id = u.id) RIGHT JOIN v ON u.id = v.id",
      [true, true, false]),
    ("SELECT t.id, u.id, v.id FROM t LEFT JOIN (u RIGHT JOIN v ON u.id = v.id) ON t.id = v.id",
      [false, true, true]),
    ("SELECT t.id, u.id, v.id FROM (t LEFT JOIN u ON t.id = u.id) JOIN v ON u.id = v.id",
      [false, true, false]),
    ("SELECT t.id, t.label, u.id, u.enabled FROM t FULL JOIN u ON t.id = u.id",
      [true, true, true, true]),
    ("SELECT t.id, u.id FROM t JOIN u ON NULL", [false, false]),
    ("SELECT a.id, b.id FROM t a JOIN t b ON a.id = b.id", [false, false]) ]
  for (sql, expected) in nullableCases do
    let output ← queryOutput sql
    SQLean.Tests.assert (output.map (·.type.nullable) == expected) s!"join nullability: {sql}"
  let wildcard ← queryOutput "SELECT u.*, t.* FROM t LEFT JOIN u ON t.id = u.id"
  SQLean.Tests.assert (wildcard == [
      ⟨"id", ⟨.int32, true⟩⟩, ⟨"enabled", ⟨.bool, true⟩⟩,
      ⟨"id", ⟨.int32, false⟩⟩, ⟨"label", ⟨.text, true⟩⟩])
    "qualified wildcard order or nullability changed"
  let modifiers ← queryOutput "SELECT typed.* FROM t LEFT JOIN typed ON TRUE"
  SQLean.Tests.assert (modifiers == [
      ⟨"amount", ⟨.numeric [8, 2], true⟩⟩, ⟨"label", ⟨.varchar [20], true⟩⟩,
      ⟨"at", ⟨.timestamp [3], true⟩⟩])
    "outer join lost exact type modifiers"
  let invalid := [
    "SELECT id FROM t JOIN u ON t.id = u.id",
    "SELECT t.id FROM t JOIN u ON id = 1",
    "SELECT t.id FROM t x JOIN u ON x.id = u.id",
    "SELECT x.id FROM t x JOIN u x ON TRUE",
    "SELECT 1 FROM t JOIN t ON TRUE",
    "SELECT t.id FROM t JOIN u ON t.id",
    "SELECT t.id FROM t JOIN u ON CAST('true' AS TEXT)",
    "SELECT t.id FROM t WHERE CAST('true' AS TEXT)",
    "SELECT t.id FROM t CROSS JOIN (u JOIN v ON t.id = v.id)",
    "SELECT t.id FROM t, u JOIN v ON t.id = v.id",
    "SELECT t.id FROM t JOIN missing ON TRUE",
    "SELECT t.id AS projected FROM t JOIN u ON projected = u.id",
    "SELECT t.id FROM t LEFT JOIN u ON t.id = u.id FOR UPDATE",
    "SELECT t.id FROM t LEFT JOIN u ON t.id = u.id FOR UPDATE OF u",
    "SELECT t.id FROM t RIGHT JOIN u ON t.id = u.id FOR SHARE OF t",
    "SELECT t.id FROM t FULL JOIN u ON t.id = u.id FOR KEY SHARE OF t",
    "SELECT t.id FROM t FULL JOIN u ON t.id = u.id FOR NO KEY UPDATE",
    "SELECT t.id FROM (t LEFT JOIN u ON t.id = u.id) JOIN v ON u.id = v.id FOR UPDATE OF u" ]
  for sql in invalid do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV26 joinCatalog [] query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError s!"expected Invalid join: {sql}")
  let supported := [
    "SELECT t.id FROM t CROSS JOIN u JOIN v ON t.id = v.id",
    "SELECT t.id FROM t JOIN u ON t.id = u.id FOR UPDATE",
    "SELECT t.id FROM t CROSS JOIN u FOR UPDATE OF t, u",
    "SELECT t.id FROM t LEFT JOIN u ON t.id = u.id FOR UPDATE OF t",
    "SELECT u.id FROM t RIGHT JOIN u ON t.id = u.id FOR UPDATE OF u",
    "SELECT t.id FROM (t LEFT JOIN u ON t.id = u.id) JOIN v ON u.id = v.id FOR UPDATE OF t, v",
    "SELECT * FROM t JOIN u USING (id)",
    "SELECT * FROM t NATURAL JOIN u",
    "SELECT * FROM t AS x(a, b) JOIN u ON x.a = u.id",
    "SELECT * FROM t CROSS JOIN (SELECT 1 AS id) q" ]
  for sql in supported do
    let _ ← queryOutput sql
  let unsupported := [
    "SELECT t.id FROM t JOIN u ON 'true'",
    "SELECT t.id FROM t JOIN u ON 'false'",
    "SELECT t.id FROM t WHERE 'true'" ]
  for sql in unsupported do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV26 joinCatalog [] query with
    | .error (.unsupported _) => pure ()
    | _ => throw (IO.userError s!"expected Unsupported source: {sql}")
  for source in [
      Advanced.From.join .cross (.table "t") (.table "u") (.on (.literal (.bool true))),
      Advanced.From.join .inner (.table "t") (.table "u") .none ] do
    let query : Advanced.Query := { body := .select { items := [.all], source := some source } }
    match SelectContract.checkQuery .basicV26 joinCatalog [] query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError "malformed handbuilt join condition must be Invalid")
  let sql := "SELECT ? AS p, t.id FROM (t JOIN u ON t.id = u.id AND ?) JOIN v ON u.id = v.id AND ? WHERE ? ORDER BY t.id OFFSET ? LIMIT ?"
  let params ← expectOk sql (Assurance.parseContractParameterTypes "int,bool,bool,bool,int,int")
  let query ← expectOk sql (Advanced.parseQuery sql)
  let certificate ← expectOk sql
    ((SelectContract.checkQuery .basicV26 joinCatalog params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  SQLean.Tests.assert (Advanced.queryParameters 1024 query ==
      (List.range 6).map (fun n => Advanced.Parameter.anonymous (n + 1)))
    "SELECT/FROM/WHERE/OFFSET/LIMIT source order changed"
  let rendered ← expectOk sql ((RenderContract.check .postgres16V01 query).mapError reprStr)
  SQLean.Tests.assert (rendered.sql ==
      "SELECT $1 AS \"p\", \"t\".\"id\" FROM ((\"t\" INNER JOIN \"u\" ON ((\"t\".\"id\" = \"u\".\"id\") AND $2)) INNER JOIN \"v\" ON ((\"u\".\"id\" = \"v\".\"id\") AND $3)) WHERE $4 ORDER BY \"t\".\"id\" ASC OFFSET $5 LIMIT $6;")
    "join translation changed placeholder placement"
  match SelectContract.checkQuery .basicV26 joinCatalog params { query with offsetFirst := false } with
  | .error (.invalid _) => pure ()
  | _ => throw (IO.userError "manual pagination reorder must violate anonymous source order")
  match SelectContract.checkQuery .basicV26 joinCatalog params query 1 with
  | .error (.inconclusive _) => pure ()
  | _ => throw (IO.userError "join traversal exhaustion must be Inconclusive")
  pure (nullableCases.length + invalid.length + supported.length + unsupported.length + 7)

private def stringField (record : Lean.Json) (name : String) : IO String :=
  expectOk s!"join fixture {name}" ((record.getObjVal? name) >>= Lean.Json.getStr?)

/-- Every synthetic case declares its full catalog and parameters and must
receive a complete independent SELECT certificate with exact output metadata. -/
def joinCorpusTests : IO Nat := do
  let source ← IO.FS.readFile "fixtures/join_contract/synthetic.json"
  let json ← expectOk "join fixture JSON" (Lean.Json.parse source)
  let records ← expectOk "join fixture array" json.getArr?
  SQLean.Tests.assert (records.size == 50) "expected exactly 50 join queries"
  let catalog ← expectOk "join fixture catalog"
    (Advanced.decodeCatalogJson (← IO.FS.readFile "fixtures/join_contract/schema.json"))
  let mut ids : List String := []
  let mut sources : List String := []
  for record in records do
    let id ← stringField record "id"
    let sql ← stringField record "sql"
    SQLean.Tests.assert ((← stringField record "source_kind") == "synthetic") s!"{id}: wrong fixture population"
    SQLean.Tests.assert ((← stringField record "catalogFile") == "fixtures/join_contract/schema.json")
      s!"{id}: wrong catalog"
    let params ← expectOk id (Assurance.parseContractParameterTypes (← stringField record "parameter_types"))
    let expected ← expectOk id ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
    let expected ← expected.toList.mapM fun column => do
      let name ← stringField column "name"
      let type ← stringField column "type"
      let nullable ← expectOk id ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
      let base ← match type with
        | "int32" => pure SelectContract.ScalarType.int32
        | "text" => pure .text
        | "bool" => pure .bool
        | _ => throw (IO.userError s!"{id}: unexpected output type {type}")
      pure (SelectContract.OutputColumn.mk name ⟨base, nullable⟩)
    let query ← expectOk id (Advanced.parseQuery sql)
    let certificate ← expectOk id
      ((SelectContract.checkQuery .basicV26 catalog params query).mapError reprStr)
    SQLean.Tests.assert (certificate.output == expected) s!"{id}: exact output mismatch"
    have _preserved := RenderContract.translateParameters_valid certificate.valid
    let identity ← expectOk id ((RenderContract.check .identityV01 query).mapError reprStr)
    let postgres ← expectOk id ((RenderContract.check .postgres16V01 query).mapError reprStr)
    have _identity : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
    have _postgres : Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
      postgres.roundTrip
    ids := id :: ids
    sources := sql :: sources
  SQLean.Tests.assert (decide ids.Nodup && decide sources.Nodup) "duplicate join fixture identities or SQL"
  pure records.size

end SQLean.Tests
