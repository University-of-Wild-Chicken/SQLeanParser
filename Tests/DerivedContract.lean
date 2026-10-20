import SQLean.Assurance
import SQLean.SchemaJson
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

namespace SQLean.Tests

private def derivedCatalog : Advanced.Catalog := [
  { name := "t", columns := [
      { name := "id", type := ⟨.int, []⟩, nullable := some false },
      { name := "label", type := ⟨.text, []⟩, nullable := some true }] },
  { name := "u", columns := [
      { name := "id", type := ⟨.int, []⟩, nullable := some false },
      { name := "enabled", type := ⟨.bool, []⟩, nullable := some false }] }]

private def derivedOutput (sql : String) (params : SelectContract.ParameterEnv := []) :
    IO (List SelectContract.OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let certificate ← expectOk sql
    ((SelectContract.checkQuery .basicV10 derivedCatalog params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let _ ← expectOk sql ((RenderContract.check .identityV01 query).mapError reprStr)
  let _ ← expectOk sql ((RenderContract.check .postgres16V01 query).mapError reprStr)
  pure certificate.output

def derivedContractTests : IO Nat := do
  let mut count := 0
  let ordinary := [
    "SELECT * FROM (SELECT id, label FROM t) q",
    "SELECT q.* FROM (SELECT id, label FROM t) q",
    "SELECT q.id FROM (SELECT DISTINCT id FROM t ORDER BY id LIMIT 2 OFFSET 1) q",
    "SELECT q.id FROM (SELECT id FROM t FOR UPDATE) q",
    "SELECT q.id FROM (SELECT id FROM t) q JOIN u ON q.id = u.id",
    "SELECT q.id FROM (SELECT id FROM t) q CROSS JOIN u",
    "SELECT q.id FROM (SELECT id FROM t) q NATURAL JOIN u",
    "SELECT id FROM (SELECT id FROM t) q FULL JOIN u USING (id)",
    "SELECT q.id FROM t JOIN (SELECT id FROM u) q ON t.id = q.id FOR UPDATE OF t",
    "SELECT t.id FROM t LEFT JOIN (SELECT id FROM u) q ON t.id = q.id FOR UPDATE OF t",
    "SELECT q.id FROM (SELECT id FROM u) q RIGHT JOIN t ON t.id = q.id FOR SHARE OF t",
    "SELECT outer_q.* FROM (SELECT inner_q.* FROM (SELECT id, label FROM t) inner_q) outer_q" ]
  for sql in ordinary do
    let _ ← derivedOutput sql
    count := count + 1
  let exact : List (String × List SelectContract.OutputColumn) := [
    ("SELECT * FROM (SELECT id, label FROM t) q(a)",
      [⟨"a", ⟨.int32, false⟩⟩, ⟨"label", ⟨.text, true⟩⟩]),
    ("SELECT q.* FROM (SELECT id, label FROM t) q(a, b)",
      [⟨"a", ⟨.int32, false⟩⟩, ⟨"b", ⟨.text, true⟩⟩]),
    ("SELECT * FROM (SELECT id AS same_name, label AS same_name FROM t) q",
      [⟨"same_name", ⟨.int32, false⟩⟩, ⟨"same_name", ⟨.text, true⟩⟩]),
    ("SELECT q.* FROM (SELECT id, label FROM t) q(same_name, same_name)",
      [⟨"same_name", ⟨.int32, false⟩⟩, ⟨"same_name", ⟨.text, true⟩⟩]),
    ("SELECT * FROM (SELECT id AS same_name, label AS same_name FROM t) q(a, b)",
      [⟨"a", ⟨.int32, false⟩⟩, ⟨"b", ⟨.text, true⟩⟩]),
    ("SELECT q.id, q.label FROM u LEFT JOIN (SELECT id, label FROM t) q ON u.id = q.id",
      [⟨"id", ⟨.int32, true⟩⟩, ⟨"label", ⟨.text, true⟩⟩]),
    ("SELECT q.* FROM (SELECT CAST(1 AS NUMERIC(8, 2)) AS amount) q",
      [⟨"amount", ⟨.numeric [8, 2], false⟩⟩]),
    ("SELECT q.* FROM (SELECT NULL AS missing_value) q",
      [⟨"missing_value", ⟨.text, true⟩⟩]),
    ("SELECT q.* FROM (SELECT id, label FROM t) q(label)",
      [⟨"label", ⟨.int32, false⟩⟩, ⟨"label", ⟨.text, true⟩⟩]),
    ("SELECT q.* FROM (SELECT id AS a, id AS b FROM t) q(b, a)",
      [⟨"b", ⟨.int32, false⟩⟩, ⟨"a", ⟨.int32, false⟩⟩]) ]
  for (sql, expected) in exact do
    let actual ← derivedOutput sql
    SQLean.Tests.assert (actual == expected) s!"derived output metadata: {sql}"
    count := count + 1
  let invalid := [
    "SELECT q.same_name FROM (SELECT id AS same_name, label AS same_name FROM t) q",
    "SELECT q.same_name FROM (SELECT id, label FROM t) q(same_name, same_name)",
    "SELECT q.id FROM (SELECT id, label FROM t) q(a)",
    "SELECT t.id FROM (SELECT id FROM t) q",
    "SELECT inner_q.id FROM (SELECT inner_q.id FROM (SELECT id FROM t) inner_q) outer_q",
    "SELECT * FROM (SELECT id FROM t) q(a, b)",
    "SELECT * FROM (SELECT id FROM missing) q",
    "SELECT * FROM (SELECT missing FROM t) q",
    "SELECT * FROM t CROSS JOIN (SELECT t.id) q",
    "SELECT * FROM t JOIN (SELECT t.id FROM u) q ON TRUE",
    "SELECT * FROM t q CROSS JOIN (SELECT id FROM u) q",
    "SELECT q.id FROM (SELECT id FROM t) q FOR UPDATE OF t",
    "SELECT * FROM (SELECT id AS same_name, label AS same_name FROM t) q JOIN u USING (same_name)" ]
  for sql in invalid do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV10 derivedCatalog [] query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError s!"expected Invalid derived query: {sql}")
    count := count + 1
  let unsupported := [
    "SELECT * FROM LATERAL (SELECT 1 AS id) q",
    "SELECT * FROM t CROSS JOIN LATERAL (SELECT t.id) q",
    "SELECT q.id FROM (SELECT id FROM t) q FOR UPDATE",
    "SELECT q.id FROM (SELECT id FROM t) q FOR UPDATE OF q",
    "SELECT t.id FROM t JOIN (SELECT id FROM u) q ON t.id = q.id FOR UPDATE",
    "SELECT * FROM (SELECT COUNT(*) AS count_value FROM t) q",
    "SELECT * FROM (SELECT id FROM t UNION SELECT id FROM u) q",
    "SELECT * FROM (WITH inner_q AS (SELECT id FROM t) SELECT id FROM inner_q) q",
    "SELECT (SELECT id FROM t)",
    "SELECT EXISTS (SELECT id FROM t)",
    "SELECT 1 IN (SELECT id FROM t)" ]
  for sql in unsupported do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV10 derivedCatalog [] query with
    | .error (.unsupported _) => pure ()
    | _ => throw (IO.userError s!"expected Unsupported derived boundary: {sql}")
    count := count + 1
  let child : Advanced.Query := { body := .select { items := [.expression (.literal (.int 1))] } }
  for source in [
      Advanced.From.derived child "",
      Advanced.From.derived child "q" [""],
      Advanced.From.derived child "q" ["a", "b"] ] do
    let query : Advanced.Query := { body := .select { items := [.all], source := some source } }
    match SelectContract.checkQuery .basicV10 derivedCatalog [] query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError "malformed derived alias metadata must be Invalid")
    count := count + 1
  let params ← expectOk "derived placeholders"
    (Assurance.parseContractParameterTypes "int,int,int,int,int,int,int")
  let sql := "SELECT ? AS outer_value, q.* FROM (SELECT ? AS inner_value FROM (SELECT ? AS deep_value) d WHERE ? > 0 ORDER BY inner_value LIMIT ?) q WHERE ? > 0 LIMIT ?"
  let query ← expectOk sql (Advanced.parseQuery sql)
  let certificate ← expectOk sql
    ((SelectContract.checkQuery .basicV10 derivedCatalog params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  SQLean.Tests.assert (Advanced.queryParameters 1024 query ==
      (List.range 7).map (fun n => Advanced.Parameter.anonymous (n + 1)))
    "nested derived parameter source order changed"
  let _ ← expectOk sql ((RenderContract.check .postgres16V01 query).mapError reprStr)
  count := count + 1
  for (outer, inner) in [
      (Advanced.Parameter.anonymous 1, Advanced.Parameter.numbered 1),
      (Advanced.Parameter.numbered 1, Advanced.Parameter.anonymous 1) ] do
    let innerQuery : Advanced.Query := { body := .select {
      items := [.expression (.parameter inner) (some "id")] } }
    let query : Advanced.Query := { body := .select {
      items := [.expression (.parameter outer)]
      source := some (.derived innerQuery "q") } }
    match SelectContract.checkQuery .basicV10 derivedCatalog params query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError "parameter styles must not mix across derived query boundaries")
    count := count + 1
  let repeated ← expectOk "numbered repeats across queries"
    (Advanced.parseQuery "SELECT $1 AS outside FROM (SELECT $1 AS inside_value) q")
  let _ ← expectOk "numbered repeats across queries"
    ((SelectContract.checkQuery .basicV10 derivedCatalog params repeated).mapError reprStr)
  count := count + 1
  let repeatedChild : Advanced.Query := { body := .select {
    items := [.expression (.parameter (.anonymous 1)) (some "value")] } }
  let repeatedAnon : Advanced.Query := { body := .select {
    items := [.expression (.parameter (.anonymous 1))]
    source := some (.derived repeatedChild "q") } }
  match SelectContract.checkQuery .basicV10 derivedCatalog params repeatedAnon with
  | .error (.invalid _) => pure ()
  | _ => throw (IO.userError "derived queries must not restart anonymous ordinal numbering")
  count := count + 1
  match SelectContract.checkQuery .basicV10 derivedCatalog params query 2 with
  | .error (.inconclusive _) => pure ()
  | _ => throw (IO.userError "derived traversal exhaustion must be Inconclusive")
  count := count + 1
  pure count

private def stringField (record : Lean.Json) (name : String) : IO String :=
  expectOk s!"derived fixture {name}" ((record.getObjVal? name) >>= Lean.Json.getStr?)

def derivedCorpusTests : IO Nat := do
  let source ← IO.FS.readFile "fixtures/derived_contract/synthetic.json"
  let json ← expectOk "derived fixture JSON" (Lean.Json.parse source)
  let records ← expectOk "derived fixture array" json.getArr?
  SQLean.Tests.assert (records.size == 50) "expected exactly 50 derived queries"
  let catalog ← expectOk "derived fixture catalog"
    (Advanced.decodeCatalogJson (← IO.FS.readFile "fixtures/derived_contract/schema.json"))
  let mut ids : List String := []
  let mut sources : List String := []
  for record in records do
    let id ← stringField record "id"
    let sql ← stringField record "sql"
    SQLean.Tests.assert ((← stringField record "source_kind") == "synthetic") s!"{id}: wrong fixture population"
    SQLean.Tests.assert ((← stringField record "catalogFile") == "fixtures/derived_contract/schema.json")
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
      ((SelectContract.checkQuery .basicV10 catalog params query).mapError reprStr)
    SQLean.Tests.assert (certificate.output == expected) s!"{id}: exact output mismatch"
    have _preserved := RenderContract.translateParameters_valid certificate.valid
    let identity ← expectOk id ((RenderContract.check .identityV01 query).mapError reprStr)
    let postgres ← expectOk id ((RenderContract.check .postgres16V01 query).mapError reprStr)
    have _identity : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
    have _postgres : Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
      postgres.roundTrip
    ids := id :: ids
    sources := sql :: sources
  SQLean.Tests.assert (decide ids.Nodup && decide sources.Nodup) "duplicate derived fixture identities or SQL"
  pure records.size

end SQLean.Tests
