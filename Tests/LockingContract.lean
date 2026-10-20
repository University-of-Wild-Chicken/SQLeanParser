import SQLean.Assurance
import SQLean.SchemaJson
import SQLean.ScopeContract.Embedding
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

namespace SQLean.Tests

private def lockingCatalog : Advanced.Catalog := [
  { name := "t", columns := [
      { name := "id", type := ⟨.int, []⟩, nullable := some false },
      { name := "label", type := ⟨.text, []⟩, nullable := some true }] },
  { name := "u", columns := [{ name := "id", type := ⟨.int, []⟩, nullable := some false }] }]

private def lockedQuery : Advanced.Query := {
  body := .select { items := [.expression (.literal (.int 1))] }
  locking := [⟨.update, [], .nowait⟩] }

/-- The name-only embedding cannot silently erase a lock clause. -/
example : ¬ ScopeContract.AdvancedNameValid [] lockedQuery :=
  ScopeContract.locking_not_embedded (by decide)

/-- Duplicate targets and repeated clauses have direct declarative evidence. -/
example : SelectContract.LockingValid
    (SelectContract.Scope.ofTable ⟨none, "t"⟩ (some "x") [⟨"id", ⟨.int32, false⟩⟩]) false
    [⟨.update, ["x", "x"], .nowait⟩, ⟨.share, ["x"], .skipLocked⟩] :=
  .cons rfl (by decide) (.cons rfl (by decide) .nil)

def lockingContractTests : IO Nat := do
  let accepted := [
    "SELECT 1 FOR UPDATE", "SELECT 1 FOR NO KEY UPDATE NOWAIT",
    "SELECT 1 FOR SHARE SKIP LOCKED", "SELECT 1 FOR KEY SHARE",
    "SELECT id FROM t FOR UPDATE", "SELECT id FROM t x FOR UPDATE OF x",
    "SELECT id FROM t FOR UPDATE OF t, t NOWAIT",
    "SELECT id FROM t FOR SHARE OF t SKIP LOCKED FOR UPDATE OF t NOWAIT",
    "SELECT id FROM t ORDER BY id LIMIT 3 OFFSET 1 FOR KEY SHARE OF t",
    "SELECT id FROM t FOR UPDATE OFFSET 1 LIMIT 3",
    "SELECT id FROM t OFFSET 1 LIMIT 3 FOR UPDATE",
    "SELECT t.id FROM t JOIN u ON t.id = u.id FOR UPDATE OF t, u",
    "SELECT t.id FROM t LEFT JOIN u ON t.id = u.id FOR UPDATE OF t",
    "SELECT u.id FROM t RIGHT JOIN u ON t.id = u.id FOR UPDATE OF u" ]
  for sql in accepted do
    let query ← expectOk sql (Advanced.parseQuery sql)
    let certificate ← expectOk sql
      ((SelectContract.checkQuery .basicV30 lockingCatalog [] query).mapError reprStr)
    have _preserved := RenderContract.translateParameters_valid certificate.valid
    let rendered ← expectOk sql ((RenderContract.check .postgres16V01 query).mapError reprStr)
    let reparsed ← expectOk sql (Advanced.parseQuery rendered.sql)
    SQLean.Tests.assert (reparsed.locking == query.locking)
      s!"row-lock metadata changed: {sql}"
  let invalid := [
    "SELECT 1 FOR UPDATE OF t",
    "SELECT id FROM t x FOR UPDATE OF t",
    "SELECT id AS x FROM t FOR UPDATE OF x",
    "SELECT id FROM t FOR UPDATE OF missing",
    "SELECT DISTINCT id FROM t FOR UPDATE",
    "SELECT DISTINCT ON (id) id FROM t FOR UPDATE",
    "SELECT id FROM t GROUP BY id FOR UPDATE",
    "SELECT id FROM t HAVING TRUE FOR UPDATE",
    "SELECT COUNT(*) FROM t FOR UPDATE",
    "SELECT COALESCE(SUM(id), 0) FROM t FOR SHARE",
    "SELECT id FROM t ORDER BY COUNT(*) FOR KEY SHARE",
    "(SELECT id FROM t UNION SELECT id FROM u) FOR UPDATE" ]
  for sql in invalid do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV30 lockingCatalog [] query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError s!"expected invalid locked query: {sql}")
  let expandedAccepted := [
    "WITH q AS (SELECT id FROM t FOR UPDATE) SELECT id FROM q",
    "WITH q AS (SELECT id FROM t) SELECT id FROM q FOR UPDATE",
    "WITH a AS (SELECT id FROM t FOR UPDATE OF t), t AS (SELECT id FROM a) SELECT * FROM t",
    "WITH t AS (SELECT id FROM t FOR UPDATE OF t) SELECT * FROM t" ]
  for sql in expandedAccepted do
    let query ← expectOk sql (Advanced.parseQuery sql)
    let _ ← expectOk sql (Advanced.checkQuery lockingCatalog.toSchema [] query)
    let certificate ← expectOk sql
      ((SelectContract.checkQuery .basicV30 lockingCatalog [] query).mapError reprStr)
    SQLean.Tests.assert (certificate.output == [⟨"id", ⟨.int32, false⟩⟩])
      s!"CTE locking must preserve its exact independently certified output: {sql}"
    have _preserved := RenderContract.translateParameters_valid certificate.valid
    let rendered ← expectOk sql ((RenderContract.check .postgres16V01 query).mapError reprStr)
    have _roundTrip := rendered.roundTrip
  let expandedRejected := [
    "SELECT t.id FROM t LEFT JOIN u ON t.id = u.id FOR UPDATE",
    "SELECT t.id FROM t LEFT JOIN u ON t.id = u.id FOR UPDATE OF u",
    "SELECT t.id FROM t FULL JOIN u ON t.id = u.id FOR SHARE OF t",
    "SELECT q.id FROM (SELECT id FROM t) q FOR UPDATE OF q",
    "WITH q AS (SELECT id FROM t) SELECT id FROM q FOR UPDATE OF q",
    "WITH q AS (SELECT id FROM t) SELECT EXISTS (SELECT 1 FROM q FOR UPDATE OF q)",
    "WITH t AS (SELECT id FROM u), q AS (SELECT id FROM t FOR UPDATE OF t) SELECT * FROM q" ]
  for sql in expandedRejected do
    let query ← expectOk sql (Advanced.parseQuery sql)
    expectError sql (Advanced.checkQuery lockingCatalog.toSchema [] query)
  let params ← expectOk "offset-first declarations" (Assurance.parseContractParameterTypes "int,int,int")
  let query ← expectOk "offset-first source"
    (Advanced.parseQuery "SELECT ? AS v OFFSET ? LIMIT ? FOR UPDATE NOWAIT")
  SQLean.Tests.assert (query.offsetFirst &&
      query.offset == some (.parameter (.anonymous 2)) &&
      query.limit == some (.parameter (.anonymous 3)))
    "offset-first source order or identities lost"
  let certificate ← expectOk "offset-first full certificate"
    ((SelectContract.checkQuery .basicV30 [] params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let rendered ← expectOk "offset-first rendering"
    ((RenderContract.check .postgres16V01 query).mapError reprStr)
  SQLean.Tests.assert (rendered.sql ==
      "SELECT $1 AS \"v\" OFFSET $2 LIMIT $3 FOR UPDATE NOWAIT;")
    "offset-first canonical renderer changed anonymous bindings"
  SQLean.Tests.assert (Advanced.queryParameters 1024 query ==
      [.anonymous 1, .anonymous 2, .anonymous 3])
    "expanded parameter traversal ignored offset-first layout"
  let reordered := { query with offsetFirst := false }
  match SelectContract.checkQuery .basicV30 [] params reordered with
  | .error (.invalid _) => pure ()
  | _ => throw (IO.userError "manual pagination order change must invalidate anonymous ordinals")
  match SelectContract.checkQuery .basicV30 [] [] lockedQuery 0 with
  | .error (.inconclusive _) => pure ()
  | _ => throw (IO.userError "locking resource exhaustion must be inconclusive")
  pure (accepted.length + invalid.length + expandedAccepted.length + expandedRejected.length + 4)

private def stringField (record : Lean.Json) (name : String) : IO String :=
  expectOk s!"locking fixture {name}" ((record.getObjVal? name) >>= Lean.Json.getStr?)

/-- The 50 synthetic fixtures declare a real, fixed test catalog and all
parameter types. Every case must receive complete basic SELECT evidence. -/
def lockingCorpusTests : IO Nat := do
  let source ← IO.FS.readFile "fixtures/locking/synthetic.json"
  let json ← expectOk "locking fixture JSON" (Lean.Json.parse source)
  let records ← expectOk "locking fixture array" json.getArr?
  SQLean.Tests.assert (records.size == 50) "expected exactly 50 locking queries"
  let catalog ← expectOk "locking fixture catalog"
    (Advanced.decodeCatalogJson (← IO.FS.readFile "fixtures/schema.json"))
  let mut ids : List String := []
  let mut sources : List String := []
  for record in records do
    let id ← stringField record "id"
    let sql ← stringField record "sql"
    SQLean.Tests.assert ((← stringField record "source_kind") == "synthetic") s!"{id}: wrong fixture population"
    SQLean.Tests.assert ((← stringField record "catalogFile") == "fixtures/schema.json") s!"{id}: wrong catalog"
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
      ((SelectContract.checkQuery .basicV30 catalog params query).mapError reprStr)
    SQLean.Tests.assert (certificate.output == expected) s!"{id}: exact output mismatch"
    have _preserved := RenderContract.translateParameters_valid certificate.valid
    let identity ← expectOk id ((RenderContract.check .identityV01 query).mapError reprStr)
    let postgres ← expectOk id ((RenderContract.check .postgres16V01 query).mapError reprStr)
    have _identity : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
    have _postgres : Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
      postgres.roundTrip
    ids := id :: ids
    sources := sql :: sources
  SQLean.Tests.assert (decide ids.Nodup && decide sources.Nodup) "duplicate locking fixture identities or SQL"
  pure records.size

end SQLean.Tests
