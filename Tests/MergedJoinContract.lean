import SQLean.Assurance
import SQLean.SchemaJson
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

namespace SQLean.Tests

private def col (name : Name) (type : Advanced.DataType) (nullable : Bool := false) : Advanced.Column :=
  { name, type, nullable := some nullable }

private def mergedCatalog : Advanced.Catalog := [
  { name := "l", columns := [
      col "a" ⟨.text, []⟩, col "k" ⟨.int, []⟩, col "b" ⟨.bool, []⟩ true,
      col "z" ⟨.int, []⟩ true, col "s" ⟨.varchar, [5]⟩ ] },
  { name := "r", columns := [
      col "x" ⟨.int, []⟩, col "k" ⟨.bigInt, []⟩ true, col "y" ⟨.text, []⟩,
      col "z" ⟨.int, []⟩, col "s" ⟨.varchar, [5]⟩ ] },
  { name := "v", columns := [col "k" ⟨.int, []⟩, col "z" ⟨.int, []⟩] },
  { name := "p", columns := [col "payload" ⟨.bool, []⟩] },
  { name := "n1", columns := [col "k" ⟨.numeric, [8, 2]⟩] },
  { name := "n2", columns := [col "k" ⟨.numeric, [10, 3]⟩] },
  { name := "n3", columns := [col "k" ⟨.numeric, [8, 2]⟩ true] },
  { name := "d", columns := [col "k" ⟨.date, []⟩] },
  { name := "ts", columns := [col "k" ⟨.timestamp, [3]⟩ true] },
  { name := "j1", columns := [col "k" ⟨.json, []⟩] },
  { name := "j2", columns := [col "k" ⟨.json, []⟩] },
  { name := "flag", columns := [col "k" ⟨.bool, []⟩] }]

private def mergedOutput (sql : String) (params : SelectContract.ParameterEnv := []) :
    IO (List SelectContract.OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let certificate ← expectOk sql
    ((SelectContract.checkQuery .basicV15 mergedCatalog params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let _ ← expectOk sql ((RenderContract.check .identityV01 query).mapError reprStr)
  let _ ← expectOk sql ((RenderContract.check .postgres16V01 query).mapError reprStr)
  pure certificate.output

def mergedJoinContractTests : IO Nat := do
  let mut count := 0
  let leftOriginal : List SelectContract.OutputColumn := [
    ⟨"a", ⟨.text, false⟩⟩, ⟨"k", ⟨.int32, false⟩⟩, ⟨"b", ⟨.bool, true⟩⟩,
    ⟨"z", ⟨.int32, true⟩⟩, ⟨"s", ⟨.varchar [5], false⟩⟩ ]
  let rightOriginal : List SelectContract.OutputColumn := [
    ⟨"x", ⟨.int32, false⟩⟩, ⟨"k", ⟨.int64, true⟩⟩, ⟨"y", ⟨.text, false⟩⟩,
    ⟨"z", ⟨.int32, false⟩⟩, ⟨"s", ⟨.varchar [5], false⟩⟩ ]
  for (kind, mergedNullable, leftNullable, rightNullable) in [
      ("INNER", true, false, false), ("LEFT", false, false, true),
      ("RIGHT", true, true, false), ("FULL", true, true, true) ] do
    for suffix in ["USING (k)", "NATURAL"] do
      let sourceSql := if suffix == "NATURAL" then s!"l NATURAL {kind} JOIN r"
        else s!"l {kind} JOIN r {suffix}"
      let actual ← mergedOutput s!"SELECT k, l.k, r.k FROM {sourceSql}"
      SQLean.Tests.assert (actual == [
          ⟨"k", ⟨.int64, mergedNullable⟩⟩,
          ⟨"k", ⟨.int32, leftNullable⟩⟩, ⟨"k", ⟨.int64, true⟩⟩])
        s!"merged or qualified key type/nullability changed: {sourceSql}"
      count := count + 1
      let expectedLeft := if leftNullable then leftOriginal.map SelectContract.nullableColumn else leftOriginal
      let actual ← mergedOutput s!"SELECT l.* FROM {sourceSql}"
      SQLean.Tests.assert (actual == expectedLeft) s!"left wildcard reordered or coerced: {sourceSql}"
      count := count + 1
      let expectedRight := if rightNullable then rightOriginal.map SelectContract.nullableColumn else rightOriginal
      let actual ← mergedOutput s!"SELECT r.* FROM {sourceSql}"
      SQLean.Tests.assert (actual == expectedRight) s!"right wildcard reordered or coerced: {sourceSql}"
      count := count + 1
  let orderedCases : List (String × List Name) := [
    ("SELECT * FROM l JOIN r USING (k)", ["k", "a", "b", "z", "s", "x", "y", "z", "s"]),
    ("SELECT * FROM l JOIN r USING (z, k)", ["z", "k", "a", "b", "s", "x", "y", "s"]),
    ("SELECT * FROM l NATURAL JOIN r", ["k", "z", "s", "a", "b", "x", "y"]),
    ("SELECT * FROM r NATURAL JOIN l", ["k", "z", "s", "x", "y", "a", "b"]),
    ("SELECT * FROM l NATURAL LEFT JOIN p", ["a", "k", "b", "z", "s", "payload"]),
    ("SELECT * FROM (l JOIN r USING (k, z)) JOIN v USING (z, k)", ["z", "k", "a", "b", "s", "x", "y", "s"]),
    ("SELECT * FROM (l NATURAL JOIN r) NATURAL JOIN v", ["k", "z", "s", "a", "b", "x", "y"]),
    ("SELECT l.* FROM (l JOIN r USING (k)) JOIN v USING (k)", ["a", "k", "b", "z", "s"]),
    ("SELECT r.* FROM l JOIN (r JOIN v USING (k)) USING (k)", ["x", "k", "y", "z", "s"]) ]
  for (sql, expected) in orderedCases do
    let actual ← mergedOutput sql
    SQLean.Tests.assert (actual.map (·.name) == expected) s!"merged output order: {sql}"
    count := count + 1
  let exactCases : List (String × List SelectContract.ExactType) := [
    ("SELECT k, n1.k, n2.k FROM n1 JOIN n2 USING (k)",
      [⟨.numeric [], false⟩, ⟨.numeric [8, 2], false⟩, ⟨.numeric [10, 3], false⟩]),
    ("SELECT k FROM n1 JOIN n3 USING (k)", [⟨.numeric [8, 2], true⟩]),
    ("SELECT k, d.k, ts.k FROM d JOIN ts USING (k)",
      [⟨.timestamp [], true⟩, ⟨.date, false⟩, ⟨.timestamp [3], true⟩]),
    ("SELECT s FROM l NATURAL FULL JOIN r", [⟨.varchar [5], false⟩]),
    ("SELECT k FROM l FULL JOIN r USING (k) WHERE k IS NOT NULL", [⟨.int64, true⟩]),
    ("SELECT k, l.k, r.k, v.k FROM (l FULL JOIN r USING (k)) LEFT JOIN v USING (k)",
      [⟨.int64, true⟩, ⟨.int32, true⟩, ⟨.int64, true⟩, ⟨.int32, true⟩]),
    ("SELECT k, l.k, r.k, v.k FROM l LEFT JOIN (r JOIN v USING (k)) USING (k)",
      [⟨.int64, false⟩, ⟨.int32, false⟩, ⟨.int64, true⟩, ⟨.int32, true⟩]) ]
  for (sql, expected) in exactCases do
    let actual ← mergedOutput sql
    SQLean.Tests.assert (actual.map (·.type) == expected) s!"merged exact scalar types: {sql}"
    count := count + 1
  let invalid := [
    "SELECT * FROM l JOIN r USING (missing)",
    "SELECT * FROM l JOIN p USING (k)",
    "SELECT * FROM p JOIN l USING (k)",
    "SELECT * FROM l JOIN r USING (k, k)",
    "SELECT * FROM (l JOIN r ON l.k = r.k) JOIN v USING (k)",
    "SELECT * FROM (l JOIN r ON l.k = r.k) NATURAL JOIN v",
    "SELECT * FROM l JOIN (r JOIN v ON r.k = v.k) USING (k)",
    "SELECT * FROM l NATURAL JOIN (r JOIN v ON r.k = v.k)",
    "SELECT k FROM (l JOIN r USING (k)) JOIN v ON l.k = v.k",
    "SELECT * FROM j1 JOIN j2 USING (k)",
    "SELECT * FROM j1 NATURAL JOIN j2",
    "SELECT * FROM l JOIN flag USING (k)",
    "SELECT * FROM l x JOIN r x USING (k)",
    "SELECT l.k FROM l x JOIN r USING (k)",
    "SELECT k FROM l LEFT JOIN r USING (k) FOR UPDATE",
    "SELECT k FROM l NATURAL LEFT JOIN r FOR UPDATE OF r",
    "SELECT k FROM l FULL JOIN r USING (k) FOR SHARE OF l",
    "SELECT k FROM l NATURAL FULL JOIN r FOR UPDATE" ]
  for sql in invalid do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV15 mergedCatalog [] query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError s!"expected Invalid merged join: {sql}")
    count := count + 1
  for sql in [
      "SELECT k FROM l JOIN r USING (k) FOR UPDATE",
      "SELECT k FROM l NATURAL LEFT JOIN r FOR UPDATE OF l",
      "SELECT k FROM l RIGHT JOIN r USING (k) FOR UPDATE OF r",
      "SELECT * FROM (l JOIN r ON TRUE) NATURAL JOIN p" ] do
    let _ ← mergedOutput sql
    count := count + 1
  for source in [
      Advanced.From.join .inner (.table "l") (.table "r") (.using []),
      Advanced.From.join .cross (.table "l") (.table "r") (.using ["k"]),
      Advanced.From.join .cross (.table "l") (.table "r") .natural ] do
    let query : Advanced.Query := { body := .select { items := [.all], source := some source } }
    match SelectContract.checkQuery .basicV15 mergedCatalog [] query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError "malformed handbuilt merged-join condition must be Invalid")
    count := count + 1
  let emptyQualifier : Advanced.Query := {
    body := .select {
      items := [.expression (.column (some "") "k")]
      source := some (.join .inner (.table "l") (.table "r") (.using ["k"])) } }
  match SelectContract.checkQuery .basicV15 mergedCatalog [] emptyQualifier with
  | .error (.invalid _) => pure ()
  | _ => throw (IO.userError "merged key must not create an empty qualified namespace")
  count := count + 1
  let params ← expectOk "merged placeholders" (Assurance.parseContractParameterTypes "int,bool,bool,int,int")
  for source in ["(l JOIN p ON ?) JOIN r USING (k)", "(l JOIN p ON ?) NATURAL JOIN r"] do
    let sql := s!"SELECT ? AS projected, k FROM {source} WHERE ? OFFSET ? LIMIT ?"
    let query ← expectOk sql (Advanced.parseQuery sql)
    let certificate ← expectOk sql
      ((SelectContract.checkQuery .basicV15 mergedCatalog params query).mapError reprStr)
    have _preserved := RenderContract.translateParameters_valid certificate.valid
    SQLean.Tests.assert (Advanced.queryParameters 1024 query ==
        (List.range 5).map (fun n => Advanced.Parameter.anonymous (n + 1)))
      "merged join changed SELECT/FROM/WHERE/pagination parameter order"
    let _ ← expectOk sql ((RenderContract.check .postgres16V01 query).mapError reprStr)
    count := count + 1
    match SelectContract.checkQuery .basicV15 mergedCatalog params { query with offsetFirst := false } with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError "merged join accepted reordered anonymous pagination")
    count := count + 1
    match SelectContract.checkQuery .basicV15 mergedCatalog params query 1 with
    | .error (.inconclusive _) => pure ()
    | _ => throw (IO.userError "merged join exhaustion must be Inconclusive")
    count := count + 1
  pure count

private def stringField (record : Lean.Json) (name : String) : IO String :=
  expectOk s!"merged join fixture {name}" ((record.getObjVal? name) >>= Lean.Json.getStr?)

private def mergedFixtureTests (factor : String) : IO Nat := do
  let source ← IO.FS.readFile s!"fixtures/{factor}_contract/synthetic.json"
  let json ← expectOk s!"{factor} fixture JSON" (Lean.Json.parse source)
  let records ← expectOk s!"{factor} fixture array" json.getArr?
  SQLean.Tests.assert (records.size == 50) s!"expected exactly 50 {factor} queries"
  let catalog ← expectOk "merged join fixture catalog"
    (Advanced.decodeCatalogJson (← IO.FS.readFile "fixtures/merged_join_contract/schema.json"))
  let mut ids : List String := []
  let mut sources : List String := []
  for record in records do
    let id ← stringField record "id"
    let sql ← stringField record "sql"
    SQLean.Tests.assert ((← stringField record "source_kind") == "synthetic") s!"{id}: wrong fixture population"
    SQLean.Tests.assert ((← stringField record "catalogFile") == "fixtures/merged_join_contract/schema.json")
      s!"{id}: wrong catalog"
    let params ← expectOk id (Assurance.parseContractParameterTypes (← stringField record "parameter_types"))
    let expected ← expectOk id ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
    let expected ← expected.toList.mapM fun column => do
      let name ← stringField column "name"
      let type ← stringField column "type"
      let nullable ← expectOk id ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
      let base ← match type with
        | "int32" => pure SelectContract.ScalarType.int32
        | "bigint" | "int64" => pure .int64
        | "text" => pure .text
        | "bool" => pure .bool
        | _ => throw (IO.userError s!"{id}: unexpected output type {type}")
      pure (SelectContract.OutputColumn.mk name ⟨base, nullable⟩)
    let query ← expectOk id (Advanced.parseQuery sql)
    let certificate ← expectOk id
      ((SelectContract.checkQuery .basicV15 catalog params query).mapError reprStr)
    SQLean.Tests.assert (certificate.output == expected) s!"{id}: exact output mismatch"
    have _preserved := RenderContract.translateParameters_valid certificate.valid
    let identity ← expectOk id ((RenderContract.check .identityV01 query).mapError reprStr)
    let postgres ← expectOk id ((RenderContract.check .postgres16V01 query).mapError reprStr)
    have _identity : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
    have _postgres : Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
      postgres.roundTrip
    ids := id :: ids
    sources := sql :: sources
  SQLean.Tests.assert (decide ids.Nodup && decide sources.Nodup) s!"duplicate {factor} fixture identities or SQL"
  pure records.size

def usingCorpusTests : IO Nat := mergedFixtureTests "using"

def naturalCorpusTests : IO Nat := mergedFixtureTests "natural"

def mergedJoinCorpusTests : IO Nat := do
  pure ((← usingCorpusTests) + (← naturalCorpusTests))

end SQLean.Tests
