import SQLean.Assurance
import SQLean.SchemaJson
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

namespace SQLean.Tests

private def qualifiedLeft : Advanced.CatalogTable := {
  name := "t", schema := some "s1", exposeUnqualified := true
  columns := [
    {name := "id", type := ⟨.int, []⟩, nullable := some false},
    {name := "tag", type := ⟨.text, []⟩, nullable := some false},
    {name := "only_left", type := ⟨.text, []⟩, nullable := some false}] }

private def qualifiedRight : Advanced.CatalogTable := {
  name := "t", schema := some "s2", exposeUnqualified := false
  columns := [
    {name := "id", type := ⟨.bigInt, []⟩, nullable := some true},
    {name := "tag", type := ⟨.text, []⟩, nullable := some false},
    {name := "only_right", type := ⟨.bool, []⟩, nullable := some false}] }

private def qualifiedCatalog : Advanced.Catalog := [
  qualifiedLeft, qualifiedRight,
  {name := "legacy", columns := [{name := "id", type := ⟨.int, []⟩, nullable := some false}]},
  {name := "s1.t", columns := [{name := "id", type := ⟨.bool, []⟩, nullable := some false}]},
  {name := "Mixed.Table", schema := some "Odd.Schema", exposeUnqualified := false,
    columns := [{name := "select", type := ⟨.text, []⟩, nullable := some false}]},
  {name := "select", schema := some "s1", exposeUnqualified := false,
    columns := [{name := "from", type := ⟨.int, []⟩, nullable := some false}]}]

private def leftNamespace : SelectContract.Scope :=
  .ofTable ⟨some "s1", "t"⟩ none [⟨"id", ⟨.int32, false⟩⟩]

private def rightNamespace : SelectContract.Scope :=
  .ofTable ⟨some "s2", "t"⟩ none [⟨"id", ⟨.int64, true⟩⟩]

/-- These namespace and locking witnesses do not call a checker. -/
example : SelectContract.JoinAliasesDistinct leftNamespace rightNamespace := by decide
example : SelectContract.Resolves (leftNamespace ++ rightNamespace) (some "t")
    "id" ⟨"id", ⟨.int32, false⟩⟩ (some "s1") := by decide
example : ¬ SelectContract.Resolves (leftNamespace ++ rightNamespace) (some "t")
    "id" ⟨"id", ⟨.int32, false⟩⟩ := by decide
example : SelectContract.LockTargets
    (SelectContract.joinScope .left leftNamespace rightNamespace) ["t"] := by decide
example : ¬ SelectContract.LockTargets
    (SelectContract.joinScope .right leftNamespace rightNamespace) ["t"] := by decide
example : SelectContract.SourceValid .basicV25 [qualifiedLeft] []
    (some (.table "t" (some "x") ["key_id"] (some "s1")))
    (.ofTable ⟨some "s1", "t"⟩ (some "x")
      [⟨"key_id", ⟨.int32, false⟩⟩, ⟨"tag", ⟨.text, false⟩⟩,
       ⟨"only_left", ⟨.text, false⟩⟩]) [] := by
  apply SelectContract.SourceValid.tableRenamed (table := qualifiedLeft)
    (bindings := [⟨"id", ⟨.int32, false⟩⟩, ⟨"tag", ⟨.text, false⟩⟩,
      ⟨"only_left", ⟨.text, false⟩⟩])
  · simp
  · rfl
  · decide
  · exact .cons rfl (.cons rfl (.cons rfl .nil))
  · decide

private def qualifiedField (id : String) (record : Lean.Json) (name : String) : IO String :=
  expectOk s!"{id}: {name}" ((record.getObjVal? name) >>= Lean.Json.getStr?)

private def qualifiedCertificate (query : Advanced.Query)
    (catalog : Advanced.Catalog := qualifiedCatalog)
    (params : SelectContract.ParameterEnv := []) : IO (List SelectContract.OutputColumn) := do
  let certificate ← expectOk "qualified SELECT"
    ((SelectContract.checkQuery .basicV25 catalog params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let identity ← expectOk "qualified identity renderer"
    ((RenderContract.check .identityV01 query).mapError reprStr)
  let postgres ← expectOk "qualified PostgreSQL renderer"
    ((RenderContract.check .postgres16V01 query).mapError reprStr)
  have _identity : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
  have _postgres : Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
    postgres.roundTrip
  pure certificate.output

private def qualifiedOutput (sql : String) (catalog : Advanced.Catalog := qualifiedCatalog)
    (parameterTypes : String := "") : IO (List SelectContract.OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let params ← expectOk sql (Assurance.parseContractParameterTypes parameterTypes)
  qualifiedCertificate query catalog params

def qualifiedNamesContractTests : IO Nat := do
  let mut count := 0
  for (sql, expected) in [
      ("SELECT id FROM s1.t", SelectContract.ExactType.mk .int32 false),
      ("SELECT t.id FROM s1.t", ⟨.int32, false⟩),
      ("SELECT s1.t.id FROM s1.t", ⟨.int32, false⟩),
      ("SELECT s1.t.id FROM t", ⟨.int32, false⟩),
      ("SELECT id FROM s2.t", ⟨.int64, true⟩),
      ("SELECT t.id FROM s2.t", ⟨.int64, true⟩),
      ("SELECT s2.t.id FROM s2.t", ⟨.int64, true⟩),
      ("SELECT x.id FROM s1.t x", ⟨.int32, false⟩),
      ("SELECT x.key_id FROM s1.t x(key_id)", ⟨.int32, false⟩),
      ("SELECT x.tag FROM s1.t x(key_id)", ⟨.text, false⟩),
      ("SELECT x.label FROM s1.t x(key_id,label,other)", ⟨.text, false⟩),
      ("SELECT t.id FROM s1.t AS t", ⟨.int32, false⟩),
      ("SELECT \"s1.t\".id FROM s1.t AS \"s1.t\"", ⟨.int32, false⟩),
      ("SELECT id FROM \"s1.t\"", ⟨.bool, false⟩),
      ("SELECT \"s1.t\".id FROM \"s1.t\"", ⟨.bool, false⟩),
      ("SELECT \"Odd.Schema\".\"Mixed.Table\".select FROM \"Odd.Schema\".\"Mixed.Table\"", ⟨.text, false⟩),
      ("SELECT s1.select.from FROM s1.select", ⟨.int32, false⟩)] do
    let output ← qualifiedOutput sql
    SQLean.Tests.assert (output.map (·.type) == [expected]) s!"exact qualified selection: {sql}"
    count := count + 1
  for (sql, names) in [
      ("SELECT x.* FROM s1.t x(key_id)", ["key_id", "tag", "only_left"]),
      ("SELECT * FROM s1.t x(a,a)", ["a", "a", "only_left"]),
      ("SELECT x.* FROM s1.t x(a,a,a)", ["a", "a", "a"])] do
    let output ← qualifiedOutput sql
    SQLean.Tests.assert (output.map (·.name) == names) "column alias prefixes preserve order and duplicates"
    SQLean.Tests.assert (output.map (·.type) == [⟨.int32, false⟩, ⟨.text, false⟩, ⟨.text, false⟩])
      "column aliases preserve exact original types"
    count := count + 1
  for (kind, leftNullable, rightNullable) in [
      ("CROSS", false, false), ("INNER", false, false), ("LEFT", false, true),
      ("RIGHT", true, false), ("FULL", true, true)] do
    let source := s!"s1.t {kind} JOIN s2.t" ++ (if kind == "CROSS" then "" else " ON s1.t.id = s2.t.id")
    for (projection, expected) in [
        ("s1.t.id", [SelectContract.ExactType.mk .int32 leftNullable]),
        ("s2.t.id", [⟨.int64, true⟩]),
        ("s1.t.*", [⟨.int32, leftNullable⟩, ⟨.text, leftNullable⟩, ⟨.text, leftNullable⟩]),
        ("s2.t.*", [⟨.int64, true⟩, ⟨.text, rightNullable⟩, ⟨.bool, rightNullable⟩]),
        ("only_left, only_right", [⟨.text, leftNullable⟩, ⟨.bool, rightNullable⟩])] do
      let output ← qualifiedOutput s!"SELECT {projection} FROM {source}"
      SQLean.Tests.assert (output.map (·.type) == expected) "qualified join retains each exact namespace"
      count := count + 1
    for projection in ["t.id", "t.only_left", "t.*"] do
      let sql := s!"SELECT {projection} FROM {source}"
      let query ← expectOk sql (Advanced.parseQuery sql)
      match SelectContract.checkQuery .basicV25 qualifiedCatalog [] query with
      | .error (.invalid diagnostic) =>
          SQLean.Tests.assert (diagnostic.code == "ambiguous_relation_reference")
            "relation ambiguity must precede column lookup"
      | _ => throw (IO.userError s!"ambiguous basename acquired a certificate: {sql}")
      count := count + 1
  for (kind, nullable) in [("INNER", true), ("LEFT", false), ("RIGHT", true), ("FULL", true)] do
    for natural in [false, true] do
      let source := if natural then s!"s1.t NATURAL {kind} JOIN s2.t"
        else s!"s1.t {kind} JOIN s2.t USING(id)"
      let output ← qualifiedOutput s!"SELECT id, s1.t.id, s2.t.id FROM {source}"
      SQLean.Tests.assert (output.map (·.type) ==
          [⟨.int64, nullable⟩, ⟨.int32, kind == "RIGHT" || kind == "FULL"⟩, ⟨.int64, true⟩])
        "qualified USING/NATURAL lookup must retain original key types separately"
      count := count + 1
  for sql in [
      "SELECT s1.t.id FROM s1.t x", "SELECT s1.t.* FROM s1.t AS t",
      "SELECT t.id FROM s1.t x", "SELECT s2.t.id FROM t",
      "SELECT s1.t.id FROM s1.t AS \"s1.t\"",
      "SELECT t FROM s1.t CROSS JOIN s2.t",
      "SELECT * FROM s1.t CROSS JOIN s1.t",
      "SELECT * FROM t CROSS JOIN s1.t",
      "SELECT * FROM s1.t AS t CROSS JOIN s2.t",
      "SELECT * FROM s1.t AS x CROSS JOIN s2.t AS x",
      "SELECT * FROM s1.t CROSS JOIN (SELECT 1 AS id) t",
      "SELECT s1.q.id FROM (SELECT id FROM s1.t) q",
      "SELECT * FROM missing.t",
      "SELECT x.a FROM s1.t x(a,a)",
      "SELECT * FROM s1.t x(a,b,c,d)",
      "SELECT s1.t.id FROM s1.t x(key_id)",
      "SELECT * FROM s1.t FOR UPDATE OF missing",
      "SELECT * FROM s1.t AS x FOR UPDATE OF t",
      "SELECT * FROM s1.t RIGHT JOIN s2.t ON TRUE FOR UPDATE OF t",
      "SELECT * FROM s1.t FULL JOIN s2.t ON TRUE FOR UPDATE OF t",
      "SELECT * FROM s1.t LEFT JOIN s2.t ON TRUE FOR UPDATE",
      "SELECT s1.t.id FROM s1.t LEFT JOIN s2.t ON TRUE FOR UPDATE OF t FOR SHARE OF missing"] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV25 qualifiedCatalog [] query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError s!"qualified namespace or lock error accepted: {sql}")
    count := count + 1
  for sql in [
      "SELECT * FROM s1.t CROSS JOIN s2.t FOR UPDATE OF t",
      "SELECT * FROM s1.t LEFT JOIN s2.t ON TRUE FOR UPDATE OF t",
      "SELECT * FROM s2.t LEFT JOIN s1.t ON TRUE FOR SHARE OF t",
      "SELECT * FROM s1.t l RIGHT JOIN s2.t r ON TRUE FOR UPDATE OF r",
      "SELECT s1.t.id FROM s1.t FOR UPDATE OF t, t",
      "SELECT q.id FROM (SELECT s1.t.id FROM s1.t) q",
      "SELECT q.*, s2.t.id FROM (SELECT s1.t.id FROM s1.t) q JOIN s2.t USING(id)",
      "SELECT ? AS before_source, s1.t.id FROM s1.t JOIN s2.t ON ? WHERE ?"] do
    discard <| qualifiedOutput sql qualifiedCatalog
      (if sql.startsWith "SELECT ?" then "INTEGER,BOOLEAN,BOOLEAN" else "")
    count := count + 1
  for (sql, code) in [
      ("SELECT * FROM s1.legacy", "relation_schema_metadata"),
      ("SELECT s1.legacy.id FROM legacy", "relation_schema_metadata"),
      ("SELECT t.to_json FROM s1.t", "whole_row_function"),
      ("SELECT s1.t.to_json FROM s1.t", "whole_row_function"),
      ("SELECT x.to_json FROM s1.t x", "whole_row_function"),
      ("SELECT q.missing FROM (SELECT 1 AS id) q", "whole_row_function"),
      ("SELECT t FROM s1.t", "whole_row_reference"),
      ("SELECT q FROM (SELECT 1 AS id) q", "whole_row_reference"),
      ("SELECT ctid FROM s1.t", "system_column"),
      ("SELECT tableoid FROM s1.t", "system_column"),
      ("SELECT xmin FROM s1.t", "system_column"),
      ("SELECT xmax FROM s1.t", "system_column"),
      ("SELECT cmin FROM s1.t", "system_column"),
      ("SELECT cmax FROM s1.t", "system_column"),
      ("SELECT ctid FROM (SELECT 1 AS ctid) q CROSS JOIN s1.t", "system_column"),
      ("SELECT ctid FROM s1.t x(ctid) CROSS JOIN s2.t", "system_column"),
      ("SELECT * FROM pg_temp.t", "namespace_alias"),
      ("SELECT pg_temp.t.id FROM s1.t", "namespace_alias"),
      ("SELECT pg_temp.t.* FROM s1.t", "namespace_alias"),
      ("SELECT q.id FROM (SELECT id FROM s1.t) q FOR UPDATE OF q", "derived_locking")] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV25 qualifiedCatalog [] query with
    | .error (.unsupported diagnostic) => SQLean.Tests.assert (diagnostic.code == code) s!"{sql}: explicit gap"
    | _ => throw (IO.userError s!"qualified coverage boundary mislabeled: {sql}")
    count := count + 1
  for sql in [
      "SELECT ctid FROM (SELECT 1 AS ctid) q",
      "SELECT ctid FROM s1.t x(ctid)",
      "SELECT q.ctid FROM (SELECT 1 AS ctid) q CROSS JOIN s1.t",
      "SELECT tableoid FROM (SELECT 1 AS tableoid) q"] do
    let output ← qualifiedOutput sql
    SQLean.Tests.assert (output.map (·.type) == [⟨.int32, false⟩])
      "unambiguous declared scalar outputs remain available"
    count := count + 1
  for aliases in [["a"], [""]] do
    let query : Advanced.Query := {body := .select {
      items := [.all]
      source := some (.table "t" none aliases (some "s1"))}}
    match SelectContract.checkQuery .basicV25 qualifiedCatalog [] query with
    | .error (.invalid diagnostic) =>
        SQLean.Tests.assert (diagnostic.code == "table_column_aliases") "manual alias list requires relation alias"
    | _ => throw (IO.userError "column aliases without a relation alias acquired a certificate")
    count := count + 1
  let emptyColumnAlias : Advanced.Query := {body := .select {
    items := [.all]
    source := some (.table "t" (some "x") [""] (some "s1"))}}
  match SelectContract.checkQuery .basicV25 qualifiedCatalog [] emptyColumnAlias with
  | .error (.invalid diagnostic) =>
      SQLean.Tests.assert (diagnostic.code == "table_column_aliases") "empty column alias rejected"
  | _ => throw (IO.userError "empty table column alias acquired a certificate")
  count := count + 1
  let switched := qualifiedCatalog.map fun table =>
    if table.name == "t" then {table with exposeUnqualified := table.schema == some "s2"} else table
  SQLean.Tests.assert ((← qualifiedOutput "SELECT s2.t.id FROM t" switched) ==
      [⟨"id", ⟨.int64, true⟩⟩]) "explicit exposure changes the selected identity"
  count := count + 1
  let hidden := qualifiedCatalog.map fun table => {table with exposeUnqualified := false}
  discard <| qualifiedOutput "SELECT s1.t.id FROM s1.t" hidden
  let bare ← expectOk "unexposed" (Advanced.parseQuery "SELECT * FROM t")
  match SelectContract.checkQuery .basicV25 hidden [] bare with
  | .error (.invalid diagnostic) => SQLean.Tests.assert (diagnostic.code == "relation_binding") "no inferred search path"
  | _ => throw (IO.userError "unqualified exposure was guessed from qualified catalog entries")
  count := count + 2
  for catalog in [
      [qualifiedLeft, qualifiedLeft],
      [qualifiedLeft, {qualifiedRight with exposeUnqualified := true}],
      [qualifiedLeft, {qualifiedLeft with schema := none, exposeUnqualified := false}],
      [{qualifiedLeft with schema := some ""}]] do
    SQLean.Tests.assert (!(decide (SelectContract.CatalogWellFormed catalog))) "invalid exact catalog namespace"
    expectError "advanced catalog namespace check" (Advanced.checkCatalog catalog)
    match SelectContract.checkQuery .basicV25 catalog [] bare with
    | .error (.invalid diagnostic) => SQLean.Tests.assert (diagnostic.code == "invalid_environment") "invalid metadata tier"
    | _ => throw (IO.userError "invalid namespace metadata acquired a certificate")
    count := count + 1
  match SelectContract.checkQuery .basicV25
      [{qualifiedLeft with schema := some "pg_temp"}] [] bare with
  | .error (.unsupported diagnostic) =>
      SQLean.Tests.assert (diagnostic.code == "namespace_alias") "pg_temp is an alias, not a distinct physical identity"
  | _ => throw (IO.userError "pg_temp catalog acquired a physical-identity certificate")
  count := count + 1
  for (fields, schema, visible) in [
      ("", (none : Option Name), true),
      (",\"schema\":\"s1\"", some "s1", false),
      (",\"schema\":\"s1\",\"exposeUnqualified\":true", some "s1", true),
      (",\"exposeUnqualified\":false", none, false)] do
    let json := "{\"tables\":[{\"name\":\"t\",\"columns\":[{\"name\":\"id\",\"type\":\"int\"}]" ++ fields ++ "}]}"
    let catalog ← expectOk "qualified catalog JSON" (Advanced.decodeCatalogJson json)
    match catalog with
    | [table] => SQLean.Tests.assert (table.schema == schema && table.exposeUnqualified == visible) "JSON visibility defaults"
    | _ => throw (IO.userError "JSON catalog shape")
    count := count + 1
  for item in [
      Advanced.SelectItem.expression (.column none "id" (some "s1")),
      Advanced.SelectItem.all none (some "s1")] do
    let query : Advanced.Query := {body := .select {items := [item], source := some (.table "t" none [] (some "s1"))}}
    match SelectContract.checkQuery .basicV25 qualifiedCatalog [] query with
    | .error (.invalid diagnostic) => SQLean.Tests.assert (diagnostic.code == "qualified_reference_shape") "manual qualifier shape"
    | _ => throw (IO.userError "schema without a relation qualifier acquired a certificate")
    count := count + 1
  let query ← expectOk "qualified fuel" (Advanced.parseQuery "SELECT s1.t.id FROM s1.t")
  match SelectContract.checkQuery .basicV25 qualifiedCatalog [] query 0 with
  | .error (.inconclusive _) => pure ()
  | _ => throw (IO.userError "qualified fuel exhaustion must be Inconclusive")
  pure (count + 1)

def qualifiedNamesCorpusTests : IO Nat := do
  let json ← expectOk "qualified synthetic JSON"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/qualified_names/synthetic.json"))
  let records ← expectOk "qualified synthetic records" json.getArr?
  SQLean.Tests.assert (records.size == 50) "expected fifty qualified synthetic queries"
  let catalog ← expectOk "qualified catalog"
    (Advanced.decodeCatalogJson (← IO.FS.readFile "fixtures/qualified_names/schema.json"))
  let mut ids : List String := []
  let mut statements : List String := []
  for record in records do
    let id ← qualifiedField "synthetic" record "id"
    let sql ← qualifiedField id record "sql"
    SQLean.Tests.assert ((← qualifiedField id record "source_kind") == "synthetic") s!"{id}: population"
    let parameters ← qualifiedField id record "parameter_types"
    let expected ← expectOk id ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
    let expected ← expected.toList.mapM fun column => do
      let name ← qualifiedField id column "name"
      let type ← qualifiedField id column "type"
      let nullable ← expectOk id ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
      pure (name, type, nullable)
    let actual ← qualifiedOutput sql catalog parameters
    let labels := actual.map fun column =>
      (column.name, (match column.type.base with
        | .int32 => "int32" | .int64 => "int64" | .bool => "bool"
        | base => base.dataType.toSql.toLower.replace ", " ","), column.type.nullable)
    SQLean.Tests.assert (labels == expected)
      s!"{id}: exact namespace output {reprStr labels}; expected {reprStr expected}"
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (decide ids.Nodup && decide statements.Nodup) "duplicate qualified synthetic identities or SQL"
  pure records.size

/-- These authentic queries depend on external catalogs. Only exact syntax and
rendering certificates are asserted; no source schema/binding types are invented. -/
def qualifiedNamesConcreteRenderingTests : IO Nat := do
  let source ← IO.FS.readFile "fixtures/qualified_names/concrete.jsonl"
  let lines := (source.splitOn "\n").filter fun line => !line.trimAscii.toString.isEmpty
  SQLean.Tests.assert (lines.length == 50) "expected fifty unchanged qualified source queries"
  let mut ids : List String := []
  let mut statements : List String := []
  for line in lines do
    let record ← expectOk "qualified concrete JSON" (Lean.Json.parse line)
    let id ← qualifiedField "concrete" record "id"
    let sql ← qualifiedField id record "sql"
    SQLean.Tests.assert (id.startsWith "qualified_names:" && (← qualifiedField id record "raw_sql") == sql)
      s!"{id}: unchanged qualified source population"
    let query ← expectOk id (Advanced.parseQuery sql)
    let identity ← expectOk id ((RenderContract.check .identityV01 query).mapError reprStr)
    let postgres ← expectOk id ((RenderContract.check .postgres16V01 query).mapError reprStr)
    have _identity := identity.roundTrip
    have _postgres := postgres.roundTrip
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (decide ids.Nodup && decide statements.Nodup) "duplicate qualified source identities or SQL"
  pure ids.length

end SQLean.Tests
