import SQLean.Assurance
import SQLean.SchemaJson
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

namespace SQLean.Tests
open SelectContract

private def cteColumns : List OutputColumn := [⟨"x", ⟨.int32, false⟩⟩]
private def cteBody : Advanced.Query :=
  {body := .select {items := [.expression (.literal (.int 1)) (some "x")]}}

/-- A body derivation, without invoking the executable checker. -/
private theorem cteBody_valid :
    QueryValid .basicV30 [] [] [] cteBody cteColumns [] := by
  apply QueryValid.basic (cteUses := []) (visible := []) (by decide) .nil
    (scope := .empty) (sourceUses := []) (selectUses := []) (whereUses := [])
    (orderUses := []) (limitUses := []) (offsetUses := [])
  · exact .empty
  · exact .expression (.int (by decide)) (by decide) .nil
  · decide
  · decide
  · exact .absent
  · exact .nil
  · exact .absent
  · exact .absent
  · exact .nil
  · rfl
  · rfl
  · rfl

private def cteDefinition : Advanced.CTE := ⟨"c", cteBody, []⟩
private def cteEnvironment : CTEEnv := [⟨"c", cteColumns⟩]
private def cteScope : Scope := .ofCTE "c" none cteColumns
private def cteQuery : Advanced.Query := {
  ctes := [cteDefinition]
  body := .select {items := [.all], source := some (.table "c")} }

private theorem cteDefinitions_valid :
    CTEsValid .basicV30 [] [] [] [cteDefinition] cteEnvironment [] :=
  .cons (head := cteDefinition) (output := cteColumns) cteBody_valid (by decide) .nil

private theorem cteReference_valid :
    SourceValid .basicV30 [] [] cteEnvironment (some (.table "c")) cteScope [] :=
  .cte (binding := ⟨"c", cteColumns⟩) (alias := none) rfl (by simp) (by decide) (Or.inl rfl)

private theorem cteQuery_valid : SelectValid .basicV30 [] [] cteQuery cteColumns := by
  apply SelectValid.certified (uses := [])
  · decide
  · decide
  · apply QueryValid.basic (cteUses := []) (visible := cteEnvironment)
      (by decide) cteDefinitions_valid
      (scope := cteScope) (sourceUses := []) (selectUses := []) (whereUses := [])
      (orderUses := []) (limitUses := []) (offsetUses := [])
    · exact cteReference_valid
    · exact .all (qualifier := none) rfl (by decide) .nil
    · decide
    · decide
    · exact .absent
    · exact .nil
    · exact .absent
    · exact .absent
    · exact .nil
    · rfl
    · rfl
    · rfl
  · decide

example : SelectValid .basicV30 [] [] (RenderContract.translateParameters cteQuery) cteColumns :=
  RenderContract.translateParameters_valid cteQuery_valid

example : (Certificate.mk cteColumns cteQuery_valid).outputCatalog = [] := rfl
example : LockTargets cteScope [] := by decide
example : ¬ LockTargets cteScope ["c"] := by decide
example : cteScope.relations.filter (fun r => r.matches "c" (some "public")) = [] := by decide

private def cteField (record : Lean.Json) (field : String) : IO String :=
  expectOk field ((record.getObjVal? field) >>= Lean.Json.getStr?)

private def cteExpected (record : Lean.Json) : IO (List OutputColumn) := do
  let columns ← expectOk "output columns" ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
  columns.toList.mapM fun column => do
    let name ← cteField column "name"
    let label ← cteField column "type"
    let nullable ← expectOk name ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
    let base ← match label with
      | "int32" => pure ScalarType.int32
      | "int32[]" => pure (.array .int32)
      | "bool" => pure .bool
      | "text" => pure .text
      | other => do
          let declaration ← expectOk name (Advanced.parseDataType other)
          match concreteType declaration with
          | some base => pure base
          | none => throw (IO.userError s!"unsupported fixture output declaration {other}")
    pure (OutputColumn.mk name ⟨base, nullable⟩)

private def cteCertificate (query : Advanced.Query) (catalog : Advanced.Catalog := [])
    (params : ParameterEnv := []) : IO (List OutputColumn) := do
  let certificate ← expectOk "CTE complete query"
    ((SelectContract.checkQuery .basicV30 catalog params query).mapError reprStr)
  have _catalog : certificate.outputCatalog = catalog := certificate.catalog_unchanged
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let identity ← expectOk "CTE identity" ((RenderContract.check .identityV01 query).mapError reprStr)
  let postgres ← expectOk "CTE PostgreSQL" ((RenderContract.check .postgres16V01 query).mapError reprStr)
  have _identity := identity.roundTrip
  have _postgres := postgres.roundTrip
  pure certificate.output

private def cteOutput (sql : String) (catalog : Advanced.Catalog := [])
    (declarations : String := "") : IO (List OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let params ← expectOk sql (Assurance.parseContractParameterTypes declarations)
  cteCertificate query catalog params

def cteContractTests : IO Nat := do
  let catalog ← expectOk "CTE test catalog"
    (Advanced.decodeCatalogJson (← IO.FS.readFile "fixtures/cte_contract/schema.json"))
  let valid : List (String × List OutputColumn) := [
    ("WITH c AS (SELECT 1 AS x UNION SELECT 2) SELECT x FROM c", cteColumns),
    ("WITH c AS (SELECT NULL AS x) SELECT x FROM c", [⟨"x", ⟨.text, true⟩⟩]),
    ("WITH c AS (SELECT 1 AS x) SELECT * FROM (WITH c AS (SELECT x+1 AS x FROM c) SELECT x FROM c) d",
      cteColumns),
    ("WITH a AS (SELECT 1 AS x), b AS (SELECT x AS y FROM a) SELECT y FROM b",
      [⟨"y", ⟨.int32, false⟩⟩]),
    ("WITH c(x,x) AS (SELECT 1,2) SELECT c.* FROM c", cteColumns ++ cteColumns),
    ("WITH c AS (SELECT 1 AS a, 2 AS b) SELECT d.x,d.b FROM c d(x)",
      [⟨"x", ⟨.int32, false⟩⟩, ⟨"b", ⟨.int32, false⟩⟩]),
    ("WITH c AS (SELECT 1 AS ctid) SELECT ctid FROM c", [⟨"ctid", ⟨.int32, false⟩⟩]),
    ("WITH c AS (SELECT 1 AS x) SELECT x FROM c FOR UPDATE", cteColumns),
    ("WITH c AS (SELECT DISTINCT 1 AS x) SELECT x FROM c FOR SHARE", cteColumns)]
  for (sql, expected) in valid do
    SQLean.Tests.assert ((← cteOutput sql catalog) == expected) s!"exact CTE metadata: {sql}"
  let invalid := [
    "WITH c AS (SELECT 1), c AS (SELECT 2) SELECT 1",
    "WITH c AS (SELECT x FROM c) SELECT 1",
    "WITH a AS (SELECT x FROM b), b AS (SELECT 1 AS x) SELECT * FROM a",
    "WITH c(a,b) AS (SELECT 1) SELECT 1",
    "WITH c AS (SELECT 1 AS x) SELECT * FROM c d(a,b)",
    "WITH c AS (SELECT 1 AS x,2 AS x) SELECT x FROM c",
    "WITH c AS (SELECT 1 AS x) SELECT c.x FROM c d",
    "WITH c AS (SELECT 1 AS x) SELECT ctid FROM c",
    "WITH c AS (SELECT 1 AS x) SELECT xmin FROM c",
    "WITH c AS (SELECT 1 AS x) SELECT x FROM c FOR UPDATE OF c",
    "WITH c AS (SELECT 1 AS x) SELECT x FROM c d FOR UPDATE OF d",
    "WITH unused AS (SELECT 1 + TRUE) SELECT 1",
    "WITH unused AS (SELECT missing FROM items) SELECT 1",
    "WITH unused AS (SELECT DISTINCT id FROM items FOR UPDATE) SELECT 1",
    "WITH unused AS (SELECT id FROM items FOR UPDATE OF absent) SELECT 1"]
  for sql in invalid do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV30 catalog [] query with
    | .error (.invalid _) => pure ()
    | result => throw (IO.userError s!"CTE Invalid expected: {sql}: {reprStr (result.map (fun _ => ()))}")
  let unsupported := [
    "WITH RECURSIVE c AS (SELECT 1 AS x) SELECT x FROM c",
    "WITH c AS (SELECT COUNT(*) AS x FROM items) SELECT x FROM c",
    "WITH c AS (SELECT 1 AS x) SELECT c FROM c",
    "WITH c AS (SELECT 1 AS x) SELECT d FROM c d",
    "WITH c AS (SELECT 1 AS x) SELECT c.unknown FROM c",
    "WITH c AS (SELECT 1 AS x) SELECT (SELECT x FROM c)",
    "WITH c AS (SELECT 1 AS x) SELECT * FROM LATERAL (SELECT x FROM c) d",
    "WITH c AS (SELECT 1 AS x) SELECT c.x FROM (SELECT 1 AS y) d LEFT JOIN c ON FALSE FOR UPDATE OF d",
    "WITH unused AS (SELECT i.id FROM items i LEFT JOIN labels l ON FALSE FOR UPDATE OF l) SELECT 1",
    "WITH used AS (SELECT i.id FROM items i LEFT JOIN labels l ON FALSE FOR UPDATE OF l) SELECT * FROM used"]
  for sql in unsupported do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV30 catalog [] query with
    | .error (.unsupported _) => pure ()
    | result => throw (IO.userError s!"CTE Unsupported expected: {sql}: {reprStr (result.map (fun _ => ()))}")
  let parameterCases := [
    ("WITH unused AS (SELECT ? AS x) SELECT ? AS y", "int,int", [1,2]),
    ("WITH c AS (SELECT ? AS x) SELECT a.x,b.x FROM c a CROSS JOIN c b", "int", [1]),
    ("WITH c AS (SELECT ? AS x) SELECT ? AS y FROM c WHERE x > ?", "int,int,int", [1,2,3]),
    ("WITH c AS (SELECT $2 AS x) SELECT $1 AS y FROM c WHERE x > $2", "int,int", [2,1,2])]
  for (sql, declarations, indices) in parameterCases do
    let query ← expectOk sql (Advanced.parseQuery sql)
    let params ← expectOk sql (Assurance.parseContractParameterTypes declarations)
    let _ ← cteCertificate query catalog params
    SQLean.Tests.assert ((Advanced.queryParameters 1024 query).map (fun p => match p with | .numbered n | .anonymous n => n) == indices)
      s!"definition occurrences are counted once before main query: {sql}"
  let lexical ← expectOk "lexical mutation" (Advanced.parseQuery
    "WITH c AS (SELECT ? AS x) SELECT ? AS y FROM c")
  let params ← expectOk "lexical declarations" (Assurance.parseContractParameterTypes "int,int")
  let duplicateDefinitions := lexical.ctes ++
    lexical.ctes.map (fun definition => {definition with name := "other"})
  let missingFirst := lexical.ctes.map (fun definition => {definition with query := cteBody})
  for changed in [{lexical with ctes := duplicateDefinitions}, {lexical with ctes := missingFirst}] do
    match SelectContract.checkQuery .basicV30 [] params changed with
    | .error (.invalid diagnostic) =>
        SQLean.Tests.assert (diagnostic.code == "parameter_notation")
          "definition insertion/removal cannot silently restart anonymous numbering"
    | _ => throw (IO.userError "malformed global definition parameter order was certified")
  for changed in [
      {cteQuery with ctes := [{cteDefinition with name := ""}]},
      {cteQuery with ctes := [{cteDefinition with columns := [""]}]}] do
    match SelectContract.checkQuery .basicV30 [] [] changed with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError "malformed unused definition metadata was certified")
  let incomplete ← expectOk "resource test" (Advanced.parseQuery
    "WITH a AS (SELECT 1 AS x), b AS (SELECT x FROM a) SELECT * FROM b")
  for fuel in [0,1,2] do
    match SelectContract.checkQuery .basicV30 catalog [] incomplete fuel with
    | .error (.inconclusive _) => pure ()
    | _ => throw (IO.userError "CTE resource exhaustion must remain Inconclusive")
  pure (valid.length + invalid.length + unsupported.length + parameterCases.length + 7)

def cteCorpusTests : IO Nat := do
  let records ← expectOk "CTE authored fixtures"
    ((Lean.Json.parse (← IO.FS.readFile "fixtures/cte_contract/synthetic.json")) >>= Lean.Json.getArr?)
  SQLean.Tests.assert (records.size == 50) "exactly fifty authored CTE queries"
  let catalog ← expectOk "CTE authored catalog"
    (Advanced.decodeCatalogJson (← IO.FS.readFile "fixtures/cte_contract/schema.json"))
  let mut ids : List String := []
  let mut sqls : List String := []
  for record in records do
    let id ← cteField record "id"
    let sql ← cteField record "sql"
    SQLean.Tests.assert ((← cteField record "source_kind") == "synthetic" &&
      (← cteField record "catalogFile") == "fixtures/cte_contract/schema.json")
      s!"{id}: exact authored fixture population"
    let params ← expectOk id (Assurance.parseContractParameterTypes (← cteField record "parameter_types"))
    let query ← expectOk id (Advanced.parseQuery sql)
    SQLean.Tests.assert (!query.ctes.isEmpty && !query.recursive) s!"{id}: nonrecursive WITH required"
    let output ← cteCertificate query catalog params
    SQLean.Tests.assert (output == (← cteExpected record)) s!"{id}: exact ordered CTE output"
    ids := id :: ids
    sqls := sql :: sqls
  SQLean.Tests.assert (decide ids.Nodup && decide sqls.Nodup) "duplicate authored CTE IDs/SQL"
  pure records.size

private def cteSourceRegistry : List (String × List OutputColumn) :=
  let pg := "cte_contract:postgres:src/test/regress/sql/with.sql:statement-"
  let sqlc := "cte_contract:sqlc:internal/endtoend/testdata/"
  let mz := "cte_contract:materialize:test/sqllogictest/"
  let ints := fun names => names.map (fun name => OutputColumn.mk name ⟨.int32, false⟩)
  [(pg ++ "0", ints ["x","y","x","y"]),
   (pg ++ "148", ints ["foo"]), (pg ++ "297", ints ["x"]),
   (sqlc ++ "cte_join_self/postgresql/pgx/query.sql:statement-0",
     [⟨"id1", ⟨.text, false⟩⟩, ⟨"id2", ⟨.text, false⟩⟩]),
   (sqlc ++ "cte_select_one/postgresql/pgx/query.sql:statement-0", ints ["foo"]),
   (mz ++ "cte.slt:sqllogic-query-260", ints ["v"]),
   (mz ++ "cte.slt:sqllogic-query-273", ints ["v","v"]),
   (mz ++ "cte.slt:sqllogic-query-287", ints ["?column?"]),
   (mz ++ "cockroach/with.slt:sqllogic-query-80",
     [⟨"a", ⟨.bool, false⟩⟩, ⟨"b", ⟨.bool, false⟩⟩]),
   (mz ++ "cockroach/with.slt:sqllogic-query-86",
     [⟨"a", ⟨.bool, false⟩⟩, ⟨"b", ⟨.bool, false⟩⟩]),
   (mz ++ "cockroach/with.slt:sqllogic-query-109", ints ["?column?"]),
   (mz ++ "cockroach/with.slt:sqllogic-query-200", ints ["?column?"]),
   ("cte_contract:duckdb:test/sql/cte/test_cte.test:sqllogic-query-61", ints ["zzz","y"])]

def cteConcreteContractTests : IO Nat := do
  let registry ← expectOk "fixed CTE source metadata"
    ((Lean.Json.parse (← IO.FS.readFile "fixtures/cte_contract/source_contracts.json")) >>= Lean.Json.getArr?)
  let registry ← registry.toList.mapM fun record => do
    pure ((← cteField record "id"), (← cteExpected record))
  SQLean.Tests.assert (registry == cteSourceRegistry && registry.length == 13 &&
    (registry.map (fun row => row.2.length)).sum == 21 && decide (registry.map Prod.fst).Nodup)
    "independently registered closed CTE identities and 21 ordered outputs"
  let source ← IO.FS.readFile "fixtures/cte_contract/concrete.jsonl"
  let lines := (source.splitOn "\n").filter (fun line => !line.trimAscii.toString.isEmpty)
  SQLean.Tests.assert (lines.length == 50) "exactly fifty unchanged CTE sources"
  let mut ids : List String := []
  let mut sqls : List String := []
  let mut certified := 0
  for line in lines do
    let record ← expectOk "CTE source" (Lean.Json.parse line)
    let id ← cteField record "id"
    let sql ← cteField record "sql"
    SQLean.Tests.assert ((← cteField record "raw_sql") == sql &&
      (← expectOk id (record.getObjVal? "parameter_types")) == Lean.Json.null)
      s!"{id}: preserve original source and unspecified declarations"
    let query ← expectOk id (Advanced.parseQuery sql)
    SQLean.Tests.assert (!query.ctes.isEmpty && !query.recursive) s!"{id}: fixed WITH population"
    let identity ← expectOk id ((RenderContract.check .identityV01 query).mapError reprStr)
    let postgres ← expectOk id ((RenderContract.check .postgres16V01 query).mapError reprStr)
    have _identity := identity.roundTrip
    have _postgres := postgres.roundTrip
    match cteSourceRegistry.lookup id with
    | none => pure ()
    | some expected =>
        SQLean.Tests.assert ((Advanced.queryParameters 1024 query).isEmpty)
          s!"{id}: no fabricated parameter assumptions"
        SQLean.Tests.assert ((← cteCertificate query) == expected) s!"{id}: closed exact source output"
        certified := certified + 1
    ids := id :: ids
    sqls := sql :: sqls
  SQLean.Tests.assert (certified == 13 && decide ids.Nodup && decide sqls.Nodup &&
    (cteSourceRegistry.map Prod.fst).all ids.contains)
    "fixed source eligibility must be covered exactly once"
  pure certified

end SQLean.Tests
