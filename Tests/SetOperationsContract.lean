import SQLean.Assurance
import SQLean.SchemaJson
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

namespace SQLean.Tests
open SelectContract

private def nullArm : Advanced.Query :=
  {body := .select {items := [.expression .null]}}
private def integerArm : Advanced.Query :=
  {body := .select {items := [.expression (.literal (.int 1))]}}

/-- Unknown input evidence is distinct from complete SELECT's TEXT output. -/
private theorem nullArm_valid :
    SetOperandValid .basicV30 [] [] [] nullArm [⟨"?column?", .unknown true⟩] [] := by
  apply SetOperandValid.basic (cteUses := []) (visible := []) (by decide) .nil
    (scope := .empty) (sourceUses := []) (selectUses := []) (whereUses := [])
    (orderUses := []) (limitUses := []) (offsetUses := [])
    (output := [⟨"?column?", ⟨.text, true⟩⟩]) (pending := [⟨"?column?", .unknown true⟩])
  · exact .empty
  · exact .expression .null (by simp) .nil
  · exact .expression .null (by simp) .nil
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

private theorem integerArm_valid :
    SetOperandValid .basicV30 [] [] [] integerArm
      [⟨"?column?", .known ⟨.int32, false⟩⟩] [] := by
  apply SetOperandValid.basic (cteUses := []) (visible := []) (by decide) .nil
    (scope := .empty) (sourceUses := []) (selectUses := []) (whereUses := [])
    (orderUses := []) (limitUses := []) (offsetUses := [])
    (output := [⟨"?column?", ⟨.int32, false⟩⟩])
    (pending := [⟨"?column?", .known ⟨.int32, false⟩⟩])
  · exact .empty
  · exact .expression (.int (by decide)) (by simp) .nil
  · exact .expression (.int (by decide)) (by simp) .nil
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

private def nullUnion : Advanced.Query := {body := .set .union true nullArm integerArm}
private theorem nullUnion_valid :
    SelectValid .basicV30 [] [] nullUnion [⟨"?column?", ⟨.int32, true⟩⟩] := by
  apply SelectValid.certified (uses := [])
  · decide
  · decide
  · exact .set (cteUses := []) (visible := []) (by decide) .nil
      nullArm_valid integerArm_valid rfl rfl
      (.cons (by decide) (by decide) (by decide) (by decide) .nil)
      (by decide) .nil .absent .absent
  · decide

example : SelectValid .basicV30 [] [] (RenderContract.translateParameters nullUnion)
    [⟨"?column?", ⟨.int32, true⟩⟩] :=
  RenderContract.translateParameters_valid nullUnion_valid

example : (Certificate.mk _ nullUnion_valid).outputCatalog = [] := rfl

private def setField (record : Lean.Json) (field : String) : IO String :=
  expectOk field ((record.getObjVal? field) >>= Lean.Json.getStr?)

private def setType (label : String) : IO ScalarType :=
  match label with
  | "int32" => pure .int32
  | "int64" => pure .int64
  | "bool" => pure .bool
  | "bpchar" => pure (.char [])
  | other => do
    let declaration ← expectOk other (Advanced.parseDataType (other.replace "bpchar" "char"))
    match concreteType declaration with
    | some base => pure base
    | none => throw (IO.userError s!"unregistered exact set output type {other}")

private def setExpected (record : Lean.Json) : IO (List OutputColumn) := do
  let columns ← expectOk "set output columns" ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
  columns.toList.mapM fun column => do
    let name ← setField column "name"
    let base ← setType (← setField column "type")
    let nullable ← expectOk name ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
    pure ⟨name, ⟨base, nullable⟩⟩

private def setCertificate (query : Advanced.Query) (catalog : Advanced.Catalog := [])
    (params : ParameterEnv := []) : IO (List OutputColumn) := do
  let certificate ← expectOk "complete set query"
    ((SelectContract.checkQuery .basicV30 catalog params query).mapError reprStr)
  have _catalog := certificate.catalog_unchanged
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let identity ← expectOk "set identity" ((RenderContract.check .identityV01 query).mapError reprStr)
  let postgres ← expectOk "set PostgreSQL" ((RenderContract.check .postgres16V01 query).mapError reprStr)
  have _identity := identity.roundTrip
  have _postgres := postgres.roundTrip
  pure certificate.output

private def setOutput (sql : String) : IO (List OutputColumn) := do
  setCertificate (← expectOk sql (Advanced.parseQuery sql))

def setOperationsContractTests : IO Nat := do
  let valid : List (String × List OutputColumn) := [
    ("SELECT NULL AS x UNION SELECT 1", [⟨"x", ⟨.int32, true⟩⟩]),
    ("SELECT '1' AS x INTERSECT SELECT 1", [⟨"x", ⟨.int32, false⟩⟩]),
    ("SELECT 'bad' AS x UNION SELECT 1", [⟨"x", ⟨.int32, false⟩⟩]),
    ("SELECT NULL AS x UNION ALL (SELECT NULL UNION SELECT 1)", [⟨"x", ⟨.int32, true⟩⟩]),
    ("(SELECT NULL AS x LIMIT 1) UNION SELECT 1", [⟨"x", ⟨.int32, true⟩⟩]),
    ("(SELECT NULL AS x ORDER BY 1+1) UNION SELECT 1", [⟨"x", ⟨.int32, true⟩⟩]),
    ("(SELECT NULL AS x,NULL AS y ORDER BY 1) UNION SELECT NULL,1",
      [⟨"x", ⟨.text, true⟩⟩, ⟨"y", ⟨.int32, true⟩⟩]),
    ("(SELECT NULL AS x,NULL AS x ORDER BY x) UNION ALL SELECT NULL,1",
      [⟨"x", ⟨.text, true⟩⟩, ⟨"x", ⟨.int32, true⟩⟩]),
    ("SELECT 1 AS x,1 AS x ORDER BY x", [⟨"x", ⟨.int32, false⟩⟩, ⟨"x", ⟨.int32, false⟩⟩]),
    ("SELECT CAST(1 AS NUMERIC(8,2)) AS x UNION SELECT CAST(2 AS NUMERIC(8,2))",
      [⟨"x", ⟨.numeric [8,2], false⟩⟩]),
    ("SELECT CAST(1 AS NUMERIC(8,2)) AS x UNION SELECT NULL", [⟨"x", ⟨.numeric [], true⟩⟩]),
    ("SELECT CAST('a' AS CHAR(3)) AS x UNION ALL SELECT CAST('b' AS TEXT)", [⟨"x", ⟨.char [], false⟩⟩]),
    ("SELECT CAST('a' AS TEXT) AS x UNION ALL SELECT CAST('b' AS CHAR(3))", [⟨"x", ⟨.text, false⟩⟩]),
    ("SELECT ARRAY[1] AS x UNION SELECT ARRAY[CAST(2 AS BIGINT)]", [⟨"x", ⟨.array .int64, false⟩⟩]),
    ("WITH c AS (SELECT NULL UNION SELECT 1) SELECT * FROM c", [⟨"?column?", ⟨.int32, true⟩⟩]),
    ("SELECT * FROM (SELECT 1 AS x FOR UPDATE) d UNION SELECT 2", [⟨"x", ⟨.int32, false⟩⟩]),
    ("WITH c AS (SELECT 1 AS x UNION SELECT 2) SELECT * FROM c FOR UPDATE", [⟨"x", ⟨.int32, false⟩⟩])]
  for (sql, output) in valid do
    SQLean.Tests.assert ((← setOutput sql) == output) s!"set exact metadata {sql}"
  let invalid := [
    "SELECT NULL UNION SELECT NULL UNION SELECT 1",
    "(SELECT NULL AS x ORDER BY 1) UNION SELECT 1",
    "(SELECT NULL AS x ORDER BY x) UNION SELECT 1",
    "SELECT DISTINCT NULL AS x UNION SELECT 1",
    "SELECT * FROM (SELECT NULL AS x) d UNION SELECT 1",
    "WITH c AS (SELECT NULL AS x) SELECT x FROM c UNION SELECT 1",
    "SELECT 1 UNION SELECT 1,2", "SELECT TRUE UNION SELECT 1",
    "SELECT 1 AS x UNION SELECT 2 AS y ORDER BY y",
    "SELECT 1 AS x UNION SELECT 2 ORDER BY x+1",
    "SELECT 1 AS x UNION SELECT 2 ORDER BY +1",
    "SELECT 1 AS x UNION SELECT 2 ORDER BY NULL",
    "SELECT 1 AS x UNION SELECT 2 ORDER BY 0",
    "SELECT 1 AS x UNION SELECT 2 ORDER BY 2",
    "SELECT 1 AS x UNION SELECT 2 ORDER BY 2147483648",
    "SELECT 1 AS x,1 AS x UNION SELECT 2,2 ORDER BY x",
    "(SELECT 1 FOR UPDATE) UNION SELECT 2",
    "SELECT 1 UNION (SELECT 2 FOR SHARE)",
    "(SELECT 1 UNION SELECT 2) FOR UPDATE"]
  for sql in invalid do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV30 [] [] query with
    | .error (.invalid _) => pure ()
    | result => throw (IO.userError s!"set Invalid expected {sql}: {reprStr (result.map (fun _ => ()))}")
  let unsupported := [
    "SELECT 1 AS x,CAST(1 AS INTEGER) AS x ORDER BY x",
    "(SELECT 1 AS x,2 AS x ORDER BY x) UNION SELECT 1,2",
    "WITH RECURSIVE c AS (SELECT 1 UNION SELECT 2) SELECT * FROM c",
    "SELECT COUNT(*) UNION SELECT 1",
    "SELECT (SELECT 1) UNION SELECT 2"]
  for sql in unsupported do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV30 [] [] query with
    | .error (.unsupported _) => pure ()
    | result => throw (IO.userError s!"set Unsupported expected {sql}: {reprStr (result.map (fun _ => ()))}")
  let mut count := valid.length + invalid.length + unsupported.length
  for op in ["UNION ALL","UNION","INTERSECT ALL","INTERSECT","EXCEPT ALL","EXCEPT"] do
    for type in ["JSON","JSON[]"] do
      let sql := s!"SELECT NULL::{type} AS x {op} SELECT NULL::{type}"
      let query ← expectOk sql (Advanced.parseQuery sql)
      if op == "UNION ALL" then
        SQLean.Tests.assert ((← setCertificate query) == [⟨"x", ⟨← setType type, true⟩⟩]) sql
      else
        match SelectContract.checkQuery .basicV30 [] [] query with
        | .error (.invalid _) => pure ()
        | result => throw (IO.userError s!"analysis-time element equality {sql}: {reprStr (result.map (fun _ => ()))}")
      count := count + 1
  for (sql, declarations, indices) in [
      ("WITH c AS (SELECT ? AS x) SELECT ? AS v UNION ALL SELECT ? LIMIT ? OFFSET ?", "int,int,int,int,int", [1,2,3,4,5]),
      ("(SELECT ? AS v ORDER BY ? LIMIT ?) UNION ALL (SELECT ? AS v OFFSET ?)", "int,int,int,int,int", [1,2,3,4,5]),
      ("WITH c AS (SELECT $3 AS x) SELECT $2 AS v FROM c UNION SELECT $1 FROM c OFFSET $4 LIMIT $5", "int,int,int,int,int", [3,2,1,4,5])] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    let params ← expectOk sql (Assurance.parseContractParameterTypes declarations)
    let _ ← setCertificate query [] params
    SQLean.Tests.assert ((Advanced.queryParameters 1024 query).map (fun p => match p with | .numbered n | .anonymous n => n) == indices)
      "set lexical uses count definitions once and preserve arm/order/pagination order"
    count := count + 1
  for value in ["NULL","'a'"] do
    for ordering in ["x","x,2","1,2,x","2,1,x"] do
      let sql := s!"SELECT {value} AS x,{value} AS x ORDER BY {ordering}"
      let _ ← setOutput sql
      let _ ← setOutput s!"({sql}) UNION ALL SELECT NULL,NULL"
      count := count + 2
    for ordering in ["1,x","2,x","x,x"] do
      let sql := s!"SELECT {value} AS x,{value} AS x ORDER BY {ordering}"
      for statement in [sql, s!"({sql}) UNION ALL SELECT NULL,NULL"] do
        let query ← expectOk statement (Advanced.parseQuery statement)
        match SelectContract.checkQuery .basicV30 [] [] query with
        | .error (.invalid diagnostic) =>
          SQLean.Tests.assert (diagnostic.code == "ambiguous_output") "sequential unknown target resolution"
        | result => throw (IO.userError s!"sequential sort ambiguity {statement}: {reprStr (result.map (fun _ => ()))}")
        count := count + 1
  pure count

def setOperationsCorpusTests : IO Nat := do
  let catalog ← expectOk "set catalog" (Advanced.decodeCatalogJson
    (← IO.FS.readFile "fixtures/set_operations/schema.json"))
  let records ← expectOk "authored set cases"
    ((Lean.Json.parse (← IO.FS.readFile "fixtures/set_operations/synthetic.json")) >>= Lean.Json.getArr?)
  SQLean.Tests.assert (records.size == 150) "exactly 150 authored set queries"
  let mut ids : List String := []
  let mut sqls : List String := []
  let mut factors : List String := []
  for record in records do
    let id ← setField record "id"
    let sql ← setField record "sql"
    let factor ← setField record "factor"
    SQLean.Tests.assert ((← setField record "source_kind") == "synthetic" &&
      (← setField record "catalogFile") == "fixtures/set_operations/schema.json") id
    let params ← expectOk id (Assurance.parseContractParameterTypes (← setField record "parameter_types"))
    let query ← expectOk id (Advanced.parseQuery sql)
    SQLean.Tests.assert ((← setCertificate query catalog params) == (← setExpected record))
      s!"{id}: exact set type, modifier, label and nullability"
    ids := id :: ids
    sqls := sql :: sqls
    factors := factor :: factors
  SQLean.Tests.assert (decide ids.Nodup && decide sqls.Nodup &&
    ["union","intersect","except"].all (fun factor => (factors.filter (· == factor)).length == 50))
    "fixed 50 authored cases per set factor"
  pure records.size

private def setSourceRegistry : List (String × String × List OutputColumn) := [
  ("union", "union:postgres:src/test/regress/sql/subselect.sql:statement-6", [⟨"?column?", ⟨.int32, false⟩⟩]),
  ("union", "union:postgres:src/test/regress/sql/union.sql:statement-0", [⟨"two", ⟨.int32, false⟩⟩]),
  ("union", "union:postgres:src/test/regress/sql/union.sql:statement-1", [⟨"one", ⟨.int32, false⟩⟩]),
  ("union", "union:postgres:src/test/regress/sql/union.sql:statement-2", [⟨"two", ⟨.int32, false⟩⟩]),
  ("union", "union:postgres:src/test/regress/sql/union.sql:statement-3", [⟨"two", ⟨.int32, false⟩⟩]),
  ("union", "union:postgres:src/test/regress/sql/union.sql:statement-4", [⟨"three", ⟨.int32, false⟩⟩]),
  ("union", "union:postgres:src/test/regress/sql/union.sql:statement-5", [⟨"two", ⟨.int32, false⟩⟩]),
  ("union", "union:postgres:src/test/regress/sql/union.sql:statement-6", [⟨"three", ⟨.int32, false⟩⟩]),
  ("union", "union:postgres:src/test/regress/sql/union.sql:statement-7", [⟨"two", ⟨.numeric [], false⟩⟩]),
  ("union", "union:postgres:src/test/regress/sql/union.sql:statement-8", [⟨"two", ⟨.numeric [], false⟩⟩]),
  ("union", "union:postgres:src/test/regress/sql/union.sql:statement-9", [⟨"two", ⟨.numeric [], false⟩⟩]),
  ("union", "union:postgres:src/test/regress/sql/union.sql:statement-10", [⟨"one", ⟨.doublePrecision, false⟩⟩]),
  ("union", "union:postgres:src/test/regress/sql/union.sql:statement-11", [⟨"two", ⟨.numeric [], false⟩⟩]),
  ("union", "union:postgres:src/test/regress/sql/union.sql:statement-12", [⟨"two", ⟨.doublePrecision, false⟩⟩]),
  ("union", "union:postgres:src/test/regress/sql/union.sql:statement-13", [⟨"three", ⟨.numeric [], false⟩⟩]),
  ("union", "union:postgres:src/test/regress/sql/union.sql:statement-14", [⟨"two", ⟨.doublePrecision, false⟩⟩]),
  ("union", "union:postgres:src/test/regress/sql/union.sql:statement-15", [⟨"three", ⟨.numeric [], false⟩⟩]),
  ("union", "union:postgres:src/test/regress/sql/union.sql:statement-16", [⟨"two", ⟨.numeric [], false⟩⟩]),
  ("union", "union:postgres:src/test/regress/sql/union.sql:statement-167", [⟨"t", ⟨.int32, false⟩⟩, ⟨"x", ⟨.int32, false⟩⟩]),
  ("union", "union:postgres:src/test/regress/sql/with.sql:statement-155", [⟨"x", ⟨.int32, false⟩⟩]),
  ("union", "union:duckdb:test/sql/setops/test_setops.test:sqllogic-query-5", [⟨"?column?", ⟨.int32, false⟩⟩]),
  ("union", "union:duckdb:test/sql/setops/test_setops.test:sqllogic-query-11", [⟨"?column?", ⟨.int32, false⟩⟩, ⟨"?column?", ⟨.text, false⟩⟩]),
  ("union", "union:duckdb:test/sql/setops/test_setops.test:sqllogic-query-17", [⟨"?column?", ⟨.int32, false⟩⟩, ⟨"?column?", ⟨.text, false⟩⟩]),
  ("union", "union:duckdb:test/sql/setops/test_setops.test:sqllogic-query-24", [⟨"?column?", ⟨.int32, false⟩⟩, ⟨"?column?", ⟨.text, false⟩⟩]),
  ("union", "union:duckdb:test/sql/setops/test_setops.test:sqllogic-query-33", [⟨"?column?", ⟨.text, true⟩⟩]),
  ("union", "union:duckdb:test/sql/setops/test_setops.test:sqllogic-query-77", [⟨"?column?", ⟨.text, true⟩⟩]),
  ("union", "union:duckdb:test/sql/setops/test_setops.test:sqllogic-query-84", [⟨"?column?", ⟨.int32, false⟩⟩]),
  ("union", "union:duckdb:test/sql/setops/test_setops.test:sqllogic-query-89", [⟨"?column?", ⟨.int32, false⟩⟩, ⟨"?column?", ⟨.text, false⟩⟩]),
  ("union", "union:duckdb:test/sql/setops/test_setops.test:sqllogic-query-103", [⟨"?column?", ⟨.int32, false⟩⟩, ⟨"?column?", ⟨.text, false⟩⟩]),
  ("union", "union:duckdb:test/sql/setops/test_setops.test:sqllogic-query-109", [⟨"?column?", ⟨.int32, false⟩⟩, ⟨"?column?", ⟨.text, false⟩⟩]),
  ("union", "union:duckdb:test/sql/setops/test_union_by_name.test:sqllogic-query-147", [⟨"c", ⟨.int32, false⟩⟩]),
  ("union", "union:duckdb:test/sql/setops/setops_pushdown.test:sqllogic-query-37", [⟨"?column?", ⟨.int32, false⟩⟩]),
  ("union", "union:duckdb:test/sql/setops/setops_pushdown.test:sqllogic-query-43", [⟨"?column?", ⟨.int32, false⟩⟩]),
  ("union", "union:duckdb:test/sql/setops/setops_pushdown.test:sqllogic-query-48", [⟨"?column?", ⟨.int32, false⟩⟩]),
  ("union", "union:duckdb:test/sql/setops/test_union_type_cast.test:sqllogic-query-6", [⟨"?column?", ⟨.numeric [], false⟩⟩]),
  ("union", "union:duckdb:test/sql/setops/test_union_type_cast.test:sqllogic-query-11", [⟨"?column?", ⟨.numeric [], false⟩⟩]),
  ("union", "union:duckdb:test/sql/setops/test_union_type_cast.test:sqllogic-query-18", [⟨"?column?", ⟨.int32, false⟩⟩]),
  ("union", "union:duckdb:test/sql/setops/test_union_type_cast.test:sqllogic-query-23", [⟨"?column?", ⟨.numeric [], false⟩⟩]),
  ("union", "union:duckdb:test/sql/setops/test_union_type_cast.test:sqllogic-query-28", [⟨"?column?", ⟨.numeric [], false⟩⟩]),
  ("union", "union:duckdb:test/sql/setops/test_union_order.test:sqllogic-query-5", [⟨"?column?", ⟨.int32, true⟩⟩]),
  ("union", "union:duckdb:test/sql/setops/test_union_binding.test:sqllogic-query-281", [⟨"a", ⟨.timestamp [], true⟩⟩, ⟨"b", ⟨.timestamp [], true⟩⟩, ⟨"id", ⟨.int32, false⟩⟩]),
  ("union", "union:duckdb:test/sql/setops/union_all_projection_pushdown.test:sqllogic-query-70", [⟨"i", ⟨.text, false⟩⟩]),
  ("union", "union:duckdb:test/sql/setops/union_aggregate.test:sqllogic-query-62", [⟨"i", ⟨.int32, false⟩⟩]),
  ("union", "union:sqlite:test/with2.test:tcl-16531-statement-0", [⟨"x", ⟨.int32, false⟩⟩, ⟨"z", ⟨.int32, false⟩⟩]),
  ("union", "union:sqlite:test/join5.test:tcl-5324-statement-0", [⟨"fruit", ⟨.text, false⟩⟩, ⟨"fruit", ⟨.text, false⟩⟩, ⟨"isyellow", ⟨.int32, true⟩⟩]),
  ("union", "union:sqlite:test/with3.test:tcl-1159-statement-0", [⟨"?column?", ⟨.int32, false⟩⟩]),
  ("union", "union:sqlite:test/select4.test:tcl-14031-statement-0", [⟨"x", ⟨.int32, false⟩⟩, ⟨"y", ⟨.int32, false⟩⟩]),
  ("union", "union:sqlite:test/with1.test:tcl-24290-statement-0", [⟨"?column?", ⟨.int32, false⟩⟩]),
  ("union", "union:sqlite:test/with1.test:tcl-24490-statement-0", [⟨"?column?", ⟨.int32, false⟩⟩]),
  ("union", "union:sqlite:test/with1.test:tcl-24690-statement-0", [⟨"?column?", ⟨.int32, false⟩⟩]),
  ("intersect", "intersect:postgres:src/test/regress/sql/union.sql:statement-35", [⟨"?column?", ⟨.int32, false⟩⟩, ⟨"?column?", ⟨.int32, false⟩⟩, ⟨"?column?", ⟨.int32, false⟩⟩]),
  ("intersect", "intersect:postgres:src/test/regress/sql/union.sql:statement-36", [⟨"?column?", ⟨.int32, false⟩⟩, ⟨"?column?", ⟨.int32, false⟩⟩, ⟨"?column?", ⟨.int32, false⟩⟩]),
  ("intersect", "intersect:duckdb:test/sql/setops/test_setops.test:sqllogic-query-42", [⟨"?column?", ⟨.text, true⟩⟩]),
  ("intersect", "intersect:duckdb:test/sql/setops/setops_pushdown.test:sqllogic-query-22", [⟨"?column?", ⟨.int32, false⟩⟩]),
  ("intersect", "intersect:duckdb:test/sql/setops/setops_pushdown.test:sqllogic-query-27", [⟨"?column?", ⟨.int32, false⟩⟩]),
  ("intersect", "intersect:duckdb:test/sql/setops/setops_pushdown.test:sqllogic-query-32", [⟨"?column?", ⟨.int32, false⟩⟩]),
  ("except", "except:postgres:src/test/regress/sql/union.sql:statement-37", [⟨"?column?", ⟨.int32, false⟩⟩, ⟨"?column?", ⟨.int32, false⟩⟩, ⟨"?column?", ⟨.int32, false⟩⟩]),
  ("except", "except:postgres:src/test/regress/sql/union.sql:statement-38", [⟨"?column?", ⟨.int32, false⟩⟩, ⟨"?column?", ⟨.int32, false⟩⟩, ⟨"?column?", ⟨.int32, false⟩⟩]),
  ("except", "except:duckdb:test/sql/setops/test_setops.test:sqllogic-query-38", [⟨"?column?", ⟨.text, true⟩⟩]),
  ("except", "except:duckdb:test/sql/setops/setops_pushdown.test:sqllogic-query-6", [⟨"?column?", ⟨.int32, false⟩⟩]),
  ("except", "except:duckdb:test/sql/setops/setops_pushdown.test:sqllogic-query-11", [⟨"?column?", ⟨.int32, false⟩⟩]),
  ("except", "except:duckdb:test/sql/setops/setops_pushdown.test:sqllogic-query-17", [⟨"?column?", ⟨.int32, false⟩⟩])]

def setOperationsConcreteContractTests : IO Nat := do
  let registryJson ← expectOk "set source registry" (Lean.Json.parse
    (← IO.FS.readFile "fixtures/set_operations/source_contracts.json"))
  let mut registry : List (String × String × List OutputColumn) := []
  for factor in ["union","intersect","except"] do
    let entries ← expectOk factor ((registryJson.getObjVal? factor) >>= Lean.Json.getArr?)
    for record in entries do
      registry := registry ++ [(factor, ← setField record "id", ← setExpected record)]
  SQLean.Tests.assert (registry == setSourceRegistry && registry.length == 62 &&
    (registry.map (fun row => row.2.2.length)).sum == 83)
    "fixed independently reviewed 62-source / 83-column registry"
  let lines := ((← IO.FS.readFile "fixtures/set_operations/concrete.jsonl").splitOn "\n").filter
    (fun line => !line.trimAscii.toString.isEmpty)
  SQLean.Tests.assert (lines.length == 150) "exactly 150 unchanged set sources"
  let mut ids : List String := []
  let mut sqls : List String := []
  let mut factors : List String := []
  let mut certified := 0
  for line in lines do
    let record ← expectOk "set original" (Lean.Json.parse line)
    let id ← setField record "id"
    let factor ← setField record "factor"
    let sql ← setField record "sql"
    SQLean.Tests.assert ((← setField record "raw_sql") == sql &&
      (← expectOk id (record.getObjVal? "parameter_types")) == Lean.Json.null)
      s!"{id}: unchanged SQL and unspecified authentic bindings"
    let query ← expectOk id (Advanced.parseQuery sql)
    let identity ← expectOk id ((RenderContract.check .identityV01 query).mapError reprStr)
    let postgres ← expectOk id ((RenderContract.check .postgres16V01 query).mapError reprStr)
    have _identity := identity.roundTrip
    have _postgres := postgres.roundTrip
    match setSourceRegistry.find? (fun row => row.1 == factor && row.2.1 == id) with
    | none => pure ()
    | some (_, _, expected) =>
      SQLean.Tests.assert ((Advanced.queryParameters 1024 query).isEmpty)
        s!"{id}: no invented source parameter assumptions"
      SQLean.Tests.assert ((← setCertificate query) == expected) s!"{id}: exact authentic output"
      certified := certified + 1
    ids := id :: ids
    sqls := sql :: sqls
    factors := factor :: factors
  SQLean.Tests.assert (certified == 62 && decide ids.Nodup && decide sqls.Nodup &&
    (setSourceRegistry.map (fun row => row.2.1)).all ids.contains &&
    ["union","intersect","except"].all (fun factor => (factors.filter (· == factor)).length == 50))
    "fixed authentic eligibility and 50 originals per factor"
  pure certified

end SQLean.Tests
