import SQLean.Assurance
import SQLean.SchemaJson
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.ContractSupport
import Lean.Data.Json

namespace SQLean.Tests
open SelectContract

private def recAnchor : Advanced.Query :=
  {body := .select {items := [.expression (.literal (.int 1)) (some "x")]}}
private def recAnchorColumns : List OutputColumn := [{name := "x", type := ⟨.int32, false⟩}]
private def recInputs : List PendingColumn := [{name := "x", input := .known ⟨.int32, false⟩}]
private def recColumns : List OutputColumn := [{name := "x", type := ⟨.int32, true⟩}]
private def recEnv : CTEEnv := [⟨"r", recColumns⟩]
private def recScope : Scope := .ofCTE "r" none recColumns
private def recStep : Advanced.Query :=
  {body := .select {items := [.expression (.literal (.int 1)) (some "x")], source := some (.table "r")}}
private def recDefinition : Advanced.CTE := ⟨"r", {body := .set .union true recAnchor recStep}, []⟩

private theorem recAnchor_valid : QueryValid .basicV32 [] [] [] recAnchor recAnchorColumns [] := by
  apply QueryValid.basic (cteUses := []) (visible := []) (by decide) .nil
    (scope := .empty) (sourceUses := []) (selectUses := []) (whereUses := [])
    (orderUses := []) (limitUses := []) (offsetUses := [])
  · exact .empty
  · exact .expression (.int (by decide)) (.atom (.int (by decide)) .int) (.ordinary rfl) (by simp) .nil
  · exact .expression (.int (by decide)) (.atom (.int (by decide)) .int) (.ordinary rfl) (by simp) .nil
  · decide
  · decide
  · exact Or.inl rfl
  · exact .absent
  · exact .nil
  · exact .nil
  · exact .absent
  · exact .absent
  · exact .nil
  · rfl
  · rfl
  · rfl

private theorem recAnchor_inputs : SetOperandValid .basicV32 [] [] [] recAnchor recInputs [] := by
  apply SetOperandValid.basic (cteUses := []) (visible := []) (by decide) .nil
    (scope := .empty) (sourceUses := []) (selectUses := []) (whereUses := [])
    (orderUses := []) (limitUses := []) (offsetUses := [])
    (output := recAnchorColumns) (pending := recInputs)
  · exact .empty
  · exact .expression (.int (by decide)) (.atom (.int (by decide)) .int) (.ordinary rfl) (by simp) .nil
  · exact .expression (.int (by decide)) (.atom (.int (by decide)) .int) (.ordinary rfl) (by simp) .nil
  · decide
  · decide
  · exact Or.inl rfl
  · exact .absent
  · exact .nil
  · exact .nil
  · exact .absent
  · exact .absent
  · exact .nil
  · rfl
  · rfl
  · rfl

private theorem recStep_inputs : SetOperandValid .basicV32 [] [] recEnv recStep recInputs [] := by
  apply SetOperandValid.basic (cteUses := []) (visible := recEnv) (by decide) .nil
    (scope := recScope) (sourceUses := []) (selectUses := []) (whereUses := [])
    (orderUses := []) (limitUses := []) (offsetUses := [])
    (output := recAnchorColumns) (pending := recInputs)
  · exact .cte (binding := ⟨"r", recColumns⟩) rfl (by simp) (by decide) (Or.inl rfl)
  · exact .expression (.int (by decide)) (.atom (.int (by decide)) .int) (.ordinary rfl) (by simp) .nil
  · exact .expression (.int (by decide)) (.atom (.int (by decide)) .int) (.ordinary rfl) (by simp) .nil
  · decide
  · decide
  · exact Or.inl rfl
  · exact .absent
  · exact .nil
  · exact .nil
  · exact .absent
  · exact .absent
  · exact .nil
  · rfl
  · rfl
  · rfl

/-- A genuine self-recursive definition, derived without executing the checker.
The recursively exposed row is nullable even though both projections are 1. -/
private theorem recDefinition_valid :
    RecursiveCTEValid .basicV32 [] [] [] recDefinition recColumns [] := by
  apply RecursiveCTEValid.union (prefixUses := []) (visible := [])
    (anchorOutput := recAnchorColumns) (leftInputs := recInputs) (rightInputs := recInputs)
    (mergedOutput := recAnchorColumns) (leftUses := []) (rightUses := [])
  · decide
  · simp
  · simp [recursiveCTEReferences]
  · exact .nil
  · simp [recAnchor, recursiveReferences, recursiveCTEReferences, recursiveSelectReferences,
      recursiveItemReferences, recursiveExprReferences, recursiveExprsReferences,
      recursiveOrderReferences, recursiveOptionalExprReferences, RecursiveReferences.append]
  · simp [recStep, recursiveReferences, recursiveCTEReferences, recursiveSelectReferences,
      recursiveSourceReferences, recursiveItemReferences, recursiveExprReferences,
      recursiveExprsReferences, recursiveOrderReferences, recursiveOptionalExprReferences,
      RecursiveReferences.append]
  · exact recAnchor_valid
  · exact recAnchor_inputs
  · decide
  · exact recStep_inputs
  · rfl
  · rfl
  · exact .cons
      (left := {name := "x", input := .known ⟨.int32, false⟩})
      (right := {name := "x", input := .known ⟨.int32, false⟩})
      (base := .int32) (derivation := .none)
      (by decide) (by decide) (by decide) (by decide) rfl (Or.inl ⟨rfl, rfl⟩) .nil
  · rfl
  · rfl

example : RecursiveCTEValid .basicV32 [] [] [] (RenderContract.translateCTE recDefinition) recColumns [] :=
  RenderContract.recursive_cte_valid_translated recDefinition_valid
example : recursiveOutput recColumns = recColumns := rfl
example : recColumns.map OutputColumn.collation = recAnchorColumns.map OutputColumn.collation := rfl

private def recField (record : Lean.Json) (field : String) : IO String :=
  expectOk field ((record.getObjVal? field) >>= Lean.Json.getStr?)

private def recType (label : String) : IO ScalarType := do
  match label with
  | "int32" => pure .int32
  | "bool" => pure .bool
  | "bpchar" => pure (.char [])
  | other =>
    let declaration ← expectOk other (Advanced.parseDataType other)
    match concreteType declaration with
    | some type => pure type
    | none => throw (IO.userError s!"unregistered recursive output type {other}")

private def recExpected (record : Lean.Json) : IO (List OutputColumn) := do
  let columns ← expectOk "recursive output columns" ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
  columns.toList.mapM fun column => do
    let name ← recField column "name"
    let type ← recType (← recField column "type")
    let nullable ← expectOk name ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
    pure {name := name, type := ⟨type, nullable⟩}

private def recCertificate (query : Advanced.Query) (catalog : Advanced.Catalog := [])
    (params : ParameterEnv := []) : IO (List OutputColumn) := do
  let certificate ← expectOk "recursive independent contract"
    ((SelectContract.checkQuery .basicV32 catalog params query).mapError reprStr)
  have _catalog := certificate.catalog_unchanged
  have _preservation := RenderContract.translateParameters_valid certificate.valid
  let identity ← expectOk "recursive identity" ((RenderContract.check .identityV01 query).mapError reprStr)
  let postgres ← expectOk "recursive PostgreSQL" ((RenderContract.check .postgres16V01 query).mapError reprStr)
  have _identity := identity.roundTrip
  have _postgres := postgres.roundTrip
  pure certificate.output

def recursiveContractTests : IO Nat := do
  let defaultAnchor := "WITH RECURSIVE r AS (SELECT 'a'::TEXT AS x UNION ALL SELECT ('b'::NAME)::TEXT FROM r) SELECT * FROM r"
  let nameAnchor := "WITH RECURSIVE r AS (SELECT ('a'::NAME)::TEXT AS x UNION ALL SELECT 'b'::TEXT FROM r) SELECT * FROM r"
  let valid := [
    nameAnchor,
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL SELECT x+1 FROM r WHERE x<3) SELECT x FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION SELECT x FROM r) SELECT x FROM r",
    "WITH RECURSIVE r AS (SELECT NULL AS x UNION ALL SELECT x FROM r WHERE FALSE) SELECT x FROM r",
    "WITH RECURSIVE r AS (SELECT 'a' AS x UNION ALL SELECT x||'b' FROM r WHERE FALSE) SELECT x FROM r",
    "WITH RECURSIVE r AS (SELECT ARRAY[1] AS x UNION ALL SELECT x FROM r WHERE FALSE) SELECT x FROM r",
    "WITH RECURSIVE r AS (SELECT '1'::JSON AS x UNION ALL SELECT x FROM r WHERE FALSE) SELECT x FROM r",
    "WITH RECURSIVE r AS (SELECT ARRAY['1'::JSON] AS x UNION ALL SELECT x FROM r WHERE FALSE) SELECT x FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL (WITH a AS (SELECT x FROM r) SELECT x FROM a)) SELECT x FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL (WITH unused AS (SELECT x FROM r) SELECT 2)) SELECT x FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL SELECT x FROM (SELECT x FROM r) d) SELECT x FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL (SELECT x FROM r INTERSECT SELECT 2)) SELECT x FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL (SELECT x FROM r EXCEPT SELECT 2)) SELECT x FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL SELECT r.x FROM r LEFT JOIN (SELECT 2 AS y) d ON TRUE) SELECT x FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL SELECT r.x FROM (SELECT 2 AS y) d RIGHT JOIN r ON TRUE) SELECT x FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL (SELECT x FROM r ORDER BY 1 LIMIT 1 OFFSET 0)) SELECT x FROM r",
    "WITH RECURSIVE a AS (SELECT 1 AS x), r AS (SELECT x FROM a UNION ALL SELECT x FROM r WHERE FALSE) SELECT x FROM r",
    "WITH RECURSIVE a AS (SELECT 1 AS x UNION ALL SELECT x FROM a WHERE FALSE), r AS (SELECT x FROM a UNION ALL SELECT x FROM r WHERE FALSE) SELECT x FROM r",
    "WITH RECURSIVE r AS (WITH a AS (SELECT 1 AS x) SELECT x FROM a UNION ALL SELECT x FROM r WHERE FALSE) SELECT x FROM r",
    "WITH RECURSIVE r AS (SELECT NULL AS x UNION SELECT 1) SELECT x FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL (WITH r AS (SELECT 2 AS x) SELECT x FROM r)) SELECT x FROM r",
    "WITH RECURSIVE r(z) AS (SELECT 1 AS x,2 AS y UNION ALL SELECT z,y FROM r WHERE FALSE) SELECT * FROM r",
    "WITH RECURSIVE r(z,z) AS (SELECT 1,2 UNION ALL SELECT 3,4 FROM r WHERE FALSE) SELECT * FROM r"]
  for sql in valid do
    let query ← expectOk sql (Advanced.parseQuery sql)
    let output ← recCertificate query
    if sql == nameAnchor then
      SQLean.Tests.assert
        (output == [{name := "x", type := ⟨.text, true⟩, collation := some .c}])
        "NAME anchor retains C collation and recursive nullable output"
  let invalid := [
    defaultAnchor,
    "WITH RECURSIVE r AS (SELECT * FROM r) SELECT * FROM r",
    "WITH RECURSIVE r AS (SELECT x FROM r UNION ALL SELECT 1) SELECT * FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL SELECT a.x FROM r a CROSS JOIN r b) SELECT * FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL (WITH unused AS (SELECT x FROM r) SELECT x FROM r)) SELECT * FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL SELECT r.x FROM (SELECT 2 AS y) d LEFT JOIN r ON TRUE) SELECT * FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL SELECT r.x FROM r FULL JOIN (SELECT 2 AS y) d ON TRUE) SELECT * FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL (SELECT x FROM r INTERSECT ALL SELECT 2)) SELECT * FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL (SELECT 2 EXCEPT SELECT x FROM r)) SELECT * FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL (SELECT x FROM r EXCEPT ALL SELECT 2)) SELECT * FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x INTERSECT SELECT x FROM r) SELECT * FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL SELECT x FROM r ORDER BY 1) SELECT * FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL SELECT x FROM r LIMIT 1) SELECT * FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL SELECT x FROM r OFFSET 1) SELECT * FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL SELECT x FROM r FOR UPDATE) SELECT * FROM r",
    "WITH RECURSIVE r AS (WITH unused AS (SELECT x FROM r) SELECT 1 AS x UNION ALL SELECT x FROM r) SELECT * FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL SELECT x::BIGINT FROM r) SELECT * FROM r",
    "WITH RECURSIVE r AS (SELECT NULL AS x UNION ALL SELECT 1 FROM r) SELECT * FROM r",
    "WITH RECURSIVE r AS (SELECT 'a'::VARCHAR(3) AS x UNION ALL SELECT x::VARCHAR(4) FROM r) SELECT * FROM r",
    "WITH RECURSIVE r AS (SELECT '1'::JSON AS x UNION SELECT x FROM r) SELECT * FROM r",
    "WITH RECURSIVE r AS (SELECT ARRAY['1'::JSON] AS x UNION SELECT x FROM r) SELECT * FROM r",
    "WITH RECURSIVE r(z,z) AS (SELECT 1,2 UNION ALL SELECT z,z FROM r) SELECT * FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL SELECT (SELECT x FROM r)) SELECT * FROM r"]
  for sql in invalid do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV32 [] [] query with
    | .error (.invalid _) => pure ()
    | other => throw (IO.userError s!"expected recursive invalid: {sql}: {reprStr (other.map fun _ => ())}")
  let unsupported := [
    "WITH RECURSIVE a AS (SELECT x FROM b), b AS (SELECT 1 AS x) SELECT * FROM a",
    "WITH RECURSIVE a AS (SELECT 1 AS x UNION ALL SELECT x FROM b), b AS (SELECT 1 AS x UNION ALL SELECT x FROM a) SELECT * FROM a",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL SELECT MAX(x) FROM r) SELECT * FROM r",
    "WITH RECURSIVE r AS (SELECT 1 AS x UNION ALL SELECT x FROM r GROUP BY x) SELECT * FROM r"]
  for sql in unsupported do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV32 [] [] query with
    | .error (.unsupported _) => pure ()
    | other => throw (IO.userError s!"expected recursive coverage boundary: {sql}: {reprStr (other.map fun _ => ())}")
  let parameterCases := [
    ("WITH RECURSIVE r(x) AS (SELECT ? UNION ALL SELECT x+? FROM r WHERE x<?) SELECT ? AS marker,x FROM r OFFSET ? LIMIT ?", "int,int,int,int,int,int", [1,2,3,4,5,6]),
    ("WITH RECURSIVE unused AS (SELECT ? AS x), r(x) AS (SELECT ? UNION ALL SELECT x+? FROM r WHERE FALSE) SELECT ?", "int,int,int,int", [1,2,3,4]),
    ("WITH RECURSIVE r(x) AS (SELECT $2 UNION ALL SELECT x+$1 FROM r WHERE x<$3) SELECT $2,x FROM r", "int,int,int", [2,1,3,2])]
  for (sql, declarations, expected) in parameterCases do
    let query ← expectOk sql (Advanced.parseQuery sql)
    let params ← expectOk sql (Assurance.parseContractParameterTypes declarations)
    let _ ← recCertificate query [] params
    SQLean.Tests.assert ((Advanced.queryParameters 1024 query).map parameterIndex == expected)
      s!"recursive definitions count lexical occurrences once: {sql}"
  let query ← expectOk "recursive resource" (Advanced.parseQuery valid.head!)
  for fuel in [0,1,2] do
    match SelectContract.checkQuery .basicV32 [] [] query fuel with
    | .error (.inconclusive _) => pure ()
    | _ => throw (IO.userError "recursive fuel exhaustion did not remain inconclusive")
  pure (valid.length + invalid.length + unsupported.length + parameterCases.length + 3)

def recursiveCorpusTests : IO Nat := do
  let records ← expectOk "recursive authored fixtures"
    ((Lean.Json.parse (← IO.FS.readFile "fixtures/recursive_contract/synthetic.json")) >>= Lean.Json.getArr?)
  let catalog ← expectOk "recursive catalog"
    (Advanced.decodeCatalogJson (← IO.FS.readFile "fixtures/recursive_contract/schema.json"))
  SQLean.Tests.assert (records.size == 50) "fifty authored recursive SELECTs"
  let mut ids : List String := []
  let mut sqls : List String := []
  for record in records do
    let id ← recField record "id"
    let sql ← recField record "sql"
    let params ← expectOk id (Assurance.parseContractParameterTypes (← recField record "parameter_types"))
    let query ← expectOk id (Advanced.parseQuery sql)
    let output ← recCertificate query catalog params
    SQLean.Tests.assert (sameOutputTypes output (← recExpected record)) s!"{id}: exact recursive output {reprStr output}"
    ids := id :: ids
    sqls := sql :: sqls
  SQLean.Tests.assert (decide ids.Nodup && decide sqls.Nodup) "unique authored recursive population"
  pure records.size

private def recursiveSourceRegistry : List (String × List OutputColumn) :=
  [("recursive_contract:postgres:src/test/regress/sql/with.sql:statement-9", [{name := "n", type := ⟨.int32, true⟩}]),
   ("recursive_contract:postgres:src/test/regress/sql/with.sql:statement-11", [{name := "n", type := ⟨.int32, true⟩}]),
   ("recursive_contract:postgres:src/test/regress/sql/with.sql:statement-103", [{name := "id", type := ⟨.int32, true⟩}]),
   ("recursive_contract:postgres:src/test/regress/sql/with.sql:statement-104", [{name := "id", type := ⟨.int32, true⟩}]),
   ("recursive_contract:postgres:src/test/regress/sql/with.sql:statement-157", [{name := "x", type := ⟨.int32, true⟩}]),
   ("recursive_contract:duckdb:test/sql/cte/recursive_cte_column_pruning.test:sqllogic-query-72", [{name := "a", type := ⟨.int32, true⟩}]),
   ("recursive_contract:duckdb:test/sql/cte/test_recursive_cte_union.test:sqllogic-query-6", [{name := "x", type := ⟨.int32, true⟩}]),
   ("recursive_contract:duckdb:test/sql/cte/test_recursive_cte_union.test:sqllogic-query-13", [{name := "x", type := ⟨.int32, true⟩}]),
   ("recursive_contract:duckdb:test/sql/cte/test_recursive_cte_union.test:sqllogic-query-21", [{name := "zz", type := ⟨.int32, true⟩}]),
   ("recursive_contract:duckdb:test/sql/cte/test_recursive_cte_union.test:sqllogic-query-28", [{name := "zz", type := ⟨.int32, true⟩}]),
   ("recursive_contract:duckdb:test/sql/cte/test_recursive_cte_union.test:sqllogic-query-36", [{name := "x", type := ⟨.int32, true⟩}]),
   ("recursive_contract:duckdb:test/sql/cte/test_recursive_cte_union.test:sqllogic-query-42", [{name := "x", type := ⟨.int32, true⟩}]),
   ("recursive_contract:duckdb:test/sql/cte/test_recursive_cte_union.test:sqllogic-query-58", [{name := "x", type := ⟨.int32, true⟩}, {name := "y", type := ⟨.text, true⟩}]),
   ("recursive_contract:duckdb:test/sql/cte/test_recursive_cte_union.test:sqllogic-query-87", [{name := "x", type := ⟨.int32, true⟩}]),
   ("recursive_contract:duckdb:test/sql/cte/test_recursive_cte_union.test:sqllogic-query-94", [{name := "x", type := ⟨.int32, true⟩}]),
   ("recursive_contract:duckdb:test/sql/cte/recursive_array_slice.test:sqllogic-query-60", [{name := "arr", type := ⟨(.array .int32), true⟩}]),
   ("recursive_contract:duckdb:test/sql/cte/test_recursive_cte_union_all.test:sqllogic-query-6", [{name := "x", type := ⟨.int32, true⟩}]),
   ("recursive_contract:duckdb:test/sql/cte/test_recursive_cte_union_all.test:sqllogic-query-14", [{name := "x", type := ⟨.int32, true⟩}]),
   ("recursive_contract:duckdb:test/sql/cte/test_recursive_cte_union_all.test:sqllogic-query-30", [{name := "x", type := ⟨.int32, true⟩}, {name := "y", type := ⟨.text, true⟩}]),
   ("recursive_contract:duckdb:test/sql/cte/test_nested_recursive_cte.test:sqllogic-query-5", [{name := "x", type := ⟨.int32, true⟩}]),
   ("recursive_contract:duckdb:test/sql/cte/test_recursive_cte_tutorial.test:sqllogic-query-109", [{name := "n", type := ⟨.int32, true⟩}, {name := "fibₙ", type := ⟨.int64, true⟩}])]

def recursiveConcreteContractTests : IO Nat := do
  let registry ← expectOk "fixed recursive metadata"
    ((Lean.Json.parse (← IO.FS.readFile "fixtures/recursive_contract/source_contracts.json")) >>= Lean.Json.getArr?)
  let registry ← registry.toList.mapM fun row => do
    pure ((← recField row "id"), (← recExpected row))
  SQLean.Tests.assert (registry == recursiveSourceRegistry && registry.length == 21 &&
    (registry.map (fun row => row.2.length)).sum == 24)
    "independently preregistered recursive identities and 24 ordered outputs"
  let text ← IO.FS.readFile "fixtures/recursive_contract/concrete.jsonl"
  let lines := (text.splitOn "\n").filter (fun line => !line.trimAscii.toString.isEmpty)
  SQLean.Tests.assert (lines.length == 50) "fifty unchanged recursive source statements"
  let mut ids : List String := []
  let mut certified := 0
  for line in lines do
    let record ← expectOk "recursive concrete record" (Lean.Json.parse line)
    let id ← recField record "id"
    let sql ← recField record "sql"
    SQLean.Tests.assert (sql == (← recField record "raw_sql")) s!"{id}: unchanged source bytes"
    let query ← expectOk id (Advanced.parseQuery sql)
    let _ ← expectOk id ((RenderContract.check .identityV01 query).mapError reprStr)
    let _ ← expectOk id ((RenderContract.check .postgres16V01 query).mapError reprStr)
    match recursiveSourceRegistry.find? (fun pair => pair.1 == id) with
    | none => pure ()
    | some (_, expected) =>
      SQLean.Tests.assert ((Advanced.queryParameters 1024 query).isEmpty) s!"{id}: no invented source parameters"
      SQLean.Tests.assert (sameOutputTypes (← recCertificate query) expected) s!"{id}: exact closed recursive output"
      certified := certified + 1
    ids := id :: ids
  SQLean.Tests.assert (certified == 21 && decide ids.Nodup &&
    (recursiveSourceRegistry.map Prod.fst).all ids.contains) "fixed recursive source eligibility"
  pure certified

end SQLean.Tests
