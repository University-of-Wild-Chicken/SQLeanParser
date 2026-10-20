import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

namespace SQLean.Tests

example : SelectContract.ExprValid [] .empty
    (.distinctFrom (.literal (.int 1)) (.literal (.int 2)))
    (some ⟨.bool, false⟩) [] :=
  .distinctScalar (.int (by decide)) (.int (by decide)) trivial trivial rfl

example : SelectContract.ExprValid [⟨1, ⟨.json, []⟩, true⟩] .empty
    (.distinctFrom (.parameter (.anonymous 1)) .null true)
    (some ⟨.bool, false⟩) [.anonymous 1] :=
  .distinctNullRight (.parameter (binding := ⟨1, ⟨.json, []⟩, true⟩)
    (base := .json) (by simp) rfl rfl)

example : SelectContract.ExprValid [] .empty
    (.distinctFrom (.row []) (.row []) true) (some ⟨.bool, false⟩) [] :=
  .distinctRows .nil .nil rfl

example : SelectContract.ExprValid [] .empty
    (.distinctFrom (.row [.null, .null]) .null true) (some ⟨.bool, false⟩) [] :=
  .distinctRowNullRight (.cons .null (.cons .null .nil))

example : SelectContract.ExprValid [] .empty
    (.isNull (.row [.literal (.int 1), .null]) true) (some ⟨.bool, false⟩) [] :=
  .isNullRow (.cons (.int (by decide)) (.cons .null .nil))

example : SelectContract.distinctSignature (.known ⟨.json, true⟩) (.unknown true) = none := rfl
example : SelectContract.rowDistinctSignature [] [] = some [] := rfl
example : SelectContract.rowDistinctSignature [.unknown true] [] = none := rfl
example : ¬ SelectContract.OrdinaryDistinctOperand .null := id
example : ¬ SelectContract.OrdinaryDistinctOperand (.row []) := id

private def nullField (id : String) (record : Lean.Json) (field : String) : IO String :=
  expectOk s!"{id}: {field}" ((record.getObjVal? field) >>= Lean.Json.getStr?)

private def nullCertificate (query : Advanced.Query)
    (params : SelectContract.ParameterEnv := []) : IO (List SelectContract.OutputColumn) := do
  let certificate ← expectOk "null predicate SELECT"
    ((SelectContract.checkQuery .basicV31 [] params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let identity ← expectOk "null predicate identity renderer"
    ((RenderContract.check .identityV01 query).mapError reprStr)
  let postgres ← expectOk "null predicate PostgreSQL renderer"
    ((RenderContract.check .postgres16V01 query).mapError reprStr)
  have _identity : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
  have _postgres : Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
    postgres.roundTrip
  pure certificate.output

private def nullOutput (sql : String) (parameterTypes : String := "") :
    IO (List SelectContract.OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let params ← expectOk sql (Assurance.parseContractParameterTypes parameterTypes)
  nullCertificate query params

private def nullDeclarations : List String :=
  ["SMALLINT", "INTEGER", "BIGINT", "NUMERIC(8,2)", "REAL", "DOUBLE PRECISION",
   "TEXT", "VARCHAR(5)", "CHAR(5)", "NAME", "BOOLEAN", "DATE", "TIME",
   "TIME WITH TIME ZONE", "TIMESTAMP", "TIMESTAMP WITH TIME ZONE", "INTERVAL",
   "UUID", "JSON", "JSONB", "BYTEA", "INTEGER[]", "BIGINT[]", "TEXT[]",
   "VARCHAR(5)[]", "JSON[]", "JSONB[]", "NAME[]"]

/-- Independently registered native analysis matrix, rather than asking the
normative resolver to choose its own expected acceptance result. JSON arrays
are analysis-valid but deliberately not certified for element equality. -/
private def nullPairAdmitted (left right : String) : Bool :=
  let numeric := ["SMALLINT", "INTEGER", "BIGINT", "NUMERIC(8,2)", "REAL", "DOUBLE PRECISION"]
  let strings := ["TEXT", "VARCHAR(5)", "CHAR(5)", "NAME"]
  let dates := ["DATE", "TIMESTAMP", "TIMESTAMP WITH TIME ZONE"]
  let times := ["TIME", "TIME WITH TIME ZONE"]
  (numeric.contains left && numeric.contains right) ||
    (strings.contains left && strings.contains right) ||
    (dates.contains left && dates.contains right) ||
    (times.contains left && times.contains right) ||
    (left == "TIME" && right == "INTERVAL") || (left == "INTERVAL" && right == "TIME") ||
    (left == right && !["JSON", "JSON[]"].contains left)

private def expectNullPair (query : Advanced.Query) (params : SelectContract.ParameterEnv)
    (left right : String) : IO Unit := do
  if nullPairAdmitted left right then
    SQLean.Tests.assert ((← nullCertificate query params) == [⟨"v", ⟨.bool, false⟩⟩])
      s!"DISTINCT exact declared inputs: {left}, {right}"
  else if left == "JSON[]" && right == "JSON[]" then
    match SelectContract.checkQuery .basicV31 [] params query with
    | .error (.unsupported diagnostic) =>
        SQLean.Tests.assert (diagnostic.code == "array_element_operator")
          "JSON array native runtime equality gap must remain explicit"
    | _ => throw (IO.userError "uncertified JSON array equality acquired a certificate")
  else match SelectContract.checkQuery .basicV31 [] params query with
    | .error (.invalid diagnostic) =>
        SQLean.Tests.assert (diagnostic.code == "distinct_signature")
          "known incompatible equality operands must be Invalid"
    | _ => throw (IO.userError s!"incompatible DISTINCT operands accepted: {left}, {right}")

def nullPredicatesContractTests : IO Nat := do
  let mut count := 0
  for negated in [false, true] do
    let op := if negated then "IS NOT DISTINCT FROM" else "IS DISTINCT FROM"
    let scalarQuery ← expectOk "scalar DISTINCT matrix" (Advanced.parseQuery s!"SELECT $1 {op} $2 AS v")
    let rowQuery ← expectOk "flat-row DISTINCT matrix"
      (Advanced.parseQuery s!"SELECT ROW($1,1) {op} ROW($2,1) AS v")
    for left in nullDeclarations do
      for right in nullDeclarations do
        for leftNullable in [false, true] do
          for rightNullable in [false, true] do
            let params ← expectOk "DISTINCT declarations" (Assurance.parseContractParameterTypes
              (left ++ (if leftNullable then "?" else "") ++ "," ++
                right ++ (if rightNullable then "?" else "")))
            expectNullPair scalarQuery params left right
            count := count + 1
        let params ← expectOk "flat-row declarations"
          (Assurance.parseContractParameterTypes (left ++ "?," ++ right ++ "?"))
        expectNullPair rowQuery params left right
        count := count + 1
    for declaration in nullDeclarations do
      for nullable in [false, true] do
        let params := declaration ++ (if nullable then "?" else "")
        for expr in [s!"$1 {op} NULL", s!"NULL {op} $1"] do
          SQLean.Tests.assert ((← nullOutput s!"SELECT {expr} AS v" params) ==
            [⟨"v", ⟨.bool, false⟩⟩]) "raw NULL bypasses operator resolution for every admitted type"
          count := count + 1
    for expr in [
        s!"NULL {op} NULL", s!"'1' {op} 1", s!"'bad' {op} 1",
        s!"'{"{}"}'::JSON {op} NULL", s!"ARRAY['{"{}"}'::JSON] {op} NULL",
        s!"ROW() {op} ROW()", s!"ROW(NULL) {op} ROW(NULL)",
        s!"ROW(1,NULL) {op} ROW(1,NULL)", s!"ROW(1,NULL) {op} ROW(1,2)",
        s!"ROW(NULL::JSON) {op} NULL", s!"NULL {op} ROW(NULL::JSON)",
        s!"ROW(NULL,NULL) {op} NULL", s!"NULL {op} ROW(NULL,NULL)",
        s!"ARRAY[1,NULL] {op} ARRAY[1,NULL]", s!"'NaN'::DOUBLE PRECISION {op} 'NaN'::DOUBLE PRECISION",
        s!"1::SMALLINT {op} 1::BIGINT", s!"DATE '2024-01-01' {op} TIMESTAMP '2024-01-01 00:00:00'"] do
      SQLean.Tests.assert ((← nullOutput s!"SELECT {expr} AS v") == [⟨"v", ⟨.bool, false⟩⟩])
        s!"DISTINCT syntax-path/value boundary: {expr}"
      count := count + 1
    for (expr, params) in [
        (s!"? {op} ?", "INTEGER?,INTEGER?"),
        (s!"$2 {op} $1", "NAME,TEXT?"),
        (s!"ROW(?,?) {op} ROW(?,?)", "INTEGER?,TEXT?,BIGINT?,NAME?"),
        (s!"ROW($2,$1) {op} ROW($1,$2)", "INTEGER,INTEGER?"),
        (s!"ROW(?,NULL) {op} NULL", "JSON?"),
        (s!"NULL {op} ROW(NULL,?)", "JSON[]?")] do
      SQLean.Tests.assert ((← nullOutput s!"SELECT {expr} AS v" params) ==
        [⟨"v", ⟨.bool, false⟩⟩]) "lexical scalar/row operand order and raw NULL"
      count := count + 1
    for (expr, code) in [
        (s!"NULL::JSON {op} NULL::JSON", "distinct_signature"),
        (s!"'{"{}"}'::JSON {op} NULL::JSON", "distinct_signature"),
        (s!"ROW(NULL::JSON) {op} ROW(NULL)", "distinct_signature"),
        (s!"ROW() {op} ROW(1)", "distinct_row_arity"),
        (s!"ROW(1,2) {op} ROW(1)", "distinct_row_arity"),
        (s!"ARRAY[1] {op} ARRAY[1::BIGINT]", "distinct_signature"),
        (s!"NULL {op} ARRAY[]", "array_constructor_type")] do
      let sql := s!"SELECT {expr}"
      let query ← expectOk sql (Advanced.parseQuery sql)
      match SelectContract.checkQuery .basicV31 [] [] query with
      | .error (.invalid diagnostic) =>
          SQLean.Tests.assert (diagnostic.code == code) s!"exact DISTINCT failure for {expr}"
      | _ => throw (IO.userError s!"invalid DISTINCT expression acquired a certificate: {expr}")
      count := count + 1
    for expr in [s!"ROW(ROW(1)) {op} ROW(ROW(1))", s!"ROW(ROW(1)) {op} NULL",
        s!"ROW(1) {op} 'record input'", s!"(SELECT 1) {op} NULL",
        s!"'{"{}"}'::JSON[] {op} '{"{}"}'::JSON[]"] do
      let query ← expectOk expr (Advanced.parseQuery s!"SELECT {expr}")
      match SelectContract.checkQuery .basicV31 [] [] query with
      | .error (.unsupported _) => pure ()
      | _ => throw (IO.userError s!"unmodeled composite/subquery/equality dependency accepted: {expr}")
      count := count + 1
  for spelling in ["ISNULL", "NOTNULL", "IS NULL", "IS NOT NULL"] do
    for declaration in nullDeclarations do
      for nullable in [false, true] do
        SQLean.Tests.assert ((← nullOutput s!"SELECT $1 {spelling} AS v"
          (declaration ++ (if nullable then "?" else ""))) == [⟨"v", ⟨.bool, false⟩⟩])
          "null tests require no equality operator"
        count := count + 1
    for expr in ["ROW()", "ROW(NULL)", "ROW(NULL,NULL)", "ROW(1,NULL)", "ROW(1,2)",
        "ROW(NULL::JSON,'{}'::JSON)", "ROW(ARRAY[NULL]::INTEGER[],NULL)"] do
      SQLean.Tests.assert ((← nullOutput s!"SELECT {expr} {spelling} AS v") ==
        [⟨"v", ⟨.bool, false⟩⟩]) "flat-row field-sensitive null tests"
      count := count + 1
    for expr in ["ROW(ROW(1))", "(SELECT 1)"] do
      let query ← expectOk expr (Advanced.parseQuery s!"SELECT {expr} {spelling}")
      match SelectContract.checkQuery .basicV31 [] [] query with
      | .error (.unsupported _) => pure ()
      | _ => throw (IO.userError "null test acquired unsupported composite/subquery evidence")
      count := count + 1
  for (sql, label, type) in [
      ("SELECT 1 IS DISTINCT FROM 2", "?column?", SelectContract.ScalarType.bool),
      ("SELECT ROW(NULL) NOTNULL", "?column?", .bool),
      ("SELECT CAST(1 IS DISTINCT FROM 2 AS TEXT)", "text", .text),
      ("SELECT CASE WHEN TRUE THEN 1 IS DISTINCT FROM 2 ELSE FALSE END", "case", .bool)] do
    SQLean.Tests.assert ((← nullOutput sql) == [⟨label, ⟨type, false⟩⟩]) "null-predicate default labels"
    count := count + 1
  let query ← expectOk "null predicate fuel" (Advanced.parseQuery "SELECT ROW(1) IS DISTINCT FROM ROW(2)")
  match SelectContract.checkQuery .basicV31 [] [] query 1 with
  | .error (.inconclusive _) => pure ()
  | _ => throw (IO.userError "null predicate fuel exhaustion must remain Inconclusive")
  let params ← expectOk "null predicate lexical types" (Assurance.parseContractParameterTypes "INTEGER,INTEGER")
  let query : Advanced.Query := {body := .select {items := [.expression
    (.distinctFrom (.parameter (.anonymous 2)) (.parameter (.anonymous 1)))]}}
  match SelectContract.checkQuery .basicV31 [] params query with
  | .error (.invalid diagnostic) =>
      SQLean.Tests.assert (diagnostic.code == "parameter_notation") "DISTINCT cannot reorder anonymous uses"
  | _ => throw (IO.userError "DISTINCT anonymous order was not enforced")
  let missing ← expectOk "raw NULL parameter" (Advanced.parseQuery "SELECT $1 IS DISTINCT FROM NULL")
  match SelectContract.checkQuery .basicV31 [] [] missing with
  | .error (.invalid _) => pure ()
  | _ => throw (IO.userError "raw NULL comparison invented a missing parameter declaration")
  pure (count + 3)

def nullPredicatesCorpusTests : IO Nat := do
  let mut count := 0
  for factor in ["distinct_from", "null_predicates"] do
    let records ← expectOk factor
      ((Lean.Json.parse (← IO.FS.readFile s!"fixtures/{factor}/synthetic.json")) >>= Lean.Json.getArr?)
    SQLean.Tests.assert (records.size == 50) s!"{factor}: fifty authored queries required"
    let mut ids : List String := []
    let mut statements : List String := []
    for record in records do
      let id ← nullField factor record "id"
      let sql ← nullField id record "sql"
      SQLean.Tests.assert ((← nullField id record "source_kind") == "synthetic") s!"{id}: source population"
      let parameters ← nullField id record "parameter_types"
      let columns ← expectOk id ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
      SQLean.Tests.assert (columns.size == 1) s!"{id}: one authored Boolean output"
      let column := columns[0]!
      let name ← nullField id column "name"
      let type ← nullField id column "type"
      let nullable ← expectOk id ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
      SQLean.Tests.assert (name == "v" && type == "bool" && !nullable &&
        (← nullOutput sql parameters) == [⟨"v", ⟨.bool, false⟩⟩])
        s!"{id}: exact nonnullable Boolean certificate"
      ids := id :: ids
      statements := sql :: statements
    SQLean.Tests.assert (decide ids.Nodup && decide statements.Nodup) s!"{factor}: duplicate authored query"
    count := count + records.size
  pure count

/-- Membership and output expectations are supplied by a closed source registry,
never by whether the executable checker happens to succeed. -/
private def nullConcreteFactor (factor : String)
    (registry : List (String × Option (List SelectContract.OutputColumn)))
    (nestedRows : List String := []) : IO Nat := do
  SQLean.Tests.assert (registry.length == 50 && decide (registry.map Prod.fst).Nodup)
    s!"{factor}: exactly fifty distinct registered source identities"
  let expectations ← expectOk factor
    (Lean.Json.parse (← IO.FS.readFile "fixtures/null_predicates/source_contracts.json"))
  let expectations ← expectOk factor ((expectations.getObjVal? factor) >>= Lean.Json.getArr?)
  let mut expectationIds : List String := []
  for expectation in expectations do
    let id ← nullField factor expectation "id"
    let output ← expectOk id ((expectation.getObjVal? "output_columns") >>= Lean.Json.getArr?)
    let output ← output.toList.mapM fun column => do
      let name ← nullField id column "name"
      let typeName ← nullField id column "type"
      let type ← match typeName with
        | "bool" => pure SelectContract.ScalarType.bool
        | "varchar" => pure (.varchar [])
        | _ => throw (IO.userError s!"{id}: unexpected registered output type {typeName}")
      let nullable ← expectOk id ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
      pure (⟨name, ⟨type, nullable⟩⟩ : SelectContract.OutputColumn)
    SQLean.Tests.assert (registry.lookup id == some (some output))
      s!"{id}: independently registered source metadata disagrees with the Lean inventory"
    expectationIds := id :: expectationIds
  SQLean.Tests.assert (decide expectationIds.Nodup &&
    expectationIds.length == (registry.filter (fun entry => entry.2.isSome)).length)
    s!"{factor}: metadata fixture must name every eligible query exactly once"
  let rows := (← IO.FS.readFile s!"fixtures/{factor}/concrete.jsonl").splitOn "\n"
    |>.filter (!·.trimAscii.toString.isEmpty)
  SQLean.Tests.assert (rows.length == 50) s!"{factor}: exactly fifty unchanged source queries"
  let mut seen : List String := []
  let mut sqls : List String := []
  let mut certified := 0
  for row in rows do
    let record ← expectOk factor (Lean.Json.parse row)
    let id ← nullField factor record "id"
    let expected ← match registry.lookup id with
      | some expected => pure expected
      | none => throw (IO.userError s!"{factor}: unregistered source identity {id}")
    let sql ← nullField id record "sql"
    SQLean.Tests.assert (sql == (← nullField id record "raw_sql") &&
      (← expectOk id (record.getObjVal? "parameter_types")) == .null)
      s!"{id}: unchanged source or unspecified environment metadata altered"
    let observations ← expectOk id (record.getObjVal? "observed_syntax")
    let sourceFree ← expectOk id ((observations.getObjVal? "source_free") >>= Lean.Json.getBool?)
    let slots ← expectOk id ((record.getObjVal? "observed_parameter_slots") >>= Lean.Json.getArr?)
    let query ← expectOk id (Advanced.parseQuery sql)
    SQLean.Tests.assert (slots.isEmpty && (Advanced.queryParameters 1024 query).isEmpty &&
      sourceFree == (expected.isSome || nestedRows.contains id))
      s!"{id}: fixed source dependency or parameter classification changed"
    match expected with
    | some columns =>
        SQLean.Tests.assert query.ctes.isEmpty s!"{id}: closed source acquired a WITH context"
        match query.body with
        | .select select =>
            SQLean.Tests.assert select.source.isNone s!"{id}: closed source acquired a FROM context"
        | _ => throw (IO.userError s!"{id}: closed source body changed")
        SQLean.Tests.assert ((← nullCertificate query) == columns)
          s!"{id}: exact fixed source output names, types or nullable flags"
        certified := certified + 1
    | none =>
        let identity ← expectOk id ((RenderContract.check .identityV01 query).mapError reprStr)
        let postgres ← expectOk id ((RenderContract.check .postgres16V01 query).mapError reprStr)
        have _identity := identity.roundTrip
        have _postgres := postgres.roundTrip
        if nestedRows.contains id then
          match SelectContract.checkQuery .basicV31 [] [] query with
          | .error (.unsupported diagnostic) =>
              SQLean.Tests.assert (diagnostic.code == "record_value")
                s!"{id}: nested composite source must retain its explicit typing boundary"
          | _ => throw (IO.userError s!"{id}: unmodeled nested row acquired complete validity")
    seen := id :: seen
    sqls := sql :: sqls
  SQLean.Tests.assert (decide seen.Nodup && decide sqls.Nodup &&
    registry.all (fun entry => seen.contains entry.1) &&
    certified == (registry.filter (fun entry => entry.2.isSome)).length)
    s!"{factor}: every fixed source and certificate expectation must be replayed exactly once"
  pure certified

/-- Source identities and exact metadata were registered from unchanged input syntax
before invoking checking; catalog-dependent and nested-composite cases stay render-only. -/
private def distinctSourceRegistry : List (String × Option (List SelectContract.OutputColumn)) :=
[  ("distinct_from:postgres:src/test/regress/sql/select_distinct.sql:statement-61", some [⟨"yes", ⟨.bool, false⟩⟩]),
  ("distinct_from:postgres:src/test/regress/sql/select_distinct.sql:statement-62", some [⟨"no", ⟨.bool, false⟩⟩]),
  ("distinct_from:postgres:src/test/regress/sql/select_distinct.sql:statement-63", some [⟨"yes", ⟨.bool, false⟩⟩]),
  ("distinct_from:postgres:src/test/regress/sql/select_distinct.sql:statement-64", some [⟨"no", ⟨.bool, false⟩⟩]),
  ("distinct_from:postgres:src/test/regress/sql/select_distinct.sql:statement-65", some [⟨"no", ⟨.bool, false⟩⟩]),
  ("distinct_from:postgres:src/test/regress/sql/select_distinct.sql:statement-66", some [⟨"yes", ⟨.bool, false⟩⟩]),
  ("distinct_from:postgres:src/test/regress/sql/select_distinct.sql:statement-67", some [⟨"no", ⟨.bool, false⟩⟩]),
  ("distinct_from:postgres:src/test/regress/sql/select_distinct.sql:statement-68", some [⟨"yes", ⟨.bool, false⟩⟩]),
  ("distinct_from:postgres:src/test/regress/sql/create_index_spgist.sql:statement-66", none),
  ("distinct_from:postgres:src/test/regress/sql/create_index_spgist.sql:statement-69", none),
  ("distinct_from:postgres:src/test/regress/sql/create_index_spgist.sql:statement-72", none),
  ("distinct_from:postgres:src/test/regress/sql/create_index_spgist.sql:statement-89", none),
  ("distinct_from:postgres:src/test/regress/sql/create_index_spgist.sql:statement-92", none),
  ("distinct_from:postgres:src/test/regress/sql/create_index_spgist.sql:statement-95", none),
  ("distinct_from:postgres:src/test/regress/sql/select_distinct.sql:statement-57", none),
  ("distinct_from:postgres:src/test/regress/sql/select_distinct.sql:statement-58", none),
  ("distinct_from:postgres:src/test/regress/sql/select_distinct.sql:statement-59", none),
  ("distinct_from:postgres:src/test/regress/sql/select_distinct.sql:statement-60", none),
  ("distinct_from:materialize:test/sqllogictest/distinct_from.slt:sqllogic-query-12", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("distinct_from:materialize:test/sqllogictest/distinct_from.slt:sqllogic-query-17", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("distinct_from:materialize:test/sqllogictest/distinct_from.slt:sqllogic-query-22", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("distinct_from:materialize:test/sqllogictest/distinct_from.slt:sqllogic-query-27", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("distinct_from:materialize:test/sqllogictest/distinct_from.slt:sqllogic-query-32", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("distinct_from:materialize:test/sqllogictest/distinct_from.slt:sqllogic-query-37", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("distinct_from:materialize:test/sqllogictest/distinct_from.slt:sqllogic-query-42", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("distinct_from:materialize:test/sqllogictest/distinct_from.slt:sqllogic-query-47", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("distinct_from:materialize:test/sqllogictest/distinct_from.slt:sqllogic-query-52", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("distinct_from:materialize:test/sqllogictest/distinct_from.slt:sqllogic-query-57", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("distinct_from:materialize:test/sqllogictest/distinct_from.slt:sqllogic-query-63", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("distinct_from:materialize:test/sqllogictest/distinct_from.slt:sqllogic-query-68", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("distinct_from:materialize:test/sqllogictest/distinct_from.slt:sqllogic-query-73", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("distinct_from:materialize:test/sqllogictest/distinct_from.slt:sqllogic-query-78", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("distinct_from:materialize:test/sqllogictest/distinct_from.slt:sqllogic-query-83", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("distinct_from:materialize:test/sqllogictest/distinct_from.slt:sqllogic-query-169", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("distinct_from:materialize:test/sqllogictest/distinct_from.slt:sqllogic-query-138", none),
  ("distinct_from:materialize:test/sqllogictest/distinct_from.slt:sqllogic-query-146", none),
  ("distinct_from:materialize:test/sqllogictest/distinct_from.slt:sqllogic-query-154", none),
  ("distinct_from:materialize:test/sqllogictest/distinct_from.slt:sqllogic-query-160", none),
  ("distinct_from:duckdb:test/sql/types/null/test_boolean_null.test:sqllogic-query-33", some [⟨"?column?", ⟨.bool, false⟩⟩, ⟨"?column?", ⟨.bool, false⟩⟩, ⟨"?column?", ⟨.bool, false⟩⟩, ⟨"?column?", ⟨.bool, false⟩⟩, ⟨"?column?", ⟨.bool, false⟩⟩, ⟨"?column?", ⟨.bool, false⟩⟩, ⟨"?column?", ⟨.bool, false⟩⟩, ⟨"?column?", ⟨.bool, false⟩⟩, ⟨"?column?", ⟨.bool, false⟩⟩, ⟨"?column?", ⟨.bool, false⟩⟩]),
  ("distinct_from:duckdb:test/sql/join/inner/test_join_is_not_distinct.test:sqllogic-query-13", none),
  ("distinct_from:duckdb:test/sql/join/inner/test_join_is_not_distinct.test:sqllogic-query-67", none),
  ("distinct_from:duckdb:test/sql/join/inner/test_join_is_not_distinct.test:sqllogic-query-121", none),
  ("distinct_from:duckdb:test/sql/join/inner/test_join_is_not_distinct.test:sqllogic-query-196", none),
  ("distinct_from:duckdb:test/sql/join/inner/test_join_is_not_distinct.test:sqllogic-query-214", none),
  ("distinct_from:duckdb:test/sql/join/inner/test_join_is_not_distinct.test:sqllogic-query-239", none),
  ("distinct_from:duckdb:test/sql/join/inner/test_join_is_distinct.test:sqllogic-query-13", none),
  ("distinct_from:duckdb:test/sql/join/inner/test_join_is_distinct.test:sqllogic-query-67", none),
  ("distinct_from:duckdb:test/sql/join/inner/test_join_is_distinct.test:sqllogic-query-121", none),
  ("distinct_from:duckdb:test/sql/join/inner/test_join_is_distinct.test:sqllogic-query-196", none),
  ("distinct_from:duckdb:test/sql/join/inner/test_join_is_distinct.test:sqllogic-query-241", none)]

private def postfixSourceRegistry : List (String × Option (List SelectContract.OutputColumn)) :=
[  ("null_predicates:materialize:test/sqllogictest/comparison.slt:sqllogic-query-17", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("null_predicates:materialize:test/sqllogictest/comparison.slt:sqllogic-query-27", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("null_predicates:materialize:test/sqllogictest/cockroach/tuple.slt:sqllogic-query-1015", some [⟨"r", ⟨.bool, false⟩⟩]),
  ("null_predicates:duckdb:test/sql/peg_parser/transformer/is_predicate_operators.test:sqllogic-query-15", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("null_predicates:duckdb:test/sql/peg_parser/transformer/is_predicate_operators.test:sqllogic-query-20", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("null_predicates:duckdb:test/sql/parser/is_not_null_cast.test:sqllogic-query-15", some [⟨"varchar", ⟨.varchar [], false⟩⟩, ⟨"varchar", ⟨.varchar [], false⟩⟩]),
  ("null_predicates:h2:h2/src/test/org/h2/test/scripts/predicates/null.sql:embedded-sql-562", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("null_predicates:h2:h2/src/test/org/h2/test/scripts/predicates/null.sql:embedded-sql-600", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("null_predicates:h2:h2/src/test/org/h2/test/scripts/predicates/null.sql:embedded-sql-643", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("null_predicates:h2:h2/src/test/org/h2/test/scripts/predicates/null.sql:embedded-sql-686", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("null_predicates:h2:h2/src/test/org/h2/test/scripts/predicates/null.sql:embedded-sql-732", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("null_predicates:h2:h2/src/test/org/h2/test/scripts/predicates/null.sql:embedded-sql-768", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("null_predicates:h2:h2/src/test/org/h2/test/scripts/predicates/null.sql:embedded-sql-808", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("null_predicates:h2:h2/src/test/org/h2/test/scripts/predicates/null.sql:embedded-sql-847", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("null_predicates:h2:h2/src/test/org/h2/test/scripts/predicates/null.sql:embedded-sql-890", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("null_predicates:h2:h2/src/test/org/h2/test/scripts/predicates/null.sql:embedded-sql-923", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("null_predicates:h2:h2/src/test/org/h2/test/scripts/predicates/null.sql:embedded-sql-959", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("null_predicates:h2:h2/src/test/org/h2/test/scripts/predicates/null.sql:embedded-sql-995", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("null_predicates:h2:h2/src/test/org/h2/test/scripts/predicates/null.sql:embedded-sql-3152", none),
  ("null_predicates:h2:h2/src/test/org/h2/test/scripts/predicates/null.sql:embedded-sql-3730", none),
  ("null_predicates:h2:h2/src/test/org/h2/test/scripts/predicates/null.sql:embedded-sql-4336", none),
  ("null_predicates:h2:h2/src/test/org/h2/test/scripts/predicates/null.sql:embedded-sql-4874", none),
  ("null_predicates:sqlite:test/join.test:tcl-26467-statement-0", none),
  ("null_predicates:sqlite:test/join.test:tcl-28275-statement-8", none),
  ("null_predicates:sqlite:test/join.test:tcl-28275-statement-9", none),
  ("null_predicates:sqlite:test/join.test:tcl-28275-statement-13", none),
  ("null_predicates:sqlite:test/join.test:tcl-28275-statement-14", none),
  ("null_predicates:sqlite:test/join8.test:tcl-14420-statement-5", none),
  ("null_predicates:sqlite:test/join8.test:tcl-25203-statement-5", none),
  ("null_predicates:sqlite:test/joinH.test:tcl-632-statement-0", none),
  ("null_predicates:sqlite:test/joinH.test:tcl-802-statement-0", none),
  ("null_predicates:sqlite:test/types.test:tcl-6966-statement-0", none),
  ("null_predicates:postgres:src/test/regress/sql/rowtypes.sql:statement-88", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("null_predicates:postgres:src/test/regress/sql/rules.sql:statement-81", none),
  ("null_predicates:h2:h2/src/test/org/h2/test/scripts/predicates/null.sql:embedded-sql-5423", none),
  ("null_predicates:h2:h2/src/test/org/h2/test/scripts/predicates/null.sql:embedded-sql-5574", none),
  ("null_predicates:h2:h2/src/test/org/h2/test/scripts/predicates/null.sql:embedded-sql-5721", none),
  ("null_predicates:h2:h2/src/test/org/h2/test/scripts/predicates/null.sql:embedded-sql-5869", none),
  ("null_predicates:h2:h2/src/test/org/h2/test/scripts/predicates/null.sql:embedded-sql-5999", none),
  ("null_predicates:h2:h2/src/test/org/h2/test/scripts/predicates/null.sql:embedded-sql-6178", none),
  ("null_predicates:turso:sqlite/conformance/sqlite-sqltests/null/default.sqltest:embedded-sql-34", some [⟨"?column?", ⟨.bool, false⟩⟩, ⟨"?column?", ⟨.bool, false⟩⟩]),
  ("null_predicates:turso:sqlite/conformance/sqlite-sqltests/null/default.sqltest:embedded-sql-184", some [⟨"?column?", ⟨.bool, false⟩⟩, ⟨"?column?", ⟨.bool, false⟩⟩]),
  ("null_predicates:sqlglot:tests/dialects/test_postgres.py:embedded-sql-2650", none),
  ("null_predicates:sqlglot:tests/dialects/test_postgres.py:embedded-sql-23802", none),
  ("null_predicates:sqlglot:tests/dialects/test_postgres.py:embedded-sql-24024", none),
  ("null_predicates:sqlglot:tests/dialects/test_postgres.py:embedded-sql-115713", none),
  ("null_predicates:sqlglot:tests/dialects/test_postgres.py:embedded-sql-115802", none),
  ("null_predicates:sqlparser-rs:tests/sqlparser_common.rs:embedded-sql-657110", some [⟨"?column?", ⟨.bool, false⟩⟩]),
  ("null_predicates:jsqlparser:src/test/java/net/sf/jsqlparser/expression/operators/relational/IsNullExpressionTest.java:embedded-sql-464", none),
  ("null_predicates:calcite:core/src/test/resources/sql/struct.iq:embedded-sql-3099", none)]

def nullPredicatesConcreteContractTests : IO Nat := do
  let distinct ← nullConcreteFactor "distinct_from" distinctSourceRegistry
  let nullTests ← nullConcreteFactor "null_predicates" postfixSourceRegistry
    ["null_predicates:calcite:core/src/test/resources/sql/struct.iq:embedded-sql-3099"]
  SQLean.Tests.assert (distinct == 25 && nullTests == 22)
    "fixed source certification populations must remain 25 DISTINCT and 22 null-test queries"
  pure (distinct + nullTests)

end SQLean.Tests
