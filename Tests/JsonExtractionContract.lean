import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.ContractSupport
import Lean.Data.Json

namespace SQLean.Tests

/-- Even a non-NULL JSONB input and INTEGER index have a nullable extraction
result: the value need not contain an element at that index. -/
example : SelectContract.ExprValid [⟨1, ⟨.jsonb, []⟩, false⟩] .empty
    (.jsonAccess .field (.parameter (.anonymous 1)) (.literal (.int 1)))
    (some ⟨.jsonb, true⟩) [.anonymous 1] :=
  .jsonAccess (selected := ⟨[.jsonb, .int32], .jsonb⟩)
    (.parameter (binding := ⟨1, ⟨.jsonb, []⟩, false⟩) (base := .jsonb)
      (by simp) rfl rfl) (.int (by decide)) rfl

example : SelectContract.jsonAccessSignature .field
    (.known ⟨.json, false⟩) (.unknown false) =
    some ⟨[.json, .text], .json⟩ := rfl

example : SelectContract.jsonAccessSignature .path
    (.unknown true) (.known ⟨.array .text, false⟩) = none := rfl

private def jsonCertificate (query : Advanced.Query)
    (params : SelectContract.ParameterEnv := []) :
    IO (List SelectContract.OutputColumn) := do
  let certificate ← expectOk "JSON extraction SELECT"
    ((SelectContract.checkQuery .basicV32 [] params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let identity ← expectOk "JSON extraction identity renderer"
    ((RenderContract.check .identityV01 query).mapError reprStr)
  let postgres ← expectOk "JSON extraction PostgreSQL renderer"
    ((RenderContract.check .postgres16V01 query).mapError reprStr)
  have _identity : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
  have _postgres : Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
    postgres.roundTrip
  pure certificate.output

private def jsonOutput (sql : String) (parameterTypes : String := "") :
    IO (List SelectContract.OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let params ← expectOk sql (Assurance.parseContractParameterTypes parameterTypes)
  jsonCertificate query params

private def jsonField (id : String) (record : Lean.Json) (name : String) : IO String :=
  expectOk s!"{id}: {name}" ((record.getObjVal? name) >>= Lean.Json.getStr?)

private def jsonOperatorInventoryTests : IO Nat := do
  let json ← expectOk "JSON extraction inventory JSON"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/json_extraction/operator_signatures.json"))
  let records ← expectOk "JSON extraction inventory records" json.getArr?
  SQLean.Tests.assert (records.size == 12) "expected exactly twelve JSON extraction declarations"
  let mut observed : List (Advanced.JsonAccessOp × SelectContract.FunctionOverload) := []
  for record in records do
    let spelling ← jsonField "extraction inventory" record "operator"
    let op ← match SelectContract.jsonAccessOperators.filter
        (SelectContract.jsonAccessSpelling · == spelling) with
      | [op] => pure op
      | _ => throw (IO.userError s!"unknown extraction inventory operator: {spelling}")
    let parseType := fun field => do
      let name ← jsonField spelling record field
      let declaration ← expectOk name (Advanced.parseDataType name)
      match SelectContract.concreteType declaration with
      | some base => pure (declaration, base.unmodified)
      | none => throw (IO.userError s!"unsupported extraction inventory type: {name}")
    let (leftDeclaration, left) ← parseType "left"
    let (rightDeclaration, right) ← parseType "right"
    let (_, output) ← parseType "output"
    let selected : SelectContract.FunctionOverload := ⟨[left, right], output⟩
    SQLean.Tests.assert
      (SelectContract.jsonAccessSignature op (.known ⟨left, false⟩) (.known ⟨right, false⟩) ==
        some selected) s!"extraction exact selected overload: {spelling}, {reprStr selected}"
    SQLean.Tests.assert
      (SelectContract.jsonAccessFunctionName op left right ==
        some (← jsonField spelling record "function")) "extraction native function identity"
    let query : Advanced.Query := { body := .select { items := [
      .expression (.jsonAccess op (.cast .null leftDeclaration) (.cast .null rightDeclaration))
        (some "v")] } }
    SQLean.Tests.assert (sameOutputTypes (← jsonCertificate query) [{name := "v", type := ⟨output, true⟩}])
      "extraction inventory full-query output"
    observed := (op, selected) :: observed
  let expected := SelectContract.jsonAccessOperators.flatMap fun op =>
    (SelectContract.jsonAccessCatalog op).map fun selected => (op, selected)
  SQLean.Tests.assert (decide observed.Nodup && expected.all observed.contains &&
      observed.all expected.contains)
    "JSON extraction fixture differs from the complete selected catalog inventory"
  pure records.size

def jsonExtractionContractTests : IO Nat := do
  let mut count ← jsonOperatorInventoryTests
  let declarations : List (String × Bool × Bool) := [
    ("SMALLINT", true, false), ("INTEGER", true, false), ("BIGINT", false, false),
    ("NUMERIC(8,2)", false, false), ("REAL", false, false), ("DOUBLE PRECISION", false, false),
    ("TEXT", true, false), ("VARCHAR(5)", true, false), ("CHAR(5)", true, false),
    ("BOOLEAN", false, false), ("DATE", false, false), ("TIME(3)", false, false),
    ("TIME(3) WITH TIME ZONE", false, false), ("TIMESTAMP(3)", false, false),
    ("TIMESTAMP(3) WITH TIME ZONE", false, false), ("INTERVAL(3)", false, false),
    ("UUID", false, false), ("JSON", false, false), ("JSONB", false, false),
    ("BYTEA", false, false), ("INTEGER[]", false, false), ("TEXT[]", false, true),
    ("VARCHAR(5)[]", false, true), ("CHAR(5)[]", false, true),
    ("JSONB[]", false, false), ("TEXT[][]", false, true)]
  for (source, sourceBase) in [("JSON", SelectContract.ScalarType.json), ("JSONB", .jsonb)] do
    for op in SelectContract.jsonAccessOperators do
      let spelling := SelectContract.jsonAccessSpelling op
      let isPath := op == .path || op == .pathText
      let output := if op == .fieldText || op == .pathText then SelectContract.ScalarType.text else sourceBase
      for (key, arrowAllowed, pathAllowed) in declarations do
        let sql := s!"SELECT NULL::{source} {spelling} NULL::{key} AS v"
        let query ← expectOk sql (Advanced.parseQuery sql)
        if (if isPath then pathAllowed else arrowAllowed) then
          SQLean.Tests.assert (sameOutputTypes (← jsonCertificate query) [{name := "v", type := ⟨output, true⟩}])
            s!"extraction implicit key/path coercion: {sql}"
        else
          match SelectContract.checkQuery .basicV32 [] [] query with
          | .error (.invalid _) => pure ()
          | _ => throw (IO.userError s!"invalid extraction key type accepted: {sql}")
        count := count + 1
      for key in ["NULL", "'a'", "'{}'"] do
        let sql := s!"SELECT NULL::{source} {spelling} {key} AS v"
        SQLean.Tests.assert (sameOutputTypes (← jsonOutput sql) [{name := "v", type := ⟨output, true⟩}])
          s!"unknown RHS extraction context: {sql}"
        count := count + 1
      for leftNullable in [false, true] do
        for rightNullable in [false, true] do
          let parameters := source ++ (if leftNullable then "?" else "") ++
            (if isPath then ",VARCHAR(5)[]" else ",SMALLINT") ++
            (if rightNullable then "?" else "")
          SQLean.Tests.assert (sameOutputTypes (← jsonOutput s!"SELECT $1 {spelling} $2 AS v" parameters) [{name := "v", type := ⟨output, true⟩}]) "extraction must remain nullable for non-NULL operands"
          count := count + 1
      let rhs := if isPath then "'{}'" else "'a'"
      SQLean.Tests.assert (sameOutputTypes (← jsonOutput ("SELECT '{}'::" ++ s!"{source} {spelling} {rhs}")) [{name := "?column?", type := ⟨output, true⟩}]) "extraction default label must not inherit operand labels"
      count := count + 1
  for op in SelectContract.jsonAccessOperators do
    let spelling := SelectContract.jsonAccessSpelling op
    let key := if op == .path || op == .pathText then "ARRAY['a']" else "'a'"
    for source in ["NULL", "'{}'", "'null'"] do
      let sql := s!"SELECT {source} {spelling} {key}"
      let query ← expectOk sql (Advanced.parseQuery sql)
      match SelectContract.checkQuery .basicV32 [] [] query with
      | .error (.invalid _) => pure ()
      | _ => throw (IO.userError s!"ambiguous unknown extraction input must be Invalid: {sql}")
      count := count + 1
    for source in ["TEXT", "INTEGER", "BYTEA", "BOOLEAN", "UUID", "JSON[]", "JSONB[]"] do
      let sql := s!"SELECT NULL::{source} {spelling} {key}"
      let query ← expectOk sql (Advanced.parseQuery sql)
      match SelectContract.checkQuery .basicV32 [] [] query with
      | .error (.invalid _) => pure ()
      | _ => throw (IO.userError s!"non-JSON extraction input must be Invalid: {sql}")
      count := count + 1
  let examples : List (String × SelectContract.ScalarType) := [
    ("SELECT '{\"a\":1}'::JSON -> 'a' AS v", .json),
    ("SELECT '{\"a\":1}'::JSONB -> 'a' AS v", .jsonb),
    ("SELECT '{\"a\":1}'::JSONB ->> 'a' AS v", .text),
    ("SELECT '[10,20]'::JSONB -> -1 AS v", .jsonb),
    ("SELECT '[10,20]'::JSON -> '1' AS v", .json),
    ("SELECT '[null]'::JSONB -> 0 AS v", .jsonb),
    ("SELECT '[null]'::JSONB ->> 0 AS v", .text),
    ("SELECT '{}'::JSON -> 'missing' AS v", .json),
    ("SELECT '7'::JSON -> 'a' AS v", .json),
    ("SELECT '{\"a\":1}'::JSONB -> CAST('a' AS CHAR(3)) AS v", .jsonb),
    ("SELECT '{\"a\":[10,20]}'::JSON #> '{a,1}' AS v", .json),
    ("SELECT '{\"a\":[10,20]}'::JSONB #>> ARRAY['a','1'] AS v", .text),
    ("SELECT '{\"a\":1}'::JSONB #> ARRAY['a'::CHAR(3)] AS v", .jsonb),
    ("SELECT '{\"a\":1}'::JSON #> ARRAY['a'::VARCHAR(3)] AS v", .json),
    ("SELECT '{\"a\":1}'::JSONB #> '[0:0]={a}'::TEXT[] AS v", .jsonb),
    ("SELECT '{}'::JSONB #> ARRAY[NULL::TEXT] AS v", .jsonb),
    ("SELECT '{\"a\":{\"b\":{\"c\":{\"d\":1}}}}'::JSONB #> ARRAY[['a','b'],['c','d']] AS v", .jsonb),
    ("SELECT '[10,20]'::JSONB #> '{-1}' AS v", .jsonb),
    ("SELECT '[10,20]'::JSONB #> '{bad-index}' AS v", .jsonb),
    ("SELECT '[10,20]'::JSONB #> '{999999999999999999999999}' AS v", .jsonb),
    ("SELECT 'null'::JSON #> '{}' AS v", .json),
    ("SELECT 'null'::JSON #>> '{}' AS v", .text),
    ("SELECT '{}'::JSON #> 'malformed array' AS v", .json),
    ("SELECT '{\"a\":{\"b\":1}}'::JSONB -> 'a' ->> 'b' AS v", .text),
    ("SELECT '{\"a\":\"x\"}'::JSONB ->> 'a' || 'y' AS v", .text),
    ("SELECT '{\"a\":1}'::JSONB || '{}'::JSONB ->> 'a' AS v", .text),
    ("SELECT '{\"?\":1}'::JSONB ->> '?' AS v", .text),
    ("SELECT d.a -> 'a' AS v FROM (SELECT '{\"a\":1}'::JSON AS a) d", .json),
    ("SELECT DISTINCT '{\"a\":1}'::JSONB -> 'a' AS v ORDER BY v", .jsonb)]
  for (sql, output) in examples do
    SQLean.Tests.assert (sameOutputTypes (← jsonOutput sql) [{name := "v", type := ⟨output, true⟩}])
      s!"extraction composition/output: {sql}"
    count := count + 1
  for sql in [
      "SELECT DISTINCT '{\"a\":1}'::JSON -> 'a'",
      "SELECT '{}'::JSON -> 'a' = '{}'::JSON -> 'b'",
      "SELECT '[1]'::JSONB -> 2147483648",
      "SELECT '[1]'::JSONB -> -2147483649"] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV32 [] [] query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError s!"extraction enclosing/INTEGER boundary must be Invalid: {sql}")
    count := count + 1
  for sql in [
      "SELECT (SELECT '{}'::JSONB) -> 'a'",
      "SELECT '{}'::JSONB -> (SELECT 'a')",
      "SELECT unknown_function() -> 'a'",
      "SELECT ROW(1,2) -> 'a'"] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV32 [] [] query with
    | .error (.unsupported _) => pure ()
    | _ => throw (IO.userError s!"extraction child coverage must stay Unsupported: {sql}")
    count := count + 1
  for (sql, parameters, output) in [
      ("SELECT ? -> ? AS v", "jsonb,text", SelectContract.ScalarType.jsonb),
      ("SELECT $2 #>> $1 AS v", "varchar(5)[],json", .text),
      ("SELECT (CASE WHEN ? THEN ? ELSE ? END) -> (? || ?) AS v", "bool,jsonb,jsonb,text,text", .jsonb),
      ("SELECT d.a #> ARRAY[?,?] AS v FROM (SELECT ?::JSONB AS a) d", "text,text,jsonb", .jsonb)] do
    SQLean.Tests.assert (sameOutputTypes (← jsonOutput sql parameters) [{name := "v", type := ⟨output, true⟩}])
      s!"extraction lexical parameter order: {sql}"
    count := count + 1
  let params ← expectOk "extraction parameters" (Assurance.parseContractParameterTypes "jsonb,text")
  let bad : Advanced.Query := { body := .select { items := [.expression
    (.jsonAccess .field (.parameter (.numbered 1)) (.parameter (.anonymous 2)))] } }
  match SelectContract.checkQuery .basicV32 [] params bad with
  | .error (.invalid _) => pure ()
  | _ => throw (IO.userError "mixed extraction parameter styles must be Invalid")
  count := count + 1
  let query ← expectOk "extraction exhaustion" (Advanced.parseQuery "SELECT '{}'::JSONB -> 'a'")
  match SelectContract.checkQuery .basicV32 [] [] query 1 with
  | .error (.inconclusive _) => pure ()
  | _ => throw (IO.userError "extraction exhaustion must be Inconclusive")
  count := count + 1
  pure count

def jsonExtractionCorpusTests : IO Nat := do
  let json ← expectOk "JSON extraction fixture JSON"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/json_extraction/synthetic.json"))
  let records ← expectOk "JSON extraction fixture records" json.getArr?
  SQLean.Tests.assert (records.size == 50) "expected exactly 50 JSON extraction synthetic queries"
  let mut ids : List String := []
  let mut statements : List String := []
  for record in records do
    let id ← jsonField "extraction fixture" record "id"
    let sql ← jsonField id record "sql"
    SQLean.Tests.assert ((← jsonField id record "source_kind") == "synthetic") s!"{id}: population"
    let parameters ← jsonField id record "parameter_types"
    let expected ← expectOk id ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
    let expected ← expected.toList.mapM fun column => do
      let name ← jsonField id column "name"
      let type ← jsonField id column "type"
      let nullable ← expectOk id ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
      pure (name, type, nullable)
    let actual ← jsonOutput sql parameters
    let labels := actual.map fun column =>
      let type := match column.type.base with
        | .bool => "bool"
        | .int32 => "int32"
        | .text => "text"
        | base => (base.dataType.toSql.toLower).replace ", " ","
      (column.name, type, column.type.nullable)
    SQLean.Tests.assert (labels == expected)
      s!"{id}: exact JSON extraction output {reprStr labels}; expected {reprStr expected}"
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (decide ids.Nodup && decide statements.Nodup)
    "duplicate JSON extraction corpus identities or SQL"
  pure records.size

/-- This entire fixed concrete population is source-free and has no parameters.
It therefore receives full query evidence with the genuinely empty environment,
without inventing an application schema or selecting cases by checker success. -/
def jsonExtractionConcreteContractTests : IO Nat := do
  let source ← IO.FS.readFile "fixtures/json_extraction/concrete.jsonl"
  let lines := (source.splitOn "\n").filter (fun line => !line.trimAscii.toString.isEmpty)
  SQLean.Tests.assert (lines.length == 50) "expected exactly fifty unchanged concrete extraction queries"
  let expected : List (String × SelectContract.ScalarType) := [
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-116", .json),
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-117", .json),
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-119", .json),
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-122", .json),
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-123", .json),
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-125", .json),
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-128", .text),
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-129", .text),
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-133", .text),
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-134", .text),
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-136", .text),
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-137", .text),
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-159", .json),
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-161", .json),
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-167", .json),
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-171", .json),
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-173", .json),
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-179", .json),
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-163", .text),
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-165", .text),
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-187", .text),
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-191", .text),
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-193", .text),
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-199", .text),
    ("json_extraction:postgres:src/test/regress/sql/json.sql:statement-206", .text),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-106", .jsonb),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-107", .jsonb),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-111", .jsonb),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-114", .jsonb),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-680", .jsonb),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-687", .jsonb),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-690", .jsonb),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-117", .text),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-118", .text),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-122", .text),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-125", .text),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-127", .text),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-300", .jsonb),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-302", .jsonb),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-308", .jsonb),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-312", .jsonb),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-314", .jsonb),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-700", .jsonb),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-304", .text),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-306", .text),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-328", .text),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-332", .text),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-334", .text),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-340", .text),
    ("json_extraction:postgres:src/test/regress/sql/jsonb.sql:statement-347", .text)]
  SQLean.Tests.assert (expected.length == 50 && decide (expected.map Prod.fst).Nodup)
    "concrete extraction expected identities must be complete and unique"
  let mut ids : List String := []
  let mut statements : List String := []
  for line in lines do
    let record ← expectOk "concrete extraction JSON" (Lean.Json.parse line)
    let id ← jsonField "concrete extraction" record "id"
    let output ← match expected.find? (fun entry => entry.1 == id) with
      | some (_, output) => pure output
      | none => throw (IO.userError s!"unregistered concrete extraction identity: {id}")
    let sql ← jsonField id record "sql"
    SQLean.Tests.assert ((← jsonField id record "raw_sql") == sql &&
        (← jsonField id record "source") == "postgres" &&
        (← jsonField id record "source_kind") == "engine-regression")
      s!"{id}: concrete extraction source population changed"
    let slots ← expectOk id ((record.getObjVal? "observed_parameter_slots") >>= Lean.Json.getArr?)
    SQLean.Tests.assert slots.isEmpty s!"{id}: no concrete parameter assumptions are authorized"
    let query ← expectOk id (Advanced.parseQuery sql)
    match query.body with
    | .select select =>
        SQLean.Tests.assert (select.source.isNone && query.ctes.isEmpty)
          s!"{id}: concrete contract population must remain source-free"
    | _ => throw (IO.userError s!"{id}: unexpected concrete query structure")
    SQLean.Tests.assert (Advanced.queryParameters 1024 query == [])
      s!"{id}: concrete query contains undeclared parameters"
    SQLean.Tests.assert (sameOutputTypes (← jsonCertificate query) [{name := "?column?", type := ⟨output, true⟩}])
      s!"{id}: exact concrete extraction certificate output"
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (decide ids.Nodup && decide statements.Nodup)
    "duplicate concrete extraction identity or SQL"
  pure lines.length

end SQLean.Tests
