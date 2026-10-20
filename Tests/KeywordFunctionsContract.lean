import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

namespace SQLean.Tests

example : SelectContract.ExprValid [] .empty
    (.call ["left"] [.literal (.text "abc"), .literal (.int 2)])
    (some ⟨.text, false⟩) [] :=
  .call (.cons .text (.cons (.int (by decide)) .nil)) rfl

example : SelectContract.ExprValid [] .empty
    (.call ["pg_catalog", "right"] [.literal (.text "abc"), .null])
    (some ⟨.text, true⟩) [] :=
  .call (.cons .text (.cons .null .nil)) rfl

example : SelectContract.callSignature ["left"]
    [.known ⟨.name, false⟩, .known ⟨.smallInt, false⟩] = some ⟨.text, false⟩ := rfl

example : SelectContract.callSignature ["right"]
    [.known ⟨.char [5], true⟩, .known ⟨.int32, false⟩] = some ⟨.text, true⟩ := rfl

example : SelectContract.callSignature ["left"]
    [.known ⟨.text, false⟩, .known ⟨.int64, false⟩] = none := rfl

private def keywordField (id : String) (record : Lean.Json) (field : String) : IO String :=
  expectOk s!"{id}: {field}" ((record.getObjVal? field) >>= Lean.Json.getStr?)

private def keywordCertificate (query : Advanced.Query)
    (params : SelectContract.ParameterEnv := []) : IO (List SelectContract.OutputColumn) := do
  let certificate ← expectOk "keyword function SELECT"
    ((SelectContract.checkQuery .basicV31 [] params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let identity ← expectOk "keyword function identity renderer"
    ((RenderContract.check .identityV01 query).mapError reprStr)
  let postgres ← expectOk "keyword function PostgreSQL renderer"
    ((RenderContract.check .postgres16V01 query).mapError reprStr)
  have _identity : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
  have _postgres : Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
    postgres.roundTrip
  pure certificate.output

private def keywordOutput (sql : String) (parameterTypes : String := "") :
    IO (List SelectContract.OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let params ← expectOk sql (Assurance.parseContractParameterTypes parameterTypes)
  keywordCertificate query params

private def keywordInventoryTests : IO Nat := do
  let records ← expectOk "keyword function declarations"
    ((Lean.Json.parse (← IO.FS.readFile "fixtures/keyword_functions/function_signatures.json")) >>=
      Lean.Json.getArr?)
  SQLean.Tests.assert (records.size == 2) "exactly two keyword function declarations required"
  let mut names : List String := []
  for record in records do
    let name ← keywordField "inventory" record "name"
    let inputs ← expectOk name ((record.getObjVal? "inputs") >>= Lean.Json.getArr?)
    let inputs ← inputs.toList.mapM fun value => expectOk name value.getStr?
    let output ← keywordField name record "output"
    let selected : SelectContract.FunctionOverload := ⟨[.text, .int32], .text⟩
    SQLean.Tests.assert (["left", "right"].contains name && inputs == ["text", "integer"] &&
      output == "text" && SelectContract.functionNames.contains name &&
      SelectContract.functionCatalog name == [selected] &&
      SelectContract.resolveOverload (SelectContract.functionCatalog name)
        [.known ⟨.text, false⟩, .known ⟨.int32, false⟩] == some selected)
      s!"{name}: exact native declaration and selected inputs"
    names := name :: names
  SQLean.Tests.assert (decide names.Nodup && ["left", "right"].all names.contains)
    "keyword function inventory must cover both names exactly once"
  pure 2

def keywordFunctionsContractTests : IO Nat := do
  let mut count ← keywordInventoryTests
  let declarations := ["SMALLINT", "INTEGER", "BIGINT", "NUMERIC(8,2)", "REAL",
    "DOUBLE PRECISION", "TEXT", "VARCHAR(5)", "CHAR(5)", "NAME", "BOOLEAN", "DATE",
    "TIME", "TIME WITH TIME ZONE", "TIMESTAMP", "TIMESTAMP WITH TIME ZONE",
    "INTERVAL", "INTERVAL DAY TO SECOND(2)", "UUID", "JSON", "JSONB", "BYTEA",
    "INTEGER[]", "TEXT[]", "NAME[]"]
  -- The independent native matrix has every pair of these 25 declarations.
  -- Both nullable flags expand each static pair without changing coercion.
  for name in ["left", "right"] do
    let sql := s!"SELECT {name}($1,$2) AS v"
    let query ← expectOk sql (Advanced.parseQuery sql)
    for first in declarations do
      for second in declarations do
        let admitted := ["TEXT", "VARCHAR(5)", "CHAR(5)", "NAME"].contains first &&
          ["SMALLINT", "INTEGER"].contains second
        for leftNullable in [false, true] do
          for rightNullable in [false, true] do
            let params ← expectOk sql (Assurance.parseContractParameterTypes
              (first ++ (if leftNullable then "?" else "") ++ "," ++
                second ++ (if rightNullable then "?" else "")))
            if admitted then
              SQLean.Tests.assert ((← keywordCertificate query params) ==
                [⟨"v", ⟨.text, leftNullable || rightNullable⟩⟩])
                s!"{name}: admitted exact inputs {first}, {second}"
            else match SelectContract.checkQuery .basicV31 [] params query with
              | .error (.invalid diagnostic) =>
                  SQLean.Tests.assert (diagnostic.code == "function_signature")
                    s!"{name}: incompatible declared inputs must fail signature resolution"
              | _ => throw (IO.userError s!"{name}: incompatible input accepted: {first}, {second}")
            count := count + 1
  for name in ["left", "right"] do
    for (arguments, nullable) in [
        ("NULL,NULL", true), ("'abc',NULL", true), ("NULL,2", true), ("'abc','2'", false),
        ("'abc','bad'", false), ("'abc','2147483648'", false), ("'abc',-2147483648", false),
        ("'abc',2147483647", false), ("'abc',CAST(2.5 AS INTEGER)", false),
        ("CAST('a  ' AS CHAR(5)),2", false), ("CAST('a  ' AS VARCHAR(5)),2", false),
        ("CAST('é😀' AS NAME),2", false), ("'áb',1", false), ("'👨‍👩‍👧',-1", false),
        ("NULL,CAST('bad' AS INTEGER)", true)] do
      let sql := s!"SELECT {name}({arguments})"
      SQLean.Tests.assert ((← keywordOutput sql) == [⟨name, ⟨.text, nullable⟩⟩])
        s!"{name}: contextual input or deferred value obligation"
      count := count + 1
    for (sql, params, nullable) in [
        (s!"SELECT {name}(?,?) AS v", "TEXT,INTEGER", false),
        (s!"SELECT {name}($2,$1) AS v", "SMALLINT?,NAME", true),
        (s!"SELECT {name}($1,CAST($1 AS INTEGER)) AS v", "TEXT", false),
        (s!"SELECT {name}(CAST(? AS NAME),CAST(? AS INTEGER)) AS v", "TEXT?,NUMERIC", true),
        (s!"SELECT pg_catalog.{name}('abc',2) AS v", "", false),
        (s!"SELECT \"{name}\"('abc',2) AS v", "", false)] do
      SQLean.Tests.assert ((← keywordOutput sql params) == [⟨"v", ⟨.text, nullable⟩⟩])
        "keyword calls retain lexical occurrence order and exact declarations"
      count := count + 1
    for expr in [s!"{name}('abc',2)", s!"CAST({name}('abc',2) AS TEXT)",
        s!"CASE WHEN TRUE THEN {name}('abc',1) ELSE {name}('xyz',1) END"] do
      SQLean.Tests.assert ((← keywordOutput s!"SELECT {expr}") ==
        [⟨name, ⟨.text, false⟩⟩]) "strong function label survives composition"
      count := count + 1
    for arguments in ["", "'abc'", "'abc',1,2", "'abc',2147483648",
        "'abc',TRUE", "'abc',2.5", "'abc',CAST('2' AS TEXT)", "CAST('abc' AS BYTEA),1"] do
      let sql := s!"SELECT {name}({arguments})"
      let query ← expectOk sql (Advanced.parseQuery sql)
      match SelectContract.checkQuery .basicV31 [] [] query with
      | .error (.invalid diagnostic) =>
          SQLean.Tests.assert (diagnostic.code == "function_signature") "known wrong signature is Invalid"
      | _ => throw (IO.userError s!"{sql}: known incompatible signature accepted")
      count := count + 1
    for sql in [s!"SELECT application.{name}('abc',1)", s!"SELECT \"{name.toUpper}\"('abc',1)",
        s!"SELECT {name}(string=>'abc',n=>1)", s!"SELECT {name}((SELECT 'abc'),1)"] do
      let query ← expectOk sql (Advanced.parseQuery sql)
      match SelectContract.checkQuery .basicV31 [] [] query with
      | .error (.unsupported _) => pure ()
      | _ => throw (IO.userError s!"{sql}: unregistered routine/dependency must remain Unsupported")
      count := count + 1
  let query ← expectOk "keyword resource limit" (Advanced.parseQuery "SELECT left('abc',1)")
  match SelectContract.checkQuery .basicV31 [] [] query 1 with
  | .error (.inconclusive _) => pure ()
  | _ => throw (IO.userError "keyword call resource limit must remain Inconclusive")
  let query : Advanced.Query := {body := .select {items := [.expression
    (.call ["right"] [.parameter (.anonymous 2), .parameter (.anonymous 1)])]}}
  let params ← expectOk "keyword lexical declarations" (Assurance.parseContractParameterTypes "INTEGER,TEXT")
  match SelectContract.checkQuery .basicV31 [] params query with
  | .error (.invalid diagnostic) =>
      SQLean.Tests.assert (diagnostic.code == "parameter_notation")
        "function argument types must not permit anonymous occurrence reordering"
  | _ => throw (IO.userError "keyword function reordered anonymous occurrences")
  pure (count + 2)

private def keywordTypeLabel (base : SelectContract.ScalarType) : String :=
  match base with
  | .bool => "bool" | .int32 => "int32" | .text => "text"
  | base => base.dataType.toSql.toLower.replace ", " ","

def keywordFunctionsCorpusTests : IO Nat := do
  let records ← expectOk "keyword synthetic records"
    ((Lean.Json.parse (← IO.FS.readFile "fixtures/keyword_functions/synthetic.json")) >>= Lean.Json.getArr?)
  SQLean.Tests.assert (records.size == 50) "fifty authored keyword function queries required"
  let mut ids : List String := []
  let mut statements : List String := []
  for record in records do
    let id ← keywordField "synthetic" record "id"
    let sql ← keywordField id record "sql"
    SQLean.Tests.assert ((← keywordField id record "source_kind") == "synthetic") s!"{id}: source population"
    let parameters ← keywordField id record "parameter_types"
    let expected ← expectOk id ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
    let expected ← expected.toList.mapM fun column => do
      let name ← keywordField id column "name"
      let type ← keywordField id column "type"
      let nullable ← expectOk id ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
      pure (name, type, nullable)
    let actual ← keywordOutput sql parameters
    let labels := actual.map fun column =>
      (column.name, keywordTypeLabel column.type.base, column.type.nullable)
    SQLean.Tests.assert (labels == expected)
      s!"{id}: exact keyword output {reprStr labels}; expected {reprStr expected}"
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (decide ids.Nodup && decide statements.Nodup) "duplicate authored keyword queries"
  pure records.size

private def keywordSourceRegistry : List (String × List SelectContract.OutputColumn) :=
  let materialize := "keyword_functions:materialize:test/sqllogictest/string.slt:sqllogic-query-"
  let dolt := "keyword_functions:doltgresql:testing/generation/function_coverage/output/"
  let single := fun (id name : String) (nullable : Bool) =>
    (id, [SelectContract.OutputColumn.mk name ⟨.text, nullable⟩])
  [("keyword_functions:postgres:src/test/regress/sql/text.sql:statement-16",
    [⟨"left", ⟨.text, false⟩⟩, ⟨"right", ⟨.text, false⟩⟩])] ++
  ([1251, 1256, 1263, 1268, 1273, 1287, 1293] : List Nat).map
    (fun index => single (materialize ++ toString index) "left" ([1251, 1256].contains index)) ++
  ([1381, 1386, 1393, 1398, 1403, 1417, 1423] : List Nat).map
    (fun index => single (materialize ++ toString index) "right" ([1381, 1386].contains index)) ++
  ([1287, 3096, 4987, 6830, 7133, 9001, 10863, 12761, 14700, 15026, 16981,
      18966, 20926, 22891, 23211, 813, 2093] : List Nat).map
    (fun index => single (dolt ++ "left_test.go:go-string-" ++ toString index) "left" false) ++
  ([1294, 3121, 5030, 6891, 7197, 9083, 10963, 12879, 14836, 15165, 17138,
      19141, 21119, 23102, 23425, 815, 2108] : List Nat).map
    (fun index => single (dolt ++ "right_test.go:go-string-" ++ toString index) "right" false)

def keywordFunctionsConcreteContractTests : IO Nat := do
  let riverId := "keyword_functions:river:riverdriver/riverpgxv5/internal/dbsqlc/schema.sql.go:indexReindexArtifacts"
  let expectedIds := riverId :: keywordSourceRegistry.map Prod.fst
  SQLean.Tests.assert (keywordSourceRegistry.length == 49 && expectedIds.length == 50 &&
    decide expectedIds.Nodup && (keywordSourceRegistry.map (fun row => row.2.length)).sum == 50)
    "fixed keyword source population and output positions"
  let source ← IO.FS.readFile "fixtures/keyword_functions/concrete.jsonl"
  let lines := (source.splitOn "\n").filter (fun line => !line.trimAscii.toString.isEmpty)
  SQLean.Tests.assert (lines.length == 50) "fifty unchanged keyword source statements required"
  let mut ids : List String := []
  let mut statements : List String := []
  let mut certified := 0
  for line in lines do
    let record ← expectOk "keyword source" (Lean.Json.parse line)
    let id ← keywordField "source" record "id"
    let sql ← keywordField id record "sql"
    SQLean.Tests.assert (expectedIds.contains id && (← keywordField id record "raw_sql") == sql &&
      (← expectOk id (record.getObjVal? "parameter_types")) == Lean.Json.null)
      s!"{id}: source identity/bytes or unspecified declaration metadata changed"
    let observations ← expectOk id (record.getObjVal? "observed_syntax")
    let sourceFree ← expectOk id ((observations.getObjVal? "source_free") >>= Lean.Json.getBool?)
    let slots ← expectOk id ((record.getObjVal? "observed_parameter_slots") >>= Lean.Json.getArr?)
    let slots ← slots.toList.mapM fun slot => expectOk id slot.getNat?
    let query ← expectOk id (Advanced.parseQuery sql)
    if id == riverId then
      SQLean.Tests.assert (!sourceFree && query.ctes.length == 1 && slots == [1, 2] &&
        Advanced.queryParameters 1024 query ==
          ([1, 2, 1, 1] : List Nat).map Advanced.Parameter.numbered)
        "River dependency and exact lexical occurrences must remain explicit"
      let identity ← expectOk id ((RenderContract.check .identityV01 query).mapError reprStr)
      let postgres ← expectOk id ((RenderContract.check .postgres16V01 query).mapError reprStr)
      have _identity := identity.roundTrip
      have _postgres := postgres.roundTrip
    else
      SQLean.Tests.assert (sourceFree && query.ctes.isEmpty && slots.isEmpty &&
        (Advanced.queryParameters 1024 query).isEmpty)
        s!"{id}: closed source acquired context or parameter dependencies"
      match query.body with
      | .select select =>
          SQLean.Tests.assert select.source.isNone s!"{id}: closed source acquired FROM"
      | _ => throw (IO.userError s!"{id}: registered source body changed")
      match keywordSourceRegistry.lookup id with
      | none => throw (IO.userError s!"{id}: source has no registered complete-query expectation")
      | some expected =>
          SQLean.Tests.assert ((← keywordCertificate query) == expected)
            s!"{id}: exact registered output names, types and nullable flags"
      certified := certified + 1
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (certified == 49 && decide ids.Nodup && decide statements.Nodup &&
    expectedIds.all ids.contains) "complete source registry must be replayed exactly once"
  pure certified

end SQLean.Tests
