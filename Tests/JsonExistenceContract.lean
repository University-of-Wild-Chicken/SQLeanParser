import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

namespace SQLean.Tests

/-- Unknown literals receive operator context without being confused with
known TEXT expressions. The POINT overload makes only ?| ambiguous here. -/
example : SelectContract.jsonExistenceSignature .key (.unknown false) (.unknown false) =
    some ⟨[.jsonb, .text], .bool⟩ := rfl
example : SelectContract.jsonExistenceSignature .all (.unknown true) (.unknown false) =
    some ⟨[.jsonb, .array .text], .bool⟩ := rfl
example : SelectContract.jsonExistenceSignature .any (.unknown false) (.unknown false) = none := rfl
example : SelectContract.jsonExistenceSignature .key
    (.known ⟨.text, false⟩) (.unknown false) = none := rfl

example : SelectContract.ExprValid [⟨1, ⟨.jsonb, []⟩, false⟩] .empty
    (.jsonExistence .key (.parameter (.anonymous 1)) (.literal (.text "a")))
    (some ⟨.bool, false⟩) [.anonymous 1] :=
  .jsonExistence (selected := ⟨[.jsonb, .text], .bool⟩)
    (.parameter (binding := ⟨1, ⟨.jsonb, []⟩, false⟩) (base := .jsonb)
      (by simp) rfl rfl) .text rfl

example : SelectContract.ExprValid [] .empty
    (.jsonExistence .all .null (.literal (.text "{a}")))
    (some ⟨.bool, true⟩) [] :=
  .jsonExistence (selected := ⟨[.jsonb, .array .text], .bool⟩) .null .text rfl

private def existenceField (id : String) (record : Lean.Json) (name : String) : IO String :=
  expectOk s!"{id}: {name}" ((record.getObjVal? name) >>= Lean.Json.getStr?)

private def existenceCertificate (query : Advanced.Query)
    (params : SelectContract.ParameterEnv := []) : IO (List SelectContract.OutputColumn) := do
  let certificate ← expectOk "JSONB existence SELECT"
    ((SelectContract.checkQuery .basicV27 [] params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let identity ← expectOk "JSONB existence identity renderer"
    ((RenderContract.check .identityV01 query).mapError reprStr)
  let postgres ← expectOk "JSONB existence PostgreSQL renderer"
    ((RenderContract.check .postgres16V01 query).mapError reprStr)
  have _identity : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
  have _postgres : Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
    postgres.roundTrip
  pure certificate.output

private def existenceOutput (sql : String) (parameterTypes : String := "") :
    IO (List SelectContract.OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let params ← expectOk sql (Assurance.parseContractParameterTypes parameterTypes)
  existenceCertificate query params

private def existenceInventoryTests : IO Nat := do
  let records ← expectOk "JSONB existence inventory"
    ((Lean.Json.parse (← IO.FS.readFile "fixtures/json_existence/function_signatures.json")) >>= Lean.Json.getArr?)
  SQLean.Tests.assert (records.size == 3) "expected three JSONB existence declarations"
  let mut observed : List Advanced.JsonExistenceOp := []
  for record in records do
    let spelling ← existenceField "inventory" record "operator"
    let op ← match SelectContract.jsonExistenceOperators.filter
        (SelectContract.jsonExistenceSpelling · == spelling) with
      | [op] => pure op
      | _ => throw (IO.userError s!"unknown existence operator: {spelling}")
    let parseType := fun field => do
      let name ← existenceField spelling record field
      let type ← expectOk name (Advanced.parseDataType name)
      match SelectContract.concreteType type with
      | some base => pure (type, base.unmodified)
      | none => throw (IO.userError s!"unsupported existence catalog type: {name}")
    let (leftType, left) ← parseType "left"
    let (rightType, right) ← parseType "right"
    let (_, output) ← parseType "output"
    let selected : SelectContract.FunctionOverload := ⟨[left, right], output⟩
    SQLean.Tests.assert (SelectContract.jsonExistenceCatalog op == [selected] &&
      SelectContract.jsonExistenceSignature op (.known ⟨left, false⟩) (.known ⟨right, false⟩) == some selected)
      s!"{spelling}: exact selected signature"
    SQLean.Tests.assert (SelectContract.jsonExistenceFunctionName op ==
      (← existenceField spelling record "function")) s!"{spelling}: exact native function"
    let query : Advanced.Query := {body := .select {items := [
      .expression (.jsonExistence op (.cast .null leftType) (.cast .null rightType)) (some "v")]}}
    SQLean.Tests.assert ((← existenceCertificate query) == [⟨"v", ⟨.bool, true⟩⟩])
      "existence inventory independent full certificate"
    observed := op :: observed
  SQLean.Tests.assert (decide observed.Nodup && SelectContract.jsonExistenceOperators.all observed.contains)
    "existence inventory must contain each declaration exactly once"
  pure records.size

def jsonExistenceContractTests : IO Nat := do
  let mut count ← existenceInventoryTests
  /- This matrix is registered independently of the signature function: a closed
  list marks JSONB subjects, scalar string keys and string-array keys explicitly. -/
  let declarations : List (String × Bool × Bool × Bool) := [
    ("", false, false, false),
    ("SMALLINT", false, false, false), ("INTEGER", false, false, false),
    ("BIGINT", false, false, false), ("NUMERIC(8,2)", false, false, false),
    ("REAL", false, false, false), ("DOUBLE PRECISION", false, false, false),
    ("TEXT", false, true, false), ("VARCHAR(3)", false, true, false),
    ("CHAR(3)", false, true, false), ("BOOLEAN", false, false, false),
    ("DATE", false, false, false), ("TIME", false, false, false),
    ("TIME WITH TIME ZONE", false, false, false), ("TIMESTAMP", false, false, false),
    ("TIMESTAMP WITH TIME ZONE", false, false, false), ("INTERVAL", false, false, false),
    ("UUID", false, false, false), ("JSON", false, false, false),
    ("JSONB", true, false, false), ("BYTEA", false, false, false),
    ("TEXT[]", false, false, true), ("VARCHAR(3)[]", false, false, true),
    ("CHAR(3)[]", false, false, true), ("INTEGER[]", false, false, false),
    ("JSON[]", false, false, false), ("JSONB[]", false, false, false),
    ("TEXT[][]", false, false, true)]
  let expression := fun (name : String) => do
    if name.isEmpty then pure Advanced.Expr.null
    else pure (.cast .null (← expectOk name (Advanced.parseDataType name)))
  for op in SelectContract.jsonExistenceOperators do
    for (left, isJsonb, _, _) in declarations do
      for (right, _, isText, isTextArray) in declarations do
        let expected := (left.isEmpty || isJsonb) &&
          (right.isEmpty || (if op == .key then isText else isTextArray)) &&
          !(op == .any && left.isEmpty && right.isEmpty)
        let expr := Advanced.Expr.jsonExistence op (← expression left) (← expression right)
        let query : Advanced.Query := {body := .select {items := [.expression expr (some "v")]}}
        if expected then
          SQLean.Tests.assert ((← existenceCertificate query) == [⟨"v", ⟨.bool, true⟩⟩])
            s!"existence matrix exact output: {reprStr op}/{left}/{right}"
        else
          match SelectContract.checkQuery .basicV27 [] [] query with
          | .error (.invalid diagnostic) =>
              SQLean.Tests.assert (diagnostic.code == "json_existence_signature") "closed unsupported overload must be Invalid"
          | _ => throw (IO.userError s!"existence matrix expected Invalid: {reprStr op}/{left}/{right}")
        count := count + 1
  for op in SelectContract.jsonExistenceOperators do
    let spelling := SelectContract.jsonExistenceSpelling op
    let rightType := if op == .key then "TEXT" else "TEXT[]"
    for leftNullable in [false, true] do
      for rightNullable in [false, true] do
        let parameters := (if leftNullable then "JSONB?" else "JSONB") ++ "," ++
          rightType ++ (if rightNullable then "?" else "")
        SQLean.Tests.assert ((← existenceOutput s!"SELECT $1 {spelling} $2 AS v" parameters) ==
          [⟨"v", ⟨.bool, leftNullable || rightNullable⟩⟩]) "existence outer nullability"
        count := count + 1
  let examples : List (String × String × SelectContract.ScalarType × Bool) := [
    ("SELECT '{\"a\":1}' ? 'a' AS v", "v", .bool, false),
    ("SELECT '{\"a\":1}' ?& '{a}' AS v", "v", .bool, false),
    ("SELECT '{\"a\":1}' ?| ARRAY['a'] AS v", "v", .bool, false),
    ("SELECT '{}'::JSONB ? NULL AS v", "v", .bool, true),
    ("SELECT NULL ?& '{}' AS v", "v", .bool, true),
    ("SELECT '{}'::JSONB ?| ARRAY[NULL] AS v", "v", .bool, false),
    ("SELECT '{}'::JSONB ?& ARRAY[NULL] AS v", "v", .bool, false),
    ("SELECT 'null'::JSONB ?& ARRAY[]::TEXT[] AS v", "v", .bool, false),
    ("SELECT NULL::JSONB ?| ARRAY[]::TEXT[] AS v", "v", .bool, true),
    ("SELECT '{\"a\":1}'::JSONB ? 'a'::CHAR(3) AS v", "v", .bool, false),
    ("SELECT '{\"a\":1}'::JSONB ?& ARRAY['a'::CHAR(3)] AS v", "v", .bool, false),
    ("SELECT '{\"a\":1}'::JSONB ?| ARRAY[['a',NULL],['b','a']] AS v", "v", .bool, false),
    ("SELECT '{}'::JSONB ?& '[0:1]={a,b}'::TEXT[] AS v", "v", .bool, false),
    ("SELECT 'invalid-json' ? 'a' AS v", "v", .bool, false),
    ("SELECT '{}'::JSONB ?& 'invalid-array' AS v", "v", .bool, false),
    ("SELECT '{}'::JSONB ? 'a'", "?column?", .bool, false),
    ("SELECT '{}'::JSONB ?| ARRAY['a']", "?column?", .bool, false),
    ("SELECT '{}'::JSONB ?& ARRAY['a']", "?column?", .bool, false),
    ("SELECT CAST(('{}'::JSONB ? 'a') AS BOOLEAN)", "bool", .bool, false),
    ("SELECT CASE WHEN TRUE THEN FALSE ELSE ('{}'::JSONB ? 'a') END", "case", .bool, false),
    ("SELECT '{\"a\":1}'::JSONB ? 'a' || 'b' AS v", "v", .text, false),
    ("SELECT '{\"a\":1}'::JSONB ? ('a' || 'b') AS v", "v", .bool, false),
    ("SELECT '{\"a\":{\"b\":1}}'::JSONB -> 'a' ? 'b' AS v", "v", .bool, true),
    ("SELECT '{}'::JSONB || '{\"a\":1}'::JSONB ? 'a' AS v", "v", .bool, false),
    ("SELECT COALESCE(NULL::JSONB,'{}') ? 'a' AS v", "v", .bool, false),
    ("SELECT CASE WHEN TRUE THEN '{}'::JSONB ELSE NULL END ? 'a' AS v", "v", .bool, true),
    ("SELECT NOT ('{}'::JSONB ? 'a') AS v", "v", .bool, false),
    ("SELECT DISTINCT '{}'::JSONB ? 'a' AS v ORDER BY v", "v", .bool, false),
    ("SELECT q.data ? 'a' AS v FROM (SELECT '{}'::JSONB AS data) q", "v", .bool, false),
    ("SELECT 1 AS v WHERE '{}'::JSONB ? 'a'", "v", .int32, false)]
  for (sql, name, type, nullable) in examples do
    SQLean.Tests.assert ((← existenceOutput sql) == [⟨name, ⟨type, nullable⟩⟩])
      s!"existence composition/output: {sql}"
    count := count + 1
  for sql in [
      "SELECT '{\"a\":1}' ?| '{a}'", "SELECT NULL ?| NULL",
      "SELECT COALESCE(NULL,'{}') ? 'a'", "SELECT '{}'::JSON ? 'a'",
      "SELECT '{}'::JSONB ?| 'a'::TEXT", "SELECT '{}'::JSONB ? 1",
      "SELECT '{}'::JSONB ?& ARRAY[1]", "SELECT '{}'::JSONB ? ARRAY['a']"] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV27 [] [] query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError s!"expected invalid existence signature: {sql}")
    count := count + 1
  for sql in [
      "SELECT (SELECT '{}'::JSONB) ? 'a'", "SELECT '{}'::JSONB ? (SELECT 'a')",
      "SELECT unknown_function() ?& ARRAY['a']", "SELECT ROW(1,2) ? 'a'"] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV27 [] [] query with
    | .error (.unsupported _) => pure ()
    | _ => throw (IO.userError s!"unsupported existence child must remain unsupported: {sql}")
    count := count + 1
  for (sql, parameters, nullable) in [
      ("SELECT ? ? ? AS v", "JSONB,TEXT", false),
      ("SELECT ? ?| ? AS v", "JSONB,TEXT[]", false),
      ("SELECT ? ?& ? AS v", "JSONB,TEXT[]?", true),
      ("SELECT $2 ? $1 AS v", "TEXT,JSONB?", true),
      ("SELECT (CASE WHEN ? THEN ? ELSE ? END) ? ? AS v", "BOOLEAN,JSONB,JSONB,TEXT", false),
      ("SELECT ? ? q.key_name AS v FROM (SELECT ? AS key_name) q", "JSONB,TEXT", false),
      ("SELECT (? ? ?) AND (? ? ?) AS v", "JSONB,TEXT,JSONB,TEXT", false)] do
    SQLean.Tests.assert ((← existenceOutput sql parameters) == [⟨"v", ⟨.bool, nullable⟩⟩])
      s!"existence lexical placeholder order: {sql}"
    count := count + 1
  for (expr, parameterTypes) in [
      (Advanced.Expr.jsonExistence .key (.parameter (.numbered 1)) (.parameter (.anonymous 2)), "JSONB,TEXT"),
      (.jsonExistence .key (.parameter (.anonymous 2)) (.parameter (.anonymous 1)), "TEXT,JSONB")] do
    let parameters ← expectOk "existence bindings" (Assurance.parseContractParameterTypes parameterTypes)
    let query : Advanced.Query := {body := .select {items := [.expression expr]}}
    match SelectContract.checkQuery .basicV27 [] parameters query with
    | .error (.invalid diagnostic) =>
        SQLean.Tests.assert (diagnostic.code == "parameter_notation")
          "well-typed existence operands must fail specifically on parameter notation"
    | _ => throw (IO.userError "mixed or out-of-order anonymous existence operands must be Invalid")
    count := count + 1
  let query : Advanced.Query := {body := .select {items := [
    .expression (.jsonExistence .key (.cast .null ⟨.jsonb, []⟩) (.literal (.text "a")))]}}
  match SelectContract.checkQuery .basicV27 [] [] query 1 with
  | .error (.inconclusive _) => pure ()
  | _ => throw (IO.userError "existence resource exhaustion must be Inconclusive")
  pure (count + 1)

def jsonExistenceCorpusTests : IO Nat := do
  let records ← expectOk "JSONB existence synthetic records"
    ((Lean.Json.parse (← IO.FS.readFile "fixtures/json_existence/synthetic.json")) >>= Lean.Json.getArr?)
  SQLean.Tests.assert (records.size == 50) "expected fifty JSONB existence authored queries"
  let mut ids : List String := []
  let mut statements : List String := []
  for record in records do
    let id ← existenceField "synthetic" record "id"
    let sql ← existenceField id record "sql"
    SQLean.Tests.assert ((← existenceField id record "source_kind") == "synthetic") s!"{id}: population"
    let parameters ← existenceField id record "parameter_types"
    let expected ← expectOk id ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
    let expected ← expected.toList.mapM fun column => do
      let name ← existenceField id column "name"
      let type ← existenceField id column "type"
      let nullable ← expectOk id ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
      pure (name, type, nullable)
    let actual ← existenceOutput sql parameters
    let labels := actual.map fun column =>
      (column.name, (match column.type.base with
        | .bool => "bool" | .int32 => "int32" | .text => "text"
        | base => base.dataType.toSql.toLower.replace ", " ","), column.type.nullable)
    SQLean.Tests.assert (labels == expected) s!"{id}: exact existence output {reprStr labels}; expected {reprStr expected}"
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (decide ids.Nodup && decide statements.Nodup) "duplicate existence fixture identities or SQL"
  pure records.size

/-- The eligibility registry is fixed before validation: forty-four literal-only
queries receive complete certificates; six external-catalog queries retain
rendering evidence only. The River parameter is preserved, never assigned a
fabricated binding environment. -/
def jsonExistenceConcreteContractTests : IO Nat := do
  let source ← IO.FS.readFile "fixtures/json_existence/concrete.jsonl"
  let lines := (source.splitOn "\n").filter (fun line => !line.trimAscii.toString.isEmpty)
  SQLean.Tests.assert (lines.length == 50) "expected fifty unchanged existence source queries"
  let pgId := fun (n : Nat) => s!"json_existence:postgres:src/test/regress/sql/jsonb.sql:statement-{n}"
  let cockroachId := fun (n : Nat) => s!"json_existence:cockroach:pkg/sql/logictest/testdata/logic_test/json:sqllogic-query-{n}"
  let materializeId := fun (n : Nat) => s!"json_existence:materialize:test/sqllogictest/jsonb.slt:sqllogic-query-{n}"
  let contribId := "json_existence:postgres:contrib/pg_stat_statements/sql/select.sql:statement-25"
  let riverId := "json_existence:river:riverdriver/riverpgxv5/internal/dbsqlc/river_job.sql.go:jobGetCancelRequested"
  let pgNumbers : List Nat := [
    189, 190, 191, 192, 201, 202, 203, 204, 205, 211, 212, 213, 214, 215, 216,
    707, 708, 709, 710, 711, 712]
  let cockroachNumbers : List Nat := [467, 472, 477, 482, 487, 492, 498, 504, 509, 514, 519, 524, 529, 534]
  let materializeNumbers : List Nat := [657, 663, 668, 719, 745, 751, 756, 761]
  let certifiedIds := [contribId] ++ pgNumbers.map pgId ++
    cockroachNumbers.map cockroachId ++ materializeNumbers.map materializeId
  let renderingIds := [riverId] ++ ([193, 194, 504, 506, 507] : List Nat).map pgId
  let expectedIds := certifiedIds ++ renderingIds
  let doubleOutputIds := ([467, 472, 477, 487] : List Nat).map cockroachId ++
    ([657, 719] : List Nat).map materializeId
  let nullableIds := ([663, 668] : List Nat).map materializeId
  SQLean.Tests.assert (certifiedIds.length == 44 && renderingIds.length == 6 &&
    decide expectedIds.Nodup && doubleOutputIds.length == 6 && nullableIds.length == 2)
    "existence source populations must be fixed and disjoint"
  let mut ids : List String := []
  let mut statements : List String := []
  let mut certified := 0
  let mut positions := 0
  for line in lines do
    let record ← expectOk "existence source JSON" (Lean.Json.parse line)
    let id ← existenceField "source" record "id"
    SQLean.Tests.assert (expectedIds.contains id) s!"unregistered existence source identity: {id}"
    let sql ← existenceField id record "sql"
    SQLean.Tests.assert ((← existenceField id record "raw_sql") == sql) s!"{id}: source bytes changed"
    let sourceName ← existenceField id record "source"
    SQLean.Tests.assert (id.startsWith s!"json_existence:{sourceName}:" &&
      (← existenceField id record "source_kind") == (if id == riverId then "application-constant" else "engine-regression"))
      s!"{id}: provenance population changed"
    let sourceFree ← expectOk id do
      let observations ← record.getObjVal? "observed_syntax"
      (observations.getObjVal? "source_free") >>= Lean.Json.getBool?
    SQLean.Tests.assert (sourceFree == certifiedIds.contains id) s!"{id}: eligibility changed"
    let slots ← expectOk id ((record.getObjVal? "observed_parameter_slots") >>= Lean.Json.getArr?)
    let expectedSlots : List Nat := if id == riverId then [1] else []
    let observedSlots ← slots.toList.mapM fun slot => expectOk id slot.getNat?
    SQLean.Tests.assert (observedSlots == expectedSlots) s!"{id}: observed parameter slots changed"
    let query ← expectOk id (Advanced.parseQuery sql)
    SQLean.Tests.assert (Advanced.queryParameters 1024 query == expectedSlots.map Advanced.Parameter.numbered)
      s!"{id}: exact source parameter occurrences"
    match query.body with
    | .select select =>
        SQLean.Tests.assert (query.ctes.isEmpty && select.source.isNone == sourceFree)
          s!"{id}: source eligibility AST changed"
    | _ => throw (IO.userError s!"{id}: unexpected source structure")
    if certifiedIds.contains id then
      let width := if doubleOutputIds.contains id then 2 else 1
      let expected : List SelectContract.OutputColumn :=
        List.replicate width ⟨"?column?", ⟨.bool, nullableIds.contains id⟩⟩
      SQLean.Tests.assert ((← existenceCertificate query) == expected)
        s!"{id}: complete source certificate exact output"
      certified := certified + 1
      positions := positions + width
    else
      let identity ← expectOk id ((RenderContract.check .identityV01 query).mapError reprStr)
      let postgres ← expectOk id ((RenderContract.check .postgres16V01 query).mapError reprStr)
      have _identity := identity.roundTrip
      have _postgres := postgres.roundTrip
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (certified == 44 && positions == 50 && decide ids.Nodup &&
      decide statements.Nodup && expectedIds.all ids.contains)
    "existence source registry must contain all fifty original statements exactly once"
  pure certified

end SQLean.Tests
