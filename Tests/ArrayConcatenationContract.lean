import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.ContractSupport
import Lean.Data.Json

namespace SQLean.Tests

example : SelectContract.arrayConcatSignature
    (.known ⟨.array (.numeric [8, 2]), false⟩)
    (.known ⟨.numeric [8, 2], true⟩) =
    some ⟨.append, [.array (.numeric []), .numeric []], .array (.numeric [])⟩ := rfl

example : SelectContract.arrayConcatSignature
    (.known ⟨.array .json, false⟩) (.unknown true) =
    some ⟨.cat, [.array .json, .array .json], .array .json⟩ := rfl

/-- A NULL element does not make an appended array nullable. This derivation
uses a binding with a nullable array and a second nullable element binding. -/
example : SelectContract.ExprValid
    [⟨1, ⟨.array .int, []⟩, true⟩, ⟨2, ⟨.int, []⟩, true⟩] .empty
    (.concat (.parameter (.anonymous 1)) (.parameter (.anonymous 2)))
    (some ⟨.array .int32, false⟩) [.anonymous 1, .anonymous 2] :=
  .arrayConcat (selected := ⟨.append, [.array .int32, .int32], .array .int32⟩)
    (.parameter (binding := ⟨1, ⟨.array .int, []⟩, true⟩) (base := .array .int32)
      (by simp) rfl rfl)
    (.parameter (binding := ⟨2, ⟨.int, []⟩, true⟩) (base := .int32)
      (by simp) rfl rfl) rfl

private def arrayConcatCertificate (query : Advanced.Query)
    (params : SelectContract.ParameterEnv := []) :
    IO (List SelectContract.OutputColumn) := do
  let certificate ← expectOk "array concatenation SELECT"
    ((SelectContract.checkQuery .basicV32 [] params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let identity ← expectOk "array concatenation identity renderer"
    ((RenderContract.check .identityV01 query).mapError reprStr)
  let postgres ← expectOk "array concatenation PostgreSQL renderer"
    ((RenderContract.check .postgres16V01 query).mapError reprStr)
  have _identity : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
  have _postgres : Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
    postgres.roundTrip
  pure certificate.output

private def arrayConcatOutput (sql : String) (parameterTypes : String := "") :
    IO (List SelectContract.OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let params ← expectOk sql (Assurance.parseContractParameterTypes parameterTypes)
  arrayConcatCertificate query params

private def arrayConcatField (id : String) (record : Lean.Json) (name : String) : IO String :=
  expectOk s!"{id}: {name}" ((record.getObjVal? name) >>= Lean.Json.getStr?)

private def arrayConcatTypeLabel : SelectContract.ScalarType → String
  | .char [] => "bpchar"
  | .array element => arrayConcatTypeLabel element ++ "[]"
  | base => (base.dataType.toSql.toLower).replace ", " ","

private def arrayConcatInventoryTests : IO Nat := do
  let json ← expectOk "array concatenation catalog JSON"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/array_concatenation/operator_signatures.json"))
  let records ← expectOk "array concatenation catalog records" json.getArr?
  SQLean.Tests.assert (records.size == 3) "expected exactly three array concatenation declarations"
  let mut observed : List (List String × String × String) := []
  for record in records do
    SQLean.Tests.assert ((← arrayConcatField "catalog" record "operator") == "||")
      "array concatenation catalog operator"
    let left ← arrayConcatField "catalog" record "left"
    let right ← arrayConcatField "catalog" record "right"
    let output ← arrayConcatField "catalog" record "output"
    let function ← arrayConcatField "catalog" record "function"
    observed := ([left, right], output, function) :: observed
  let expected := SelectContract.arrayConcatOperators.map fun operator =>
    (operator.catalogInputs, operator.catalogOutput, operator.functionName)
  SQLean.Tests.assert (decide observed.Nodup && expected.all observed.contains &&
      observed.all expected.contains)
    "array concatenation fixture differs from the complete admitted catalog"
  pure records.size

def arrayConcatenationContractTests : IO Nat := do
  let mut count ← arrayConcatInventoryTests
  let declarations : Array (String × SelectContract.ScalarType) := #[
    ("SMALLINT", .smallInt), ("INTEGER", .int32), ("BIGINT", .int64),
    ("NUMERIC(8,2)", .numeric []), ("REAL", .real), ("DOUBLE PRECISION", .doublePrecision),
    ("TEXT", .text), ("VARCHAR(5)", .varchar []), ("CHAR(5)", .char []),
    ("BOOLEAN", .bool), ("DATE", .date), ("TIME(3)", .time []),
    ("TIME(3) WITH TIME ZONE", .timeTZ []), ("TIMESTAMP(3)", .timestamp []),
    ("TIMESTAMP(3) WITH TIME ZONE", .timestampTZ []), ("INTERVAL(3)", .interval []),
    ("UUID", .uuid), ("JSON", .json), ("JSONB", .jsonb), ("BYTEA", .bytea)]
  -- Registered PG16 result identities for all sixty-four compatible pairs.
  -- Each row contains (right-input index, result-element index). Every other
  -- pair is an explicit negative; no checker-success selection is performed.
  let pairs : Array (List (Nat × Nat)) := #[
    [(0,0),(1,1),(2,2),(3,3),(4,4),(5,5)],
    [(0,1),(1,1),(2,2),(3,3),(4,4),(5,5)],
    [(0,2),(1,2),(2,2),(3,3),(4,4),(5,5)],
    [(0,3),(1,3),(2,3),(3,3),(4,4),(5,5)],
    [(0,4),(1,4),(2,4),(3,4),(4,4),(5,5)],
    [(0,5),(1,5),(2,5),(3,5),(4,5),(5,5)],
    [(6,6),(7,6),(8,6)], [(6,7),(7,7),(8,7)], [(6,8),(7,8),(8,8)],
    [(9,9)], [(10,10),(13,13),(14,14)], [(11,11),(12,12)],
    [(11,12),(12,12)], [(10,13),(13,13),(14,14)],
    [(10,14),(13,14),(14,14)], [(15,15)], [(16,16)], [(17,17)], [(18,18)], [(19,19)]]
  SQLean.Tests.assert (pairs.size == declarations.size &&
      (pairs.toList.map List.length).sum == 64) "array concatenation expected matrix dimensions"
  for i in [:declarations.size] do
    let (leftName, leftBase) := declarations[i]!
    for j in [:declarations.size] do
      let (rightName, rightBase) := declarations[j]!
      let expected := (pairs[i]!).lookup j
      for operator in SelectContract.arrayConcatOperators do
        let (left, right, leftType, rightType) := match operator with
          | .cat => (leftName ++ "[]", rightName ++ "[]", leftBase.asArray, rightBase.asArray)
          | .append => (leftName ++ "[]", rightName, leftBase.asArray, rightBase)
          | .prepend => (leftName, rightName ++ "[]", leftBase, rightBase.asArray)
        let sql := s!"SELECT NULL::{left} || NULL::{right} AS v"
        let query ← expectOk sql (Advanced.parseQuery sql)
        match expected with
        | some resultIndex =>
            let element := (declarations[resultIndex]!).2
            let inputs := match operator with
              | .cat => [element.asArray, element.asArray]
              | .append => [element.asArray, element]
              | .prepend => [element, element.asArray]
            SQLean.Tests.assert
              (SelectContract.arrayConcatSignature (.known ⟨leftType, true⟩)
                (.known ⟨rightType, true⟩) == some ⟨operator, inputs, element.asArray⟩)
              s!"array concatenation exact selected instantiation: {sql}"
            SQLean.Tests.assert (sameOutputTypes (← arrayConcatCertificate query) [{name := "v", type := ⟨element.asArray, operator == .cat⟩}])
              s!"array concatenation matrix output: {sql}"
        | none =>
            match SelectContract.checkQuery .basicV32 [] [] query with
            | .error (.invalid diagnostic) =>
                SQLean.Tests.assert (diagnostic.code == "concatenation_signature")
                  s!"incompatible array element signature: {sql}"
            | _ => throw (IO.userError s!"incompatible array elements must be Invalid: {sql}")
        count := count + 1
    for (unknown, nullable) in [("NULL", true), ("'{}'", false)] do
      for sql in [s!"SELECT NULL::{leftName}[] || {unknown} AS v",
          s!"SELECT {unknown} || NULL::{leftName}[] AS v"] do
        SQLean.Tests.assert (sameOutputTypes (← arrayConcatOutput sql) [{name := "v", type := ⟨leftBase.asArray, nullable⟩}])
          s!"unknown operand must select array_cat: {sql}"
        count := count + 1
  for operator in SelectContract.arrayConcatOperators do
    for leftNullable in [false, true] do
      for rightNullable in [false, true] do
        let (left, right) := match operator with
          | .cat => ("INTEGER[]", "INTEGER[]")
          | .append => ("INTEGER[]", "INTEGER")
          | .prepend => ("INTEGER", "INTEGER[]")
        let parameters := left ++ (if leftNullable then "?" else "") ++ "," ++
          right ++ (if rightNullable then "?" else "")
        let nullable := operator == .cat && leftNullable && rightNullable
        SQLean.Tests.assert (sameOutputTypes (← arrayConcatOutput "SELECT $1 || $2 AS v" parameters) [{name := "v", type := ⟨.array .int32, nullable⟩}]) "array family-specific NULL propagation"
        count := count + 1
  let examples : List (String × SelectContract.ScalarType × Bool) := [
    ("SELECT NULL::INTEGER[] || ARRAY[1,NULL,3] AS v", .int32, false),
    ("SELECT ARRAY[1,NULL,3] || NULL::INTEGER[] AS v", .int32, false),
    ("SELECT ARRAY[]::INTEGER[] || NULL::INTEGER[] AS v", .int32, false),
    ("SELECT NULL::INTEGER[] || ARRAY[]::INTEGER[] AS v", .int32, false),
    ("SELECT ARRAY[]::INTEGER[] || ARRAY[]::INTEGER[] AS v", .int32, false),
    ("SELECT NULL::INTEGER[] || NULL::INTEGER[] AS v", .int32, true),
    ("SELECT NULL::INTEGER[] || NULL::INTEGER AS v", .int32, false),
    ("SELECT NULL::INTEGER || NULL::INTEGER[] AS v", .int32, false),
    ("SELECT ARRAY[1] || NULL::INTEGER AS v", .int32, false),
    ("SELECT NULL::INTEGER || ARRAY[1] AS v", .int32, false),
    ("SELECT ARRAY[1] || '2' AS v", .int32, false),
    ("SELECT ARRAY['a'] || 'b' AS v", .text, false),
    ("SELECT ARRAY['1'::JSON] || ARRAY['null'::JSON] AS v", .json, false),
    ("SELECT ARRAY['1'::JSON] || 'null'::JSON AS v", .json, false),
    ("SELECT 'null'::JSON || ARRAY['1'::JSON] AS v", .json, false),
    ("SELECT ARRAY['1'::JSON] || ('{}'::JSON -> 'missing') AS v", .json, false),
    ("SELECT ARRAY[1.23::NUMERIC(8,2)] || ARRAY[2.34::NUMERIC(8,2)] AS v", .numeric [], false),
    ("SELECT ARRAY['a'::VARCHAR(5)] || ARRAY['b'::VARCHAR(5)] AS v", .varchar [], false),
    ("SELECT ARRAY['a'::CHAR(5)] || ARRAY['b'::TEXT] AS v", .char [], false),
    ("SELECT ARRAY['a'::TEXT] || ARRAY['b'::CHAR(5)] AS v", .text, false),
    ("SELECT ARRAY[[1,2]] || ARRAY[[3,4]] AS v", .int32, false),
    ("SELECT ARRAY[1,2] || ARRAY[[3,4],[5,6]] AS v", .int32, false),
    ("SELECT ARRAY[[1,2],[3,4]] || ARRAY[5,6] AS v", .int32, false),
    ("SELECT ARRAY[1,2] || ARRAY[[[3,4]]] AS v", .int32, false),
    ("SELECT ARRAY[[1,2]] || ARRAY[[3,4,5]] AS v", .int32, false),
    ("SELECT ARRAY[[1,2]] || 3 AS v", .int32, false),
    ("SELECT 3 || ARRAY[[1,2]] AS v", .int32, false),
    ("SELECT '[0:1]={1,2}'::INTEGER[] || '[5:6]={3,4}'::INTEGER[] AS v", .int32, false),
    ("SELECT '[0:1]={1,2}'::INTEGER[] || 3 AS v", .int32, false),
    ("SELECT 3 || '[0:1]={1,2}'::INTEGER[] AS v", .int32, false),
    ("SELECT COALESCE(NULL::INTEGER[],ARRAY[1]) || 2 AS v", .int32, false),
    ("SELECT (NULL::INTEGER[] || NULL::INTEGER) || 2 AS v", .int32, false),
    ("SELECT d.a || 2 AS v FROM (SELECT ARRAY[1] AS a) d", .int32, false)]
  for (sql, element, nullable) in examples do
    SQLean.Tests.assert (sameOutputTypes (← arrayConcatOutput sql) [{name := "v", type := ⟨element.asArray, nullable⟩}])
      s!"array concatenation composition/type: {sql}"
    count := count + 1
  SQLean.Tests.assert (sameOutputTypes (← arrayConcatOutput "SELECT ARRAY[1] || ARRAY[2]") [{name := "?column?", type := ⟨.array .int32, false⟩}]) "array concatenation default label"
  count := count + 1
  for sql in ["SELECT ARRAY[] || ARRAY[1]", "SELECT ARRAY[1] || ARRAY[]"] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV32 [] [] query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError s!"untyped empty constructors must remain Invalid: {sql}")
    count := count + 1
  for sql in ["SELECT ARRAY[1] || (SELECT ARRAY[2])",
      "SELECT (SELECT 1) || ARRAY[2]"] do
    SQLean.Tests.assert (sameOutputTypes (← arrayConcatOutput sql)
      [{name := "?column?", type := ⟨.array .int32, false⟩}])
      "non-strict array concatenation with a nonnullable array absorbs scalar subquery NULL"
    count := count + 1
  for sql in ["SELECT ARRAY[1] || unknown_function()", "SELECT ROW(1,2) || ARRAY[1]"] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV32 [] [] query with
    | .error (.unsupported _) => pure ()
    | _ => throw (IO.userError s!"array child coverage must remain Unsupported: {sql}")
    count := count + 1
  for (sql, parameters, nullable) in [
      ("SELECT ? || ? AS v", "int[],int[]", false),
      ("SELECT $2 || $1 AS v", "int?,int[]?", false),
      ("SELECT (? || ?) || ? AS v", "int[]?,int[]?,int[]?", true),
      ("SELECT ? || d.a AS v FROM (SELECT ?::INTEGER[] AS a) d", "int,int[]?", false)] do
    SQLean.Tests.assert (sameOutputTypes (← arrayConcatOutput sql parameters) [{name := "v", type := ⟨.array .int32, nullable⟩}]) s!"array lexical parameter order: {sql}"
    count := count + 1
  let params ← expectOk "array bindings" (Assurance.parseContractParameterTypes "int[],int[]")
  for expr in [
      Advanced.Expr.concat (.parameter (.numbered 1)) (.parameter (.anonymous 2)),
      .concat (.parameter (.anonymous 2)) (.parameter (.anonymous 1))] do
    let query : Advanced.Query := { body := .select { items := [.expression expr] } }
    match SelectContract.checkQuery .basicV32 [] params query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError "mixed/reordered array parameters must be Invalid")
    count := count + 1
  let query ← expectOk "array exhaustion" (Advanced.parseQuery "SELECT ARRAY[1] || ARRAY[2]")
  match SelectContract.checkQuery .basicV32 [] [] query 1 with
  | .error (.inconclusive _) => pure ()
  | _ => throw (IO.userError "array concatenation exhaustion must be Inconclusive")
  pure (count + 1)

def arrayConcatenationCorpusTests : IO Nat := do
  let json ← expectOk "array concatenation fixture JSON"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/array_concatenation/synthetic.json"))
  let records ← expectOk "array concatenation fixture records" json.getArr?
  SQLean.Tests.assert (records.size == 50) "expected exactly fifty synthetic array concatenations"
  let mut ids : List String := []
  let mut statements : List String := []
  for record in records do
    let id ← arrayConcatField "array fixture" record "id"
    let sql ← arrayConcatField id record "sql"
    SQLean.Tests.assert ((← arrayConcatField id record "source_kind") == "synthetic") s!"{id}: population"
    let parameters ← arrayConcatField id record "parameter_types"
    let expected ← expectOk id ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
    let expected ← expected.toList.mapM fun column => do
      let name ← arrayConcatField id column "name"
      let type ← arrayConcatField id column "type"
      let nullable ← expectOk id ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
      pure (name, type, nullable)
    let actual ← arrayConcatOutput sql parameters
    let labels := actual.map fun column =>
      (column.name, arrayConcatTypeLabel column.type.base, column.type.nullable)
    SQLean.Tests.assert (labels == expected)
      s!"{id}: exact array concatenation output {reprStr labels}; expected {reprStr expected}"
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (decide ids.Nodup && decide statements.Nodup)
    "duplicate array concatenation corpus identities or SQL"
  pure records.size

/-- All fifty registered source queries are source-free and parameter-free.
The expected types below describe PostgreSQL analysis, including the original
RisingWave queries; they do not assert cross-engine evaluation equivalence. -/
def arrayConcatenationConcreteContractTests : IO Nat := do
  let source ← IO.FS.readFile "fixtures/array_concatenation/concrete.jsonl"
  let lines := (source.splitOn "\n").filter (fun line => !line.trimAscii.toString.isEmpty)
  SQLean.Tests.assert (lines.length == 50) "expected exactly fifty concrete array concatenations"
  let postgres : List (Nat × String × SelectContract.ScalarType) := [
    (160, "{1,2,3}", .int32), (161, "{0,1,2}", .int32),
    (162, "{1,2,3,4}", .int32), (163, "ARRAY", .text),
    (164, "{{1,2},{3,4},{5,6}}", .int32), (165, "{0,0,1,1,2,2}", .int32),
    (166, "{0,1,2,3}", .int32), (167, "?column?", .numeric [])]
  let risingwave : List (Nat × SelectContract.ScalarType) := [
    (31, .varchar []), (36, .text),
    (41, .smallInt), (46, .smallInt), (51, .smallInt),
    (56, .int32), (61, .int32), (66, .int32),
    (71, .int64), (76, .int64), (81, .int64),
    (116, .int32), (121, .int32), (126, .int32),
    (131, .int32), (136, .int32), (141, .int32),
    (146, .int64), (151, .int64), (156, .int64),
    (191, .int64), (196, .int64), (201, .int64),
    (206, .int64), (211, .int64), (216, .int64),
    (221, .int64), (226, .int64), (231, .int64),
    (311, .numeric []), (316, .numeric []), (321, .numeric []),
    (326, .real), (331, .real), (336, .real),
    (386, .real), (391, .real), (396, .real),
    (401, .real), (406, .real), (411, .real), (666, .timestamp [])]
  let expected : List (String × String × String × SelectContract.ScalarType) :=
    (postgres.map fun (n, name, element) =>
      (s!"array_concatenation:postgres:src/test/regress/sql/arrays.sql:statement-{n}",
        "postgres", name, element)) ++
    (risingwave.map fun (n, element) =>
      (s!"array_concatenation:risingwave:e2e_test/batch/functions/array_concat.slt.part:sqllogic-query-{n}",
        "risingwave", "?column?", element))
  let expectedIds := expected.map (fun entry => entry.1)
  SQLean.Tests.assert (postgres.length == 8 && risingwave.length == 42 &&
      decide expectedIds.Nodup) "concrete array identities must be complete and unique"
  let mut ids : List String := []
  let mut statements : List String := []
  for line in lines do
    let record ← expectOk "concrete array concatenation JSON" (Lean.Json.parse line)
    let id ← arrayConcatField "concrete array concatenation" record "id"
    let (_, origin, name, element) ← match expected.find? (fun entry => entry.1 == id) with
      | some entry => pure entry
      | none => throw (IO.userError s!"unregistered concrete array concatenation identity: {id}")
    let sql ← arrayConcatField id record "sql"
    SQLean.Tests.assert ((← arrayConcatField id record "raw_sql") == sql &&
        (← arrayConcatField id record "source") == origin &&
        (← arrayConcatField id record "source_kind") == "engine-regression")
      s!"{id}: concrete array provenance changed"
    if origin == "risingwave" then
      SQLean.Tests.assert ((← arrayConcatField id record "source_dialect") == "risingwave")
        s!"{id}: source dialect must remain explicit"
    let slots ← expectOk id ((record.getObjVal? "observed_parameter_slots") >>= Lean.Json.getArr?)
    SQLean.Tests.assert slots.isEmpty s!"{id}: no concrete parameter assumptions are authorized"
    let sourceFree ← expectOk id do
      let observations ← record.getObjVal? "observed_syntax"
      (observations.getObjVal? "source_free") >>= Lean.Json.getBool?
    SQLean.Tests.assert sourceFree s!"{id}: concrete validity population must remain source-free"
    let query ← expectOk id (Advanced.parseQuery sql)
    match query.body with
    | .select select =>
        SQLean.Tests.assert (select.source.isNone && query.ctes.isEmpty)
          s!"{id}: concrete certified query AST must remain source-free"
    | _ => throw (IO.userError s!"{id}: unexpected concrete certified query structure")
    SQLean.Tests.assert (Advanced.queryParameters 1024 query == [])
      s!"{id}: concrete query contains undeclared parameters"
    SQLean.Tests.assert (sameOutputTypes (← arrayConcatCertificate query) [{name := name, type := ⟨element.asArray, false⟩}])
      s!"{id}: exact PostgreSQL concrete array concatenation output"
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (decide ids.Nodup && decide statements.Nodup && expectedIds.all ids.contains)
    "concrete array population must match every registered identity"
  pure lines.length

end SQLean.Tests
