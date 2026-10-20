import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

namespace SQLean.Tests

example : SelectContract.arrayPredicateSignature
    (.known ⟨.array (.varchar [5]), false⟩)
    (.known ⟨.array (.varchar [9]), true⟩) =
    some ⟨[.array (.varchar []), .array (.varchar [])], .bool⟩ := rfl

example : SelectContract.arrayPredicateSignature
    (.known ⟨.array .int32, false⟩) (.known ⟨.array .int64, false⟩) = none := rfl

example : SelectContract.arrayPredicateMissingEquality
    (.known ⟨.array .json, true⟩) (.unknown true) = true := rfl

example : SelectContract.ExprValid [⟨1, ⟨.array .text, []⟩, false⟩] .empty
    (.overlap (.parameter (.anonymous 1)) (.literal (.text "{a,NULL}")))
    (some ⟨.bool, false⟩) [.anonymous 1] :=
  .overlap (selected := ⟨[.array .text, .array .text], .bool⟩)
    (.parameter (binding := ⟨1, ⟨.array .text, []⟩, false⟩) (base := .array .text)
      (by simp) rfl rfl) .text rfl

private def arrayPredicateExpr (op : SelectContract.ArrayPredicateOperator)
    (left right : Advanced.Expr) : Advanced.Expr :=
  match op with
  | .contains => .containment left right false
  | .containedBy => .containment left right true
  | .overlap => .overlap left right

private def arrayPredicateCertificate (query : Advanced.Query)
    (params : SelectContract.ParameterEnv := []) :
    IO (List SelectContract.OutputColumn) := do
  let certificate ← expectOk "array predicate SELECT"
    ((SelectContract.checkQuery .basicV19 [] params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let identity ← expectOk "array predicate identity renderer"
    ((RenderContract.check .identityV01 query).mapError reprStr)
  let postgres ← expectOk "array predicate PostgreSQL renderer"
    ((RenderContract.check .postgres16V01 query).mapError reprStr)
  have _identity : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
  have _postgres : Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
    postgres.roundTrip
  pure certificate.output

private def arrayPredicateOutput (sql : String) (parameterTypes : String := "") :
    IO (List SelectContract.OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let params ← expectOk sql (Assurance.parseContractParameterTypes parameterTypes)
  arrayPredicateCertificate query params

private def arrayPredicateField (id : String) (record : Lean.Json) (name : String) : IO String :=
  expectOk s!"{id}: {name}" ((record.getObjVal? name) >>= Lean.Json.getStr?)

private def arrayPredicateInventoryTests : IO Nat := do
  let json ← expectOk "array predicate catalog JSON"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/array_containment/operator_signatures.json"))
  let records ← expectOk "array predicate catalog records" json.getArr?
  SQLean.Tests.assert (records.size == 3) "expected three generic anyarray predicate declarations"
  let mut observed : List (String × List String × String × String) := []
  for record in records do
    let op ← arrayPredicateField "catalog" record "operator"
    let left ← arrayPredicateField op record "left"
    let right ← arrayPredicateField op record "right"
    let output ← arrayPredicateField op record "output"
    let function ← arrayPredicateField op record "function"
    observed := (op, [left, right], output, function) :: observed
  let expected := SelectContract.arrayPredicateOperators.map fun op =>
    (op.toSql, op.catalogInputs, op.catalogOutput, op.functionName)
  SQLean.Tests.assert (decide observed.Nodup && expected.all observed.contains &&
      observed.all expected.contains) "generic array predicate catalog inventory changed"
  let equalityJson ← expectOk "array element equality JSON"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/array_containment/element_equality_signatures.json"))
  let equalityRecords ← expectOk "array element equality records" equalityJson.getArr?
  SQLean.Tests.assert (equalityRecords.size == 19) "expected nineteen concrete element equalities"
  let mut elements : List SelectContract.ScalarType := []
  for record in equalityRecords do
    let parseType := fun field => do
      let name ← arrayPredicateField "element equality" record field
      if name == "bpchar" then pure (SelectContract.ScalarType.char [])
      else
        let declaration ← expectOk name (Advanced.parseDataType name)
        match SelectContract.concreteType declaration with
        | some base => pure base.unmodified
        | none => throw (IO.userError s!"unsupported element equality type: {name}")
    let element ← parseType "element"
    let left ← parseType "left"
    let right ← parseType "right"
    let output ← parseType "output"
    SQLean.Tests.assert ((← arrayPredicateField "equality" record "operator") == "=" &&
        !(← arrayPredicateField "equality" record "function").isEmpty)
      "element equality must identify a native equality function"
    SQLean.Tests.assert
      (SelectContract.comparisonOverload .eq (.known ⟨element, false⟩) (.known ⟨element, false⟩) ==
        some ⟨[left, right], output⟩) "element equality declared signature differs from normative selection"
    SQLean.Tests.assert
      (SelectContract.arrayPredicateSignature (.known ⟨element.asArray, false⟩)
        (.known ⟨element.asArray, false⟩) == some ⟨[element.asArray, element.asArray], .bool⟩)
      "element equality must enable the exact array predicate instantiation"
    elements := element :: elements
  SQLean.Tests.assert (decide elements.Nodup &&
      SelectContract.arrayPredicateElementTypes.all elements.contains &&
      elements.all SelectContract.arrayPredicateElementTypes.contains)
    "element equality fixture must match the complete closed inventory"
  pure (records.size + equalityRecords.size)

def arrayPredicateContractTests : IO Nat := do
  let mut count ← arrayPredicateInventoryTests
  let declarations : Array (String × SelectContract.ScalarType) := #[
    ("SMALLINT", .smallInt), ("INTEGER", .int32), ("BIGINT", .int64),
    ("NUMERIC(8,2)", .numeric []), ("REAL", .real), ("DOUBLE PRECISION", .doublePrecision),
    ("TEXT", .text), ("VARCHAR(5)", .varchar []), ("CHAR(5)", .char []),
    ("BOOLEAN", .bool), ("DATE", .date), ("TIME(3)", .time []),
    ("TIME(3) WITH TIME ZONE", .timeTZ []), ("TIMESTAMP(3)", .timestamp []),
    ("TIMESTAMP(3) WITH TIME ZONE", .timestampTZ []), ("INTERVAL(3)", .interval []),
    ("UUID", .uuid), ("JSON", .json), ("JSONB", .jsonb), ("BYTEA", .bytea)]
  for op in SelectContract.arrayPredicateOperators do
    for i in [:declarations.size] do
      let (leftName, leftBase) := declarations[i]!
      for j in [:declarations.size] do
        let rightName := (declarations[j]!).1
        let sql := s!"SELECT NULL::{leftName}[] {op.toSql} NULL::{rightName}[] AS v"
        let query ← expectOk sql (Advanced.parseQuery sql)
        if i == j && leftBase != .json then
          SQLean.Tests.assert ((← arrayPredicateCertificate query) == [⟨"v", ⟨.bool, true⟩⟩])
            s!"exact anyarray element identity: {sql}"
        else match SelectContract.checkQuery .basicV19 [] [] query with
        | .error (.unsupported diagnostic) =>
            SQLean.Tests.assert (i == j && leftBase == .json &&
                diagnostic.code == "array_element_equality") s!"array equality coverage: {sql}"
        | .error (.invalid _) =>
            SQLean.Tests.assert (i != j) s!"matching element types cannot be rejected: {sql}"
        | _ => throw (IO.userError s!"unexpected array predicate matrix result: {sql}")
        count := count + 1
      for (unknown, nullable) in [("NULL", true), ("'{}'", false)] do
        for sql in [s!"SELECT $1 {op.toSql} {unknown} AS v",
            s!"SELECT {unknown} {op.toSql} $1 AS v"] do
          if leftBase == .json then
            let query ← expectOk sql (Advanced.parseQuery sql)
            let params ← expectOk sql (Assurance.parseContractParameterTypes (leftName ++ "[]"))
            match SelectContract.checkQuery .basicV19 [] params query with
            | .error (.unsupported diagnostic) =>
                SQLean.Tests.assert (diagnostic.code == "array_element_equality")
                  "unknown JSON[] context must retain equality boundary"
            | _ => throw (IO.userError "unknown JSON[] predicate must be Unsupported")
          else
            SQLean.Tests.assert ((← arrayPredicateOutput sql (leftName ++ "[]")) ==
              [⟨"v", ⟨.bool, nullable⟩⟩]) s!"unknown array predicate context: {sql}"
          count := count + 1
    for leftNullable in [false, true] do
      for rightNullable in [false, true] do
        let params := (if leftNullable then "INTEGER[]?" else "INTEGER[]") ++ "," ++
          (if rightNullable then "INTEGER[]?" else "INTEGER[]")
        SQLean.Tests.assert ((← arrayPredicateOutput s!"SELECT $1 {op.toSql} $2 AS v" params) ==
          [⟨"v", ⟨.bool, leftNullable || rightNullable⟩⟩]) "array predicate strict NULL propagation"
        count := count + 1
    for (left, right) in [
        ("ARRAY[NULL::INTEGER]", "ARRAY[NULL::INTEGER]"),
        ("ARRAY[1,1]", "ARRAY[1]"), ("ARRAY[1]", "ARRAY[1,1]"),
        ("ARRAY[]::INTEGER[]", "ARRAY[]::INTEGER[]"),
        ("ARRAY[[1,2],[3,4]]", "ARRAY[4,1]"),
        ("'[0:1]={1,2}'::INTEGER[]", "'[5:6]={2,1}'::INTEGER[]"),
        ("ARRAY['null'::JSONB]", "ARRAY['null'::JSONB]"),
        ("ARRAY[1.23::NUMERIC(8,2)]", "ARRAY[1.230::NUMERIC(9,3)]"),
        ("ARRAY['a'::VARCHAR(5)]", "ARRAY['a'::VARCHAR(9)]"),
        ("ARRAY['a'::CHAR(5)]", "ARRAY['a'::CHAR(9)]"),
        ("ARRAY[TIMESTAMP(3) '2020-01-01']", "ARRAY[TIMESTAMP(6) '2020-01-01']"),
        ("ARRAY[1]", "'malformed array'")] do
      let sql := s!"SELECT {left} {op.toSql} {right} AS v"
      SQLean.Tests.assert ((← arrayPredicateOutput sql) == [⟨"v", ⟨.bool, false⟩⟩])
        s!"array shape/modifier/null-element typing: {sql}"
      count := count + 1
    for left in ["NULL", "'{}'"] do
      for right in ["NULL", "'{}'"] do
        let sql := s!"SELECT {left} {op.toSql} {right}"
        let query ← expectOk sql (Advanced.parseQuery sql)
        match SelectContract.checkQuery .basicV19 [] [] query with
        | .error (.invalid _) => pure ()
        | _ => throw (IO.userError s!"ambiguous array predicate must be Invalid: {sql}")
        count := count + 1
    for (left, right) in [("ARRAY[1]", "1"), ("1", "ARRAY[1]"),
        ("ARRAY['a']", "'a'::TEXT"), ("'a'::TEXT", "ARRAY['a']"),
        ("ARRAY['1'::JSON]", "ARRAY['1'::JSONB]")] do
      let sql := s!"SELECT {left} {op.toSql} {right}"
      let query ← expectOk sql (Advanced.parseQuery sql)
      match SelectContract.checkQuery .basicV19 [] [] query with
      | .error (.invalid _) => pure ()
      | _ => throw (IO.userError s!"known nonmatching array signature must be Invalid: {sql}")
      count := count + 1
    for (left, right) in [("ARRAY[]::JSON[]", "ARRAY[]::JSON[]"),
        ("ARRAY['1'::JSON]", "ARRAY['1'::JSON]"), ("NULL::JSON[]", "'{}'")] do
      let query ← expectOk "JSON[] predicate" (Advanced.parseQuery s!"SELECT {left} {op.toSql} {right}")
      match SelectContract.checkQuery .basicV19 [] [] query with
      | .error (.unsupported diagnostic) =>
          SQLean.Tests.assert (diagnostic.code == "array_element_equality") "JSON[] equality gap"
      | _ => throw (IO.userError "JSON[] predicates must retain missing-equality coverage boundary")
      count := count + 1
    SQLean.Tests.assert ((← arrayPredicateOutput s!"SELECT ARRAY[1] {op.toSql} ARRAY[1]") ==
      [⟨"?column?", ⟨.bool, false⟩⟩]) "array predicate default label"
    count := count + 1
    for sql in [s!"SELECT ARRAY[1] {op.toSql} (SELECT ARRAY[1])",
        s!"SELECT unknown_function() {op.toSql} ARRAY[1]",
        s!"SELECT ROW(1,2) {op.toSql} ARRAY[1]"] do
      let query ← expectOk sql (Advanced.parseQuery sql)
      match SelectContract.checkQuery .basicV19 [] [] query with
      | .error (.unsupported _) => pure ()
      | _ => throw (IO.userError s!"array predicate child coverage: {sql}")
      count := count + 1
    for (sql, params) in [
        (s!"SELECT ? {op.toSql} ? AS v", "INTEGER[],INTEGER[]"),
        (s!"SELECT $2 {op.toSql} $1 AS v", "INTEGER[],INTEGER[]"),
        (s!"SELECT ? {op.toSql} d.a AS v FROM (SELECT ?::INTEGER[] AS a) d", "INTEGER[],INTEGER[]")] do
      SQLean.Tests.assert ((← arrayPredicateOutput sql params) == [⟨"v", ⟨.bool, false⟩⟩])
        s!"array predicate lexical parameter order: {sql}"
      count := count + 1
    let params ← expectOk "predicate bindings" (Assurance.parseContractParameterTypes "INTEGER[],INTEGER[]")
    let bad : Advanced.Query := { body := .select { items := [.expression
      (arrayPredicateExpr op (.parameter (.anonymous 2)) (.parameter (.anonymous 1)))] } }
    match SelectContract.checkQuery .basicV19 [] params bad with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError "swapped array predicate ordinals must be Invalid")
    count := count + 1
    let query ← expectOk "predicate exhaustion" (Advanced.parseQuery s!"SELECT ARRAY[1] {op.toSql} ARRAY[1]")
    match SelectContract.checkQuery .basicV19 [] [] query 1 with
    | .error (.inconclusive _) => pure ()
    | _ => throw (IO.userError "array predicate exhaustion must be Inconclusive")
    count := count + 1
  for sql in ["SELECT '{}'::JSONB && '{}'::JSONB", "SELECT 1 && 1",
      "SELECT 'a'::TEXT && 'b'::TEXT"] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV19 [] [] query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError s!"closed nonarray overlap must be Invalid: {sql}")
    count := count + 1
  pure count

def arrayPredicateCorpusTests : IO Nat := do
  let mut count := 0
  for factor in ["array_containment", "array_overlap"] do
    let json ← expectOk s!"{factor} JSON"
      (Lean.Json.parse (← IO.FS.readFile s!"fixtures/{factor}/synthetic.json"))
    let records ← expectOk factor json.getArr?
    SQLean.Tests.assert (records.size == 50) s!"expected fifty {factor} synthetic queries"
    let mut ids : List String := []
    let mut statements : List String := []
    for record in records do
      let id ← arrayPredicateField factor record "id"
      let sql ← arrayPredicateField id record "sql"
      SQLean.Tests.assert ((← arrayPredicateField id record "source_kind") == "synthetic")
        s!"{id}: synthetic population"
      let parameters ← arrayPredicateField id record "parameter_types"
      let expected ← expectOk id ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
      let expected ← expected.toList.mapM fun column => do
        let name ← arrayPredicateField id column "name"
        let type ← arrayPredicateField id column "type"
        let nullable ← expectOk id ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
        pure (name, type, nullable)
      let actual ← arrayPredicateOutput sql parameters
      let labels := actual.map fun column =>
        (column.name, if column.type.base == .bool then "bool" else "unexpected", column.type.nullable)
      SQLean.Tests.assert (labels == expected)
        s!"{id}: exact array predicate output {reprStr labels}; expected {reprStr expected}"
      ids := id :: ids
      statements := sql :: statements
    SQLean.Tests.assert (decide ids.Nodup && decide statements.Nodup)
      s!"duplicate {factor} identities or SQL"
    count := count + records.size
  pure count

/-- Registered source-free statements have genuinely empty environments.
The other original queries retain rendering certificates only; notably, no
schema or parameter type is invented for the application/table-dependent SQL. -/
def arrayPredicateConcreteContractTests : IO Nat := do
  let groups : List (String × List (String × List Nat)) := [
    ("array_containment", [
      ("risingwave:e2e_test/batch/functions/array_predicates.slt.part:sqllogic-query-", [1,6,11,16]),
      ("rum:sql/array.sql:statement-", [7,8,39,40,41,42,43,44,45,46,47,48,50,51,52,53,54,55,56,57]),
      ("postgres:src/test/regress/sql/arrays.sql:statement-",
        [170,172,174,176,178,180,182,184,185,187,189,191,193,195]),
      ("postgres:src/test/regress/sql/create_index.sql:statement-",
        [122,124,130,132,134,136,139,141,144,146,148,150])]),
    ("array_overlap", [
      ("risingwave:e2e_test/batch/functions/array_predicates.slt.part:sqllogic-query-", [21,26,46,51]),
      ("rum:sql/array.sql:statement-", [6,27,28,29,30,31,32,33,34,35,36,37]),
      ("postgres:src/test/regress/sql/arrays.sql:statement-", [171,173,175,179,183,186,188,190,194]),
      ("postgres:src/test/regress/sql/create_index.sql:statement-",
        [123,131,133,135,140,145,147,149,154,161,162,163]),
      ("readyset:logictests/sqlparser/psql/array_overlap.test:sqllogic-query-", [15,22,30,35,40,46,52]),
      ("readyset:readyset-e2e-tests/tests/array_operators.rs:rust-string-", [5900,6027,6155,6276]),
      ("sqlc:examples/booktest/postgresql/query.sql:statement-", [4]),
      ("yugabyte:src/postgres/src/test/regress/sql/yb.orig.ybgin_misc.sql:statement-", [53])])]
  let mut certifiedCount := 0
  for (factor, registrations) in groups do
    let expectedIds := registrations.flatMap fun (stem, numbers) =>
      numbers.map fun n => factor ++ ":" ++ stem ++ toString n
    SQLean.Tests.assert (expectedIds.length == 50 && decide expectedIds.Nodup)
      s!"{factor}: exact concrete identities must be complete and unique"
    let sourceFreeIds :=
      (registrations.filter fun entry => entry.1.startsWith "risingwave:").flatMap
        (fun (stem, numbers) => numbers.map fun n => factor ++ ":" ++ stem ++ toString n) ++
      (if factor == "array_containment" then [7,8] else [6]).map
        (fun n => factor ++ ":rum:sql/array.sql:statement-" ++ toString n)
    let expectedCertified := if factor == "array_containment" then 6 else 5
    SQLean.Tests.assert (sourceFreeIds.length == expectedCertified &&
        decide sourceFreeIds.Nodup && sourceFreeIds.all expectedIds.contains)
      s!"{factor}: concrete full-certificate boundary must be registered"
    let source ← IO.FS.readFile s!"fixtures/{factor}/concrete.jsonl"
    let lines := (source.splitOn "\n").filter fun line => !line.trimAscii.toString.isEmpty
    SQLean.Tests.assert (lines.length == 50) s!"{factor}: expected fifty unchanged concrete sources"
    let mut observed : List String := []
    let mut statements : List String := []
    let mut certified := 0
    for line in lines do
      let record ← expectOk factor (Lean.Json.parse line)
      let id ← arrayPredicateField factor record "id"
      SQLean.Tests.assert (expectedIds.contains id) s!"{factor}: unregistered concrete identity {id}"
      let sql ← arrayPredicateField id record "sql"
      let origin ← arrayPredicateField id record "source"
      SQLean.Tests.assert ((← arrayPredicateField id record "raw_sql") == sql &&
          (id.splitOn ":").getD 1 "" == origin) s!"{id}: unchanged source/provenance required"
      let isSourceFree ← expectOk id do
        let observations ← record.getObjVal? "observed_syntax"
        (observations.getObjVal? "source_free") >>= Lean.Json.getBool?
      SQLean.Tests.assert (isSourceFree == sourceFreeIds.contains id)
        s!"{id}: fixed concrete validity boundary changed"
      let query ← expectOk id (Advanced.parseQuery sql)
      if sourceFreeIds.contains id then
        match query.body with
        | .select select =>
            SQLean.Tests.assert (select.source.isNone && query.ctes.isEmpty)
              s!"{id}: certified source AST must remain source-free"
        | _ => throw (IO.userError s!"{id}: certified source changed query structure")
        let slots ← expectOk id ((record.getObjVal? "observed_parameter_slots") >>= Lean.Json.getArr?)
        SQLean.Tests.assert (slots.isEmpty && Advanced.queryParameters 1024 query == [])
          s!"{id}: no parameter assumptions are authorized for the certified source population"
        SQLean.Tests.assert ((← arrayPredicateCertificate query) ==
          [⟨"?column?", ⟨.bool, origin == "rum"⟩⟩]) s!"{id}: exact concrete predicate output"
        certified := certified + 1
      else
        match query.body with
        | .select select =>
            SQLean.Tests.assert select.source.isSome
              s!"{id}: unregistered source-free case cannot silently receive rendering-only assurance"
        | _ => throw (IO.userError s!"{id}: rendering-only source changed query structure")
        let identity ← expectOk id ((RenderContract.check .identityV01 query).mapError reprStr)
        let postgres ← expectOk id ((RenderContract.check .postgres16V01 query).mapError reprStr)
        have _identity := identity.roundTrip
        have _postgres := postgres.roundTrip
      observed := id :: observed
      statements := sql :: statements
    SQLean.Tests.assert (certified == expectedCertified && decide observed.Nodup &&
        decide statements.Nodup && expectedIds.all observed.contains)
      s!"{factor}: concrete certificate/rendering populations must match every registered source"
    certifiedCount := certifiedCount + certified
  pure certifiedCount

end SQLean.Tests
