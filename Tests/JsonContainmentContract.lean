import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

namespace SQLean.Tests

/-- JSON null is still a non-NULL JSONB value. Containment needs no additional
missing-element nullability, unlike extraction. -/
example : SelectContract.ExprValid [⟨1, ⟨.jsonb, []⟩, false⟩] .empty
    (.containment (.parameter (.anonymous 1)) (.literal (.text "null")))
    (some ⟨.bool, false⟩) [.anonymous 1] :=
  .containment (selected := ⟨[.jsonb, .jsonb], .bool⟩)
    (.parameter (binding := ⟨1, ⟨.jsonb, []⟩, false⟩) (base := .jsonb)
      (by simp) rfl rfl) .text rfl

example : SelectContract.ExprValid [⟨1, ⟨.jsonb, []⟩, false⟩] .empty
    (.containment .null (.parameter (.anonymous 1)) true)
    (some ⟨.bool, true⟩) [.anonymous 1] :=
  .containment (selected := ⟨[.jsonb, .jsonb], .bool⟩) .null
    (.parameter (binding := ⟨1, ⟨.jsonb, []⟩, false⟩) (base := .jsonb)
      (by simp) rfl rfl) rfl

example : SelectContract.jsonContainmentSignature
    (.unknown false) (.unknown true) = none := rfl

example : SelectContract.jsonContainmentSignature
    (.known ⟨.text, false⟩) (.known ⟨.jsonb, false⟩) = none := rfl

private def containmentCertificate (query : Advanced.Query)
    (params : SelectContract.ParameterEnv := []) :
    IO (List SelectContract.OutputColumn) := do
  let certificate ← expectOk "JSONB containment SELECT"
    ((SelectContract.checkQuery .basicV30 [] params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let identity ← expectOk "JSONB containment identity renderer"
    ((RenderContract.check .identityV01 query).mapError reprStr)
  let postgres ← expectOk "JSONB containment PostgreSQL renderer"
    ((RenderContract.check .postgres16V01 query).mapError reprStr)
  have _identity : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
  have _postgres : Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
    postgres.roundTrip
  pure certificate.output

private def containmentOutput (sql : String) (parameterTypes : String := "") :
    IO (List SelectContract.OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let params ← expectOk sql (Assurance.parseContractParameterTypes parameterTypes)
  containmentCertificate query params

private def containmentField (id : String) (record : Lean.Json) (name : String) : IO String :=
  expectOk s!"{id}: {name}" ((record.getObjVal? name) >>= Lean.Json.getStr?)

private def containmentInventoryTests : IO Nat := do
  let json ← expectOk "JSONB containment inventory JSON"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/json_containment/operator_signatures.json"))
  let records ← expectOk "JSONB containment inventory records" json.getArr?
  SQLean.Tests.assert (records.size == 2) "expected exactly two JSONB containment declarations"
  let mut observed : List Bool := []
  for record in records do
    let spelling ← containmentField "containment inventory" record "operator"
    let direction ← match SelectContract.jsonContainmentDirections.filter
        (SelectContract.jsonContainmentSpelling · == spelling) with
      | [direction] => pure direction
      | _ => throw (IO.userError s!"unknown containment inventory operator: {spelling}")
    let parseType := fun field => do
      let name ← containmentField spelling record field
      let declaration ← expectOk name (Advanced.parseDataType name)
      match SelectContract.concreteType declaration with
      | some base => pure (declaration, base.unmodified)
      | none => throw (IO.userError s!"unsupported containment inventory type: {name}")
    let (leftDeclaration, left) ← parseType "left"
    let (rightDeclaration, right) ← parseType "right"
    let (_, output) ← parseType "output"
    SQLean.Tests.assert
      (SelectContract.jsonContainmentSignature (.known ⟨left, false⟩) (.known ⟨right, false⟩) ==
        some ⟨[left, right], output⟩) s!"containment exact selected overload: {spelling}"
    SQLean.Tests.assert
      (SelectContract.jsonContainmentFunctionName direction ==
        (← containmentField spelling record "function")) "containment native function identity"
    let query : Advanced.Query := { body := .select { items := [
      .expression (.containment (.cast .null leftDeclaration) (.cast .null rightDeclaration)
        direction) (some "v")] } }
    SQLean.Tests.assert ((← containmentCertificate query) == [⟨"v", ⟨.bool, true⟩⟩])
      "containment inventory full-query output"
    observed := direction :: observed
  SQLean.Tests.assert (decide observed.Nodup &&
      SelectContract.jsonContainmentDirections.all observed.contains &&
      observed.all SelectContract.jsonContainmentDirections.contains)
    "JSONB containment fixture differs from complete selected catalog inventory"
  pure records.size

def jsonContainmentContractTests : IO Nat := do
  let mut count ← containmentInventoryTests
  for direction in SelectContract.jsonContainmentDirections do
    let spelling := SelectContract.jsonContainmentSpelling direction
    for leftNullable in [false, true] do
      for rightNullable in [false, true] do
        let params := (if leftNullable then "jsonb?" else "jsonb") ++ "," ++
          (if rightNullable then "jsonb?" else "jsonb")
        SQLean.Tests.assert ((← containmentOutput s!"SELECT $1 {spelling} $2 AS v" params) ==
          [⟨"v", ⟨.bool, leftNullable || rightNullable⟩⟩])
          "containment nullability must propagate exactly the operand flags"
        count := count + 1
    for (unknown, nullable) in [("'{}'", false), ("'null'", false), ("NULL", true)] do
      for sql in [s!"SELECT {unknown} {spelling} $1 AS v",
          s!"SELECT $1 {spelling} {unknown} AS v"] do
        SQLean.Tests.assert ((← containmentOutput sql "jsonb") ==
          [⟨"v", ⟨.bool, nullable⟩⟩]) s!"single unknown JSONB context: {sql}"
        count := count + 1
    for left in ["NULL", "'{}'", "'null'"] do
      for right in ["NULL", "'{}'", "'null'"] do
        let sql := s!"SELECT {left} {spelling} {right}"
        let query ← expectOk sql (Advanced.parseQuery sql)
        match SelectContract.checkQuery .basicV30 [] [] query with
        | .error (.invalid diagnostic) =>
            SQLean.Tests.assert (diagnostic.code == "json_containment_signature")
              "unknown containment must retain the signature diagnostic"
        | _ => throw (IO.userError s!"two unknown containment operands must be Invalid: {sql}")
        count := count + 1
    for declaration in ["SMALLINT", "INTEGER", "BIGINT", "NUMERIC(8,2)", "REAL",
        "DOUBLE PRECISION", "TEXT", "VARCHAR(5)", "CHAR(5)", "BOOLEAN", "DATE",
        "TIME(3)", "TIME(3) WITH TIME ZONE", "TIMESTAMP(3)",
        "TIMESTAMP(3) WITH TIME ZONE", "INTERVAL(3)", "UUID", "JSON", "BYTEA"] do
      for (left, right) in [(s!"NULL::{declaration}", "NULL::JSONB"),
          ("NULL::JSONB", s!"NULL::{declaration}"),
          (s!"NULL::{declaration}", "NULL"), ("NULL", s!"NULL::{declaration}")] do
        let sql := s!"SELECT {left} {spelling} {right}"
        let query ← expectOk sql (Advanced.parseQuery sql)
        match SelectContract.checkQuery .basicV30 [] [] query with
        | .error (.invalid _) => pure ()
        | _ => throw (IO.userError s!"unavailable non-JSONB containment signature: {sql}")
        count := count + 1
    for (left, right, expected, nullable) in [
        ("ARRAY[1]", "ARRAY[2]", "valid", false),
        ("ARRAY[1]", "ARRAY[2::BIGINT]", "invalid", false),
        ("NULL::JSON[]", "NULL::JSON[]", "unsupported", true),
        ("NULL::TEXT[]", "NULL::TEXT[]", "valid", true),
        ("NULL::JSONB[]", "NULL", "valid", true), ("NULL", "NULL::JSONB[]", "valid", true),
        ("NULL::JSONB[]", "NULL::JSONB", "invalid", true),
        ("NULL::JSONB", "NULL::JSONB[]", "invalid", true)] do
      let sql := s!"SELECT {left} {spelling} {right}"
      let query ← expectOk sql (Advanced.parseQuery sql)
      if expected == "valid" then
        SQLean.Tests.assert ((← containmentCertificate query) == [⟨"?column?", ⟨.bool, nullable⟩⟩])
          s!"promoted array containment output: {sql}"
      else match SelectContract.checkQuery .basicV30 [] [] query with
      | .error (.unsupported diagnostic) =>
          SQLean.Tests.assert (expected == "unsupported" && diagnostic.code == "array_element_equality")
            "array element equality boundary"
      | .error (.invalid _) => SQLean.Tests.assert (expected == "invalid") "array signature boundary"
      | _ => throw (IO.userError s!"unexpected array containment boundary: {sql}")
      count := count + 1
    SQLean.Tests.assert ((← containmentOutput ("SELECT '{}'::JSONB " ++ spelling ++ " '{}'::JSONB")) ==
      [⟨"?column?", ⟨.bool, false⟩⟩]) "containment default label"
    count := count + 1
  let examples : List (String × SelectContract.ScalarType × Bool) := [
    ("SELECT '{\"a\":1,\"b\":2}'::JSONB @> '{\"a\":1}' AS v", .bool, false),
    ("SELECT '{\"a\":1}' <@ '{\"a\":1,\"b\":2}'::JSONB AS v", .bool, false),
    ("SELECT '{\"a\":{\"b\":1,\"c\":2}}'::JSONB @> '{\"a\":{\"b\":1}}' AS v", .bool, false),
    ("SELECT '[1,2,3]'::JSONB @> '[3,1,1]' AS v", .bool, false),
    ("SELECT '[1,2,3]'::JSONB @> '2' AS v", .bool, false),
    ("SELECT '2'::JSONB <@ '[1,2,3]' AS v", .bool, false),
    ("SELECT 'null'::JSONB @> 'null' AS v", .bool, false),
    ("SELECT '[null]'::JSONB @> 'null' AS v", .bool, false),
    ("SELECT NULL::JSONB <@ '{}' AS v", .bool, true),
    ("SELECT '{}'::JSONB @> 'malformed JSON' AS v", .bool, false),
    ("SELECT '{\"a\":1}'::JSONB @> '{}'::JSONB || 'x' AS v", .text, false),
    ("SELECT '{}'::JSONB || '{\"a\":1}'::JSONB @> '{\"a\":1}' AS v", .bool, false),
    ("SELECT '{\"a\":{\"b\":1}}'::JSONB -> 'a' @> '{\"b\":1}' AS v", .bool, true),
    ("SELECT CASE WHEN TRUE THEN '{}'::JSONB ELSE NULL END @> '{}' AS v", .bool, true),
    ("SELECT COALESCE(NULL::JSONB,'{}') <@ '{}'::JSONB AS v", .bool, false),
    ("SELECT NOT ('{}'::JSONB @> 'null') AS v", .bool, false),
    ("SELECT DISTINCT '{}'::JSONB <@ '{}' AS v ORDER BY v", .bool, false),
    ("SELECT d.a @> '{}' AS v FROM (SELECT '{}'::JSONB AS a) d", .bool, false),
    ("SELECT 1 AS v WHERE '{}'::JSONB @> '{}'", .int32, false),
    ("SELECT '{}'::JSONB @> '{}' = TRUE AS v", .bool, false)]
  for (sql, output, nullable) in examples do
    SQLean.Tests.assert ((← containmentOutput sql) == [⟨"v", ⟨output, nullable⟩⟩])
      s!"containment composition/output: {sql}"
    count := count + 1
  for sql in [
      "SELECT (SELECT '{}'::JSONB) @> '{}'",
      "SELECT '{}'::JSONB <@ (SELECT '{}'::JSONB)",
      "SELECT unknown_function() @> '{}'",
      "SELECT ROW(1,2) <@ '{}'::JSONB"] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV30 [] [] query with
    | .error (.unsupported _) => pure ()
    | _ => throw (IO.userError s!"containment child coverage must stay Unsupported: {sql}")
    count := count + 1
  for (sql, params, nullable) in [
      ("SELECT ? @> ? AS v", "jsonb,jsonb", false),
      ("SELECT $2 <@ $1 AS v", "jsonb?,jsonb", true),
      ("SELECT (CASE WHEN ? THEN ? ELSE ? END) @> ? AS v", "bool,jsonb,jsonb,jsonb", false),
      ("SELECT ? @> d.a AS v FROM (SELECT ?::JSONB AS a) d", "jsonb,jsonb", false)] do
    SQLean.Tests.assert ((← containmentOutput sql params) == [⟨"v", ⟨.bool, nullable⟩⟩])
      s!"containment lexical parameter order: {sql}"
    count := count + 1
  let params ← expectOk "containment bindings" (Assurance.parseContractParameterTypes "jsonb,jsonb")
  for expr in [
      Advanced.Expr.containment (.parameter (.numbered 1)) (.parameter (.anonymous 2)),
      .containment (.parameter (.anonymous 2)) (.parameter (.anonymous 1)) true] do
    let query : Advanced.Query := { body := .select { items := [.expression expr] } }
    match SelectContract.checkQuery .basicV30 [] params query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError "mixed or reordered containment parameters must be Invalid")
    count := count + 1
  let query ← expectOk "containment exhaustion" (Advanced.parseQuery "SELECT '{}'::JSONB @> '{}'")
  match SelectContract.checkQuery .basicV30 [] [] query 1 with
  | .error (.inconclusive _) => pure ()
  | _ => throw (IO.userError "containment exhaustion must be Inconclusive")
  pure (count + 1)

def jsonContainmentCorpusTests : IO Nat := do
  let json ← expectOk "JSONB containment fixture JSON"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/json_containment/synthetic.json"))
  let records ← expectOk "JSONB containment fixture records" json.getArr?
  SQLean.Tests.assert (records.size == 50) "expected exactly 50 JSONB containment synthetic queries"
  let mut ids : List String := []
  let mut statements : List String := []
  for record in records do
    let id ← containmentField "containment fixture" record "id"
    let sql ← containmentField id record "sql"
    SQLean.Tests.assert ((← containmentField id record "source_kind") == "synthetic") s!"{id}: population"
    let parameters ← containmentField id record "parameter_types"
    let expected ← expectOk id ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
    let expected ← expected.toList.mapM fun column => do
      let name ← containmentField id column "name"
      let type ← containmentField id column "type"
      let nullable ← expectOk id ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
      pure (name, type, nullable)
    let actual ← containmentOutput sql parameters
    let labels := actual.map fun column =>
      let type := match column.type.base with
        | .bool => "bool"
        | .int32 => "int32"
        | .text => "text"
        | base => (base.dataType.toSql.toLower).replace ", " ","
      (column.name, type, column.type.nullable)
    SQLean.Tests.assert (labels == expected)
      s!"{id}: exact JSONB containment output {reprStr labels}; expected {reprStr expected}"
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (decide ids.Nodup && decide statements.Nodup)
    "duplicate JSONB containment corpus identities or SQL"
  pure records.size

/-- The registered literal-only source population receives whole-query
certificates with actually empty environments. The other eight authentic
queries retain rendering evidence only; no catalog is fabricated for them. -/
def jsonContainmentConcreteContractTests : IO Nat := do
  let source ← IO.FS.readFile "fixtures/json_containment/concrete.jsonl"
  let lines := (source.splitOn "\n").filter (fun line => !line.trimAscii.toString.isEmpty)
  SQLean.Tests.assert (lines.length == 50) "expected exactly fifty concrete containment queries"
  let certifiedNumbers : List Nat := [
    139, 140, 141, 142, 143, 145, 146, 147, 148, 149, 150, 151,
    159, 160, 161, 162, 163, 165, 166, 167, 168, 169, 170, 171, 172,
    641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657]
  let renderingNumbers : List Nat := [499, 500, 501, 502, 503, 665, 666, 667]
  let identity := fun (n : Nat) => s!"json_containment:postgres:src/test/regress/sql/jsonb.sql:statement-{n}"
  let certifiedIds := certifiedNumbers.map identity
  let renderingIds := renderingNumbers.map identity
  let expectedIds := certifiedIds ++ renderingIds
  SQLean.Tests.assert (certifiedIds.length == 42 && renderingIds.length == 8 &&
      decide expectedIds.Nodup) "concrete containment populations must be complete and disjoint"
  let mut ids : List String := []
  let mut statements : List String := []
  let mut count := 0
  for line in lines do
    let record ← expectOk "concrete containment JSON" (Lean.Json.parse line)
    let id ← containmentField "concrete containment" record "id"
    SQLean.Tests.assert (expectedIds.contains id) s!"unregistered concrete containment identity: {id}"
    let sql ← containmentField id record "sql"
    SQLean.Tests.assert ((← containmentField id record "raw_sql") == sql &&
        (← containmentField id record "source") == "postgres" &&
        (← containmentField id record "source_kind") == "engine-regression")
      s!"{id}: concrete containment source population changed"
    let slots ← expectOk id ((record.getObjVal? "observed_parameter_slots") >>= Lean.Json.getArr?)
    SQLean.Tests.assert slots.isEmpty s!"{id}: no concrete parameter assumptions are authorized"
    let sourceFree ← expectOk id do
      let observations ← record.getObjVal? "observed_syntax"
      (observations.getObjVal? "source_free") >>= Lean.Json.getBool?
    SQLean.Tests.assert (sourceFree == certifiedIds.contains id)
      s!"{id}: explicit concrete validity/rendering boundary changed"
    let query ← expectOk id (Advanced.parseQuery sql)
    SQLean.Tests.assert (Advanced.queryParameters 1024 query == [])
      s!"{id}: concrete query contains undeclared parameters"
    if certifiedIds.contains id then
      match query.body with
      | .select select =>
          SQLean.Tests.assert (select.source.isNone && query.ctes.isEmpty)
            s!"{id}: certified concrete population must remain source-free"
      | _ => throw (IO.userError s!"{id}: unexpected certified concrete structure")
      SQLean.Tests.assert ((← containmentCertificate query) == [⟨"?column?", ⟨.bool, false⟩⟩])
        s!"{id}: exact concrete containment certificate output"
      count := count + 1
    else
      match query.body with
      | .select select =>
          SQLean.Tests.assert (select.source.isSome && query.ctes.isEmpty)
            s!"{id}: rendering-only concrete source shape changed"
      | _ => throw (IO.userError s!"{id}: unexpected rendering-only query structure")
      let identity ← expectOk id ((RenderContract.check .identityV01 query).mapError reprStr)
      let postgres ← expectOk id ((RenderContract.check .postgres16V01 query).mapError reprStr)
      have _identity := identity.roundTrip
      have _postgres := postgres.roundTrip
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (count == 42 && decide ids.Nodup && decide statements.Nodup &&
      expectedIds.all ids.contains) "concrete containment identities must match both fixed populations"
  pure count

end SQLean.Tests
