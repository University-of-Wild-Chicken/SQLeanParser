import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

namespace SQLean.Tests

example : SelectContract.SubstringArguments .forFrom
    [.unknown false, .known ⟨.int32, false⟩, .known ⟨.int32, true⟩]
    [.unknown false, .known ⟨.int32, true⟩, .known ⟨.int32, false⟩] := .forFrom

example : SelectContract.SubstringLengthValid (.known ⟨.bool, false⟩)
    ⟨.int32, false⟩ := .known rfl rfl

example : SelectContract.substringNullable ⟨[.text, .text], .text⟩
    [.unknown false, .unknown false] = true := rfl

private def substringField (id : String) (record : Lean.Json) (name : String) : IO String :=
  expectOk s!"{id}: {name}" ((record.getObjVal? name) >>= Lean.Json.getStr?)

private def substringCertificate (query : Advanced.Query)
    (params : SelectContract.ParameterEnv := []) :
    IO (List SelectContract.OutputColumn) := do
  let certificate ← expectOk "SUBSTRING SELECT"
    ((SelectContract.checkQuery .basicV23 [] params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let identity ← expectOk "SUBSTRING identity renderer"
    ((RenderContract.check .identityV01 query).mapError reprStr)
  let postgres ← expectOk "SUBSTRING PostgreSQL renderer"
    ((RenderContract.check .postgres16V01 query).mapError reprStr)
  have _identity : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
  have _postgres : Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
    postgres.roundTrip
  pure certificate.output

private def substringOutput (sql : String) (parameterTypes : String := "") :
    IO (List SelectContract.OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let params ← expectOk sql (Assurance.parseContractParameterTypes parameterTypes)
  substringCertificate query params

private def substringInventoryTests : IO Nat := do
  let json ← expectOk "SUBSTRING catalog JSON"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/substring/function_signatures.json"))
  let records ← expectOk "SUBSTRING catalog records" json.getArr?
  SQLean.Tests.assert (records.size == 6) "expected six admitted SUBSTRING declarations"
  let mut observed : List SelectContract.FunctionOverload := []
  for record in records do
    SQLean.Tests.assert ((← substringField "catalog" record "name") == "substring")
      "SUBSTRING catalog function name"
    let inputJson ← expectOk "SUBSTRING inputs" ((record.getObjVal? "inputs") >>= Lean.Json.getArr?)
    let inputs ← inputJson.toList.mapM fun value => do
      let name ← expectOk "SUBSTRING input name" value.getStr?
      let declaration ← expectOk name (Advanced.parseDataType name)
      match SelectContract.concreteType declaration with
      | some base => pure base.unmodified
      | none => throw (IO.userError s!"unsupported SUBSTRING catalog type {name}")
    let outputName ← substringField "catalog" record "output"
    let declaration ← expectOk outputName (Advanced.parseDataType outputName)
    let output ← match SelectContract.concreteType declaration with
      | some base => pure base.unmodified
      | none => throw (IO.userError "unsupported SUBSTRING catalog output")
    let signature : SelectContract.FunctionOverload := ⟨inputs, output⟩
    let args := inputs.map fun type => SelectContract.ScalarInput.known ⟨type, false⟩
    SQLean.Tests.assert (SelectContract.resolveOverload SelectContract.substringCatalog args ==
        some signature) "exact SUBSTRING declaration must be selected"
    let nullable := inputs == [.text, .text] || inputs == [.text, .text, .text]
    SQLean.Tests.assert (SelectContract.callSignature ["substring"] args ==
        some ⟨output, nullable⟩) "ordinary SUBSTRING call uses matching nullable metadata"
    observed := signature :: observed
  SQLean.Tests.assert (decide observed.Nodup && observed.all SelectContract.substringCatalog.contains &&
      SelectContract.substringCatalog.all observed.contains) "SUBSTRING catalog inventory differs"
  SQLean.Tests.assert ((SelectContract.functionCatalog "substr").length == 4 &&
      (SelectContract.functionCatalog "substring").length == 6)
    "SUBSTR positional declarations must remain separate from SUBSTRING regex overloads"
  pure (records.size + 1)

def substringContractTests : IO Nat := do
  let mut count ← substringInventoryTests
  -- Independently authored native type classes: implicit INT32 position,
  -- implicit TEXT regex pattern, and explicit FOR-only INT32 conversion.
  let declarations : List (String × Bool × Bool × Bool × Bool) := [
    ("SMALLINT", true, false, true, false), ("INTEGER", true, false, true, false),
    ("BIGINT", false, false, true, false), ("NUMERIC(8,2)", false, false, true, false),
    ("REAL", false, false, true, false), ("DOUBLE PRECISION", false, false, true, false),
    ("TEXT", false, true, true, false), ("VARCHAR(5)", false, true, true, false),
    ("CHAR(5)", false, true, true, false), ("BOOLEAN", false, false, true, false),
    ("DATE", false, false, false, false), ("TIME(3)", false, false, false, false),
    ("TIME(3) WITH TIME ZONE", false, false, false, false),
    ("TIMESTAMP(3)", false, false, false, false),
    ("TIMESTAMP(3) WITH TIME ZONE", false, false, false, false),
    ("INTERVAL DAY TO SECOND(3)", false, false, false, false),
    ("UUID", false, false, false, false), ("JSON", false, false, false, false),
    ("JSONB", false, false, true, true), ("BYTEA", false, false, false, false)]
  for (declaration, positional, pattern, explicitLength, castNullable) in declarations do
    for array in [false, true] do
      for nullable in [false, true] do
        let parameter := declaration ++ (if array then "[]" else "") ++ (if nullable then "?" else "")
        for (expression, valid, expectedNullable) in [
            ("SUBSTRING('abcdef' FROM $1)", !array && (positional || pattern), nullable || pattern),
            ("SUBSTRING('abcdef' FROM 1 FOR $1)", !array && positional, nullable),
            ("SUBSTRING('abcdef' FOR $1 FROM 1)", !array && positional, nullable),
            ("SUBSTRING('abcdef' FOR $1)", !array && explicitLength, nullable || castNullable),
            ("SUBSTRING('abcdef' SIMILAR $1 ESCAPE 2)", !array && positional, nullable)] do
          let sql := "SELECT " ++ expression ++ " AS v"
          let query ← expectOk sql (Advanced.parseQuery sql)
          let params ← expectOk parameter (Assurance.parseContractParameterTypes parameter)
          if valid then
            SQLean.Tests.assert ((← substringCertificate query params) ==
                [⟨"v", ⟨.text, expectedNullable⟩⟩]) s!"SUBSTRING typed argument: {sql}; {parameter}"
          else match SelectContract.checkQuery .basicV23 [] params query with
          | .error (.invalid diagnostic) =>
              SQLean.Tests.assert (["substring_signature", "substring_length_cast"].contains diagnostic.code)
                s!"SUBSTRING unsupported concrete signature diagnosis: {sql}; {parameter}"
          | _ => throw (IO.userError s!"SUBSTRING invalid signature accepted: {sql}; {parameter}")
          count := count + 1
  for (declaration, _, pattern, _, _) in declarations do
    for nullable in [false, true] do
      let parameter := declaration ++ (if nullable then "?" else "")
      let sql := "SELECT SUBSTRING($1 FROM 2 FOR 3) AS v"
      let query ← expectOk sql (Advanced.parseQuery sql)
      let params ← expectOk parameter (Assurance.parseContractParameterTypes parameter)
      if pattern || declaration == "BYTEA" then
        let result : SelectContract.ScalarType := if declaration == "BYTEA" then .bytea else .text
        SQLean.Tests.assert ((← substringCertificate query params) == [⟨"v", ⟨result, nullable⟩⟩])
          s!"SUBSTRING subject type and erased modifiers: {parameter}"
      else match SelectContract.checkQuery .basicV23 [] params query with
      | .error (.invalid diagnostic) =>
          SQLean.Tests.assert (diagnostic.code == "substring_signature") "invalid SUBSTRING subject"
      | _ => throw (IO.userError s!"SUBSTRING invalid subject accepted: {parameter}")
      count := count + 1
  for (expression, result, nullable) in [
      ("SUBSTRING('abc' FROM '2')", SelectContract.ScalarType.text, true),
      ("SUBSTRING('abc' FROM NULL)", .text, true),
      ("SUBSTRING(NULL FROM 1)", .text, true),
      ("SUBSTRING('abc' FROM 'a' FOR '#')", .text, true),
      ("SUBSTRING('abc' FOR '#' FROM 'a')", .text, true),
      ("SUBSTRING('abc' SIMILAR 1 ESCAPE 2)", .text, false),
      ("SUBSTRING('abc'::BYTEA SIMILAR 1 ESCAPE 2)", .bytea, false),
      ("SUBSTRING('abc'::BYTEA FROM '2')", .bytea, false),
      ("SUBSTRING('abc' FOR TRUE)", .text, false),
      ("SUBSTRING('abc' FOR 2.5)", .text, false),
      ("SUBSTRING('abc' FOR CAST(2.5 AS DOUBLE PRECISION))", .text, false),
      ("SUBSTRING('abc' FOR CAST('2' AS JSONB))", .text, true),
      ("SUBSTRING('abc' FOR NULL)", .text, true),
      ("SUBSTRING('abc' FROM -1 FOR -2)", .text, false),
      ("SUBSTRING('abc' FOR 'not an integer')", .text, false),
      ("SUBSTRING('abc' FOR CAST('null' AS JSONB))", .text, true),
      ("SUBSTRING('abc' FROM '[')", .text, true),
      ("SUBSTRING('abc' SIMILAR '%' ESCAPE '##')", .text, true),
      ("SUBSTRING('abc', 'does not match')", .text, true),
      ("SUBSTRING('abc', 'a', '#')", .text, true),
      ("SUBSTRING('abc'::BYTEA, 2, 1)", .bytea, false),
      ("SUBSTR('abc', 2)", .text, false)] do
    SQLean.Tests.assert ((← substringOutput ("SELECT " ++ expression ++ " AS v")) ==
        [⟨"v", ⟨result, nullable⟩⟩]) s!"SUBSTRING overload, unknown, or runtime boundary: {expression}"
    count := count + 1
  for sql in [
      "SELECT SUBSTRING('abc' FROM 1::BIGINT)", "SELECT SUBSTRING('abc' FROM TRUE)",
      "SELECT SUBSTRING('abc'::BYTEA FROM 'a'::TEXT)", "SELECT SUBSTRING('abc' FOR DATE '2024-01-01')",
      "SELECT SUBSTRING()", "SELECT SUBSTRING('abc')", "SELECT SUBSTRING('a', 1, 2, 3)",
      "SELECT SUBSTR('abc', 'a'::TEXT)"] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV23 [] [] query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError s!"SUBSTRING invalid arity or type: {sql}")
    count := count + 1
  for sql in [
      "SELECT SUBSTRING((SELECT 'abc') FROM 1)",
      "SELECT SUBSTRING(unregistered_subject() FOR 2)"] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV23 [] [] query with
    | .error (.unsupported _) => pure ()
    | _ => throw (IO.userError s!"SUBSTRING child coverage status: {sql}")
    count := count + 1
  for form in [Advanced.SubstringForm.from, .fromFor, .forFrom, .forOnly, .similar] do
    for arity in [0, 1, 2, 3, 4] do
      if arity != form.arity then
        let expr : Advanced.Expr := .substring form (List.replicate arity (.literal (.int 1)))
        let query : Advanced.Query := {body := .select {items := [.expression expr none]}}
        match SelectContract.checkQuery .basicV23 [] [] query with
        | .error (.invalid diagnostic) =>
            SQLean.Tests.assert (diagnostic.code == "substring_arity") "manual special-form arity"
        | _ => throw (IO.userError "malformed hand-built SUBSTRING acquired a certificate")
        count := count + 1
  for sql in [
      "SELECT SUBSTRING('abc' FROM 1)", "SELECT CAST(SUBSTRING('abc' FROM 1) AS VARCHAR(5))",
      "SELECT CASE WHEN TRUE THEN 'a' ELSE SUBSTRING('abc' FROM 1) END"] do
    let output ← substringOutput sql
    SQLean.Tests.assert (output.map (·.name) == ["substring"]) "strong SUBSTRING default label"
    count := count + 1
  for (sql, types) in [
      ("SELECT SUBSTRING(? FOR ? FROM ?)", "TEXT,INTEGER,INTEGER"),
      ("SELECT SUBSTRING(? FOR ? FROM ?)", "TEXT,TEXT,TEXT"),
      ("SELECT SUBSTRING($3 FOR $1 FROM $2)", "INTEGER,INTEGER,TEXT"),
      ("SELECT SUBSTRING(? FOR ?), SUBSTRING(? SIMILAR ? ESCAPE ?)", "TEXT,BOOLEAN,TEXT,TEXT,TEXT"),
      ("SELECT SUBSTRING($1 FROM $2 FOR $2)", "TEXT,INTEGER")] do
    discard <| substringOutput sql types
    count := count + 1
  let params ← expectOk "SUBSTRING params" (Assurance.parseContractParameterTypes "TEXT,INTEGER,INTEGER")
  for uses in [[1,3,2], [1,2,4]] do
    let expr : Advanced.Expr := .substring .forFrom (uses.map fun n => .parameter (.anonymous n))
    let query : Advanced.Query := {body := .select {items := [.expression expr none]}}
    match SelectContract.checkQuery .basicV23 [] params query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError "SUBSTRING semantic permutation must not bypass lexical parameter order")
    count := count + 1
  let query ← expectOk "SUBSTRING fuel" (Advanced.parseQuery "SELECT SUBSTRING('abc' FROM 1)")
  match SelectContract.checkQuery .basicV23 [] [] query 0 with
  | .error (.inconclusive _) => pure ()
  | _ => throw (IO.userError "SUBSTRING fuel exhaustion must be Inconclusive")
  pure (count + 1)

def substringCorpusTests : IO Nat := do
  let json ← expectOk "SUBSTRING synthetic JSON"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/substring/synthetic.json"))
  let records ← expectOk "SUBSTRING synthetic records" json.getArr?
  SQLean.Tests.assert (records.size == 50) "expected fifty SUBSTRING synthetic queries"
  let mut ids : List String := []
  let mut statements : List String := []
  for record in records do
    let id ← substringField "synthetic" record "id"
    let sql ← substringField id record "sql"
    SQLean.Tests.assert ((← substringField id record "source_kind") == "synthetic") s!"{id}: population"
    let parameters ← substringField id record "parameter_types"
    let expected ← expectOk id ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
    let expected ← expected.toList.mapM fun column => do
      let name ← substringField id column "name"
      let type ← substringField id column "type"
      let nullable ← expectOk id ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
      pure (name, type, nullable)
    let actual ← substringOutput sql parameters
    let labels := actual.map fun column =>
      (column.name, column.type.base.dataType.toSql.toLower.replace ", " ",", column.type.nullable)
    SQLean.Tests.assert (labels == expected)
      s!"{id}: exact SUBSTRING output {reprStr labels}; expected {reprStr expected}"
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (decide ids.Nodup && decide statements.Nodup)
    "duplicate SUBSTRING synthetic identities or SQL"
  pure records.size

/-- Fixed authentic source identities, with independently registered output
metadata. Every source is checked with genuinely empty catalog/bindings;
none can be moved into a weaker population after a failed certificate. -/
def substringConcreteContractTests : IO Nat := do
  let pgStrings : List (Nat × String × SelectContract.ScalarType × Bool) := [
    (73, "34567890", .bool, false), (74, "456", .bool, false),
    (75, "tring", .text, false), (76, "string", .text, false),
    (78, "bcd", .text, true), (79, "bcd", .text, true),
    (80, "True", .bool, false), (81, "True", .bool, false),
    (82, "True", .bool, false), (83, "True", .bool, false),
    (84, "bcdef", .text, true), (85, "abcdefg", .text, true),
    (86, "bcdef", .text, true), (87, "bcdef", .text, true),
    (88, "bcdef", .text, true), (90, "bcdefg", .text, true),
    (91, "abcdefg", .text, true), (92, "cde", .text, true),
    (93, "cde", .text, true), (94, "t", .bool, false),
    (430, "34567890", .bytea, false), (431, "456", .bytea, false),
    (432, "tring", .bytea, false), (433, "string", .bytea, false)]
  let cockroach : List (Nat × SelectContract.ScalarType × Bool) := [
    (155, .text, false), (160, .text, false), (165, .text, false),
    (170, .text, false), (185, .text, false), (218, .text, false),
    (223, .text, true), (228, .text, true), (233, .text, true),
    (296, .bytea, false), (311, .bytea, false)]
  let expected : List (String × SelectContract.OutputColumn) :=
    pgStrings.map (fun (n, name, type, nullable) =>
      (s!"substring:postgres:src/test/regress/sql/strings.sql:statement-{n}", ⟨name, ⟨type, nullable⟩⟩)) ++
    [12,13,14].map (fun (n : Nat) =>
      (s!"substring:postgres:src/test/regress/sql/regex.sql:statement-{n}",
        ⟨"substring", ⟨.text, true⟩⟩)) ++
    cockroach.map (fun (n, type, nullable) =>
      (s!"substring:cockroach:pkg/sql/logictest/testdata/logic_test/builtin_function:sqllogic-query-{n}",
        ⟨"substring", ⟨type, nullable⟩⟩)) ++
    [415,420,425,430,435,440,456,461,466,471,476,489].map (fun (n : Nat) =>
      (s!"substring:materialize:test/sqllogictest/string.slt:sqllogic-query-{n}",
        ⟨"substring", ⟨.text, false⟩⟩))
  SQLean.Tests.assert (expected.length == 50 && decide (expected.map (·.1)).Nodup)
    "SUBSTRING authentic registry must contain fifty distinct identities"
  let source ← IO.FS.readFile "fixtures/substring/concrete.jsonl"
  let lines := (source.splitOn "\n").filter fun line => !line.trimAscii.toString.isEmpty
  SQLean.Tests.assert (lines.length == 50) "expected fifty unchanged SUBSTRING sources"
  let mut observed : List String := []
  let mut statements : List String := []
  for line in lines do
    let record ← expectOk "SUBSTRING concrete" (Lean.Json.parse line)
    let id ← substringField "concrete" record "id"
    let registered ← match expected.find? (fun entry => entry.1 == id) with
      | some entry => pure entry.2
      | none => throw (IO.userError s!"unregistered SUBSTRING concrete identity {id}")
    let sql ← substringField id record "sql"
    SQLean.Tests.assert ((← substringField id record "raw_sql") == sql)
      s!"{id}: authentic source must remain unchanged"
    let observations ← expectOk id (record.getObjVal? "observed_syntax")
    SQLean.Tests.assert (← expectOk id ((observations.getObjVal? "source_free") >>= Lean.Json.getBool?))
      s!"{id}: fixed source-free population"
    let slots ← expectOk id ((record.getObjVal? "observed_parameter_slots") >>= Lean.Json.getArr?)
    let query ← expectOk id (Advanced.parseQuery sql)
    SQLean.Tests.assert (slots.isEmpty && query.ctes.isEmpty &&
        Advanced.queryParameters 1024 query == []) s!"{id}: genuinely empty query environment"
    match query.body with
    | .select select =>
        SQLean.Tests.assert (select.source.isNone && select.items.length == 1)
          s!"{id}: registered single source-free projection"
    | _ => throw (IO.userError s!"{id}: registered SELECT structure changed")
    SQLean.Tests.assert ((← substringCertificate query) == [registered])
      s!"{id}: exact authentic SUBSTRING output"
    observed := id :: observed
    statements := sql :: statements
  SQLean.Tests.assert (decide observed.Nodup && decide statements.Nodup &&
      expected.all (fun entry => observed.contains entry.1))
    "SUBSTRING concrete certificates must cover every registered identity exactly once"
  pure observed.length

end SQLean.Tests
