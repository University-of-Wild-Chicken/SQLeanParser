import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

namespace SQLean.Tests

/-- A concrete CHAR left operand selects bpchar/text, retaining the native
padding distinction instead of converting both arguments to TEXT. -/
example : SelectContract.ExprValid [⟨1, ⟨.char, [5]⟩, false⟩] .empty
    (.pattern (.parameter (.anonymous 1)) (.literal (.text "a")) true)
    (some ⟨.bool, false⟩) [.anonymous 1] :=
  .ilike (selected := ⟨[.char [], .text], .bool⟩)
    (.parameter (binding := ⟨1, ⟨.char, [5]⟩, false⟩) (base := .char [5])
      (by simp) rfl rfl) .text rfl

example (insensitive negated : Bool) : SelectContract.ExprValid [] .empty
    (.regex (.literal (.text "a")) .null insensitive negated)
    (some ⟨.bool, true⟩) [] :=
  .regex (selected := ⟨[.text, .text], .bool⟩) .text .null rfl

example : SelectContract.stringMatchSignature
    (.known ⟨.bytea, false⟩) (.unknown false) = none := rfl

private def patternCertificate (query : Advanced.Query)
    (params : SelectContract.ParameterEnv := []) :
    IO (List SelectContract.OutputColumn) := do
  let certificate ← expectOk "pattern SELECT"
    ((SelectContract.checkQuery .basicV15 [] params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let identity ← expectOk "pattern identity renderer"
    ((RenderContract.check .identityV01 query).mapError reprStr)
  let postgres ← expectOk "pattern PostgreSQL renderer"
    ((RenderContract.check .postgres16V01 query).mapError reprStr)
  have _identity : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
  have _postgres : Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
    postgres.roundTrip
  pure certificate.output

private def patternOutput (sql : String) (parameterTypes : String := "") :
    IO (List SelectContract.OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let params ← expectOk sql (Assurance.parseContractParameterTypes parameterTypes)
  patternCertificate query params

private def patternField (id : String) (record : Lean.Json) (name : String) : IO String :=
  expectOk s!"{id}: {name}" ((record.getObjVal? name) >>= Lean.Json.getStr?)

private def patternOperatorInventoryTests : IO Nat := do
  let json ← expectOk "pattern operator inventory JSON"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/pattern_matching/operator_signatures.json"))
  let records ← expectOk "pattern operator inventory records" json.getArr?
  SQLean.Tests.assert (records.size == 10) "expected exactly ten selected pattern operator declarations"
  let mut observed : List (String × String × String × String × String) := []
  for record in records do
    let spelling ← patternField "pattern inventory" record "operator"
    let left ← patternField spelling record "left"
    let right ← patternField spelling record "right"
    let output ← patternField spelling record "output"
    let function ← patternField spelling record "function"
    let operator ← match SelectContract.stringMatchOperators.filter (·.toSql == spelling) with
      | [operator] => pure operator
      | _ => throw (IO.userError s!"unknown pattern operator inventory spelling: {spelling}")
    let declaration : Advanced.DataType ← match left with
      | "text" => pure ⟨.text, []⟩
      | "bpchar" => pure ⟨.char, [5]⟩
      | _ => throw (IO.userError s!"unknown pattern lhs inventory type: {left}")
    let base ← match SelectContract.concreteType declaration with
      | some base => pure base
      | none => throw (IO.userError s!"unsupported inventory declaration: {left}")
    let expected : SelectContract.FunctionOverload :=
      ⟨[if left == "bpchar" then .char [] else .text, .text], .bool⟩
    SQLean.Tests.assert
      (SelectContract.stringMatchSignature (.known ⟨base, true⟩) (.known ⟨.text, false⟩) ==
        some expected && SelectContract.stringMatchOverloads.contains expected)
      s!"pattern selected exact argument types: {spelling}, {left}"
    let a : Advanced.Expr := .cast .null declaration
    let b : Advanced.Expr := .literal (.text "a")
    let expression := match operator with
      | .ilike => Advanced.Expr.pattern a b true
      | .regex insensitive negated => .regex a b insensitive negated
    let query : Advanced.Query := { body := .select { items := [.expression expression (some "v")] } }
    SQLean.Tests.assert ((← patternCertificate query) == [⟨"v", ⟨.bool, true⟩⟩])
      s!"pattern catalog full-query certificate: {spelling}, {left}"
    observed := (spelling, left, right, output, function) :: observed
  let expected := SelectContract.stringMatchOperators.flatMap fun operator =>
    [false, true].map fun charLeft =>
      (operator.toSql, if charLeft then "bpchar" else "text", "text", "boolean",
        operator.functionName charLeft)
  SQLean.Tests.assert (decide observed.Nodup && expected.all observed.contains &&
      observed.all expected.contains)
    "pattern fixture differs from the complete selected catalog inventory"
  pure records.size

def patternMatchingContractTests : IO Nat := do
  let mut count ← patternOperatorInventoryTests
  let operands : List (String × Bool) := [
    ("'a'", false), ("NULL", true), ("CAST('a' AS TEXT)", false),
    ("CAST('a' AS VARCHAR(5))", false), ("CAST('a' AS CHAR(5))", false)]
  for operator in ["ILIKE", "NOT ILIKE", "~", "~*", "!~", "!~*"] do
    for (left, leftNullable) in operands do
      for (right, rightNullable) in operands do
        let sql := s!"SELECT {left} {operator} {right} AS v"
        SQLean.Tests.assert ((← patternOutput sql) ==
          [⟨"v", ⟨.bool, leftNullable || rightNullable⟩⟩]) s!"pattern operand/context: {sql}"
        count := count + 1
    for leftNullable in [false, true] do
      for rightNullable in [false, true] do
        let declarations := "char(5)" ++ (if leftNullable then "?" else "") ++
          ",varchar(3)" ++ (if rightNullable then "?" else "")
        let sql := s!"SELECT $1 {operator} $2 AS v"
        SQLean.Tests.assert ((← patternOutput sql declarations) ==
          [⟨"v", ⟨.bool, leftNullable || rightNullable⟩⟩]) s!"pattern nullable parameters: {sql}"
        count := count + 1
  for left in [SelectContract.ScalarType.text, .varchar [5], .char [5]] do
    for right in [SelectContract.ScalarType.text, .varchar [3], .char [3]] do
      let expected : SelectContract.FunctionOverload :=
        ⟨[if left == .char [5] then .char [] else .text, .text], .bool⟩
      SQLean.Tests.assert
        (SelectContract.stringMatchSignature (.known ⟨left, false⟩) (.known ⟨right, false⟩) ==
          some expected) s!"pattern CHAR-left selection: {reprStr left}, {reprStr right}"
      count := count + 1
  let examples := [
    "SELECT 'abc' ILIKE 'a' || 'bc' AS v",
    "SELECT 'a' || 'bc' ~ '^abc$' AS v",
    "SELECT 'ABC' ~* '^abc$' AS v",
    "SELECT 'ABC' !~ '^abc$' AS v",
    "SELECT 'ABC' !~* '^abc$' AS v",
    "SELECT NOT 'abc' ~ '^abc$' AS v",
    "SELECT 'abc' ~ '^abc$' = TRUE AS v",
    "SELECT 'abc' ILIKE 'a%' AND TRUE AS v",
    "SELECT CASE WHEN 'abc' ~ '^a' THEN TRUE ELSE FALSE END AS v",
    "SELECT COALESCE(NULL ILIKE 'x', FALSE) AS v",
    "SELECT d.a ILIKE d.b AS v FROM (SELECT 'ABC' AS a,'a%' AS b) d",
    "SELECT DISTINCT 'abc' ~ 'b' AS v ORDER BY v",
    "SELECT 'abc' ILIKE 'a%' AS v WHERE 'abc' !~ 'x'",
    "SELECT CAST('abc' AS CHAR(5)) ILIKE 'abc' AS v",
    "SELECT CAST('abc' AS CHAR(5)) ~ '^abc$' AS v",
    "SELECT 'abc' ILIKE CAST('abc' AS CHAR(5)) AS v",
    "SELECT 'abc' ~ CAST('abc' AS CHAR(5)) AS v",
    "SELECT 'abc' ~ '[' AS v"]
  for sql in examples do
    SQLean.Tests.assert ((← patternOutput sql) == [⟨"v", ⟨.bool, false⟩⟩]) s!"pattern composition: {sql}"
    count := count + 1
  for sql in ["SELECT NULL ~ '[' AS v", "SELECT 'abc' ILIKE NULL AS v",
      "SELECT NULL NOT ILIKE 'x' AS v"] do
    SQLean.Tests.assert ((← patternOutput sql) == [⟨"v", ⟨.bool, true⟩⟩]) s!"pattern NULL result: {sql}"
    count := count + 1
  for sql in ["SELECT 'abc' ~ 'a' || 'bc' AS v", "SELECT 'abc' !~ '^a' || 'x' AS v",
      "SELECT 'abc' ~* 'ABC' || 'x' AS v", "SELECT 'abc' !~* 'ABC' || 'x' AS v"] do
    SQLean.Tests.assert ((← patternOutput sql) == [⟨"v", ⟨.text, false⟩⟩])
      s!"generic regex/concat operator precedence: {sql}"
    count := count + 1
  for sql in ["SELECT 'a' ILIKE 'a'", "SELECT 'a' ~ 'a'"] do
    SQLean.Tests.assert ((← patternOutput sql) == [⟨"?column?", ⟨.bool, false⟩⟩])
      "pattern default output label"
    count := count + 1
  for declaration in ["integer", "numeric(8,2)", "boolean", "date", "uuid",
      "json", "jsonb", "bytea", "integer[]", "text[]"] do
    for operator in ["ILIKE", "~", "~*", "!~", "!~*"] do
      for sql in [s!"SELECT NULL::{declaration} {operator} 'a'",
          s!"SELECT 'a' {operator} NULL::{declaration}"] do
        let query ← expectOk sql (Advanced.parseQuery sql)
        match SelectContract.checkQuery .basicV15 [] [] query with
        | .error (.invalid _) => pure ()
        | _ => throw (IO.userError s!"nonstring pattern input must be Invalid: {sql}")
        count := count + 1
  for sql in ["SELECT (SELECT 'a') ILIKE 'a'", "SELECT 'a' ~ (SELECT 'a')",
      "SELECT unknown_function() ~ 'a'", "SELECT ROW('a') ILIKE 'a'"] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV15 [] [] query with
    | .error (.unsupported _) => pure ()
    | _ => throw (IO.userError s!"pattern child coverage must remain Unsupported: {sql}")
    count := count + 1
  for sql in ["SELECT CAST('a' AS BYTEA) LIKE CAST('a' AS BYTEA) AS v",
      "SELECT CAST('a' AS BYTEA) NOT LIKE CAST('b' AS BYTEA) AS v",
      "SELECT 'abc' LIKE 'a%' AS v"] do
    SQLean.Tests.assert ((← patternOutput sql) == [⟨"v", ⟨.bool, false⟩⟩])
      s!"existing LIKE/BYTEA rule changed: {sql}"
    count := count + 1
  for (sql, declarations) in [
      ("SELECT (? || ?) ~ (? || ?) AS v", "text,int,text,text"),
      ("SELECT $2 ILIKE $1 AS v", "text,char(5)"),
      ("SELECT ? ILIKE d.p AS v FROM (SELECT ? || ? AS p) d WHERE ? !~ ?",
        "text,text,text,text,text")] do
    SQLean.Tests.assert ((← patternOutput sql declarations) == [⟨"v", ⟨.bool, false⟩⟩])
      s!"pattern lexical parameter order: {sql}"
    count := count + 1
  let params ← expectOk "pattern parameters" (Assurance.parseContractParameterTypes "text,text")
  for expression in [
      Advanced.Expr.regex (.parameter (.anonymous 2)) (.parameter (.anonymous 1)) false false,
      .pattern (.parameter (.anonymous 1)) (.parameter (.numbered 2)) true] do
    let query : Advanced.Query := { body := .select { items := [.expression expression] } }
    match SelectContract.checkQuery .basicV15 [] params query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError "malformed pattern parameter order/style must be Invalid")
    count := count + 1
  let query ← expectOk "pattern exhaustion" (Advanced.parseQuery "SELECT 'a' ~* 'A'")
  match SelectContract.checkQuery .basicV15 [] [] query 1 with
  | .error (.inconclusive _) => pure ()
  | _ => throw (IO.userError "pattern exhaustion must be Inconclusive")
  count := count + 1
  pure count

def patternMatchingCorpusTests : IO Nat := do
  let mut count := 0
  for factor in ["ilike", "regex"] do
    let json ← expectOk s!"{factor} fixture JSON"
      (Lean.Json.parse (← IO.FS.readFile s!"fixtures/{factor}/synthetic.json"))
    let records ← expectOk s!"{factor} fixture records" json.getArr?
    SQLean.Tests.assert (records.size == 50) s!"expected exactly 50 {factor} synthetic queries"
    let mut ids : List String := []
    let mut statements : List String := []
    for record in records do
      let id ← patternField factor record "id"
      let sql ← patternField id record "sql"
      SQLean.Tests.assert ((← patternField id record "source_kind") == "synthetic") s!"{id}: population"
      let params ← patternField id record "parameter_types"
      let expected ← expectOk id ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
      let expected ← expected.toList.mapM fun column => do
        let name ← patternField id column "name"
        let type ← patternField id column "type"
        let nullable ← expectOk id ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
        pure (name, type, nullable)
      let actual ← patternOutput sql params
      let labels := actual.map fun column =>
        let type := match column.type.base with
          | .bool => "bool"
          | .int32 => "int32"
          | .text => "text"
          | base => (base.dataType.toSql.toLower).replace ", " ","
        (column.name, type, column.type.nullable)
      SQLean.Tests.assert (labels == expected)
        s!"{id}: exact pattern output {reprStr labels}; expected {reprStr expected}"
      ids := id :: ids
      statements := sql :: statements
    SQLean.Tests.assert (decide ids.Nodup && decide statements.Nodup)
      s!"duplicate {factor} corpus identities or SQL"
    count := count + records.size
  pure count

end SQLean.Tests
