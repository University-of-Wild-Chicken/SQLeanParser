import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.ContractSupport
import Lean.Data.Json

namespace SQLean.Tests

/-- A constructor pair is typed directly from its scalar fields, without
inventing a concrete record type for either standalone constructor. -/
example : SelectContract.ExprValid [] .empty
    (.binary .le (.row [.literal (.int 1), .literal (.int 2)])
      (.row [.literal (.int 3), .literal (.int 4)]))
    (some ⟨.bool, true⟩) [] :=
  .rowComparison (op := .le)
    (selected := [⟨[.int32, .int32], .bool⟩, ⟨[.int32, .int32], .bool⟩])
    (.cons (.int (by decide)) (.cons (.int (by decide)) .nil))
    (.cons (.int (by decide)) (.cons (.int (by decide)) .nil)) rfl

example : SelectContract.rowComparisonSignature .eq [] [] = none := rfl

/-- The generic binary rule cannot bypass the specialized constructor rule. -/
example (params : SelectContract.ParameterEnv) (scope : SelectContract.Scope)
    (fields : List Advanced.Expr) (type : SelectContract.ExprType) (uses : List Advanced.Parameter) :
    ¬ SelectContract.ExprValid params scope (.row fields) type uses := by
  intro valid
  cases valid with
  | foldedInteger folded => simp [SelectContract.rawIntegerValue] at folded

private def rowCertificate (query : Advanced.Query)
    (params : SelectContract.ParameterEnv := []) :
    IO (List SelectContract.OutputColumn) := do
  let certificate ← expectOk "row-comparison SELECT"
    ((SelectContract.checkQuery .basicV32 [] params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let identity ← expectOk "row-comparison identity renderer"
    ((RenderContract.check .identityV01 query).mapError reprStr)
  let postgres ← expectOk "row-comparison PostgreSQL renderer"
    ((RenderContract.check .postgres16V01 query).mapError reprStr)
  have _identity : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
  have _postgres : Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
    postgres.roundTrip
  pure certificate.output

private def rowOutput (sql : String) (parameterTypes : String := "") :
    IO (List SelectContract.OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let params ← expectOk sql (Assurance.parseContractParameterTypes parameterTypes)
  rowCertificate query params

private def rowField (id : String) (record : Lean.Json) (name : String) : IO String :=
  expectOk s!"{id}: {name}" ((record.getObjVal? name) >>= Lean.Json.getStr?)

private def rowOperatorInventoryTests : IO Nat := do
  let json ← expectOk "row operator inventory JSON"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/array_quantified/operator_signatures.json"))
  let records ← expectOk "row operator inventory records" json.getArr?
  SQLean.Tests.assert (records.size == 192) "expected exactly 192 audited scalar operator signatures"
  let mut observed : List (Advanced.ComparisonOp × SelectContract.FunctionOverload) := []
  for record in records do
    let operator ← rowField "operator inventory" record "operator"
    let op ← match operator with
      | "=" => pure Advanced.ComparisonOp.eq
      | "<>" => pure .ne
      | "<" => pure .lt
      | "<=" => pure .le
      | ">" => pure .gt
      | ">=" => pure .ge
      | _ => throw (IO.userError s!"unexpected row operator spelling: {operator}")
    let parseType := fun field => do
      let name ← rowField operator record field
      let declaration ← expectOk name (Advanced.parseDataType name)
      match SelectContract.concreteType declaration with
      | some type => pure type.unmodified
      | none => throw (IO.userError s!"unsupported row operator inventory type: {name}")
    let left ← parseType "left"
    let right ← parseType "right"
    let selected : SelectContract.FunctionOverload := ⟨[left, right], .bool⟩
    let intInput := SelectContract.ScalarInput.known ⟨.int32, false⟩
    SQLean.Tests.assert (SelectContract.rowBtreeCompatible selected)
      s!"row inventory lacks normative B-tree eligibility: {operator} {reprStr selected}"
    SQLean.Tests.assert
      (SelectContract.rowComparisonSignature op
        [.known ⟨left, false⟩, intInput] [.known ⟨right, false⟩, intInput] ==
          some [selected, ⟨[.int32, .int32], .bool⟩])
      s!"row inventory selected different scalar operators: {operator} {reprStr selected}"
    let query : Advanced.Query := { body := .select { items := [
      .expression (.binary op.toBinOp
        (.row [.cast .null left.dataType, .literal (.int 1)])
        (.row [.cast .null right.dataType, .literal (.int 2)])) (some "v")] } }
    let actual ← rowCertificate query
    SQLean.Tests.assert (sameOutputTypes actual [{name := "v", type := ⟨.bool, true⟩}])
      s!"row operator full certificate: {operator} {reprStr selected}"
    observed := (op, selected) :: observed
  let expected := [Advanced.ComparisonOp.eq, .ne, .lt, .le, .gt, .ge] |>.flatMap fun op =>
    (SelectContract.equalityCatalog.filter (fun signature => !signature.inputs.contains .name)).map fun signature => (op, signature)
  SQLean.Tests.assert (decide observed.Nodup &&
      expected.all observed.contains && observed.all expected.contains)
    "row operator fixture differs from the complete closed inventory"
  pure records.size

def rowComparisonContractTests : IO Nat := do
  let mut count ← rowOperatorInventoryTests
  for op in ["=", "<>", "<", "<=", ">", ">="] do
    for (left, right) in [("ROW(1)", "ROW(2)"), ("ROW(1,NULL)", "ROW(2,3)"),
        ("(1,2)", "(2,3)"), ("ROW(1,2)", "(2,3)"), ("(1,2)", "ROW(2,3)")] do
      let sql := s!"SELECT {left} {op} {right}"
      let actual ← rowOutput sql
      SQLean.Tests.assert (sameOutputTypes actual [{name := "?column?", type := ⟨.bool, true⟩}]) s!"row form/operator: {sql}"
      count := count + 1
  let valid := [
    "SELECT ROW(NULL,NULL) = ROW(NULL,NULL) AS v",
    "SELECT ROW(NULL,1) <> ROW(NULL,2) AS v",
    "SELECT ROW(NULL,1) < ROW(NULL,2) AS v",
    "SELECT ROW('1',NULL) = ROW(1,2) AS v",
    "SELECT ROW('a','b') = ROW('a','b') AS v",
    "SELECT ROW('true',1) = ROW(TRUE,1) AS v",
    "SELECT ROW(1::REAL,1::INTEGER) < ROW(1::BIGINT,2::NUMERIC) AS v",
    "SELECT ROW(DATE '2024-01-01',1) < ROW(TIMESTAMP '2024-01-02',2) AS v",
    "SELECT ROW('1'::JSONB,1) < ROW('2'::JSONB,1) AS v",
    "SELECT ROW(ARRAY[1],2) < ROW(ARRAY[2],3) AS v",
    "SELECT ROW(ARRAY[1],2) = ROW('{1}',2) AS v",
    "SELECT ROW(ARRAY[NULL::INTEGER],1) = ROW(ARRAY[NULL::INTEGER],1) AS v",
    "SELECT ROW(NULL::INTEGER[],1) = ROW(NULL::INTEGER[],1) AS v",
    "SELECT ROW(ARRAY[[1,2],[3,4]],1) = ROW(ARRAY[[1,2],[3,4]],1) AS v",
    "SELECT ROW('a'::CHAR(5),1) <= ROW('b'::VARCHAR(4),1) AS v",
    "SELECT ROW('bad',1) = ROW(1,1) AS v",
    "SELECT NOT (ROW(1,2) = ROW(1,3)) AS v",
    "SELECT (ROW(1,2) < ROW(2,1)) AND TRUE AS v",
    "SELECT (1,2) < (2,1) AS v WHERE (3,4) > (2,1)",
    "SELECT d.v FROM (SELECT ROW(1,2) = ROW(1,2) AS v) d",
    "SELECT ROW((SELECT 1),1) = ROW(1,1) AS v"]
  for sql in valid do
    let actual ← rowOutput sql
    SQLean.Tests.assert (sameOutputTypes actual [{name := "v", type := ⟨.bool, true⟩}]) s!"row comparison output: {sql}"
    count := count + 1
  for op in ["=", "<>", "<", "<=", ">", ">="] do
    let sql := s!"SELECT ROW() {op} ROW()"
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV32 [] [] query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError s!"empty row comparison must be Invalid: {sql}")
    count := count + 1
  let invalid := [
    "SELECT ROW(1,2) = ROW(1)", "SELECT ROW() = ROW(1)",
    "SELECT ROW('1'::JSON,1) = ROW('1'::JSON,1)",
    "SELECT ROW(TRUE,1) = ROW(1,1)",
    "SELECT ROW(DATE '2024-01-01',1) < ROW(1,1)",
    "SELECT ROW(ARRAY[1],1) = ROW(ARRAY[1::BIGINT],1)",
    "SELECT ROW(1) + ROW(2)", "SELECT ROW(TRUE) AND ROW(FALSE)"]
  for sql in invalid do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV32 [] [] query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError s!"expected Invalid row query: {sql}")
    count := count + 1
  let unsupported := [
    "SELECT ROW()", "SELECT ROW(1)", "SELECT ROW(1,2)", "SELECT (1,2)",
    "SELECT ROW(ROW(1,NULL::INTEGER),1) = ROW(ROW(1,NULL::INTEGER),1)",
    "SELECT ROW(1,2) = NULL",
    "SELECT ROW(ARRAY['1'::JSON],1) = ROW(ARRAY['1'::JSON],1)",
    "SELECT ROW(unknown_function(),1) = ROW(1,1)",
    "SELECT ROW(COUNT(*),1) = ROW(1,1)"]
  for sql in unsupported do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV32 [] [] query with
    | .error (.unsupported _) => pure ()
    | _ => throw (IO.userError s!"expected Unsupported row query: {sql}")
    count := count + 1
  SQLean.Tests.assert (sameOutputTypes (← rowOutput "SELECT ROW(1,2) IS NULL AS v") [{name := "v", type := ⟨.bool, false⟩}]) "flat-row null tests have nonnullable Boolean output"
  count := count + 1
  for (sql, params) in [
      ("SELECT ROW($1,$2) < ROW($3,$4) AS v", "integer,text,bigint,varchar"),
      ("SELECT (?,?) = (?,?) AS v", "integer,integer[],integer,integer[]"),
      ("SELECT ROW($2,$1) = ROW($2,$1) AS v", "text,int"),
      ("SELECT ROW(?) <= ROW(?) AS v", "numeric?,real")] do
    let actual ← rowOutput sql params
    SQLean.Tests.assert (sameOutputTypes actual [{name := "v", type := ⟨.bool, true⟩}]) s!"row parameter bindings: {sql}"
    count := count + 1
  let sql := "SELECT ROW(?,ARRAY[?]) = ROW(?,ARRAY[?]) AS a, ROW(?) < ROW(?) AS b"
  let params ← expectOk sql (Assurance.parseContractParameterTypes "int,int,int,int,int,int")
  let query ← expectOk sql (Advanced.parseQuery sql)
  let _ ← rowCertificate query params
  SQLean.Tests.assert (Advanced.queryParameters 1024 query ==
    (List.range 6).map (fun n => .anonymous (n + 1))) "row parameter lexical order"
  count := count + 1
  let bad : Advanced.Query := { body := .select { items := [.expression (.binary .eq
    (.row [.parameter (.anonymous 1), .parameter (.anonymous 3)])
    (.row [.parameter (.anonymous 2), .parameter (.anonymous 4)]))] } }
  match SelectContract.checkQuery .basicV32 [] params bad with
  | .error (.invalid _) => pure ()
  | _ => throw (IO.userError "pairwise-interleaved row placeholders must be Invalid")
  count := count + 1
  match SelectContract.checkQuery .basicV32 [] params query 1 with
  | .error (.inconclusive _) => pure ()
  | _ => throw (IO.userError "row comparison exhaustion must be Inconclusive")
  count := count + 1
  pure count

def rowComparisonCorpusTests : IO Nat := do
  let json ← expectOk "row comparison fixture JSON"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/row_comparisons/synthetic.json"))
  let records ← expectOk "row comparison fixture records" json.getArr?
  SQLean.Tests.assert (records.size == 50) "expected exactly 50 row comparison synthetic queries"
  let mut ids : List String := []
  let mut statements : List String := []
  for record in records do
    let id ← rowField "row comparison fixture" record "id"
    let sql ← rowField id record "sql"
    SQLean.Tests.assert ((← rowField id record "source_kind") == "synthetic") s!"{id}: population"
    let params ← rowField id record "parameter_types"
    let expected ← expectOk id ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
    let expected ← expected.toList.mapM fun column => do
      let name ← rowField id column "name"
      let type ← rowField id column "type"
      let nullable ← expectOk id ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
      pure (name, type, nullable)
    let actual ← rowOutput sql params
    let labels := actual.map fun column =>
      let type := match column.type.base with
        | .bool => "bool"
        | base => (base.dataType.toSql.toLower).replace ", " ","
      (column.name, type, column.type.nullable)
    SQLean.Tests.assert (labels == expected)
      s!"{id}: exact row comparison output {reprStr labels}; expected {reprStr expected}"
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (decide ids.Nodup && decide statements.Nodup)
    "duplicate row comparison corpus identities or SQL"
  pure records.size

end SQLean.Tests
