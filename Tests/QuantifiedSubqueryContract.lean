import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import SQLean.RenderContract.TranslationProofs
import Tests.ContractSupport

/-! Constructor-only scalar quantified-query witnesses, exact scope/type
boundaries and parameter-preserving representation checks. Native Boolean/NULL
outcomes are a separate authored experiment; typing does not evaluate a query. -/
namespace SQLean.Tests
open SelectContract

private def quantifiedProjection (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr none]}}

private theorem quantifiedProjection_valid
    (typed : ExprValidCore (QueryValid .basicV35 [] []) [] [] .empty expr type [])
    (collation : ExprCollationValidCore (QueryValid .basicV35 [] []) .basicV35 [] [] .empty expr type derivation)
    (label : ExprLabelValidCore (QueryValid .basicV35 [] []) [] expr derivedLabel) :
    QueryValid .basicV35 [] [] [] (quantifiedProjection expr)
      [⟨derivedLabel.2, projectedType type, projectedCollation expr type derivation⟩] [] := by
  apply QueryValid.basic (cteUses := []) (visible := []) (by decide) .nil
    (scope := .empty) (sourceUses := []) (selectUses := []) (whereUses := [])
    (orderUses := []) (limitUses := []) (offsetUses := [])
  · exact .empty
  · exact .expression typed collation label (by simp) .nil
  · exact .expression typed collation label (by simp) .nil
  · simp
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact .absent
  · exact .nil
  · exact .nil
  · exact .absent
  · exact .absent
  · exact .nil
  · rfl
  · rfl
  · rfl

private def quantifiedOne := quantifiedProjection (.literal (.int 1))
private def quantifiedOneColumn : OutputColumn := ⟨"?column?", ⟨.int32, false⟩, none⟩
private theorem quantifiedOne_valid : QueryValid .basicV35 [] [] [] quantifiedOne [quantifiedOneColumn] [] :=
  quantifiedProjection_valid (.int (by decide)) (.atom (.int (by decide)) .int) (.ordinary rfl)

private def quantifiedOneExpr (quantifier : Advanced.ArrayQuantifier) : Advanced.Expr :=
  .quantifiedQuery .eq quantifier (.literal (.int 1)) quantifiedOne

private theorem quantifiedOne_typed (quantifier : Advanced.ArrayQuantifier) :
    ExprValidCore (QueryValid .basicV35 [] []) [] [] .empty
      (quantifiedOneExpr quantifier) (some ⟨.bool, false⟩) [] :=
  .quantifiedQuery (selected := ⟨[.int32, .int32], .bool⟩)
    (.int (by decide)) quantifiedOne_valid rfl

private theorem quantifiedOne_collation (quantifier : Advanced.ArrayQuantifier) :
    ExprCollationValidCore (QueryValid .basicV35 [] []) .basicV35 [] [] .empty
      (quantifiedOneExpr quantifier) (some ⟨.bool, false⟩) .none :=
  .quantifiedQuery (signature := ⟨[.int32, .int32], .bool⟩) (leftType := .int32) (rightType := .int32)
    (quantifiedOne_typed quantifier) (.atom (.int (by decide)) .int)
    quantifiedOne_valid rfl rfl rfl

private theorem quantifiedOne_select_valid (quantifier : Advanced.ArrayQuantifier) :
    SelectValid .basicV35 [] [] (quantifiedProjection (quantifiedOneExpr quantifier))
      [⟨"?column?", ⟨.bool, false⟩, none⟩] := by
  apply SelectValid.certified (uses := [])
  · decide
  · decide
  · decide
  · exact quantifiedProjection_valid (quantifiedOne_typed quantifier)
      (quantifiedOne_collation quantifier) (.ordinary rfl)
  · decide

example (quantifier : Advanced.ArrayQuantifier) :
    SelectValid .basicV35 [] []
      (RenderContract.translateParameters (quantifiedProjection (quantifiedOneExpr quantifier)))
      [⟨"?column?", ⟨.bool, false⟩, none⟩] :=
  RenderContract.translateParameters_valid (quantifiedOne_select_valid quantifier)

private def quantifiedRowOneExpr : Advanced.Expr :=
  .quantifiedQuery .le .all (.row [.literal (.int 1)]) quantifiedOne

private theorem quantifiedRowOne_typed : ExprValidCore (QueryValid .basicV35 [] []) [] [] .empty
    quantifiedRowOneExpr (some ⟨.bool, true⟩) [] :=
  .quantifiedRowQuery (selected := [⟨[.int32, .int32], .bool⟩])
    (.cons (.int (by decide)) .nil) quantifiedOne_valid (by decide) rfl rfl

private theorem quantifiedRowOne_collation : ExprCollationValidCore (QueryValid .basicV35 [] [])
    .basicV35 [] [] .empty quantifiedRowOneExpr (some ⟨.bool, true⟩) .none :=
  .quantifiedRowQuery (signatures := [⟨[.int32, .int32], .bool⟩]) quantifiedRowOne_typed
    (.cons (.atom (.int (by decide)) .int) .nil) quantifiedOne_valid rfl
    (.cons (leftType := .int32) (rightType := .int32) rfl rfl .nil)

private theorem quantifiedRowOne_select_valid : SelectValid .basicV35 [] []
    (quantifiedProjection quantifiedRowOneExpr) [⟨"?column?", ⟨.bool, true⟩, none⟩] := by
  apply SelectValid.certified (uses := [])
  · decide
  · decide
  · decide
  · exact quantifiedProjection_valid quantifiedRowOne_typed quantifiedRowOne_collation (.ordinary rfl)
  · decide

example : SelectValid .basicV35 [] []
    (RenderContract.translateParameters (quantifiedProjection quantifiedRowOneExpr))
    [⟨"?column?", ⟨.bool, true⟩, none⟩] :=
  RenderContract.translateParameters_valid quantifiedRowOne_select_valid

/-- Nullable left input remains nullable independently of the quantifier. -/
example (quantifier : Advanced.ArrayQuantifier) :
    ExprValidCore (QueryValid .basicV35 [] []) [] [] .empty
      (.quantifiedQuery .le quantifier .null quantifiedOne) (some ⟨.bool, true⟩) [] :=
  .quantifiedQuery (selected := ⟨[.int32, .int32], .bool⟩) .null quantifiedOne_valid rfl

/-- Child TEXT is finalized, whereas an array-expression quantifier selects
against the array element type. The two overload obligations differ. -/
example : comparisonOverload .eq (.known ⟨.int32, false⟩) (.known ⟨.array .int32, false⟩) = none := by decide
example : quantifiedComparisonSignature .eq (.known ⟨.int32, false⟩)
    (.known ⟨.array .int32, false⟩) = some ⟨[.int32, .int32], .bool⟩ := rfl

example (op : Advanced.ComparisonOp) (quantifier : Advanced.ArrayQuantifier)
    (left : Advanced.Expr) (child : Advanced.Query) :
    RenderContract.translateExpr (.quantifiedQuery op quantifier left child) =
      .quantifiedQuery op quantifier (RenderContract.translateExpr left)
        (RenderContract.translateParameters child) := by
  rw [RenderContract.translateExpr]

private def quantifiedOutput (sql : String) (types : String := "") : IO (List OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let params ← expectOk types (Assurance.parseContractParameterTypes types)
  let checked ← expectOk sql ((SelectContract.checkQuery .basicV35 [] params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid checked.valid
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    let rendered ← expectOk sql ((RenderContract.check profile query).mapError reprStr)
    let parsed ← expectOk rendered.sql (RenderContract.parseRendered profile rendered.sql)
    SQLean.Tests.assert (decide (parsed = RenderContract.expectedQuery profile query))
      "quantified-query roundtrip changed query/array form, quantifier, operator or parameters"
    let checkedAgain ← expectOk rendered.sql
      ((SelectContract.checkQuery .basicV35 [] params parsed).mapError reprStr)
    SQLean.Tests.assert (checkedAgain.output == checked.output) "quantified-query exact output changed"
  pure checked.output

private def quantifiedRejected (sql : String) (kind code : String) : IO Unit := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  match SelectContract.checkQuery .basicV35 [] [] query with
  | .ok _ => throw (IO.userError s!"unexpected quantified-query acceptance: {sql}")
  | .error failure =>
      let (actualKind, diagnostic) := match failure with
        | .invalid d => ("invalid", d) | .unsupported d => ("unsupported", d)
        | .inconclusive d => ("inconclusive", d)
      SQLean.Tests.assert (actualKind == kind && diagnostic.code == code)
        s!"wrong quantified-query classification: {sql}: {reprStr failure}"

private def parsedQuantifiedQuery (sql : String) : IO Unit := do
  let expr ← expectOk sql (Advanced.parseExpression sql)
  match expr with
  | .quantifiedQuery .. => pure ()
  | _ => throw (IO.userError s!"quantified SELECT was parsed as an array expression: {sql}")

private def quantifiedParameters (sql : String) (expected : List Advanced.Parameter) : IO Unit := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  SQLean.Tests.assert (Advanced.queryParameters 1024 query == expected)
    "legacy quantified-query lexical parameter traversal changed"
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    let checked ← expectOk sql ((RenderContract.check profile query).mapError reprStr)
    SQLean.Tests.assert (checked.footprint.parameters == expected) "quantified-query binding occurrences changed"
    let environment : Advanced.Parameter → String := fun p => reprStr p
    for parameter in expected do
      SQLean.Tests.assert
        (checked.transport environment (RenderContract.parameterSlot parameter) == environment parameter)
        "quantified-query parameter transport changed the bound value"
  match RenderContract.check .sqliteV01 query with
  | .error (.unsupported diagnostic) =>
      SQLean.Tests.assert (diagnostic.code == "coverage.sqlite.query-quantified-comparison")
        "wrong SQLite quantified-query boundary"
  | _ => throw (IO.userError "SQLite quantified-query syntax must remain explicitly unsupported")

def quantifiedSubqueryContractTests : IO Nat := do
  let mut count := 0
  for quantifier in ["ANY", "SOME", "ALL"] do
    for op in ["=", "<>", "<", "<=", ">", ">="] do
      let output ← quantifiedOutput s!"SELECT 1 {op} {quantifier}(SELECT 2)"
      SQLean.Tests.assert (output == [⟨"?column?", ⟨.bool, false⟩, none⟩])
        "strict nonnullable quantified-query operator metadata changed"
      count := count + 1
  for sql in ["SELECT NULL = ANY(SELECT 1 WHERE FALSE)",
      "SELECT NULL = ALL(SELECT 1 WHERE FALSE)",
      "SELECT 1 = ANY(SELECT NULL::INTEGER)",
      "SELECT NULL < ALL(SELECT 2)"] do
    let output ← quantifiedOutput sql
    SQLean.Tests.assert (output == [⟨"?column?", ⟨.bool, true⟩, none⟩])
      "quantified-query potential NULLability changed"
    count := count + 1
  for sql in ["SELECT '1' = ANY(SELECT 1)", "SELECT ARRAY[1] = ANY(SELECT ARRAY[1])",
      "SELECT 1 = ANY((SELECT ARRAY[1])::INTEGER[])",
      "SELECT 'x' COLLATE \"C\" = ANY(SELECT 'x' COLLATE \"POSIX\")",
      "SELECT q.a = ANY(SELECT 1) FROM(SELECT 1 AS a)q",
      "WITH c AS(SELECT 1 AS a) SELECT 1 = ANY(SELECT a FROM c)",
      "SELECT 1 = ALL(WITH c AS(SELECT 2 AS x) SELECT x FROM c)",
      "WITH c AS(SELECT 2 AS x) SELECT 1 < ALL(WITH c AS(SELECT 3 AS x) SELECT x FROM c)",
      "SELECT 'a' = ANY(SELECT CASE WHEN TRUE THEN (SELECT 'x' COLLATE \"C\") ELSE (SELECT 'y' COLLATE \"POSIX\") END)"] do
    discard <| quantifiedOutput sql
    count := count + 1
  for sql in ["1 = ANY(SELECT ARRAY[1])", "1 = ANY((SELECT ARRAY[1]))",
      "1 = SOME(((SELECT ARRAY[1])))", "1 = ALL(SELECT 1)"] do
    parsedQuantifiedQuery sql
    count := count + 1
  let wrapped ← expectOk "cast selects array-expression quantifier"
    (Advanced.parseExpression "1 = ANY((SELECT ARRAY[1])::INTEGER[])")
  match wrapped with
  | .quantifiedComparison .. => pure ()
  | _ => throw (IO.userError "explicit array cast must disambiguate quantified array syntax")
  for sql in ["SELECT 1 = ANY(SELECT '1')", "SELECT 1 = ANY(SELECT NULL)",
      "SELECT 1 = ANY(SELECT ARRAY[1])", "SELECT 1 = SOME((SELECT ARRAY[1]))"] do
    quantifiedRejected sql "invalid" "quantified_subquery_signature"
    count := count + 1
  quantifiedRejected "SELECT 1 = ALL(SELECT 1,2)" "invalid" "quantified_subquery_arity"
  quantifiedRejected "SELECT 1 = ANY(SELECT q.a) FROM(SELECT 1 AS a)q" "unsupported" "subquery_correlation"
  for op in ["=", "<>", "<", "<=", ">", ">="] do
    for quantifier in ["ANY", "SOME", "ALL"] do
      let output ← quantifiedOutput s!"SELECT (1,2) {op} {quantifier}(SELECT 1,3)"
      SQLean.Tests.assert (output == [⟨"?column?", ⟨.bool, true⟩, none⟩])
        "flat-row quantified metadata must retain conservative potential NULLability"
      count := count + 1
  for sql in ["SELECT ROW() = ANY(SELECT 1)", "SELECT ROW(1) = ALL(SELECT 1,2)",
      "SELECT (1,2) < ANY(SELECT 1)"] do
    quantifiedRejected sql "invalid" "quantified_row_subquery_arity"
    count := count + 1
  quantifiedRejected "SELECT (1,2) < ANY(SELECT '1',2)" "invalid" "quantified_row_subquery_signature"
  quantifiedRejected "SELECT (ROW(1,2),3) = ANY(SELECT ROW(1,2),3)" "unsupported" "record_value"
  for sql in ["SELECT ('a' COLLATE \"C\",'b' COLLATE \"POSIX\") < ANY(SELECT 'a','b')",
      "SELECT ROW(1) = ANY(SELECT 1)", "SELECT (1,NULL) <> ALL(SELECT 2,NULL::INTEGER)"] do
    discard <| quantifiedOutput sql
    count := count + 1
  quantifiedParameters "SELECT (?,?) < ALL(SELECT ?,? WHERE ?>0)"
    ((List.range 5).map (fun n => .anonymous (n + 1)))
  discard <| quantifiedOutput "SELECT (?,?) < ALL(SELECT ?,? WHERE ?>0)" "int,int,int,int,int"
  quantifiedRejected "WITH RECURSIVE t(n) AS(SELECT 1 UNION ALL SELECT 2 FROM t WHERE 1 = ANY(SELECT n FROM t)) SELECT n FROM t"
    "invalid" "recursive_reference"
  let anonymous := "WITH c AS(SELECT ? AS a) SELECT ? = ANY(SELECT ? FROM c WHERE ?>0 ORDER BY ? LIMIT ? OFFSET ?)"
  quantifiedParameters anonymous ((List.range 7).map (fun n => .anonymous (n + 1)))
  discard <| quantifiedOutput anonymous "int,int,int,int,int,int,int"
  quantifiedParameters "SELECT $4 = ALL(SELECT $2 WHERE $1=$2 ORDER BY $3)"
    [.numbered 4, .numbered 2, .numbered 1, .numbered 2, .numbered 3]
  discard <| quantifiedOutput "SELECT $4 = ALL(SELECT $2 WHERE $1=$2 ORDER BY $3)" "int,int,int,int"
  pure (count + 9)

end SQLean.Tests
