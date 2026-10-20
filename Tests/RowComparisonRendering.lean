import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import SQLean.RenderContract.ValidityPreservation
import Tests.Support

/-! Row serialization preserves field identity and lexical parameter order.
These are representation and static transport checks, not a universal
PostgreSQL/SQLite execution-equivalence theorem. -/
namespace SQLean.Tests
open Advanced

private def anon (n : Nat) : Advanced.Expr := .parameter (.anonymous n)
private def numbered (n : Nat) : Advanced.Expr := .parameter (.numbered n)
private def queryOf (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr]}}
private def comparison : Advanced.Expr :=
  .binary .le (.row [anon 1, anon 2]) (.row [anon 3, anon 4])

example (elements : List Advanced.Expr) :
    RenderContract.translateExpr (.row elements) =
      .row (elements.map RenderContract.translateExpr) := by
  rw [RenderContract.translateExpr]
  simp only [List.attach_map_val]

/-- The occurrence sequence is all left fields followed by all right fields;
it is not interleaved by the pairwise comparison signatures. -/
example : RenderContract.Admissible (queryOf comparison) := by
  refine ⟨{depth := 6, parameters := [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4]},
    ?_, ?_, ?_⟩
  · unfold queryOf comparison RenderContract.inspectQuery
    dsimp
    unfold RenderContract.inspectSelect
    dsimp
    unfold RenderContract.inspectItem RenderContract.inspectExpr
    unfold RenderContract.inspectExpr
    unfold RenderContract.inspectExpr
    rfl
  · decide
  · decide

section StaticTransport
open SelectContract RenderContract

private def params : SelectContract.ParameterEnv :=
  [⟨1, ⟨.int, []⟩, false⟩, ⟨2, ⟨.text, []⟩, false⟩,
    ⟨3, ⟨.bigInt, []⟩, false⟩, ⟨4, ⟨.text, []⟩, true⟩]

/-- Field pairs can select different scalar operators; their occurrence lists
still follow the two complete source rows. -/
private theorem comparison_valid :
    ExprValid params Scope.empty comparison (some ⟨.bool, true⟩)
      [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4] :=
  .rowComparison (op := .le)
    (selected := [⟨[.int32, .int64], .bool⟩, ⟨[.text, .text], .bool⟩])
    (.cons (.parameter (binding := ⟨1, ⟨.int, []⟩, false⟩) (by simp [params]) rfl rfl)
      (.cons (.parameter (binding := ⟨2, ⟨.text, []⟩, false⟩) (by simp [params]) rfl rfl) .nil))
    (.cons (.parameter (binding := ⟨3, ⟨.bigInt, []⟩, false⟩) (by simp [params]) rfl rfl)
      (.cons (.parameter (binding := ⟨4, ⟨.text, []⟩, true⟩) (by simp [params]) rfl rfl) .nil))
    (by decide)

example : ExprValid params Scope.empty (translateExpr comparison) (some ⟨.bool, true⟩)
    [.numbered 1, .numbered 2, .numbered 3, .numbered 4] :=
  expr_valid_translated comparison_valid

end StaticTransport

private def rejected (profile : RenderContract.Profile) (query : Advanced.Query)
    (status code : String) (budget : Nat := 1024) : IO Unit := do
  match RenderContract.check profile query budget with
  | .ok _ => throw (IO.userError s!"row unexpectedly accepted {status}/{code}")
  | .error failure =>
    SQLean.Tests.assert (failure.status == status && failure.diagnostic.code == code)
      s!"row misclassified: {reprStr failure}"

private def checkQuery (query : Advanced.Query) (parameters : List Parameter)
    (sqlite : Bool := true) : IO Nat := do
  let profiles := [RenderContract.Profile.identityV01, .postgres16V01] ++
    (if sqlite then [.sqliteV01] else [])
  for profile in profiles do
    let certificate ← expectOk "row comparison"
      ((RenderContract.check profile query).mapError reprStr)
    SQLean.Tests.assert (certificate.footprint.parameters == parameters)
      "row comparison lost or interleaved field parameters"
    let parsed ← expectOk certificate.sql (RenderContract.parseRendered profile certificate.sql)
    SQLean.Tests.assert (decide (parsed = RenderContract.expectedQuery profile query))
      "row roundtrip changed field identity or grouping"
    let again ← expectOk "row canonical stability"
      ((RenderContract.check profile parsed).mapError reprStr)
    SQLean.Tests.assert (again.sql == certificate.sql) "row canonical SQL changed"
    let environment : Parameter → String
      | .anonymous n => s!"anonymous-{n}" | .numbered n => s!"numbered-{n}"
    for parameter in parameters do
      SQLean.Tests.assert
        (certificate.transport environment (RenderContract.parameterSlot parameter) == environment parameter)
        "row transport changed a binding value"
  pure profiles.length

private def deep : Nat → Advanced.Expr
  | 0 => anon 1
  | n + 1 => .row [deep n, .null]

def rowComparisonRenderingTests : IO Nat := do
  let mut count := 0
  for op in [ComparisonOp.eq, .ne, .lt, .le, .gt, .ge] do
    let expr := Advanced.Expr.binary op.toBinOp
      (.row [anon 1, anon 2]) (.row [anon 3, anon 4])
    count := count + (← checkQuery (queryOf expr)
      [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4])
    SQLean.Tests.assert
      (expr.toSql == "(ROW(?, ?) " ++ op.toSql ++ " ROW(?, ?))")
      "PostgreSQL row normalization changed operator or field order"
    SQLean.Tests.assert
      (Advanced.SQLite.exprSql expr == "((?1, ?2) " ++ op.toSql ++ " (?3, ?4))")
      "SQLite row fields did not use native tuple syntax"
    count := count + 2
  for (expr, parameters) in [
      (.binary .eq (.row [numbered 7, numbered 2]) (.row [numbered 2, numbered 7]),
        [.numbered 7, .numbered 2, .numbered 2, .numbered 7]),
      (.binary .lt (.row [1, .null]) (.row [2, .null]), []),
      (.binary .ge (.row [.coalesce [anon 1, .null], anon 2])
        (.row [anon 3, .caseExpr none [(.literal (.bool true), anon 4)] (some .null)]),
        [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4]),
      (.binary .eq (.row [.row [1, 2], .row [3, 4]]) (.row [.row [1, 2], .row [3, 4]]), []),
      (.isNull (.row [anon 1, anon 2]), [.anonymous 1, .anonymous 2])] do
    count := count + (← checkQuery (queryOf expr) parameters)
  -- PostgreSQL can represent empty/single-field rows and standalone composites;
  -- their presence alone is not a basic-contract typing certificate.
  for elements in [([] : List Advanced.Expr), [1], [1, 2], [.row []]] do
    let expr := Advanced.Expr.row elements
    count := count + (← checkQuery (queryOf expr) [] false)
    let parsed ← expectOk expr.toSql (Advanced.parseExpression expr.toSql)
    SQLean.Tests.assert (decide (parsed = expr)) "ROW arity did not survive parsing"
    count := count + 1
  for elements in [([] : List Advanced.Expr), [1]] do
    rejected .sqliteV01 (queryOf (.row elements)) "unsupported" "coverage.sqlite.row-arity"
    count := count + 1
  let arrays := .binary BinOp.eq (.row [.array [anon 1], anon 2]) (.row [.array [anon 3], anon 4])
  count := count + (← checkQuery (queryOf arrays)
    [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4] false)
  rejected .sqliteV01 (queryOf arrays) "unsupported" "coverage.sqlite.array-constructor"
  count := count + 1
  let nestedQuery := .binary BinOp.eq (.row [.scalarQuery (queryOf (anon 1)), anon 2])
    (.row [anon 3, anon 4])
  count := count + (← checkQuery (queryOf nestedQuery)
    [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4])
  for (source, expected) in [
      ("(1, 2)", Advanced.Expr.row [1, 2]),
      ("ROW(1, 2)", .row [1, 2]),
      ("((1, 2))", .row [1, 2]),
      ("ROW()", .row []),
      ("ROW(1)", .row [1]),
      ("\"row\"(1,2)", .call ["row"] [1, 2]),
      ("row", .column none "row"),
      ("(1)", 1),
      ("((1,2))[1]", .subscript (.row [1, 2]) [.index 1]),
      ("(ROW(1,2))[1]", .subscript (.row [1, 2]) [.index 1]),
      ("((1,2),(3,4))", .row [.row [1, 2], .row [3, 4]])] do
    let parsed ← expectOk source (Advanced.parseExpression source)
    SQLean.Tests.assert (decide (parsed = expected)) "tuple normalization confused scalar grouping"
    count := count + 1
  for source in ["()", "(1,)", "ROW(,1)", "ROW(1,)", "ROW(1,,2)",
      "(1,2)[1]", "ROW(1,2)[1]"] do
    expectError source (Advanced.parseExpression source)
    count := count + 1
  rejected .postgres16V01 (queryOf (.row [anon 1, .decimal "bad"]))
    "invalid" "representation.numeric-token"
  rejected .identityV01 (queryOf (.binary .eq (.row [anon 1, anon 3]) (.row [anon 2, anon 4])))
    "invalid" "representation.parameters"
  rejected .postgres16V01 (queryOf (.row [anon 1, numbered 2]))
    "unsupported" "coverage.mixed-parameters"
  for profile in [RenderContract.Profile.identityV01, .postgres16V01, .sqliteV01] do
    rejected profile (queryOf (deep 12)) "inconclusive" "resource.depth" 8
    count := count + 1
  pure (count + 3)

end SQLean.Tests
