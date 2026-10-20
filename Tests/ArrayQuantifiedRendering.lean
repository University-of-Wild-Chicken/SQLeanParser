import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import SQLean.RenderContract.ValidityPreservation
import Tests.Support

/-! Quantified-array serialization and independent transport witnesses.
Operator choice and all three quantifier spellings remain explicit AST fields.
Runtime Boolean/NULL behavior is separate from these structural checks. -/
namespace SQLean.Tests
open Advanced

private def anon (n : Nat) : Advanced.Expr := .parameter (.anonymous n)
private def numbered (n : Nat) : Advanced.Expr := .parameter (.numbered n)
private def queryOf (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr]}}
private def quantified : Advanced.Expr :=
  .quantifiedComparison .le .some (anon 1) (.array [anon 2])

example (op : ComparisonOp) (quantifier : ArrayQuantifier) (left right : Advanced.Expr) :
    RenderContract.translateExpr (.quantifiedComparison op quantifier left right) =
      .quantifiedComparison op quantifier
        (RenderContract.translateExpr left) (RenderContract.translateExpr right) := by
  rw [RenderContract.translateExpr]

/-- The independent domain has a constructive witness without parser or
checker acceptance as a premise. -/
example : RenderContract.Admissible (queryOf quantified) := by
  refine ⟨{depth := 6, parameters := [.anonymous 1, .anonymous 2]}, ?_, ?_, ?_⟩
  · unfold queryOf quantified RenderContract.inspectQuery
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
  [⟨1, ⟨.int, []⟩, false⟩, ⟨2, ⟨.array .bigInt, []⟩, false⟩]
private def typed : Advanced.Expr :=
  .quantifiedComparison .le .some (anon 1) (anon 2)

/-- A non-NULL array declaration does not establish non-NULL elements. The
independent comparison result therefore keeps conservative NULLability. -/
private theorem typed_valid :
    ExprValid params Scope.empty typed (some ⟨.bool, true⟩) [.anonymous 1, .anonymous 2] :=
  .quantifiedComparison (selected := ⟨[.int32, .int64], .bool⟩)
    (.parameter (binding := ⟨1, ⟨.int, []⟩, false⟩) (by simp [params]) rfl rfl)
    (.parameter (binding := ⟨2, ⟨.array .bigInt, []⟩, false⟩) (by simp [params]) rfl rfl)
    (by decide)

example : ExprValid params Scope.empty (translateExpr typed)
    (some ⟨.bool, true⟩) [.numbered 1, .numbered 2] :=
  expr_valid_translated typed_valid

end StaticTransport

private def rejected (profile : RenderContract.Profile) (query : Advanced.Query)
    (status code : String) (budget : Nat := 1024) : IO Unit := do
  match RenderContract.check profile query budget with
  | .ok _ => throw (IO.userError s!"quantified array unexpectedly accepted {status}/{code}")
  | .error failure =>
    SQLean.Tests.assert (failure.status == status && failure.diagnostic.code == code)
      s!"quantified array misclassified: {reprStr failure}"

private def checkQuery (query : Advanced.Query) (parameters : List Parameter) : IO Nat := do
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    let certificate ← expectOk "quantified array"
      ((RenderContract.check profile query).mapError reprStr)
    SQLean.Tests.assert (certificate.footprint.parameters == parameters)
      "quantified comparison lost or reordered parameters"
    let parsed ← expectOk certificate.sql (RenderContract.parseRendered profile certificate.sql)
    SQLean.Tests.assert (decide (parsed = RenderContract.expectedQuery profile query))
      "quantified comparison roundtrip changed operator, spelling, or operands"
    let again ← expectOk "quantified array canonical stability"
      ((RenderContract.check profile parsed).mapError reprStr)
    SQLean.Tests.assert (again.sql == certificate.sql) "quantified array canonical SQL changed"
    let environment : Parameter → String
      | .anonymous n => s!"anonymous-{n}" | .numbered n => s!"numbered-{n}"
    for parameter in parameters do
      SQLean.Tests.assert
        (certificate.transport environment (RenderContract.parameterSlot parameter) == environment parameter)
        "quantified array transport changed a binding value"
  rejected .sqliteV01 query "unsupported" "coverage.sqlite.array-quantified-comparison"
  pure 3

private def deep : Nat → Advanced.Expr
  | 0 => anon 1
  | n + 1 => .quantifiedComparison .eq .any (deep n) (.array [1])

def arrayQuantifiedRenderingTests : IO Nat := do
  let mut count := 0
  for op in [ComparisonOp.eq, .ne, .lt, .le, .gt, .ge] do
    for quantifier in [ArrayQuantifier.any, .some, .all] do
      let expr := Advanced.Expr.quantifiedComparison op quantifier (anon 1) (.array [anon 2, anon 3])
      count := count + (← checkQuery (queryOf expr) [.anonymous 1, .anonymous 2, .anonymous 3])
      let expected := "(? " ++ op.toSql ++ " " ++ quantifier.toSql ++ "(ARRAY[?, ?]))"
      SQLean.Tests.assert (expr.toSql == expected) "quantifier spelling or operator changed"
      count := count + 1
  -- Numbered gaps/repetition, unknown operands, and nested ordinary expressions
  -- are representation cases; no additional execution claim follows.
  for (left, right, parameters) in [
      (numbered 7, .array [numbered 2, numbered 7], [.numbered 7, .numbered 2, .numbered 7]),
      (.null, .null, []),
      (.literal (.text "1"), .literal (.text "{1,NULL}"), []),
      (anon 1, .cast (.array []) ⟨.array .int, []⟩, [.anonymous 1]),
      (.coalesce [anon 1, anon 2], .array [.caseExpr none [(.literal (.bool true), anon 3)] (some .null)],
        [.anonymous 1, .anonymous 2, .anonymous 3])] do
    count := count + (← checkQuery (queryOf (.quantifiedComparison .eq .any left right)) parameters)
  let child := queryOf (.array [anon 2])
  let wrapped := queryOf (.quantifiedComparison .eq .any (anon 1)
    (.cast (.scalarQuery child) ⟨.array .int, []⟩))
  count := count + (← checkQuery wrapped [.anonymous 1, .anonymous 2])
  -- Adding parentheses cannot repair exact scalar-query RHS ambiguity.
  let ambiguous := queryOf (.quantifiedComparison .eq .any (anon 1) (.scalarQuery child))
  for profile in [RenderContract.Profile.identityV01, .postgres16V01, .sqliteV01] do
    rejected profile ambiguous "unsupported" "coverage.quantified-subquery"
    count := count + 1
  for source in ["1 = ANY(SELECT ARRAY[1])", "1 = ANY((SELECT ARRAY[1]))",
      "1 = SOME(((SELECT ARRAY[1])))", "1 = ALL(SELECT 1)", "1 + ANY(ARRAY[1])",
      "1 = ANY()", "1 = ANY(ARRAY[1], ARRAY[2])"] do
    expectError source (Advanced.parseExpression source)
    count := count + 1
  let malformed := queryOf (.quantifiedComparison .eq .all 1 (.array [.decimal "bad-number"]))
  rejected .postgres16V01 malformed "invalid" "representation.numeric-token"
  rejected .identityV01 (queryOf (.quantifiedComparison .eq .any (anon 2) (.array [anon 1])))
    "invalid" "representation.parameters"
  rejected .postgres16V01 (queryOf (.quantifiedComparison .eq .any (anon 1) (.array [numbered 1])))
    "unsupported" "coverage.mixed-parameters"
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    rejected profile (queryOf (deep 12)) "inconclusive" "resource.depth" 8
    count := count + 1
  pure (count + 3)

end SQLean.Tests
