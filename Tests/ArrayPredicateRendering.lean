import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import SQLean.RenderContract.ValidityPreservation
import SQLean.AdvancedQueryValidation
import Tests.Support

/-! Array predicates retain operator identity, grouping and lexical binding
order. Static transport preserves exact selected array types and strict outer
NULLability; it does not equate array-element NULLs with SQL NULL results. -/
namespace SQLean.Tests
open Advanced SelectContract RenderContract

private def anon (n : Nat) : Advanced.Expr := .parameter (.anonymous n)
private def numbered (n : Nat) : Advanced.Expr := .parameter (.numbered n)
private def text (value : String) : Advanced.Expr := .literal (.text value)
private def col (name : String) : Advanced.Expr := .column none name
private def queryOf (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr]}}
private def node : ArrayPredicateOperator → Advanced.Expr → Advanced.Expr → Advanced.Expr
  | .contains, left, right => .containment left right
  | .containedBy, left, right => .containment left right true
  | .overlap, left, right => .overlap left right

example (left right : Advanced.Expr) :
    translateExpr (.overlap left right) = .overlap (translateExpr left) (translateExpr right) := by
  rw [translateExpr]

example : Admissible (queryOf (.overlap (.array [anon 1]) (.array [anon 2]))) := by
  refine ⟨{depth := 6, parameters := [.anonymous 1, .anonymous 2]}, ?_, ?_, ?_⟩
  · unfold queryOf inspectQuery
    dsimp
    unfold inspectSelect
    dsimp
    unfold inspectItem inspectExpr
    unfold inspectExpr
    unfold inspectExpr
    rfl
  · decide
  · decide

section StaticTransport
private def params : SelectContract.ParameterEnv :=
  [⟨1, ⟨.array .int, []⟩, true⟩, ⟨2, ⟨.array .int, []⟩, false⟩,
    ⟨3, ⟨.array .jsonb, []⟩, false⟩, ⟨4, ⟨.array .jsonb, []⟩, false⟩]

private theorem containment_valid (containedBy : Bool) :
    ExprValid params Scope.empty (.containment (anon 1) (anon 2) containedBy)
      (some ⟨.bool, true⟩) [.anonymous 1, .anonymous 2] :=
  .arrayContainment (selected := ⟨[.array .int32, .array .int32], .bool⟩)
    (.parameter (binding := ⟨1, ⟨.array .int, []⟩, true⟩) (by simp [params]) rfl rfl)
    (.parameter (binding := ⟨2, ⟨.array .int, []⟩, false⟩) (by simp [params]) rfl rfl)
    (by decide)

example (containedBy : Bool) :
    ExprValid params Scope.empty (.containment (numbered 1) (numbered 2) containedBy)
      (some ⟨.bool, true⟩) [.numbered 1, .numbered 2] := by
  simpa [translateExpr, translateParameter, anon, numbered] using
    expr_valid_translated (containment_valid containedBy)

private theorem overlap_valid :
    ExprValid params Scope.empty (.overlap (anon 3) (anon 4))
      (some ⟨.bool, false⟩) [.anonymous 3, .anonymous 4] :=
  .overlap (selected := ⟨[.array .jsonb, .array .jsonb], .bool⟩)
    (.parameter (binding := ⟨3, ⟨.array .jsonb, []⟩, false⟩) (by simp [params]) rfl rfl)
    (.parameter (binding := ⟨4, ⟨.array .jsonb, []⟩, false⟩) (by simp [params]) rfl rfl)
    (by decide)

example : ExprValid params Scope.empty (.overlap (numbered 3) (numbered 4))
    (some ⟨.bool, false⟩) [.numbered 3, .numbered 4] := by
  simpa [translateExpr, translateParameter, anon, numbered] using expr_valid_translated overlap_valid

/-- An unknown literal receives its array declaration from the known operand.
Translation preserves the literal category rather than introducing a cast. -/
private theorem contextual_valid :
    ExprValid params Scope.empty (.overlap (anon 2) (text "{1}"))
      (some ⟨.bool, false⟩) [.anonymous 2] :=
  .overlap (selected := ⟨[.array .int32, .array .int32], .bool⟩)
    (.parameter (binding := ⟨2, ⟨.array .int, []⟩, false⟩) (by simp [params]) rfl rfl)
    .text (by decide)

example : ExprValid params Scope.empty (.overlap (numbered 2) (text "{1}"))
    (some ⟨.bool, false⟩) [.numbered 2] := by
  simpa [translateExpr, translateParameter, anon, numbered, text] using
    expr_valid_translated contextual_valid
end StaticTransport

private def rejected (profile : RenderContract.Profile) (query : Advanced.Query)
    (status code : String) (budget : Nat := 1024) : IO Unit := do
  match RenderContract.check profile query budget with
  | .ok _ => throw (IO.userError s!"array predicate unexpectedly accepted {status}/{code}")
  | .error failure =>
    SQLean.Tests.assert (failure.status == status && failure.diagnostic.code == code)
      s!"array predicate classification: {reprStr failure}"

private def checkQuery (operator : ArrayPredicateOperator) (left right : Advanced.Expr)
    (parameters : List Parameter) : IO Nat := do
  let expr := node operator left right
  let query := queryOf expr
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    let certificate ← expectOk "array predicate" ((RenderContract.check profile query).mapError reprStr)
    SQLean.Tests.assert (certificate.footprint.parameters == parameters)
      "array predicate parameter order changed"
    let parsed ← expectOk certificate.sql (parseRendered profile certificate.sql)
    SQLean.Tests.assert (decide (parsed = expectedQuery profile query))
      "array predicate roundtrip changed operands, direction or grouping"
    let again ← expectOk "array predicate stability" ((RenderContract.check profile parsed).mapError reprStr)
    SQLean.Tests.assert (again.sql == certificate.sql) "array predicate canonical SQL changed"
    let environment : Parameter → String := fun p => reprStr p
    for parameter in parameters do
      SQLean.Tests.assert
        (certificate.transport environment (parameterSlot parameter) == environment parameter)
        "array predicate parameter value changed"
  SQLean.Tests.assert (Advanced.expressionParameters 128 expr == parameters)
    "coarse expression walker lost array predicate parameters"
  expectError "coarse tier requires exact array predicate signatures" (Advanced.checkQuery [] [] query)
  rejected .sqliteV01 query "unsupported" (match operator with
    | .overlap => "coverage.sqlite.overlap" | _ => "coverage.sqlite.containment")
  pure 5

private def deep : Nat → Advanced.Expr
  | 0 => anon 1
  | n + 1 => .overlap (deep n) (.array [])

def arrayPredicateRenderingTests : IO Nat := do
  let mut count := 0
  for (operator, spelling) in [
      (ArrayPredicateOperator.contains, "@>"), (.containedBy, "<@"), (.overlap, "&&")] do
    let expr := node operator (anon 1) (anon 2)
    count := count + (← checkQuery operator (anon 1) (anon 2) [.anonymous 1, .anonymous 2])
    SQLean.Tests.assert (expr.toSql == "(? " ++ spelling ++ " ?)") "array predicate spelling changed"
    let parsed ← expectOk spelling (Advanced.parseExpression ("?" ++ spelling ++ "?"))
    SQLean.Tests.assert (decide (parsed = expr)) "array predicate adjacent tokens changed"
    count := count + 2
    for (left, right, parameters) in [
        (.array [anon 1, .null], .array [anon 2], [.anonymous 1, .anonymous 2]),
        (.array [.array [anon 1, anon 2]], .array [anon 3, anon 4],
          [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4]),
        (.concat (.array [anon 1]) (.array [anon 2]), .array [anon 3],
          [.anonymous 1, .anonymous 2, .anonymous 3]),
        (numbered 7, .coalesce [numbered 2, numbered 7],
          [.numbered 7, .numbered 2, .numbered 7]),
        (.scalarQuery (queryOf (anon 1)), anon 2, [.anonymous 1, .anonymous 2]),
        (.overlap (anon 1) (anon 2), anon 3, [.anonymous 1, .anonymous 2, .anonymous 3]),
        (anon 1, .containment (anon 2) (anon 3) true, [.anonymous 1, .anonymous 2, .anonymous 3]),
        (.cast (text "[0:1]={1,2}") ⟨.array .int, []⟩,
          .cast (text "[9:10]={1,2}") ⟨.array .int, []⟩, []),
        (.cast (anon 1) ⟨.array .json, []⟩, .cast (anon 2) ⟨.array .json, []⟩,
          [.anonymous 1, .anonymous 2])] do
      count := count + (← checkQuery operator left right parameters)
  let a := col "a"
  let b := col "b"
  let c := col "c"
  for (source, expected) in [
      ("a&&b&&c", Advanced.Expr.overlap (.overlap a b) c),
      ("a&&(b&&c)", .overlap a (.overlap b c)),
      ("a&&b@>c", .containment (.overlap a b) c),
      ("a<@b&&c", .overlap (.containment a b true) c),
      ("a&&b||c", .concat (.overlap a b) c),
      ("a||b&&c", .overlap (.concat a b) c),
      ("a&&b->c", .jsonAccess .field (.overlap a b) c),
      ("a->b&&c", .overlap (.jsonAccess .field a b) c),
      ("a&&b~c", .regex (.overlap a b) c),
      ("a~b&&c", .overlap (.regex a b) c),
      ("a&&b ILIKE c", .pattern (.overlap a b) c true),
      ("a ILIKE b&&c", .pattern a (.overlap b c) true),
      ("a&&b+c", .overlap a (.binary .add b c)),
      ("a+b&&c", .overlap (.binary .add a b) c),
      ("a&&b=c", .binary .eq (.overlap a b) c),
      ("a=b&&c", .binary .eq a (.overlap b c)),
      ("a&& -1", .overlap a (.unary .neg 1)),
      ("a&&/* nested /* comment */ okay */b", .overlap a b),
      ("a&&-- line\nb", .overlap a b),
      ("a&&b[1]", .overlap a (.subscript b [.index 1])),
      ("(a&&b)[1]", .subscript (.overlap a b) [.index 1]),
      ("a&&'&&@><@?'", .overlap a (text "&&@><@?"))] do
    let parsed ← expectOk source (Advanced.parseExpression source)
    SQLean.Tests.assert (decide (parsed = expected)) s!"overlap precedence/grouping: {source}"
    count := count + 1
  for source in ["a&&", "&&a", "a&&&b", "a&&-1", "a&&+1", "a&&~b", "a||-1"] do
    expectError source (Advanced.parseExpression source)
    count := count + 1
  for expr in [
      Advanced.Expr.overlap (.decimal "bad") (anon 1),
      .overlap (anon 1) (.array [text "ok", .decimal "bad"])] do
    rejected .postgres16V01 (queryOf expr) "invalid" "representation.numeric-token"
    count := count + 1
  rejected .identityV01 (queryOf (.overlap (anon 2) (anon 1))) "invalid" "representation.parameters"
  rejected .postgres16V01 (queryOf (.overlap (anon 1) (numbered 2)))
    "unsupported" "coverage.mixed-parameters"
  for profile in [RenderContract.Profile.identityV01, .postgres16V01, .sqliteV01] do
    rejected profile (queryOf (deep 12)) "inconclusive" "resource.depth" 8
    count := count + 1
  pure (count + 2)

end SQLean.Tests
