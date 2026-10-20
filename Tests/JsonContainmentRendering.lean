import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import SQLean.RenderContract.ValidityPreservation
import Tests.Support

/-! Containment serialization retains direction, grouping and parameter order.
The structural renderer also handles operands outside the independent JSONB
typing profile; no cross-dialect execution equivalence is asserted. -/
namespace SQLean.Tests
open Advanced

private def anon (n : Nat) : Advanced.Expr := .parameter (.anonymous n)
private def numbered (n : Nat) : Advanced.Expr := .parameter (.numbered n)
private def text (value : String) : Advanced.Expr := .literal (.text value)
private def col (name : String) : Advanced.Expr := .column none name
private def queryOf (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr]}}
private def containment : Advanced.Expr :=
  .containment (.containment (anon 1) (anon 2)) (anon 3) true

example (left right : Advanced.Expr) (containedBy : Bool) :
    RenderContract.translateExpr (.containment left right containedBy) =
      .containment (RenderContract.translateExpr left) (RenderContract.translateExpr right)
        containedBy := by
  rw [RenderContract.translateExpr]

example : RenderContract.Admissible (queryOf containment) := by
  refine ⟨{depth := 6, parameters := [.anonymous 1, .anonymous 2, .anonymous 3]}, ?_, ?_, ?_⟩
  · unfold queryOf containment RenderContract.inspectQuery
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
  [⟨1, ⟨.jsonb, []⟩, false⟩, ⟨2, ⟨.jsonb, []⟩, false⟩,
    ⟨3, ⟨.jsonb, []⟩, true⟩]

/-- Strict containment of two declared non-NULL JSONB inputs is nonnullable.
Direction is retained, rather than rewriting a contained-by expression. -/
private theorem nonnull_valid (containedBy : Bool) :
    ExprValid params Scope.empty (.containment (anon 1) (anon 2) containedBy)
      (some ⟨.bool, false⟩) [.anonymous 1, .anonymous 2] :=
  .containment (selected := ⟨[.jsonb, .jsonb], .bool⟩)
    (.parameter (binding := ⟨1, ⟨.jsonb, []⟩, false⟩) (by simp [params]) rfl rfl)
    (.parameter (binding := ⟨2, ⟨.jsonb, []⟩, false⟩) (by simp [params]) rfl rfl)
    (by decide)

example (containedBy : Bool) :
    ExprValid params Scope.empty (.containment (numbered 1) (numbered 2) containedBy)
      (some ⟨.bool, false⟩) [.numbered 1, .numbered 2] := by
  simpa [translateExpr, translateParameter, anon, numbered] using
    expr_valid_translated (nonnull_valid containedBy)

private theorem nullable_valid (containedBy : Bool) :
    ExprValid params Scope.empty (.containment (anon 1) (anon 3) containedBy)
      (some ⟨.bool, true⟩) [.anonymous 1, .anonymous 3] :=
  .containment (selected := ⟨[.jsonb, .jsonb], .bool⟩)
    (.parameter (binding := ⟨1, ⟨.jsonb, []⟩, false⟩) (by simp [params]) rfl rfl)
    (.parameter (binding := ⟨3, ⟨.jsonb, []⟩, true⟩) (by simp [params]) rfl rfl)
    (by decide)

example (containedBy : Bool) :
    ExprValid params Scope.empty (.containment (numbered 1) (numbered 3) containedBy)
      (some ⟨.bool, true⟩) [.numbered 1, .numbered 3] := by
  simpa [translateExpr, translateParameter, anon, numbered] using
    expr_valid_translated (nullable_valid containedBy)

end StaticTransport

private def rejected (profile : RenderContract.Profile) (query : Advanced.Query)
    (status code : String) (budget : Nat := 1024) : IO Unit := do
  match RenderContract.check profile query budget with
  | .ok _ => throw (IO.userError s!"containment unexpectedly accepted {status}/{code}")
  | .error failure =>
    SQLean.Tests.assert (failure.status == status && failure.diagnostic.code == code)
      s!"containment misclassified: {reprStr failure}"

private def checkQuery (query : Advanced.Query) (parameters : List Parameter) : IO Nat := do
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    let certificate ← expectOk "containment" ((RenderContract.check profile query).mapError reprStr)
    SQLean.Tests.assert (certificate.footprint.parameters == parameters)
      "containment lost or reordered operand parameters"
    let parsed ← expectOk certificate.sql (RenderContract.parseRendered profile certificate.sql)
    SQLean.Tests.assert (decide (parsed = RenderContract.expectedQuery profile query))
      "containment roundtrip changed direction, grouping or literal contents"
    let again ← expectOk "containment canonical stability"
      ((RenderContract.check profile parsed).mapError reprStr)
    SQLean.Tests.assert (again.sql == certificate.sql) "containment canonical SQL changed"
    let environment : Parameter → String
      | .anonymous n => s!"anonymous-{n}" | .numbered n => s!"numbered-{n}"
    for parameter in parameters do
      SQLean.Tests.assert
        (certificate.transport environment (RenderContract.parameterSlot parameter) == environment parameter)
        "containment transport changed a binding value"
  rejected .sqliteV01 query "unsupported" "coverage.sqlite.containment"
  pure 3

private def deep : Nat → Advanced.Expr
  | 0 => anon 1
  | n + 1 => .containment (deep n) (text "{}")

def jsonContainmentRenderingTests : IO Nat := do
  let mut count := 0
  for (containedBy, spelling) in [(false, "@>"), (true, "<@")] do
    let expr := Advanced.Expr.containment (anon 1) (anon 2) containedBy
    count := count + (← checkQuery (queryOf expr) [.anonymous 1, .anonymous 2])
    SQLean.Tests.assert (expr.toSql == "(? " ++ spelling ++ " ?)")
      "containment direction or parameter spelling changed"
    let parsed ← expectOk spelling (Advanced.parseExpression ("?" ++ spelling ++ "?"))
    SQLean.Tests.assert (decide (parsed = expr)) "adjacent containment operator token changed"
    count := count + 2
    for (left, right, parameters) in [
        (text "{\"@>\":null,\"<@\":\"雪\"}", text "O'Brien@><@", []),
        (.null, .null, []),
        (numbered 7, .coalesce [numbered 2, numbered 7],
          [.numbered 7, .numbered 2, .numbered 7]),
        (.concat (anon 1) (anon 2), .array [anon 3, anon 4],
          [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4]),
        (.scalarQuery (queryOf (anon 1)), anon 2, [.anonymous 1, .anonymous 2]),
        (.jsonAccess .field (anon 1) (anon 2), anon 3,
          [.anonymous 1, .anonymous 2, .anonymous 3]),
        (.containment (anon 1) (anon 2), anon 3,
          [.anonymous 1, .anonymous 2, .anonymous 3]),
        (anon 1, .containment (anon 2) (anon 3) true,
          [.anonymous 1, .anonymous 2, .anonymous 3]),
        (.array [anon 1, anon 2], .array [anon 3],
          [.anonymous 1, .anonymous 2, .anonymous 3])] do
      count := count + (← checkQuery (queryOf (.containment left right containedBy)) parameters)
    count := count + (← checkQuery
      (queryOf (.containment (.cast (anon 1) ⟨.jsonb, []⟩)
        (.cast (anon 2) ⟨.jsonb, []⟩) containedBy)) [.anonymous 1, .anonymous 2])
  count := count + (← checkQuery (queryOf containment) [.anonymous 1, .anonymous 2, .anonymous 3])
  let a := col "a"
  let b := col "b"
  let c := col "c"
  for (source, expected) in [
      ("a@>b<@c", Advanced.Expr.containment (.containment a b) c true),
      ("a<@b@>c", .containment (.containment a b true) c),
      ("a@>(b<@c)", .containment a (.containment b c true)),
      ("a@>b||c", .concat (.containment a b) c),
      ("a||b@>c", .containment (.concat a b) c),
      ("a@>b~c", .regex (.containment a b) c),
      ("a~b<@c", .containment (.regex a b) c true),
      ("a@>b->c", .jsonAccess .field (.containment a b) c),
      ("a->b<@c", .containment (.jsonAccess .field a b) c true),
      ("a@>b ILIKE c", .pattern (.containment a b) c true),
      ("a ILIKE b<@c", .pattern a (.containment b c true) true),
      ("a@>b+c", .containment a (.binary .add b c)),
      ("a+b<@c", .containment (.binary .add a b) c true),
      ("a@>b=c", .binary .eq (.containment a b) c),
      ("a=b<@c", .binary .eq a (.containment b c true)),
      ("a@> -1", .containment a (.unary .neg 1)),
      ("a<@ +1", .containment a (.unary .pos 1) true),
      ("a@>/* comment */b", .containment a b),
      ("a<@-- comment\nb", .containment a b true),
      ("a@>b[1]", .containment a (.subscript b [.index 1])),
      ("(a<@b)[1]", .subscript (.containment a b true) [.index 1]),
      ("a@>'@><@?'", .containment a (text "@><@?"))] do
    let parsed ← expectOk source (Advanced.parseExpression source)
    SQLean.Tests.assert (decide (parsed = expected)) s!"containment precedence/grouping: {source}"
    count := count + 1
  -- @ prevents PostgreSQL's special trailing +/- split for ordinary operators.
  for source in ["a@>", "<@a", "a@>>b", "a<<@b", "a@>-1", "a<@+1", "a@>~b"] do
    expectError source (Advanced.parseExpression source)
    count := count + 1
  for expr in [
      Advanced.Expr.containment (.decimal "bad") (anon 1),
      .containment (anon 1) (.array [text "ok", .decimal "bad"]) true] do
    rejected .postgres16V01 (queryOf expr) "invalid" "representation.numeric-token"
    count := count + 1
  rejected .identityV01 (queryOf (.containment (anon 2) (anon 1)))
    "invalid" "representation.parameters"
  rejected .postgres16V01 (queryOf (.containment (anon 1) (numbered 2) true))
    "unsupported" "coverage.mixed-parameters"
  for profile in [RenderContract.Profile.identityV01, .postgres16V01, .sqliteV01] do
    rejected profile (queryOf (deep 12)) "inconclusive" "resource.depth" 8
    count := count + 1
  pure (count + 2)

end SQLean.Tests
