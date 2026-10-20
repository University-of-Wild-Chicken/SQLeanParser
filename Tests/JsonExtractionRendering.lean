import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import SQLean.RenderContract.ValidityPreservation
import Tests.Support

/-! JSON extraction preserves operator identity, exact operand grouping and
lexical parameter order. Structural transport neither evaluates JSON nor
establishes matching extraction semantics in another database dialect. -/
namespace SQLean.Tests
open Advanced

private def anon (n : Nat) : Advanced.Expr := .parameter (.anonymous n)
private def numbered (n : Nat) : Advanced.Expr := .parameter (.numbered n)
private def text (value : String) : Advanced.Expr := .literal (.text value)
private def col (name : String) : Advanced.Expr := .column none name
private def queryOf (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr]}}
private def extraction : Advanced.Expr :=
  .jsonAccess .fieldText (.jsonAccess .field (anon 1) (anon 2)) (anon 3)

example (op : JsonAccessOp) (arg key : Advanced.Expr) :
    RenderContract.translateExpr (.jsonAccess op arg key) =
      .jsonAccess op (RenderContract.translateExpr arg) (RenderContract.translateExpr key) := by
  rw [RenderContract.translateExpr]

example : RenderContract.Admissible (queryOf extraction) := by
  refine ⟨{depth := 6, parameters := [.anonymous 1, .anonymous 2, .anonymous 3]}, ?_, ?_, ?_⟩
  · unfold queryOf extraction RenderContract.inspectQuery
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
  [⟨1, ⟨.json, []⟩, false⟩, ⟨2, ⟨.int, []⟩, false⟩,
    ⟨3, ⟨.jsonb, []⟩, false⟩, ⟨4, ⟨.varchar, [3]⟩, false⟩,
    ⟨5, ⟨.array .varchar, [3]⟩, false⟩, ⟨6, ⟨.array .text, []⟩, false⟩]

/-- Even non-NULL input and index declarations leave a possibly absent element.
The JSON result remains distinct from a TEXT extraction result. -/
private theorem json_index_valid :
    ExprValid params Scope.empty (.jsonAccess .field (anon 1) (anon 2))
      (some ⟨.json, true⟩) [.anonymous 1, .anonymous 2] :=
  .jsonAccess (selected := ⟨[.json, .int32], .json⟩)
    (.parameter (binding := ⟨1, ⟨.json, []⟩, false⟩) (by simp [params]) rfl rfl)
    (.parameter (binding := ⟨2, ⟨.int, []⟩, false⟩) (by simp [params]) rfl rfl)
    (by decide)

example : ExprValid params Scope.empty (.jsonAccess .field (numbered 1) (numbered 2))
    (some ⟨.json, true⟩) [.numbered 1, .numbered 2] := by
  simpa [translateExpr, translateParameter, anon, numbered] using
    expr_valid_translated json_index_valid

private theorem jsonb_text_valid :
    ExprValid params Scope.empty (.jsonAccess .fieldText (anon 3) (anon 4))
      (some ⟨.text, true⟩) [.anonymous 3, .anonymous 4] :=
  .jsonAccess (selected := ⟨[.jsonb, .text], .text⟩)
    (.parameter (binding := ⟨3, ⟨.jsonb, []⟩, false⟩) (by simp [params]) rfl rfl)
    (.parameter (binding := ⟨4, ⟨.varchar, [3]⟩, false⟩) (by simp [params]) rfl rfl)
    (by decide)

example : ExprValid params Scope.empty (.jsonAccess .fieldText (numbered 3) (numbered 4))
    (some ⟨.text, true⟩) [.numbered 3, .numbered 4] := by
  simpa [translateExpr, translateParameter, anon, numbered] using
    expr_valid_translated jsonb_text_valid

/-- The selected path operator takes TEXT[], retaining the source binding's
independent VARCHAR[] declaration and the explicit coercion signature. -/
private theorem jsonb_path_valid :
    ExprValid params Scope.empty (.jsonAccess .path (anon 3) (anon 5))
      (some ⟨.jsonb, true⟩) [.anonymous 3, .anonymous 5] :=
  .jsonAccess (selected := ⟨[.jsonb, .array .text], .jsonb⟩)
    (.parameter (binding := ⟨3, ⟨.jsonb, []⟩, false⟩) (by simp [params]) rfl rfl)
    (.parameter (binding := ⟨5, ⟨.array .varchar, [3]⟩, false⟩) (by simp [params]) rfl rfl)
    (by decide)

example : ExprValid params Scope.empty (.jsonAccess .path (numbered 3) (numbered 5))
    (some ⟨.jsonb, true⟩) [.numbered 3, .numbered 5] := by
  simpa [translateExpr, translateParameter, anon, numbered] using
    expr_valid_translated jsonb_path_valid

private theorem json_path_text_valid :
    ExprValid params Scope.empty (.jsonAccess .pathText (anon 1) (anon 6))
      (some ⟨.text, true⟩) [.anonymous 1, .anonymous 6] :=
  .jsonAccess (selected := ⟨[.json, .array .text], .text⟩)
    (.parameter (binding := ⟨1, ⟨.json, []⟩, false⟩) (by simp [params]) rfl rfl)
    (.parameter (binding := ⟨6, ⟨.array .text, []⟩, false⟩) (by simp [params]) rfl rfl)
    (by decide)

example : ExprValid params Scope.empty (.jsonAccess .pathText (numbered 1) (numbered 6))
    (some ⟨.text, true⟩) [.numbered 1, .numbered 6] := by
  simpa [translateExpr, translateParameter, anon, numbered] using
    expr_valid_translated json_path_text_valid

end StaticTransport

private def rejected (profile : RenderContract.Profile) (query : Advanced.Query)
    (status code : String) (budget : Nat := 1024) : IO Unit := do
  match RenderContract.check profile query budget with
  | .ok _ => throw (IO.userError s!"JSON extraction unexpectedly accepted {status}/{code}")
  | .error failure =>
    SQLean.Tests.assert (failure.status == status && failure.diagnostic.code == code)
      s!"JSON extraction misclassified: {reprStr failure}"

private def checkQuery (query : Advanced.Query) (parameters : List Parameter) : IO Nat := do
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    let certificate ← expectOk "JSON extraction" ((RenderContract.check profile query).mapError reprStr)
    SQLean.Tests.assert (certificate.footprint.parameters == parameters)
      "JSON extraction lost or reordered subject/key parameters"
    let parsed ← expectOk certificate.sql (RenderContract.parseRendered profile certificate.sql)
    SQLean.Tests.assert (decide (parsed = RenderContract.expectedQuery profile query))
      "JSON extraction roundtrip changed operator, grouping or literal contents"
    let again ← expectOk "JSON canonical stability"
      ((RenderContract.check profile parsed).mapError reprStr)
    SQLean.Tests.assert (again.sql == certificate.sql) "JSON canonical SQL changed"
    let environment : Parameter → String
      | .anonymous n => s!"anonymous-{n}" | .numbered n => s!"numbered-{n}"
    for parameter in parameters do
      SQLean.Tests.assert
        (certificate.transport environment (RenderContract.parameterSlot parameter) == environment parameter)
        "JSON extraction transport changed a binding value"
  rejected .sqliteV01 query "unsupported" "coverage.sqlite.json-extraction"
  pure 3

private def deep : Nat → Advanced.Expr
  | 0 => anon 1
  | n + 1 => .jsonAccess .field (deep n) (text "key")

def jsonExtractionRenderingTests : IO Nat := do
  let mut count := 0
  for (op, spelling) in [
      (JsonAccessOp.field, "->"), (.fieldText, "->>"), (.path, "#>"), (.pathText, "#>>")] do
    let expr := Advanced.Expr.jsonAccess op (anon 1) (anon 2)
    count := count + (← checkQuery (queryOf expr) [.anonymous 1, .anonymous 2])
    SQLean.Tests.assert (expr.toSql == "(? " ++ spelling ++ " ?)")
      "JSON operator or parameter spelling changed"
    let parsed ← expectOk spelling (Advanced.parseExpression ("?" ++ spelling ++ "?"))
    SQLean.Tests.assert (decide (parsed = expr)) "adjacent JSON operator token changed"
    count := count + 2
    for (arg, key, parameters) in [
        (text "{\"a\":null,\"->>\":\"雪\"}", text "O'Brien->>#>>", []),
        (.null, .null, []),
        (numbered 7, .coalesce [numbered 2, numbered 7],
          [.numbered 7, .numbered 2, .numbered 7]),
        (.concat (anon 1) (anon 2), .array [anon 3, anon 4],
          [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4]),
        (.scalarQuery (queryOf (anon 1)), anon 2, [.anonymous 1, .anonymous 2]),
        (.jsonAccess .field (anon 1) (anon 2), anon 3,
          [.anonymous 1, .anonymous 2, .anonymous 3])] do
      count := count + (← checkQuery (queryOf (.jsonAccess op arg key)) parameters)
  count := count + (← checkQuery (queryOf extraction) [.anonymous 1, .anonymous 2, .anonymous 3])
  -- JSON/JSONB source and array-path structure remain explicit in the tree.
  for base in [TypeName.json, .jsonb] do
    for op in [JsonAccessOp.field, .fieldText, .path, .pathText] do
      let key := match op with
        | .field | .fieldText => anon 2
        | .path | .pathText => .cast (.array [anon 2, .null, anon 3]) ⟨.array .text, []⟩
      let parameters := match op with
        | .field | .fieldText => [.anonymous 1, .anonymous 2]
        | .path | .pathText => [.anonymous 1, .anonymous 2, .anonymous 3]
      count := count + (← checkQuery (queryOf (.jsonAccess op (.cast (anon 1) ⟨base, []⟩) key)) parameters)
  let a := col "a"
  let b := col "b"
  let c := col "c"
  for (source, expected) in [
      ("a->b->>c", Advanced.Expr.jsonAccess .fieldText (.jsonAccess .field a b) c),
      ("a#>b#>>c", .jsonAccess .pathText (.jsonAccess .path a b) c),
      ("a->(b->c)", .jsonAccess .field a (.jsonAccess .field b c)),
      ("a->b||c", .concat (.jsonAccess .field a b) c),
      ("a||b->c", .jsonAccess .field (.concat a b) c),
      ("a->>b~c", .regex (.jsonAccess .fieldText a b) c),
      ("a~b->>c", .jsonAccess .fieldText (.regex a b) c),
      ("a->>b ILIKE c", .pattern (.jsonAccess .fieldText a b) c true),
      ("a ILIKE b->>c", .pattern a (.jsonAccess .fieldText b c) true),
      ("a->b+c", .jsonAccess .field a (.binary .add b c)),
      ("a+b->c", .jsonAccess .field (.binary .add a b) c),
      ("a->b=c", .binary .eq (.jsonAccess .field a b) c),
      ("a=b->c", .binary .eq a (.jsonAccess .field b c)),
      ("a->-1", .jsonAccess .field a (.unary .neg 1)),
      ("a->>-1", .jsonAccess .fieldText a (.unary .neg 1)),
      ("a#> -1", .jsonAccess .path a (.unary .neg 1)),
      ("a->/* comment */b", .jsonAccess .field a b),
      ("a#>>-- comment\nb", .jsonAccess .pathText a b),
      ("a->b[1]", .jsonAccess .field a (.subscript b [.index 1])),
      ("(a->b)[1]", .subscript (.jsonAccess .field a b) [.index 1]),
      ("a->'->>#>>?'", .jsonAccess .field a (text "->>#>>?"))] do
    let parsed ← expectOk source (Advanced.parseExpression source)
    SQLean.Tests.assert (decide (parsed = expected)) s!"JSON operator precedence/grouping: {source}"
    count := count + 1
  for source in ["a->", "->a", "a#>", "a->>>b", "a#>>>b", "a#>-1", "a#>>+1"] do
    expectError source (Advanced.parseExpression source)
    count := count + 1
  -- Domain traversal sees malformed operands even behind nested extraction.
  for expr in [
      Advanced.Expr.jsonAccess .field (.decimal "bad") (anon 1),
      .jsonAccess .pathText (anon 1) (.array [text "ok", .decimal "bad"])] do
    rejected .postgres16V01 (queryOf expr) "invalid" "representation.numeric-token"
    count := count + 1
  rejected .identityV01 (queryOf (.jsonAccess .field (anon 2) (anon 1)))
    "invalid" "representation.parameters"
  rejected .postgres16V01 (queryOf (.jsonAccess .path (anon 1) (numbered 2)))
    "unsupported" "coverage.mixed-parameters"
  for profile in [RenderContract.Profile.identityV01, .postgres16V01, .sqliteV01] do
    rejected profile (queryOf (deep 12)) "inconclusive" "resource.depth" 8
    count := count + 1
  pure (count + 2)

end SQLean.Tests
