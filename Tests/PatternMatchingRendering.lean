import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import SQLean.RenderContract.ValidityPreservation
import Tests.Support

/-! Pattern serialization retains the operand tree, operator flags and raw
pattern text. Static transport does not establish regex compilation, collation
behavior or execution equivalence between database implementations. -/
namespace SQLean.Tests
open Advanced

private def anon (n : Nat) : Advanced.Expr := .parameter (.anonymous n)
private def numbered (n : Nat) : Advanced.Expr := .parameter (.numbered n)
private def text (value : String) : Advanced.Expr := .literal (.text value)
private def col (name : String) : Advanced.Expr := .column none name
private def queryOf (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr]}}
private def expression : Advanced.Expr :=
  .regex (.concat (anon 1) (anon 2)) (anon 3) true true

example (arg pattern : Advanced.Expr) (insensitive negated : Bool) :
    RenderContract.translateExpr (.regex arg pattern insensitive negated) =
      .regex (RenderContract.translateExpr arg) (RenderContract.translateExpr pattern)
        insensitive negated := by
  rw [RenderContract.translateExpr]

example : RenderContract.Admissible (queryOf expression) := by
  refine ⟨{depth := 6, parameters := [.anonymous 1, .anonymous 2, .anonymous 3]}, ?_, ?_, ?_⟩
  · unfold queryOf expression RenderContract.inspectQuery
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
  [⟨1, ⟨.char, [5]⟩, false⟩, ⟨2, ⟨.text, []⟩, true⟩,
    ⟨3, ⟨.text, []⟩, false⟩, ⟨4, ⟨.char, [3]⟩, false⟩]

/-- Concrete CHAR on the left selects the BPCHAR/TEXT operator. Translation
must preserve that family instead of silently trimming the subject to TEXT. -/
private theorem ilike_valid :
    ExprValid params Scope.empty (.pattern (anon 1) (anon 2) true)
      (some ⟨.bool, true⟩) [.anonymous 1, .anonymous 2] :=
  .ilike (selected := ⟨[.char [], .text], .bool⟩)
    (.parameter (binding := ⟨1, ⟨.char, [5]⟩, false⟩) (by simp [params]) rfl rfl)
    (.parameter (binding := ⟨2, ⟨.text, []⟩, true⟩) (by simp [params]) rfl rfl)
    (by decide)

example : ExprValid params Scope.empty (.pattern (numbered 1) (numbered 2) true)
    (some ⟨.bool, true⟩) [.numbered 1, .numbered 2] := by
  simpa [translateExpr, translateParameter, anon, numbered] using
    expr_valid_translated ilike_valid

private theorem regex_valid (insensitive negated : Bool) :
    ExprValid params Scope.empty (.regex (anon 1) (anon 2) insensitive negated)
      (some ⟨.bool, true⟩) [.anonymous 1, .anonymous 2] :=
  .regex (selected := ⟨[.char [], .text], .bool⟩)
    (.parameter (binding := ⟨1, ⟨.char, [5]⟩, false⟩) (by simp [params]) rfl rfl)
    (.parameter (binding := ⟨2, ⟨.text, []⟩, true⟩) (by simp [params]) rfl rfl)
    (by decide)

example (insensitive negated : Bool) :
    ExprValid params Scope.empty (.regex (numbered 1) (numbered 2) insensitive negated)
      (some ⟨.bool, true⟩) [.numbered 1, .numbered 2] := by
  simpa [translateExpr, translateParameter, anon, numbered] using
    expr_valid_translated (regex_valid insensitive negated)

/-- CHAR on the right is a pattern converted to TEXT; its presence does not
select the CHAR-subject family. Non-NULL bindings yield non-NULL results when
evaluation succeeds, independently of whether pattern compilation succeeds. -/
private theorem text_subject_valid :
    ExprValid params Scope.empty (.regex (anon 3) (anon 4) false true)
      (some ⟨.bool, false⟩) [.anonymous 3, .anonymous 4] :=
  .regex (selected := ⟨[.text, .text], .bool⟩)
    (.parameter (binding := ⟨3, ⟨.text, []⟩, false⟩) (by simp [params]) rfl rfl)
    (.parameter (binding := ⟨4, ⟨.char, [3]⟩, false⟩) (by simp [params]) rfl rfl)
    (by decide)

example : ExprValid params Scope.empty (.regex (numbered 3) (numbered 4) false true)
    (some ⟨.bool, false⟩) [.numbered 3, .numbered 4] := by
  simpa [translateExpr, translateParameter, anon, numbered] using
    expr_valid_translated text_subject_valid

end StaticTransport

private def rejected (profile : RenderContract.Profile) (query : Advanced.Query)
    (status code : String) (budget : Nat := 1024) : IO Unit := do
  match RenderContract.check profile query budget with
  | .ok _ => throw (IO.userError s!"pattern unexpectedly accepted {status}/{code}")
  | .error failure =>
    SQLean.Tests.assert (failure.status == status && failure.diagnostic.code == code)
      s!"pattern misclassified: {reprStr failure}"

private def checkQuery (query : Advanced.Query) (parameters : List Parameter)
    (sqliteCode : String) : IO Nat := do
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    let certificate ← expectOk "pattern" ((RenderContract.check profile query).mapError reprStr)
    SQLean.Tests.assert (certificate.footprint.parameters == parameters)
      "pattern lost or reordered operands or parameters"
    let parsed ← expectOk certificate.sql (RenderContract.parseRendered profile certificate.sql)
    SQLean.Tests.assert (decide (parsed = RenderContract.expectedQuery profile query))
      "pattern roundtrip changed flags, operands or literal content"
    let again ← expectOk "pattern canonical stability"
      ((RenderContract.check profile parsed).mapError reprStr)
    SQLean.Tests.assert (again.sql == certificate.sql) "pattern canonical SQL changed"
    let environment : Parameter → String
      | .anonymous n => s!"anonymous-{n}" | .numbered n => s!"numbered-{n}"
    for parameter in parameters do
      SQLean.Tests.assert
        (certificate.transport environment (RenderContract.parameterSlot parameter) == environment parameter)
        "pattern transport changed a binding value"
  rejected .sqliteV01 query "unsupported" sqliteCode
  pure 3

private def deep : Nat → Advanced.Expr
  | 0 => anon 1
  | n + 1 => .regex (deep n) (text "x") true false

def patternMatchingRenderingTests : IO Nat := do
  let mut count := 0
  for (insensitive, negated, operator) in [
      (false, false, "~"), (true, false, "~*"), (false, true, "!~"), (true, true, "!~*")] do
    let expr := Advanced.Expr.regex (anon 1) (anon 2) insensitive negated
    count := count + (← checkQuery (queryOf expr) [.anonymous 1, .anonymous 2] "coverage.sqlite.regex")
    SQLean.Tests.assert (expr.toSql == "(? " ++ operator ++ " ?)")
      "regex operator spelling lost an independent flag"
    let parsed ← expectOk operator (Advanced.parseExpression ("?" ++ operator ++ "?"))
    SQLean.Tests.assert (decide (parsed = expr)) "adjacent regex token changed flags"
    count := count + 2
    for (arg, pattern, parameters) in [
        (text "O'Brien\n雪", text "^(O'B|雪)[[:alpha:]]+\\s?$", []),
        (.null, text ".*", []),
        (text "x", .null, []),
        (numbered 7, .concat (numbered 2) (numbered 7), [.numbered 7, .numbered 2, .numbered 7]),
        (.concat (anon 1) (anon 2), .coalesce [anon 3, anon 4],
          [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4]),
        (.scalarQuery (queryOf (anon 1)), anon 2, [.anonymous 1, .anonymous 2])] do
      count := count + (← checkQuery (queryOf (.regex arg pattern insensitive negated))
        parameters "coverage.sqlite.regex")
  for (expr, parameters) in [
      (Advanced.Expr.pattern (anon 1) (anon 2) true, [.anonymous 1, .anonymous 2]),
      (.unary .not (.pattern (anon 1) (anon 2) true), [.anonymous 1, .anonymous 2]),
      (.pattern (text "AbC") (text "%b_") true, []),
      (.pattern (numbered 8) (.concat (numbered 1) (numbered 8)) true,
        [.numbered 8, .numbered 1, .numbered 8]),
      (.pattern (.cast (anon 1) ⟨.char, [5]⟩) (anon 2) true, [.anonymous 1, .anonymous 2])] do
    count := count + (← checkQuery (queryOf expr) parameters "coverage.sqlite.ILIKE")
  let a := col "a"
  let b := col "b"
  let c := col "c"
  for (source, expected) in [
      ("a || b ~ c", Advanced.Expr.regex (.concat a b) c),
      ("a ~ b || c", .concat (.regex a b) c),
      ("a ~ b ~ c", .regex (.regex a b) c),
      ("a ILIKE b || c", .pattern a (.concat b c) true),
      ("a || b ILIKE c", .pattern (.concat a b) c true),
      ("a ILIKE b ~ c", .pattern a (.regex b c) true),
      ("a ~ b ILIKE c", .pattern (.regex a b) c true),
      ("a ~ b = c", .binary .eq (.regex a b) c),
      ("a = b ~ c", .binary .eq a (.regex b c)),
      ("NOT a ~ b AND c", .binary .and (.unary .not (.regex a b)) c),
      ("a ~ b + c", .regex a (.binary .add b c)),
      ("a + b ~ c", .regex (.binary .add a b) c),
      ("a !~* b::TEXT", .regex a (.cast b ⟨.text, []⟩) true true),
      ("a NOT ILIKE b", .unary .not (.pattern a b true)),
      ("NOT a ILIKE b", .unary .not (.pattern a b true)),
      ("a ~ 'a!~*b||c'", .regex a (text "a!~*b||c"))] do
    let parsed ← expectOk source (Advanced.parseExpression source)
    SQLean.Tests.assert (decide (parsed = expected)) s!"pattern precedence/grouping: {source}"
    count := count + 1
  -- Negated regex is retained as an operator flag, distinct from an explicit
  -- surrounding SQL NOT node, even though their successful values may agree.
  for expr in [Advanced.Expr.regex a b false true, .unary .not (.regex a b)] do
    let parsed ← expectOk expr.toSql (Advanced.parseExpression expr.toSql)
    SQLean.Tests.assert (decide (parsed = expr)) "regex negation identity was rewritten"
    count := count + 1
  -- Regex compilation is a value obligation: malformed pattern content is
  -- still a well-represented string, not malformed SQL or an AST token.
  count := count + (← checkQuery (queryOf (.regex (text "x") (text "["))) [] "coverage.sqlite.regex")
  for source in ["a ~", "~ a", "a !~", "a ~** b", "a !~~ b", "a ILIKE", "a ~* * b"] do
    expectError source (Advanced.parseExpression source)
    count := count + 1
  -- PostgreSQL maximal operator tokens must not become a supported prefix
  -- followed by an invented unary sign. SQLite retains its native split.
  for source in ["'x'||-1", "'x'||+1", "a~-b", "a~+b", "a~*-b",
      "a!~-b", "a!~*+b", "a!=+1", "a||~b", "a<=>b", "a~**b"] do
    expectError source (Advanced.parseExpression source)
    count := count + 1
  for (source, expected) in [
      ("'x' || -1", Advanced.Expr.concat (text "x") (.unary .neg 1)),
      ("'x'||/* comment */-1", .concat (text "x") (.unary .neg 1)),
      ("'x'||-- comment\n-1", .concat (text "x") (.unary .neg 1)),
      ("a~/* comment */b", .regex a b),
      ("a!~*-- comment\nb", .regex a b true true),
      ("a~/* nested /* inner */ outer */b", .regex a b),
      ("1+-2", .binary .add 1 (.unary .neg 2)),
      ("1++2", .binary .add 1 (.unary .pos 2)),
      ("1-+2", .binary .sub 1 (.unary .pos 2)),
      ("1<=-2", .binary .le 1 (.unary .neg 2)),
      ("1<>+2", .binary .ne 1 (.unary .pos 2)),
      ("1*-2", .binary .mul 1 (.unary .neg 2)),
      ("1/-2", .binary .div 1 (.unary .neg 2)),
      ("1=+2", .binary .eq 1 (.unary .pos 2)),
      ("1+/* comment */-2", .binary .add 1 (.unary .neg 2)),
      ("1+-- comment\n2", .binary .add 1 2),
      ("1=?", .binary .eq 1 (anon 1))] do
    let parsed ← expectOk source (Advanced.parseExpression source)
    SQLean.Tests.assert (decide (parsed = expected)) s!"operator/comment boundary: {source}"
    count := count + 1
  let sqliteSigned ← expectOk "SQLite signed concat"
    (Advanced.parseSQLiteQuery "SELECT 'x'||-1")
  SQLean.Tests.assert (decide (sqliteSigned = queryOf (.concat (text "x") (.unary .neg 1))))
    "PostgreSQL operator scanning changed SQLite concatenation"
  match Advanced.parseQuery "SELECT 1 +\n  'x'||-1" with
  | .ok _ => throw (IO.userError "unsupported operator unexpectedly parsed")
  | .error failure =>
    SQLean.Tests.assert
      (failure.position.line == 2 && failure.position.column == 6 &&
        failure.message == "unsupported PostgreSQL operator '||-'")
      "maximal operator error lost its original source position"
  count := count + 2
  for expr in [
      Advanced.Expr.regex (.decimal "bad") (anon 1),
      .regex (anon 1) (.concat (text "ok") (.decimal "bad")) true true,
      .pattern (anon 1) (.decimal "bad") true] do
    rejected .postgres16V01 (queryOf expr) "invalid" "representation.numeric-token"
    count := count + 1
  rejected .identityV01 (queryOf (.regex (anon 2) (anon 1))) "invalid" "representation.parameters"
  rejected .postgres16V01 (queryOf (.regex (anon 1) (numbered 2))) "unsupported" "coverage.mixed-parameters"
  for profile in [RenderContract.Profile.identityV01, .postgres16V01, .sqliteV01] do
    rejected profile (queryOf (deep 12)) "inconclusive" "resource.depth" 8
    count := count + 1
  -- LIKE remains available on the SQLite structural profile.
  let like ← expectOk "SQLite LIKE control"
    ((RenderContract.check .sqliteV01 (queryOf (.pattern (anon 1) (anon 2)))).mapError reprStr)
  SQLean.Tests.assert (like.sql == "SELECT (?1 LIKE ?2);") "existing SQLite LIKE changed"
  pure (count + 3)

end SQLean.Tests
