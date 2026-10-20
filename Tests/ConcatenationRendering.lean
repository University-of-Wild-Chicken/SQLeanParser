import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import SQLean.RenderContract.ValidityPreservation
import Tests.Support

/-! Concatenation serialization preserves the exact operand tree and lexical
parameter sequence. PostgreSQL and SQLite give `||` different precedence and
runtime overloads; these structural checks do not assert dialect equivalence. -/
namespace SQLean.Tests
open Advanced

private def anon (n : Nat) : Advanced.Expr := .parameter (.anonymous n)
private def numbered (n : Nat) : Advanced.Expr := .parameter (.numbered n)
private def text (value : String) : Advanced.Expr := .literal (.text value)
private def queryOf (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr]}}
private def concatenation : Advanced.Expr :=
  .concat (.concat (anon 1) (anon 2)) (.concat (anon 3) (anon 4))

example (left right : Advanced.Expr) :
    RenderContract.translateExpr (.concat left right) =
      .concat (RenderContract.translateExpr left) (RenderContract.translateExpr right) := by
  rw [RenderContract.translateExpr]

/-- Independent representation evidence retains all left occurrences before
all right occurrences, including nested concatenations. -/
example : RenderContract.Admissible (queryOf concatenation) := by
  refine ⟨{depth := 6, parameters := [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4]},
    ?_, ?_, ?_⟩
  · unfold queryOf concatenation RenderContract.inspectQuery
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
  [⟨1, ⟨.text, []⟩, false⟩, ⟨2, ⟨.int, []⟩, true⟩,
    ⟨3, ⟨.jsonb, []⟩, false⟩, ⟨4, ⟨.jsonb, []⟩, false⟩,
    ⟨5, ⟨.bytea, []⟩, false⟩, ⟨6, ⟨.bytea, []⟩, true⟩]

/-- The selected text/other overload and strict NULLability survive parameter
translation; no text interpolation replaces the integer binding. -/
private theorem text_other_valid :
    ExprValid params Scope.empty (.concat (anon 1) (anon 2))
      (some ⟨.text, true⟩) [.anonymous 1, .anonymous 2] :=
  .concat (selected := ⟨.textOther, [.text, .int32], .text⟩)
    (.parameter (binding := ⟨1, ⟨.text, []⟩, false⟩) (by simp [params]) rfl rfl)
    (.parameter (binding := ⟨2, ⟨.int, []⟩, true⟩) (by simp [params]) rfl rfl)
    (by decide)

example : ExprValid params Scope.empty (.concat (numbered 1) (numbered 2))
    (some ⟨.text, true⟩) [.numbered 1, .numbered 2] := by
  simpa [translateExpr, translateParameter, anon, numbered] using
    expr_valid_translated text_other_valid

private theorem jsonb_valid :
    ExprValid params Scope.empty (.concat (anon 3) (anon 4))
      (some ⟨.jsonb, false⟩) [.anonymous 3, .anonymous 4] :=
  .concat (selected := ⟨.jsonb, [.jsonb, .jsonb], .jsonb⟩)
    (.parameter (binding := ⟨3, ⟨.jsonb, []⟩, false⟩) (by simp [params]) rfl rfl)
    (.parameter (binding := ⟨4, ⟨.jsonb, []⟩, false⟩) (by simp [params]) rfl rfl)
    (by decide)

example : ExprValid params Scope.empty (.concat (numbered 3) (numbered 4))
    (some ⟨.jsonb, false⟩) [.numbered 3, .numbered 4] := by
  simpa [translateExpr, translateParameter, anon, numbered] using
    expr_valid_translated jsonb_valid

private theorem bytea_valid :
    ExprValid params Scope.empty (.concat (anon 5) (anon 6))
      (some ⟨.bytea, true⟩) [.anonymous 5, .anonymous 6] :=
  .concat (selected := ⟨.bytea, [.bytea, .bytea], .bytea⟩)
    (.parameter (binding := ⟨5, ⟨.bytea, []⟩, false⟩) (by simp [params]) rfl rfl)
    (.parameter (binding := ⟨6, ⟨.bytea, []⟩, true⟩) (by simp [params]) rfl rfl)
    (by decide)

example : ExprValid params Scope.empty (.concat (numbered 5) (numbered 6))
    (some ⟨.bytea, true⟩) [.numbered 5, .numbered 6] := by
  simpa [translateExpr, translateParameter, anon, numbered] using
    expr_valid_translated bytea_valid

end StaticTransport

private def rejected (profile : RenderContract.Profile) (query : Advanced.Query)
    (status code : String) (budget : Nat := 1024) : IO Unit := do
  match RenderContract.check profile query budget with
  | .ok _ => throw (IO.userError s!"concatenation unexpectedly accepted {status}/{code}")
  | .error failure =>
    SQLean.Tests.assert (failure.status == status && failure.diagnostic.code == code)
      s!"concatenation misclassified: {reprStr failure}"

private def checkQuery (query : Advanced.Query) (parameters : List Parameter)
    (sqlite : Bool := true) : IO Nat := do
  let profiles := [RenderContract.Profile.identityV01, .postgres16V01] ++
    (if sqlite then [.sqliteV01] else [])
  for profile in profiles do
    let certificate ← expectOk "concatenation"
      ((RenderContract.check profile query).mapError reprStr)
    SQLean.Tests.assert (certificate.footprint.parameters == parameters)
      "concatenation lost or reordered operand parameters"
    let parsed ← expectOk certificate.sql (RenderContract.parseRendered profile certificate.sql)
    SQLean.Tests.assert (decide (parsed = RenderContract.expectedQuery profile query))
      "concatenation roundtrip changed the operand tree"
    let again ← expectOk "concatenation canonical stability"
      ((RenderContract.check profile parsed).mapError reprStr)
    SQLean.Tests.assert (again.sql == certificate.sql) "concatenation canonical SQL changed"
    let environment : Parameter → String
      | .anonymous n => s!"anonymous-{n}" | .numbered n => s!"numbered-{n}"
    for parameter in parameters do
      SQLean.Tests.assert
        (certificate.transport environment (RenderContract.parameterSlot parameter) == environment parameter)
        "concatenation transport changed a binding value"
  pure profiles.length

private def deep : Nat → Advanced.Expr
  | 0 => anon 1
  | n + 1 => .concat (deep n) (text "x")

def concatenationRenderingTests : IO Nat := do
  let mut count := 0
  for (expr, parameters) in [
      (Advanced.Expr.concat (anon 1) (anon 2), [.anonymous 1, .anonymous 2]),
      (concatenation, [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4]),
      (.concat (numbered 7) (.concat (numbered 2) (numbered 7)),
        [.numbered 7, .numbered 2, .numbered 7]),
      (.concat (.concat (text "a") (text "b")) (text "c"), []),
      (.concat (text "a") (.concat (text "b") (text "c")), []),
      (.concat (.binary .add (anon 1) (anon 2)) (.binary .mul (anon 3) (anon 4)),
        [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4]),
      (.binary .mul (anon 1) (.concat (anon 2) (anon 3)),
        [.anonymous 1, .anonymous 2, .anonymous 3]),
      (.concat .null (text "NULL"), []),
      (.concat (text "O'Brien || ? $2") (text "λ雪"), []),
      (.concat (.coalesce [anon 1, anon 2])
        (.caseExpr none [(.literal (.bool true), anon 3)] (some (anon 4))),
        [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4]),
      (.concat (.scalarQuery (queryOf (anon 1))) (anon 2), [.anonymous 1, .anonymous 2]),
      (.concat (.row [anon 1, anon 2]) (.row [anon 3, anon 4]),
        [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4])] do
    count := count + (← checkQuery (queryOf expr) parameters)
  SQLean.Tests.assert (concatenation.toSql == "((? || ?) || (? || ?))")
    "identity concatenation lost explicit grouping"
  SQLean.Tests.assert (concatenation.toSql true == "(($1 || $2) || ($3 || $4))")
    "PostgreSQL concatenation changed parameter spelling"
  SQLean.Tests.assert (Advanced.SQLite.exprSql concatenation == "((?1 || ?2) || (?3 || ?4))")
    "SQLite concatenation changed parameter spelling"
  count := count + 3
  -- The same unparenthesized source has different trees in the two dialects.
  -- Canonical parenthesization must preserve either tree on its own profile.
  for (source, pg, sqlite) in [
      ("1 + 2 || 3 * 4",
        Advanced.Expr.concat (.binary .add 1 2) (.binary .mul 3 4),
        .binary .add 1 (.binary .mul (.concat 2 3) 4)),
      ("1 || 2 + 3", .concat 1 (.binary .add 2 3), .binary .add (.concat 1 2) 3),
      ("1 * 2 || 3", .concat (.binary .mul 1 2) 3, .binary .mul 1 (.concat 2 3)),
      ("1 || 2 * 3", .concat 1 (.binary .mul 2 3), .binary .mul (.concat 1 2) 3),
      ("-1 || 2", .concat (.unary .neg 1) 2, .concat (.unary .neg 1) 2),
      ("1 || -2", .concat 1 (.unary .neg 2), .concat 1 (.unary .neg 2)),
      ("1 || 2 || 3", .concat (.concat 1 2) 3, .concat (.concat 1 2) 3),
      ("1 || (2 || 3)", .concat 1 (.concat 2 3), .concat 1 (.concat 2 3)),
      ("1 || 2 = 3", .binary .eq (.concat 1 2) 3, .binary .eq (.concat 1 2) 3),
      ("1 = 2 || 3", .binary .eq 1 (.concat 2 3), .binary .eq 1 (.concat 2 3)),
      ("'a' || 'b' LIKE 'ab'", .pattern (.concat (text "a") (text "b")) (text "ab"),
        .pattern (.concat (text "a") (text "b")) (text "ab")),
      ("'a' || 'b' IS NULL", .isNull (.concat (text "a") (text "b")),
        .isNull (.concat (text "a") (text "b")))] do
    let pgQuery ← expectOk source (Advanced.parseQuery ("SELECT " ++ source))
    let sqliteQuery ← expectOk source (Advanced.parseSQLiteQuery ("SELECT " ++ source))
    SQLean.Tests.assert (decide (pgQuery = queryOf pg)) s!"PostgreSQL concat precedence: {source}"
    SQLean.Tests.assert (decide (sqliteQuery = queryOf sqlite)) s!"SQLite concat precedence: {source}"
    count := count + 2
    count := count + (← checkQuery pgQuery [])
    if !(decide (pgQuery = sqliteQuery)) then
      count := count + (← checkQuery sqliteQuery [])
  -- Advanced representability is wider than the independent static profile.
  let arrays := Advanced.Expr.concat (.array [anon 1]) (.array [anon 2])
  count := count + (← checkQuery (queryOf arrays) [.anonymous 1, .anonymous 2] false)
  rejected .sqliteV01 (queryOf arrays) "unsupported" "coverage.sqlite.array-constructor"
  count := count + 1
  for type in [TypeName.jsonb, .bytea] do
    let expr := Advanced.Expr.concat (.cast (anon 1) ⟨type, []⟩) (.cast (anon 2) ⟨type, []⟩)
    count := count + (← checkQuery (queryOf expr) [.anonymous 1, .anonymous 2] false)
  for source in ["|| 1", "1 ||", "1 ||| 2", "1 | 2", "1 || || 2"] do
    expectError source (Advanced.parseExpression source)
    count := count + 1
  for expr in [
      Advanced.Expr.concat (.decimal "bad") (anon 1),
      .concat (anon 1) (.concat (text "ok") (.decimal "bad"))] do
    rejected .postgres16V01 (queryOf expr) "invalid" "representation.numeric-token"
    count := count + 1
  rejected .identityV01 (queryOf (.concat (anon 2) (anon 1)))
    "invalid" "representation.parameters"
  rejected .postgres16V01 (queryOf (.concat (anon 1) (numbered 2)))
    "unsupported" "coverage.mixed-parameters"
  for profile in [RenderContract.Profile.identityV01, .postgres16V01, .sqliteV01] do
    rejected profile (queryOf (deep 12)) "inconclusive" "resource.depth" 8
    count := count + 1
  pure (count + 2)

end SQLean.Tests
