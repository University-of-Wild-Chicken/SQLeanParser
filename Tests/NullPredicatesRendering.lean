import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import SQLean.RenderContract.ValidityPreservation
import SQLean.AdvancedQueryValidation
import Tests.Support

/-! Representation tests preserve raw NULL and row operands. These tests do not
identify PostgreSQL row null tests with scalar distinctness, and do not assert
cross-dialect value equivalence. PostgreSQL's IS precedence is below comparison;
SQLite's DISTINCT spelling instead shares its left-associative equality level. -/
namespace SQLean.Tests
open Advanced RenderContract

private def queryOf (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr]}}
private def anon (n : Nat) : Advanced.Expr := .parameter (.anonymous n)
private def numbered (n : Nat) : Advanced.Expr := .parameter (.numbered n)
private def truth : Advanced.Expr := .literal (.bool true)
private def falsity : Advanced.Expr := .literal (.bool false)

example (left right : Advanced.Expr) (negated : Bool) :
    translateExpr (.distinctFrom left right negated) =
      .distinctFrom (translateExpr left) (translateExpr right) negated := by
  rw [translateExpr]

/-- Raw-NULL DISTINCT retains a different constructor from a row null test. -/
example : Advanced.Expr.distinctFrom (.row [.null, .null]) .null true ≠
    .isNull (.row [.null, .null]) false := by
  intro equality
  cases equality

private def witness : Advanced.Expr := .distinctFrom (anon 1) (anon 2) true

example : Admissible (queryOf witness) := by
  refine ⟨{depth := 5, parameters := [.anonymous 1, .anonymous 2]}, ?_, ?_, ?_⟩
  · unfold queryOf witness inspectQuery
    dsimp
    unfold inspectSelect
    dsimp
    unfold inspectItem inspectExpr
    unfold inspectExpr
    rfl
  · decide
  · decide

private def checkQuery (query : Advanced.Query) (parameters : List Parameter)
    (sqlite : Bool := true) : IO Nat := do
  let profiles := [RenderContract.Profile.identityV01, .postgres16V01] ++
    (if sqlite then [.sqliteV01] else [])
  for profile in profiles do
    let cert ← expectOk "NULL predicate renderer" ((RenderContract.check profile query).mapError reprStr)
    SQLean.Tests.assert (cert.footprint.parameters == parameters) "NULL predicate reordered parameters"
    let parsed ← expectOk cert.sql (parseRendered profile cert.sql)
    SQLean.Tests.assert (decide (parsed = expectedQuery profile query)) "NULL predicate changed raw operands or grouping"
    let again ← expectOk "NULL predicate canonical" ((RenderContract.check profile parsed).mapError reprStr)
    SQLean.Tests.assert (again.sql == cert.sql) "NULL predicate canonical SQL changed"
    for parameter in parameters do
      SQLean.Tests.assert (cert.transport reprStr (parameterSlot parameter) == reprStr parameter)
        "NULL predicate transport changed a binding"
  SQLean.Tests.assert (Advanced.queryParameters 256 query == parameters) "coarse NULL predicate traversal lost parameters"
  pure profiles.length

private def parsed (source : String) (expected : Advanced.Expr) : IO Nat := do
  let actual ← expectOk source (Advanced.parseExpression source)
  SQLean.Tests.assert (decide (actual = expected)) s!"NULL predicate AST mismatch: {source}"
  pure (1 + (← checkQuery (queryOf actual) (Advanced.expressionParameters 256 actual) false))

private def sqliteParsed (source : String) (expected : Advanced.Expr) : IO Nat := do
  let actual ← expectOk source (Advanced.parseSQLiteQuery ("SELECT " ++ source))
  SQLean.Tests.assert (decide (actual = queryOf expected)) s!"SQLite NULL predicate precedence mismatch: {source}"
  let cert ← expectOk source ((RenderContract.check .sqliteV01 actual).mapError reprStr)
  let roundtrip ← expectOk cert.sql (parseRendered .sqliteV01 cert.sql)
  SQLean.Tests.assert (decide (roundtrip = expectedQuery .sqliteV01 actual)) "SQLite NULL predicate roundtrip changed grouping"
  pure 2

private def rejected (profile : RenderContract.Profile) (expr : Advanced.Expr)
    (status code : String) (budget : Nat := 1024) : IO Unit := do
  match RenderContract.check profile (queryOf expr) budget with
  | .error failure =>
      SQLean.Tests.assert (failure.status == status && failure.diagnostic.code == code)
        s!"NULL predicate boundary mismatch: {reprStr failure}"
  | .ok _ => throw (IO.userError "NULL predicate unexpectedly admitted")

private def deep : Nat → Advanced.Expr
  | 0 => anon 1
  | n + 1 => .distinctFrom (deep n) .null

def nullPredicatesRenderingTests : IO Nat := do
  let mut count := 0
  for (source, expected) in [
      ("NULL ISNULL", Advanced.Expr.isNull .null),
      ("NULL NOTNULL", .isNull .null true),
      ("NULL IS NULL", .isNull .null),
      ("NULL IS NOT NULL", .isNull .null true),
      ("NULL IS DISTINCT FROM NULL", .distinctFrom .null .null),
      ("NULL IS NOT DISTINCT FROM NULL", .distinctFrom .null .null true),
      ("1 = 1 ISNULL", .isNull (.binary .eq 1 1)),
      ("1 = 1 IS NOT NULL", .isNull (.binary .eq 1 1) true),
      ("TRUE ISNULL = FALSE", .binary .eq (.isNull truth) falsity),
      ("TRUE = FALSE ISNULL", .isNull (.binary .eq truth falsity)),
      ("TRUE ISNULL = FALSE ISNULL", .isNull (.binary .eq (.isNull truth) falsity)),
      ("TRUE ISNULL ISNULL", .isNull (.isNull truth)),
      ("TRUE IS NULL NOTNULL", .isNull (.isNull truth) true),
      ("1 ISNULL IS DISTINCT FROM FALSE", .distinctFrom (.isNull 1) falsity),
      ("1 = 1 IS DISTINCT FROM TRUE", .distinctFrom (.binary .eq 1 1) truth),
      ("TRUE IS DISTINCT FROM 1 = 1", .distinctFrom truth (.binary .eq 1 1)),
      ("1 + 2 IS NOT DISTINCT FROM 3 * 4", .distinctFrom (.binary .add 1 2) (.binary .mul 3 4) true),
      ("NOT 1 = 2 ISNULL", .unary .not (.isNull (.binary .eq 1 2))),
      ("NOT 1 IS DISTINCT FROM 2", .unary .not (.distinctFrom 1 2)),
      ("1 IS DISTINCT FROM 2 AND TRUE", .binary .and (.distinctFrom 1 2) truth),
      ("TRUE OR 1 IS NOT DISTINCT FROM 2", .binary .or truth (.distinctFrom 1 2 true)),
      ("(1 IS DISTINCT FROM 2) ISNULL", .isNull (.distinctFrom 1 2)),
      ("1 IS DISTINCT FROM (2 ISNULL)", .distinctFrom 1 (.isNull 2)),
      ("1 ISNULL IN (1)", .inList (.isNull 1) [1]),
      ("1 IN (1) ISNULL", .isNull (.inList 1 [1])),
      ("ROW(NULL, NULL) IS NOT DISTINCT FROM NULL", .distinctFrom (.row [.null, .null]) .null true),
      ("ROW(NULL, NULL) ISNULL", .isNull (.row [.null, .null])),
      ("ROW() NOTNULL", .isNull (.row []) true),
      ("(1, NULL) IS DISTINCT FROM (2, NULL)", .distinctFrom (.row [1, .null]) (.row [2, .null])),
      ("? IS DISTINCT FROM ?", .distinctFrom (anon 1) (anon 2)),
      ("? IS NOT DISTINCT/*gap*/FROM ?", .distinctFrom (anon 1) (anon 2) true),
      ("? ISNULL AND ? NOTNULL", .binary .and (.isNull (anon 1)) (.isNull (anon 2) true)),
      ("isnull(?)", .call ["isnull"] [anon 1]),
      ("notnull(?)", .call ["notnull"] [anon 1]),
      ("\"isnull\"", .column none "isnull"),
      ("t.notnull", .column (some "t") "notnull")] do
    count := count + (← parsed source expected)
  -- These chains are rejected by the pinned PostgreSQL grammar, independently
  -- of whether a later type checker could give any intermediate result a type.
  for source in ["1 IS DISTINCT FROM 2 ISNULL", "1 IS DISTINCT FROM 2 IS NULL",
      "1 IS DISTINCT FROM 2 IS DISTINCT FROM 3", "1 = 2 = 3", "1 ISNULL = 2 = 3",
      "1 IS DISTINCT 2", "1 IS DISTINCT FROM", "1 NOT DISTINCT FROM 2",
      "1 IS NOTNULL", "1 NOT NULL", "1 IS NOT NOT NULL"] do
    expectError source (Advanced.parseExpression source)
    count := count + 1
  for (source, expected) in [
      ("1 IS DISTINCT FROM 0 = 0", Advanced.Expr.binary .eq (.distinctFrom 1 0) 0),
      ("1 = 1 IS DISTINCT FROM 0", .distinctFrom (.binary .eq 1 1) 0),
      ("1 IS DISTINCT FROM 2 ISNULL", .isNull (.distinctFrom 1 2)),
      ("1 IS DISTINCT FROM 2 IS NULL", .isNull (.distinctFrom 1 2)),
      ("1 IS DISTINCT FROM 2 IS DISTINCT FROM 1", .distinctFrom (.distinctFrom 1 2) 1),
      ("1 = 2 LIKE 0", .pattern (.binary .eq 1 2) 0),
      ("1 = 1 IN (1)", .inList (.binary .eq 1 1) [1]),
      ("1 LIKE 2 = 0", .binary .eq (.pattern 1 2) 0),
      ("1 BETWEEN 0 AND 2 = 1", .binary .eq (.between 1 0 2) 1),
      ("1 LIKE 2 BETWEEN 0 AND 3", .between (.pattern 1 2) 0 3),
      ("1 IS DISTINCT FROM 2 LIKE 0", .pattern (.distinctFrom 1 2) 0),
      ("1 LIKE 2 IS DISTINCT FROM 0", .distinctFrom (.pattern 1 2) 0),
      ("1 IS DISTINCT FROM 2 < 0", .distinctFrom 1 (.binary .lt 2 0)),
      ("1 IS NOT DISTINCT FROM 2 > 0", .distinctFrom 1 (.binary .gt 2 0) true),
      ("1 IS NULL || 0", .distinctFrom 1 (.concat .null 0) true),
      ("1 IS NOT NULL + 0", .distinctFrom 1 (.binary .add .null 0)),
      ("1 IS NULL <= 0", .distinctFrom 1 (.binary .le .null 0) true),
      ("2 IS TRUE", .distinctFrom 2 truth true),
      ("2 IS NOT FALSE", .distinctFrom 2 falsity),
      ("2 IS +TRUE", .distinctFrom 2 (.unary .pos truth) true),
      ("NULL ISNULL = FALSE", .binary .eq (.isNull .null) falsity),
      ("NULL IS NULL = FALSE", .binary .eq (.isNull .null) falsity),
      ("NOT 1 = 2 ISNULL", .unary .not (.isNull (.binary .eq 1 2)))] do
    count := count + (← sqliteParsed source expected)
  for negated in [false, true] do
    for (left, right, uses) in [
        (anon 1, anon 2, [.anonymous 1, .anonymous 2]),
        (numbered 3, numbered 1, [.numbered 3, .numbered 1]),
        (.coalesce [anon 1, anon 2], anon 3, [.anonymous 1, .anonymous 2, .anonymous 3]),
        (.null, .cast (anon 1) ⟨.int, []⟩, [.anonymous 1]),
        (.isNull (anon 1), .isNull (anon 2) true, [.anonymous 1, .anonymous 2])] do
      count := count + (← checkQuery (queryOf (.distinctFrom left right negated)) uses)
    for (left, right, uses) in [
        (.row [], .row [], []),
        (.row [anon 1, anon 2], .row [anon 3, anon 4],
          [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4]),
        (.row [anon 1, .null], .null, [.anonymous 1]),
        (.null, .row [.null, anon 1], [.anonymous 1])] do
      let expr := Advanced.Expr.distinctFrom left right negated
      count := count + (← checkQuery (queryOf expr) uses false)
      rejected .sqliteV01 expr "unsupported" "coverage.sqlite.row-distinct"
      count := count + 1
    for fields in [[], [.null], [anon 1, anon 2], [.row [.null], .null]] do
      let expr := Advanced.Expr.isNull (.row fields) negated
      count := count + (← checkQuery (queryOf expr) (Advanced.expressionParameters 256 expr) false)
      rejected .sqliteV01 expr "unsupported" "coverage.sqlite.row-null-test"
      count := count + 1
  let nested : Advanced.Expr := .distinctFrom (.scalarQuery (queryOf (anon 1))) (anon 2)
  count := count + (← checkQuery (queryOf nested) [.anonymous 1, .anonymous 2])
  let query ← expectOk "predicates in clauses" (Advanced.parseQuery
    "SELECT ? ISNULL AS v FROM users WHERE ? IS DISTINCT FROM ? ORDER BY ? NOTNULL")
  count := count + (← checkQuery query [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4])
  for bad in [.decimal "1;SELECT 2", .column none "", .literal (.text "x\x00y")] do
    for expr in [.distinctFrom bad 1, .distinctFrom 1 bad] do
      match RenderContract.check .identityV01 (queryOf expr) with
      | .error (.invalid _) => pure ()
      | result => throw (IO.userError s!"distinct operand escaped independent representation checks: {reprStr (result.map (·.sql))}")
      count := count + 1
  rejected .identityV01 (.distinctFrom (anon 2) (anon 1)) "invalid" "representation.parameters"
  rejected .identityV01 (.distinctFrom (anon 1) (numbered 1)) "unsupported" "coverage.mixed-parameters"
  count := count + 2
  for profile in [RenderContract.Profile.identityV01, .postgres16V01, .sqliteV01] do
    rejected profile (deep 12) "inconclusive" "resource.depth" 8
    count := count + 1
  -- Canonicalization must not rewrite raw-NULL distinctness into a NullTest.
  SQLean.Tests.assert ((Advanced.Expr.distinctFrom (.row [.null, .null]) .null true).toSql ==
    "(ROW(NULL, NULL) IS NOT DISTINCT FROM NULL)") "row distinctness was rewritten as row IS NULL"
  count := count + 1
  pure count

end SQLean.Tests
