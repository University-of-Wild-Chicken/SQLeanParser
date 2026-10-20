import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import SQLean.RenderContract.ValidityPreservation
import SQLean.AdvancedQueryValidation
import Tests.Support

/-! EXTRACT fields are decoded data, not SQL fragments or parameter slots.
This suite checks the special grammar, canonical quoting, occurrence transport,
and the distinct SQLite and exact-static-assurance boundaries. -/
namespace SQLean.Tests
open Advanced SelectContract RenderContract

private def anon (n : Nat) : Advanced.Expr := .parameter (.anonymous n)
private def numbered (n : Nat) : Advanced.Expr := .parameter (.numbered n)
private def col (name : String) : Advanced.Expr := .column none name
private def queryOf (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr]}}

example (field : String) (arg : Advanced.Expr) :
    translateExpr (.extract field arg) = .extract field (translateExpr arg) := by
  rw [translateExpr]

example : Admissible (queryOf (.extract "year" (anon 1))) := by
  refine ⟨{depth := 5, parameters := [.anonymous 1]}, ?_, ?_, ?_⟩
  · unfold queryOf inspectQuery
    dsimp
    unfold inspectSelect
    dsimp
    unfold inspectItem inspectExpr
    unfold inspectExpr
    have noNul : "year".contains '\x00' = false := by
      rw [String.contains_char_eq]
      decide
    simp only [List.attach_cons, List.attach_nil, List.map, noNul, Bool.false_eq_true, ↓reduceIte]
    rfl
  · decide
  · decide

section StaticTransport
private def params : SelectContract.ParameterEnv :=
  [⟨1, ⟨.date, []⟩, false⟩, ⟨2, ⟨.time, [3]⟩, false⟩]

/-- A date can be infinite, so even a nonnull declared argument conservatively
allows a NULL EXTRACT result. Field validation remains a runtime obligation. -/
private theorem date_valid (field : String) :
    ExprValid params Scope.empty (.extract field (anon 1))
      (some ⟨.numeric [], true⟩) [.anonymous 1] :=
  .extract (selected := ⟨[.text, .date], .numeric []⟩)
    (.parameter (binding := ⟨1, ⟨.date, []⟩, false⟩) (by simp [params]) rfl rfl)
    (by decide)

example (field : String) :
    ExprValid params Scope.empty (.extract field (numbered 1))
      (some ⟨.numeric [], true⟩) [.numbered 1] := by
  simpa [translateExpr, translateParameter, anon, numbered] using
    expr_valid_translated (date_valid field)

/-- TIME has no infinite values; the strict overload retains outer nullability. -/
private theorem time_valid :
    ExprValid params Scope.empty (.extract "second" (anon 2))
      (some ⟨.numeric [], false⟩) [.anonymous 2] :=
  .extract (selected := ⟨[.text, .time []], .numeric []⟩)
    (.parameter (binding := ⟨2, ⟨.time, [3]⟩, false⟩) (by simp [params]) rfl rfl)
    (by decide)

example :
    ExprValid params Scope.empty (.extract "second" (numbered 2))
      (some ⟨.numeric [], false⟩) [.numbered 2] := by
  simpa [translateExpr, translateParameter, anon, numbered] using expr_valid_translated time_valid

example (field : String) (arg : Advanced.Expr) :
    outputLabel (translateExpr (.cast (.extract field arg) ⟨.int, []⟩)) = (2, "extract") := by
  simp [translateExpr, outputLabel]
end StaticTransport

private def rejected (profile : RenderContract.Profile) (query : Advanced.Query)
    (status code : String) (budget : Nat := 1024) : IO Unit := do
  match RenderContract.check profile query budget with
  | .ok _ => throw (IO.userError s!"EXTRACT unexpectedly accepted {status}/{code}")
  | .error failure =>
    SQLean.Tests.assert (failure.status == status && failure.diagnostic.code == code)
      s!"EXTRACT classification: {reprStr failure}"

private def checkExpr (field : String) (arg : Advanced.Expr)
    (parameters : List Parameter) : IO Nat := do
  let expr := Advanced.Expr.extract field arg
  let query := queryOf expr
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    let certificate ← expectOk "EXTRACT" ((RenderContract.check profile query).mapError reprStr)
    SQLean.Tests.assert (certificate.footprint.parameters == parameters)
      "EXTRACT field or argument changed parameter order"
    let parsed ← expectOk certificate.sql (parseRendered profile certificate.sql)
    SQLean.Tests.assert (decide (parsed = expectedQuery profile query))
      "EXTRACT roundtrip changed decoded field or argument"
    let again ← expectOk "EXTRACT stability" ((RenderContract.check profile parsed).mapError reprStr)
    SQLean.Tests.assert (again.sql == certificate.sql) "EXTRACT canonical SQL changed"
    let environment : Parameter → String := fun p => reprStr p
    for parameter in parameters do
      SQLean.Tests.assert
        (certificate.transport environment (parameterSlot parameter) == environment parameter)
        "EXTRACT parameter value changed"
  SQLean.Tests.assert (Advanced.expressionParameters 128 expr == parameters)
    "coarse expression walker lost nested EXTRACT parameters"
  expectError "coarse tier requires exact temporal overloads" (Advanced.checkQuery [] [] query)
  rejected .sqliteV01 query "unsupported" "coverage.sqlite.extract"
  pure 5

private def deep : Nat → Advanced.Expr
  | 0 => anon 1
  | n + 1 => .extract "epoch" (deep n)

def extractRenderingTests : IO Nat := do
  let mut count := 0
  for field in ["year", "YEAR", "years", "", "not a unit", "x'y", "μ秒", "line\nbreak",
      "' FROM NULL); SELECT $99; -- ?", "\\backslash", String.ofList (List.replicate 80 'x')] do
    count := count + (← checkExpr field (anon 1) [.anonymous 1])
  for (arg, parameters) in [
      (Advanced.Expr.extract "month" (anon 1), [.anonymous 1]),
      (.coalesce [anon 1, anon 2], [.anonymous 1, .anonymous 2]),
      (.caseExpr none [(.isNull (anon 1), anon 2)] (some (anon 3)),
        [.anonymous 1, .anonymous 2, .anonymous 3]),
      (.binary .add (numbered 7) (numbered 2), [.numbered 7, .numbered 2]),
      (.coalesce [numbered 3, numbered 3], [.numbered 3, .numbered 3]),
      (.scalarQuery (queryOf (anon 1)), [.anonymous 1]),
      (.cast (anon 1) ⟨.timestampTZ, [3]⟩, [.anonymous 1])] do
    count := count + (← checkExpr "epoch" arg parameters)
  SQLean.Tests.assert ((Advanced.Expr.extract "x'y" (anon 1)).toSql ==
    "EXTRACT('x''y' FROM ?)") "EXTRACT canonical field quoting changed"
  count := count + 1
  for (source, field) in [
      ("year", "year"), ("YEAR", "year"), ("years", "years"), ("month", "month"),
      ("day", "day"), ("hour", "hour"), ("minute", "minute"), ("second", "second"),
      ("epoch", "epoch"), ("date", "date"), ("timezone_hour", "timezone_hour"),
      ("\"YEAR\"", "YEAR"), ("'YEAR'", "YEAR"), ("''", ""), ("\"x'y\"", "x'y"),
      ("'x''y'", "x'y"), ("'a /* ? */ $8'", "a /* ? */ $8")] do
    let sql := "EXTRACT(" ++ source ++ " FROM ?)"
    let parsed ← expectOk sql (Advanced.parseExpression sql)
    SQLean.Tests.assert (decide (parsed = .extract field (anon 1)))
      s!"EXTRACT field identity: {source}"
    count := count + 1
  let a := col "a"
  let b := col "b"
  let extracted := Advanced.Expr.extract "year" a
  for (source, expected) in [
      ("EXTRACT(year FROM a + b)", .extract "year" (.binary .add a b)),
      ("EXTRACT(year FROM (a))", extracted),
      ("EXTRACT(year FROM a) + b", .binary .add extracted b),
      ("EXTRACT(year FROM a)::BIGINT", .cast extracted ⟨.bigInt, []⟩),
      ("(EXTRACT(year FROM a))[1]", .subscript extracted [.index 1]),
      ("EXTRACT(year /* comment */ FROM a)", extracted),
      ("EXTRACT(year FROM (SELECT ?))", .extract "year" (.scalarQuery (queryOf (anon 1)))),
      ("extract", col "extract"), ("t.extract", .column (some "t") "extract"),
      ("\"extract\"('year', a)", .call ["extract"] [.literal (.text "year"), a]),
      ("pg_catalog.extract('year', a)", .call ["pg_catalog", "extract"] [.literal (.text "year"), a])] do
    let parsed ← expectOk source (Advanced.parseExpression source)
    SQLean.Tests.assert (decide (parsed = expected)) s!"EXTRACT grammar boundary: {source}"
    count := count + 1
  for source in [
      "EXTRACT()", "EXTRACT(FROM a)", "EXTRACT(year FROM)", "EXTRACT(year, a)",
      "EXTRACT(year FROM a, b)", "EXTRACT(year FROM a)[1]", "EXTRACT((year) FROM a)",
      "EXTRACT(1 FROM a)", "EXTRACT(? FROM a)", "EXTRACT($1 FROM a)",
      "EXTRACT(foo.bar FROM a)", "EXTRACT(time FROM a)", "EXTRACT(current_date FROM a)",
      "EXTRACT(extract FROM a)", "EXTRACT(select FROM a)", "EXTRACT(from FROM a)",
      "EXTRACT(\"\" FROM a)", "EXTRACT('ye' 'ar' FROM a)",
      "EXTRACT(" ++ String.ofList (List.replicate 64 'x') ++ " FROM a)",
      "EXTRACT(\"" ++ String.ofList (List.replicate 64 'x') ++ "\" FROM a)"] do
    expectError source (Advanced.parseExpression source)
    count := count + 1
  expectError "SQLite EXTRACT input" (Advanced.parseSQLiteQuery "SELECT EXTRACT(year FROM ?)")
  rejected .postgres16V01 (queryOf (.extract "x\x00y" (anon 1)))
    "invalid" "representation.extract-field-nul"
  rejected .postgres16V01 (queryOf (.extract "year" (.decimal "bad")))
    "invalid" "representation.numeric-token"
  rejected .postgres16V01 (queryOf (.extract "year" (.coalesce [anon 1, numbered 2])))
    "unsupported" "coverage.mixed-parameters"
  rejected .identityV01 (queryOf (.extract "year" (.coalesce [anon 2, anon 1])))
    "invalid" "representation.parameters"
  for profile in [RenderContract.Profile.identityV01, .postgres16V01, .sqliteV01] do
    rejected profile (queryOf (deep 12)) "inconclusive" "resource.depth" 8
    count := count + 1
  pure (count + 5)

end SQLean.Tests
