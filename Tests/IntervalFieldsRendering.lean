import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import SQLean.AdvancedCatalog
import Tests.Support

/-! Interval fields are part of exact declaration identity. A literal with a
postfix qualifier normalizes directly to its qualified cast; no unqualified
intermediate conversion is inserted. -/
namespace SQLean.Tests
open Advanced SelectContract RenderContract

private def anon (n : Nat) : Advanced.Expr := .parameter (.anonymous n)
private def numbered (n : Nat) : Advanced.Expr := .parameter (.numbered n)
private def text (value : String) : Advanced.Expr := .literal (.text value)
private def queryOf (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr]}}
private def declaration (fields : IntervalFields) (precision : List Nat := []) : DataType :=
  ⟨.intervalRange fields, precision⟩

example : Admissible (queryOf (.cast (anon 1) (declaration .dayToSecond [2]))) := by
  refine ⟨{depth := 5, parameters := [.anonymous 1]}, ?_, ?_, ?_⟩
  · unfold queryOf inspectQuery
    dsimp
    unfold inspectSelect
    dsimp
    unfold inspectItem inspectExpr
    unfold inspectExpr
    rfl
  · decide
  · decide

section StaticTransport
private def params : SelectContract.ParameterEnv :=
  [⟨1, ⟨.intervalRange .yearToMonth, []⟩, true⟩]

/-- Declared parameter typmods are metadata, not enforced PREPARE typmods.
An explicit cast restores the exact range and fractional precision. -/
private theorem qualified_valid :
    ExprValid params Scope.empty (.cast (anon 1) (declaration .dayToSecond [2]))
      (some ⟨.intervalRange .dayToSecond [2], true⟩) [.anonymous 1] :=
  .cast
    (.parameter (binding := ⟨1, ⟨.intervalRange .yearToMonth, []⟩, true⟩)
      (by simp [params]) rfl rfl)
    rfl (by decide) (by decide) (by trivial)

example :
    ExprValid params Scope.empty (.cast (numbered 1) (declaration .dayToSecond [2]))
      (some ⟨.intervalRange .dayToSecond [2], true⟩) [.numbered 1] := by
  simpa [translateExpr, translateParameter, anon, numbered] using
    expr_valid_translated qualified_valid

example (fields : IntervalFields) :
    concreteType (declaration fields) = some (.intervalRange fields []) := rfl

example (fields : IntervalFields) :
    concreteType ⟨.array (.array (.intervalRange fields)), []⟩ =
      some (.array (.intervalRange fields [])) := rfl
end StaticTransport

private def rejected (profile : RenderContract.Profile) (query : Advanced.Query)
    (status code : String) (budget : Nat := 1024) : IO Unit := do
  match RenderContract.check profile query budget with
  | .ok _ => throw (IO.userError s!"interval declaration unexpectedly accepted {status}/{code}")
  | .error failure =>
    SQLean.Tests.assert (failure.status == status && failure.diagnostic.code == code)
      s!"interval rendering classification: {reprStr failure}"

private def checkType (type : DataType) (sql : String) : IO Nat := do
  let parsedType ← expectOk sql (Advanced.parseDataType sql)
  SQLean.Tests.assert (parsedType == type) "interval type parser changed fields, precision or rank"
  SQLean.Tests.assert (type.toSql == sql) "interval declaration printer changed fields or precision"
  let expr := Advanced.Expr.cast (anon 1) type
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    let certificate ← expectOk sql ((RenderContract.check profile (queryOf expr)).mapError reprStr)
    SQLean.Tests.assert (certificate.footprint.parameters == [.anonymous 1])
      "interval type consumed or lost a parameter"
    let parsed ← expectOk certificate.sql (parseRendered profile certificate.sql)
    SQLean.Tests.assert (decide (parsed = expectedQuery profile (queryOf expr)))
      "interval field/precision/rank roundtrip changed"
    let again ← expectOk sql ((RenderContract.check profile parsed).mapError reprStr)
    SQLean.Tests.assert (again.sql == certificate.sql) "interval canonical spelling is unstable"
    let environment : Parameter → String := fun parameter => reprStr parameter
    SQLean.Tests.assert (certificate.transport environment 1 == environment (.anonymous 1))
      "interval cast changed the bound parameter"
  rejected .sqliteV01 (queryOf expr) "unsupported"
    (if type.name.isArray then "coverage.sqlite.array-type" else "coverage.sqlite.PostgreSQL-type")
  pure 5

def intervalFieldsRenderingTests : IO Nat := do
  let mut count := 0
  for fields in IntervalFields.all do
    let type := declaration fields
    let sql := "INTERVAL " ++ fields.toSql
    count := count + (← checkType type sql)
    for (source, expected) in [
        ("INTERVAL '1' " ++ fields.toSql, Advanced.Expr.cast (text "1") type),
        ("CAST('1' AS " ++ sql ++ ")", .cast (text "1") type),
        ("'1'::" ++ sql, .cast (text "1") type)] do
      let parsed ← expectOk source (Advanced.parseExpression source)
      SQLean.Tests.assert (decide (parsed = expected))
        "interval literal gained an unqualified intermediate cast"
      count := count + 1
    for rank in [1, 2] do
      let name := if rank == 1 then TypeName.array type.name else .array (.array type.name)
      let suffix := if rank == 1 then "[]" else "[][]"
      count := count + (← checkType ⟨name, []⟩ (sql ++ suffix))
    if fields.allowsPrecision then
      for precision in [0, 2, 6] do
        let type := declaration fields [precision]
        let sql := "INTERVAL " ++ fields.toSql ++ "(" ++ toString precision ++ ")"
        count := count + (← checkType type sql)
        count := count + (← checkType ⟨.array type.name, type.modifiers⟩ (sql ++ "[]"))
        let source := "INTERVAL '1.234' " ++ fields.toSql ++ "(" ++ toString precision ++ ")"
        let parsed ← expectOk source (Advanced.parseExpression source)
        SQLean.Tests.assert (decide (parsed = .cast (text "1.234") type))
          "interval literal precision moved to the wrong field"
        count := count + 1
    else
      rejected .identityV01 (queryOf (.cast (anon 1) (declaration fields [2])))
        "invalid" "representation.type-modifiers"
      count := count + 1
  for source in [
      "INTERVAL(2) '1' YEAR", "INTERVAL(2) '1' SECOND(3)",
      "CAST('1' AS INTERVAL(2) YEAR)", "CAST('1' AS INTERVAL(2) SECOND(3))",
      "INTERVAL YEAR '1'", "INTERVAL DAY TO SECOND(2) '1'",
      "INTERVAL '1' YEAR(2)", "INTERVAL '1' DAY(2)",
      "INTERVAL '1' YEAR TO SECOND", "INTERVAL '1' MONTH TO DAY",
      "INTERVAL '1' SECOND TO MINUTE", "INTERVAL '1' DAY TO YEAR",
      "INTERVAL '1' SECOND(2)(3)", "INTERVAL(2,3) '1'",
      "INTERVAL '1' SECOND(-1)", "INTERVAL '1' SECOND(?)",
      "INTERVAL(7) '1'",
      "INTERVAL '1' SECOND(1.5)", "INTERVAL '1' YEAR TO"] do
    expectError source (Advanced.parseExpression source)
    count := count + 1
  for source in [
      "SELECT (INTERVAL '1') YEAR", "SELECT (INTERVAL(2) '1') SECOND",
      "SELECT 1 YEAR", "SELECT INTERVAL(2) '1' MONTH"] do
    expectError source (Advanced.parseQuery source)
    count := count + 1
  for source in [
      "SELECT INTERVAL(2) '1' AS year", "SELECT INTERVAL '1' YEAR AS month",
      "SELECT INTERVAL '1' YEAR named", "SELECT 1 AS year", "SELECT year FROM t",
      "SELECT 1 FROM t year", "SELECT 1 \"year\""] do
    let _ ← expectOk source (Advanced.parseQuery source)
    count := count + 1
  let plain ← expectOk "old interval precision" (Advanced.parseExpression "INTERVAL(2) '1.234'")
  SQLean.Tests.assert (decide (plain = .cast (text "1.234") ⟨.interval, [2]⟩))
    "existing interval precision API changed"
  let converted ← expectOk "pretyped interval" (Advanced.parseExpression "(INTERVAL '1')::INTERVAL YEAR")
  SQLean.Tests.assert
    (decide (converted = .cast (.cast (text "1") ⟨.interval, []⟩) (declaration .year)))
    "pretyped interval conversion lost its distinct inner cast"
  let knownText ← expectOk "known TEXT interval input"
    (Advanced.parseExpression "CAST(CAST('90' AS TEXT) AS INTERVAL DAY)")
  let unknownText ← expectOk "unknown interval input"
    (Advanced.parseExpression "CAST('90' AS INTERVAL DAY)")
  SQLean.Tests.assert
    (decide (knownText = .cast (.cast (text "90") ⟨.text, []⟩) (declaration .day)))
    "known TEXT input lost its explicit inner conversion"
  SQLean.Tests.assert
    (decide (unknownText = .cast (text "90") (declaration .day)) &&
      decide (knownText ≠ unknownText))
    "unknown literal input was conflated with known TEXT input"
  for expr in [knownText, unknownText] do
    for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
      let certificate ← expectOk "interval input type roundtrip"
        ((RenderContract.check profile (queryOf expr)).mapError reprStr)
      let parsed ← expectOk certificate.sql (parseRendered profile certificate.sql)
      SQLean.Tests.assert (decide (parsed = expectedQuery profile (queryOf expr)))
        "rendering changed known versus unknown interval input"
      count := count + 1
  let declarations ← expectOk "interval parameter declarations"
    (Advanced.parseParameterDeclarations "INTERVAL YEAR?,INTERVAL DAY TO SECOND(3)[]")
  SQLean.Tests.assert (declarations ==
    [(declaration .year, true), (⟨.array (.intervalRange .dayToSecond), [3]⟩, false)])
    "interval parameter declarations lost exact range or nullable marker"
  let ddl := "CREATE TABLE intervals (a INTERVAL YEAR, b INTERVAL DAY TO SECOND(2)[])"
  let _ ← expectOk ddl (Advanced.parse ddl)
  count := count + 6
  for type in [
      declaration .year [2], declaration .dayToSecond [2, 3]] do
    rejected .postgres16V01 (queryOf (.cast (anon 1) type)) "invalid" "representation.type-modifiers"
    count := count + 1
  for fields in IntervalFields.all.filter IntervalFields.allowsPrecision do
    for precision in [7, 42] do
      let type := declaration fields [precision]
      let source := "INTERVAL '1' " ++ fields.toSql ++ "(" ++ toString precision ++ ")"
      let parsed ← expectOk source (Advanced.parseExpression source)
      SQLean.Tests.assert (decide (parsed = .cast (text "1") type))
        "out-of-profile interval precision must retain its exact parsed value"
      let parsedType ← expectOk type.toSql (Advanced.parseDataType type.toSql)
      SQLean.Tests.assert (parsedType == type) "type parser clamped interval precision"
      for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
        rejected profile (queryOf parsed) "unsupported" "coverage.interval-precision"
        rejected profile (queryOf (.cast (anon 1) ⟨.array type.name, type.modifiers⟩))
          "unsupported" "coverage.interval-precision"
      count := count + 6
  for expr in [
      Advanced.Expr.cast (.coalesce [anon 2, anon 1]) (declaration .year),
      .cast (anon 2) ⟨.array (.intervalRange .dayToSecond), [2]⟩] do
    rejected .identityV01 (queryOf expr) "invalid" "representation.parameters"
    count := count + 1
  let deep := (List.range 12).foldl (fun name _ => TypeName.array name) (.intervalRange .second)
  rejected .postgres16V01 (queryOf (.cast (anon 1) ⟨deep, [2]⟩)) "inconclusive" "resource.depth" 8
  pure (count + 1)

end SQLean.Tests
