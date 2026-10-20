import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support

/-! Array concatenation reuses the structural concat AST, while independent
typing distinguishes non-strict cat/append/prepend from scalar concatenation.
Parameter transport preserves those exact selected signatures and NULL rules. -/
namespace SQLean.Tests
open Advanced SelectContract RenderContract

private def anon (n : Nat) : Advanced.Expr := .parameter (.anonymous n)
private def numbered (n : Nat) : Advanced.Expr := .parameter (.numbered n)
private def queryOf (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr]}}

private def params : SelectContract.ParameterEnv :=
  [⟨1, ⟨.array .int, []⟩, true⟩, ⟨2, ⟨.array .bigInt, []⟩, true⟩,
    ⟨3, ⟨.int, []⟩, true⟩, ⟨4, ⟨.array .json, []⟩, false⟩,
    ⟨5, ⟨.json, []⟩, true⟩]

private theorem cat_valid :
    ExprValid params Scope.empty (.concat (anon 1) (anon 2))
      (some ⟨.array .int64, true⟩) [.anonymous 1, .anonymous 2] :=
  .arrayConcat (selected := ⟨.cat, [.array .int64, .array .int64], .array .int64⟩)
    (.parameter (binding := ⟨1, ⟨.array .int, []⟩, true⟩) (by simp [params]) rfl rfl)
    (.parameter (binding := ⟨2, ⟨.array .bigInt, []⟩, true⟩) (by simp [params]) rfl rfl)
    (by decide)

example : ExprValid params Scope.empty (.concat (numbered 1) (numbered 2))
    (some ⟨.array .int64, true⟩) [.numbered 1, .numbered 2] := by
  simpa [translateExpr, translateParameter, anon, numbered] using expr_valid_translated cat_valid

/-- A NULL array and NULL element still produce a non-NULL singleton array. -/
private theorem append_valid :
    ExprValid params Scope.empty (.concat (anon 1) (anon 3))
      (some ⟨.array .int32, false⟩) [.anonymous 1, .anonymous 3] :=
  .arrayConcat (selected := ⟨.append, [.array .int32, .int32], .array .int32⟩)
    (.parameter (binding := ⟨1, ⟨.array .int, []⟩, true⟩) (by simp [params]) rfl rfl)
    (.parameter (binding := ⟨3, ⟨.int, []⟩, true⟩) (by simp [params]) rfl rfl)
    (by decide)

example : ExprValid params Scope.empty (.concat (numbered 1) (numbered 3))
    (some ⟨.array .int32, false⟩) [.numbered 1, .numbered 3] := by
  simpa [translateExpr, translateParameter, anon, numbered] using expr_valid_translated append_valid

private theorem prepend_valid :
    ExprValid params Scope.empty (.concat (anon 3) (anon 1))
      (some ⟨.array .int32, false⟩) [.anonymous 3, .anonymous 1] :=
  .arrayConcat (selected := ⟨.prepend, [.int32, .array .int32], .array .int32⟩)
    (.parameter (binding := ⟨3, ⟨.int, []⟩, true⟩) (by simp [params]) rfl rfl)
    (.parameter (binding := ⟨1, ⟨.array .int, []⟩, true⟩) (by simp [params]) rfl rfl)
    (by decide)

example : ExprValid params Scope.empty (.concat (numbered 3) (numbered 1))
    (some ⟨.array .int32, false⟩) [.numbered 3, .numbered 1] := by
  simpa [translateExpr, translateParameter, anon, numbered] using expr_valid_translated prepend_valid

/-- JSON array append requires no equality operator on JSON elements. -/
private theorem json_append_valid :
    ExprValid params Scope.empty (.concat (anon 4) (anon 5))
      (some ⟨.array .json, false⟩) [.anonymous 4, .anonymous 5] :=
  .arrayConcat (selected := ⟨.append, [.array .json, .json], .array .json⟩)
    (.parameter (binding := ⟨4, ⟨.array .json, []⟩, false⟩) (by simp [params]) rfl rfl)
    (.parameter (binding := ⟨5, ⟨.json, []⟩, true⟩) (by simp [params]) rfl rfl)
    (by decide)

example : ExprValid params Scope.empty (.concat (numbered 4) (numbered 5))
    (some ⟨.array .json, false⟩) [.numbered 4, .numbered 5] := by
  simpa [translateExpr, translateParameter, anon, numbered] using expr_valid_translated json_append_valid

private def checkQuery (expr : Advanced.Expr) (parameters : List Parameter) : IO Nat := do
  let query := queryOf expr
  for profile in [Profile.identityV01, .postgres16V01] do
    let certificate ← expectOk "array concatenation" ((check profile query).mapError reprStr)
    SQLean.Tests.assert (certificate.footprint.parameters == parameters)
      "array concatenation lost or reordered parameter occurrences"
    let parsed ← expectOk certificate.sql (parseRendered profile certificate.sql)
    SQLean.Tests.assert (decide (parsed = expectedQuery profile query))
      "array concatenation changed operand direction, bounds or type modifiers"
    let again ← expectOk "array concatenation stability" ((check profile parsed).mapError reprStr)
    SQLean.Tests.assert (again.sql == certificate.sql) "array concatenation is not canonical"
    let environment : Parameter → String := fun p => reprStr p
    for parameter in parameters do
      SQLean.Tests.assert
        (certificate.transport environment (parameterSlot parameter) == environment parameter)
        "array concatenation binding value changed"
  match check .sqliteV01 query with
  | .ok _ => throw (IO.userError "explicit arrays unexpectedly entered SQLite rendering")
  | .error failure =>
      SQLean.Tests.assert (failure.status == "unsupported" &&
        (failure.diagnostic.code == "coverage.sqlite.array-type" ||
          failure.diagnostic.code == "coverage.sqlite.array-constructor"))
        s!"array concatenation SQLite classification changed: {reprStr failure}"
  pure 3

def arrayConcatenationRenderingTests : IO Nat := do
  let mut count := 0
  for type in [DataType.mk (.array .int) [], ⟨.array .numeric, [8, 2]⟩,
      ⟨.array .varchar, [3]⟩, ⟨.array .char, [3]⟩, ⟨.array .json, []⟩] do
    for (left, right, parameters) in [
        (.cast (anon 1) type, anon 2, [.anonymous 1, .anonymous 2]),
        (anon 1, .cast (anon 2) type, [.anonymous 1, .anonymous 2]),
        (.cast (numbered 2) type, .cast (numbered 1) type, [.numbered 2, .numbered 1]),
        (.cast (.null) type, .cast (.null) type, [])] do
      count := count + (← checkQuery (.concat left right) parameters)
  for (expr, parameters) in [
      (.concat (.array [anon 1, anon 2]) (.array [anon 3]), [.anonymous 1, .anonymous 2, .anonymous 3]),
      (.concat (.array [.array [anon 1, anon 2]]) (.array [anon 3, anon 4]),
        [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4]),
      (.concat (.concat (.array [anon 1]) (anon 2)) (anon 3),
        [.anonymous 1, .anonymous 2, .anonymous 3]),
      (.concat (anon 1) (.concat (anon 2) (.array [anon 3])),
        [.anonymous 1, .anonymous 2, .anonymous 3]),
      (.concat (.array [numbered 4]) (.array [numbered 2, numbered 4]),
        [.numbered 4, .numbered 2, .numbered 4])] do
    count := count + (← checkQuery expr parameters)
  pure count

end SQLean.Tests
