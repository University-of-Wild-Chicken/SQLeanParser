import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import SQLean.RenderContract.ValidityPreservation
import Tests.Support

/-! Independent array representation witnesses and checked rendering regressions.
These establish AST/parameter transport, not runtime element coercion, shape
compatibility, or support for arrays in the SQLite rendering domain. -/
namespace SQLean.Tests
open Advanced

private def anon (n : Nat) : Advanced.Expr := .parameter (.anonymous n)
private def numbered (n : Nat) : Advanced.Expr := .parameter (.numbered n)
private def queryOf (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr]}}

private def nested : Advanced.Expr := .array [.array [anon 1], .array [anon 2]]

/-- List structure and occurrence order are retained for all finite arrays,
including empty arrays whose type needs surrounding context. -/
example (elements : List Advanced.Expr) :
    RenderContract.translateExpr (.array elements) =
      .array (elements.map RenderContract.translateExpr) := by
  simp only [RenderContract.translateExpr, List.attach_map_val]

example : RenderContract.checkSQLiteExpr (.array []) =
    .error (.unsupported ⟨"coverage.sqlite.array-constructor",
      "this SQLite rendering profile cannot preserve array-constructor without an AST rewrite"⟩) := by
  rw [RenderContract.checkSQLiteExpr]
  rfl

/-- No parser/checker result is used to inhabit the independent domain. -/
example : RenderContract.Admissible (queryOf nested) := by
  refine ⟨{depth := 6, parameters := [.anonymous 1, .anonymous 2]}, ?_, ?_, ?_⟩
  · unfold queryOf nested RenderContract.inspectQuery
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

private def params : SelectContract.ParameterEnv := [⟨1, ⟨.int, []⟩, true⟩]

private theorem parameter_valid :
    ExprValid params Scope.empty (anon 1) (some ⟨.int32, true⟩) [.anonymous 1] :=
  .parameter (binding := ⟨1, ⟨.int, []⟩, true⟩) (by simp [params]) rfl rfl

/-- An array object is non-NULL even when one of its elements may be NULL. -/
private theorem inferred_valid :
    ExprValid params Scope.empty (.array [anon 1, .null])
      (some ⟨.array .int32, false⟩) [.anonymous 1] :=
  .array (.cons parameter_valid (.cons .null .nil)) (by decide)

example : ExprValid params Scope.empty (translateExpr (.array [anon 1, .null]))
    (some ⟨.array .int32, false⟩) [.numbered 1] :=
  expr_valid_translated inferred_valid

private def contextual : Advanced.Expr :=
  .cast (.array [.array [], .array [anon 1, .null]]) ⟨.array .int, []⟩

/-- Context reaches a raw nested empty constructor; all original binding uses
are retained. This static witness makes no runtime rectangular-shape claim. -/
private theorem contextual_valid :
    ExprValid params Scope.empty contextual (some ⟨.array .int32, false⟩) [.anonymous 1] :=
  .castArray
    (.targeted
      (.nested (.targeted .nil (by decide))
        (.nested
          (.targeted
            (.ordinary (by decide) parameter_valid
              (.ordinary (by decide) .null .nil)) (by decide))
          .nil))
      (by decide))
    rfl (by decide)

example : ExprValid params Scope.empty (translateExpr contextual)
    (some ⟨.array .int32, false⟩) [.numbered 1] :=
  expr_valid_translated contextual_valid

example : outputName (translateExpr contextual) none = "array" := by
  rw [translated_output_name]
  rfl

end StaticTransport

private def rejected (profile : RenderContract.Profile) (query : Advanced.Query)
    (status code : String) (budget : Nat := 1024) : IO Unit := do
  match RenderContract.check profile query budget with
  | .ok _ => throw (IO.userError s!"array constructor unexpectedly accepted {status}/{code}")
  | .error failure =>
    SQLean.Tests.assert (failure.status == status && failure.diagnostic.code == code)
      s!"array constructor misclassified: {reprStr failure}"

private def checkQuery (query : Advanced.Query) (parameters : List Parameter) : IO Nat := do
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    let certificate ← expectOk "array constructor"
      ((RenderContract.check profile query).mapError reprStr)
    SQLean.Tests.assert (certificate.footprint.parameters == parameters)
      "array constructor traversal lost or reordered parameters"
    let parsed ← expectOk certificate.sql (RenderContract.parseRendered profile certificate.sql)
    SQLean.Tests.assert (decide (parsed = RenderContract.expectedQuery profile query))
      "array constructor roundtrip changed an AST field"
    let again ← expectOk "array canonical stability"
      ((RenderContract.check profile parsed).mapError reprStr)
    SQLean.Tests.assert (again.sql == certificate.sql)
      "array constructor canonical serialization changed"
    let environment : Parameter → String
      | .anonymous n => s!"anonymous-{n}" | .numbered n => s!"numbered-{n}"
    for parameter in parameters do
      SQLean.Tests.assert
        (certificate.transport environment (RenderContract.parameterSlot parameter) == environment parameter)
        "array constructor transport changed a binding value"
  rejected .sqliteV01 query "unsupported" "coverage.sqlite.array-constructor"
  pure 3

private def deep : Nat → Advanced.Expr
  | 0 => anon 1
  | n + 1 => .array [deep n]

def arrayConstructorRenderingTests : IO Nat := do
  let mut count := 0
  -- Empty, NULL, heterogeneous and ragged trees remain representable; static
  -- typing and runtime shape obligations are separate from rendering.
  for expr in [Advanced.Expr.array [], .array [.null], .array [1, 2],
      .array [.literal (.text "a,b"), .literal (.text "NULL"), .null],
      .array [.array [], .array [1]], .array [.array [1], .array [2, 3]],
      .array [.literal (.bool true), .literal (.text "'[x]'")]] do
    count := count + (← checkQuery (queryOf expr) [])
  for (expr, parameters) in [
      (Advanced.Expr.array [anon 1, anon 2], [.anonymous 1, .anonymous 2]),
      (nested, [.anonymous 1, .anonymous 2]),
      (.array [numbered 7, numbered 2, numbered 7], [.numbered 7, .numbered 2, .numbered 7]),
      (.array [.caseExpr none [(.literal (.bool true), anon 1)] (some (anon 2))],
        [.anonymous 1, .anonymous 2]),
      (.array [.scalarQuery (queryOf (anon 1)), anon 2], [.anonymous 1, .anonymous 2]),
      (.coalesce [.array [anon 1], .array [anon 2]], [.anonymous 1, .anonymous 2])] do
    count := count + (← checkQuery (queryOf expr) parameters)
  let placement : Advanced.Query := {
    body := .select {
      items := [.expression (.array [anon 1])]
      source := some (.derived (queryOf (.array [anon 2])) "d")
      whereClause := some (.isNull (.array [anon 3]) false) }
    orderBy := [⟨.array [anon 4], false, none⟩]
    limit := some (.array [anon 5])
    offset := some (.array [anon 6]) }
  count := count + (← checkQuery placement ((List.range 6).map fun n => .anonymous (n + 1)))
  -- Nested bracket shorthand has one explicit, stable AST representation.
  for (source, canonical) in [
      ("ARRAY[[?, ?], [?, ?]]", "ARRAY[ARRAY[?, ?], ARRAY[?, ?]]"),
      ("ARRAY[[], []]", "ARRAY[ARRAY[], ARRAY[]]"),
      ("ARRAY[ARRAY[?], ARRAY[?]]", "ARRAY[ARRAY[?], ARRAY[?]]")] do
    let actual ← expectOk source (Advanced.parseExpression source)
    let expected ← expectOk canonical (Advanced.parseExpression canonical)
    SQLean.Tests.assert (actual == expected && actual.toSql == canonical)
      s!"array shorthand normalization changed structure: {source}"
    count := count + 1
  for source in ["ARRAY[", "ARRAY[1,]", "ARRAY[,1]", "ARRAY[[1], 2]",
      "ARRAY[1, [2]]", "[1]", "ARRAY(SELECT 1)"] do
    expectError source (Advanced.parseExpression source)
    count := count + 1
  let malformed := queryOf (.array [.array [.decimal "not-a-number"]])
  for profile in [RenderContract.Profile.identityV01, .postgres16V01, .sqliteV01] do
    rejected profile malformed "invalid" "representation.numeric-token"
    count := count + 1
  rejected .postgres16V01 (queryOf (.array [anon 1, numbered 1]))
    "unsupported" "coverage.mixed-parameters"
  rejected .identityV01 (queryOf (.array [.array [anon 2]]))
    "invalid" "representation.parameters"
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    rejected profile (queryOf (deep 12)) "inconclusive" "resource.depth" 8
    count := count + 1
  pure (count + 2)

end SQLean.Tests
