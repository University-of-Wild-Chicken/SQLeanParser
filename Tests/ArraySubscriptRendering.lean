import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import SQLean.RenderContract.ValidityPreservation
import Tests.Support

/-! Bracket groups are structural: adjacent dimensions and nested subscripting
are different ASTs. These tests exercise serialization and parameter transport;
native array shape, bound conversion, and execution belong to separate evidence. -/
namespace SQLean.Tests
open Advanced

private def anon (n : Nat) : Advanced.Expr := .parameter (.anonymous n)
private def numbered (n : Nat) : Advanced.Expr := .parameter (.numbered n)
private def queryOf (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr]}}
private def sliced : Advanced.Expr :=
  .subscript (anon 1) [.slice (some (anon 2)) (some (anon 3)), .index (anon 4)]

example (base : Advanced.Expr) (subscripts : List Subscript) :
    RenderContract.translateExpr (.subscript base subscripts) =
      .subscript (RenderContract.translateExpr base)
        (subscripts.map RenderContract.translateSubscript) := by
  rw [RenderContract.translateExpr]
  simp only [List.attach_map_val]

/-- The independent domain has a kernel-checked witness that counts every bound
in lexical order, without parser or executable-checker acceptance as a premise. -/
example : RenderContract.Admissible (queryOf sliced) := by
  refine ⟨{depth := 6, parameters := [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4]},
    ?_, ?_, ?_⟩
  · unfold queryOf sliced RenderContract.inspectQuery
    dsimp
    unfold RenderContract.inspectSelect
    dsimp
    unfold RenderContract.inspectItem RenderContract.inspectExpr
    unfold RenderContract.inspectSubscript
    unfold RenderContract.inspectExpr
    rfl
  · decide
  · decide

section StaticTransport
open SelectContract RenderContract

private def params : SelectContract.ParameterEnv :=
  [⟨1, ⟨.numeric, [6, 2]⟩, false⟩, ⟨2, ⟨.int, []⟩, false⟩]
private def scope : Scope := .ofOutput "q" [{name := "a", type := ⟨.array (.varchar [5]), false⟩, collation := some .databaseDefault}]
private def base : Advanced.Expr := .column (some "q") "a"
private def bounds : List Subscript := [.slice none (some (anon 1)), .index (anon 2)]

private theorem base_valid :
    ExprValid params scope base (some ⟨.array (.varchar [5]), false⟩) [] :=
  .column (column := {name := "a", type := ⟨.array (.varchar [5]), false⟩, collation := some .databaseDefault}) (by decide)

private theorem bounds_valid :
    SubscriptsValid params scope bounds [.anonymous 1, .anonymous 2] :=
  .slice .absent
    (.present (.parameter (binding := ⟨1, ⟨.numeric, [6, 2]⟩, false⟩) (by simp [params]) rfl rfl))
    rfl rfl
    (.index (.parameter (binding := ⟨2, ⟨.int, []⟩, false⟩) (by simp [params]) rfl rfl) rfl .nil)

/-- Any slice keeps the exact array element modifiers. Neither a non-NULL
source nor numeric bounds prove that a value is in range. -/
private theorem slice_valid :
    ExprValid params scope (.subscript base bounds)
      (some ⟨.array (.varchar [5]), true⟩) [.anonymous 1, .anonymous 2] :=
  .subscript base_valid bounds_valid (by decide) (by decide)

example : ExprValid params scope (translateExpr (.subscript base bounds))
    (some ⟨.array (.varchar [5]), true⟩) [.numbered 1, .numbered 2] :=
  expr_valid_translated slice_valid

example : SubscriptsValid params scope (bounds.map translateSubscript) [.numbered 1, .numbered 2] :=
  subscripts_valid_translated bounds_valid

example : ExprValid params scope (.subscript base [.index .null])
    (some ⟨.varchar [5], true⟩) [] :=
  .subscript base_valid (.index .null rfl .nil) (by decide) (by decide)

end StaticTransport

private def rejected (profile : RenderContract.Profile) (query : Advanced.Query)
    (status code : String) (budget : Nat := 1024) : IO Unit := do
  match RenderContract.check profile query budget with
  | .ok _ => throw (IO.userError s!"subscript unexpectedly accepted {status}/{code}")
  | .error failure =>
    SQLean.Tests.assert (failure.status == status && failure.diagnostic.code == code)
      s!"subscript misclassified: {reprStr failure}"

private def checkQuery (query : Advanced.Query) (parameters : List Parameter) : IO Nat := do
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    let certificate ← expectOk "array subscript"
      ((RenderContract.check profile query).mapError reprStr)
    SQLean.Tests.assert (certificate.footprint.parameters == parameters)
      "subscripting lost or reordered base or bound parameters"
    let parsed ← expectOk certificate.sql (RenderContract.parseRendered profile certificate.sql)
    SQLean.Tests.assert (decide (parsed = RenderContract.expectedQuery profile query))
      "subscript roundtrip changed grouping or omitted bounds"
    let again ← expectOk "subscript canonical stability"
      ((RenderContract.check profile parsed).mapError reprStr)
    SQLean.Tests.assert (again.sql == certificate.sql) "subscript canonical SQL changed"
    let environment : Parameter → String
      | .anonymous n => s!"anonymous-{n}" | .numbered n => s!"numbered-{n}"
    for parameter in parameters do
      SQLean.Tests.assert
        (certificate.transport environment (RenderContract.parameterSlot parameter) == environment parameter)
        "subscript transport changed a binding value"
  rejected .sqliteV01 query "unsupported" "coverage.sqlite.array-subscripting"
  pure 3

private def deep : Nat → Advanced.Expr
  | 0 => anon 1
  | n + 1 => .subscript (deep n) [.slice none none]

def arraySubscriptRenderingTests : IO Nat := do
  let mut count := 0
  -- All omitted-bound combinations remain distinguishable from an index.
  for (suffix, expected, parameters) in [
      ([Subscript.index 1], "(?)[1]", [.anonymous 1]),
      ([.slice none none], "(?)[:]", [.anonymous 1]),
      ([.slice (some (anon 2)) none], "(?)[?:]", [.anonymous 1, .anonymous 2]),
      ([.slice none (some (anon 2))], "(?)[:?]", [.anonymous 1, .anonymous 2]),
      ([.slice (some (anon 2)) (some (anon 3))], "(?)[?:?]",
        [.anonymous 1, .anonymous 2, .anonymous 3]),
      ([.slice (some (anon 2)) (some (anon 3)), .index (anon 4)], "(?)[?:?][?]",
        [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4]),
      ([.index (anon 2), .slice (some (anon 3)) none], "(?)[?][?:]",
        [.anonymous 1, .anonymous 2, .anonymous 3])] do
    let expr := Advanced.Expr.subscript (anon 1) suffix
    count := count + (← checkQuery (queryOf expr) parameters)
    SQLean.Tests.assert (expr.toSql == expected) "subscript spelling changed bound identity"
    count := count + 1
  let grouped := Advanced.Expr.subscript (.column none "a") [.index 1, .index 2]
  let nested := Advanced.Expr.subscript (.subscript (.column none "a") [.index 1]) [.index 2]
  SQLean.Tests.assert (grouped.toSql == "(\"a\")[1][2]") "adjacent dimensions gained a nested base"
  SQLean.Tests.assert (nested.toSql == "((\"a\")[1])[2]") "nested index group was flattened"
  SQLean.Tests.assert (!(decide (grouped = nested))) "distinct bracket groups have equal ASTs"
  for expr in [grouped, nested] do
    count := count + (← checkQuery (queryOf expr) [])
  count := count + 3
  for (expr, parameters) in [
      (.subscript (numbered 7) [.slice (some (numbered 2)) (some (numbered 7))],
        [.numbered 7, .numbered 2, .numbered 7]),
      (.subscript (.array [anon 1, anon 2]) [.index (anon 3)],
        [.anonymous 1, .anonymous 2, .anonymous 3]),
      (.subscript (.cast (anon 1) ⟨.array .numeric, [6, 2]⟩) [.slice none (some (anon 2))],
        [.anonymous 1, .anonymous 2]),
      (.subscript (.coalesce [anon 1, anon 2]) [.index (anon 3)],
        [.anonymous 1, .anonymous 2, .anonymous 3]),
      (.subscript (.caseExpr none [(.literal (.bool true), anon 1)] (some (anon 2)))
        [.index (anon 3)], [.anonymous 1, .anonymous 2, .anonymous 3]),
      (.subscript (.scalarQuery (queryOf (.array [anon 1]))) [.index (anon 2)],
        [.anonymous 1, .anonymous 2]),
      (.subscript (anon 1) [.index (.subscript (anon 2) [.index (anon 3)])],
        [.anonymous 1, .anonymous 2, .anonymous 3]),
      (.subscript (.array [1]) (List.replicate 7 (.index 1)), [])] do
    count := count + (← checkQuery (queryOf expr) parameters)
  -- More than six dimensions are syntactically representable even though the
  -- independent PostgreSQL typing profile rejects its implementation limit.
  for (source, expected) in [
      ("a[1][2]", grouped), ("(a[1])[2]", nested),
      ("$1[:]", .subscript (numbered 1) [.slice none none]),
      ("(ARRAY[1])[1]", .subscript (.array [1]) [.index 1])] do
    let parsed ← expectOk source (Advanced.parseExpression source)
    SQLean.Tests.assert (decide (parsed = expected)) "parser changed contiguous bracket ownership"
    count := count + 1
  for source in ["(ARRAY[1])[]", "(ARRAY[1])[::]", "(ARRAY[1])[1,2]",
      "ARRAY[1][1]", "CAST(ARRAY[1] AS INTEGER[])[1]",
      "COALESCE(ARRAY[1], ARRAY[2])[1]", "'{1,2}'::INTEGER[][1]"] do
    expectError source (Advanced.parseExpression source)
    count := count + 1
  for profile in [RenderContract.Profile.identityV01, .postgres16V01, .sqliteV01] do
    rejected profile (queryOf (.subscript (anon 1) []))
      "invalid" "representation.empty-subscripts"
    count := count + 1
  rejected .postgres16V01 (queryOf (.subscript (anon 1) [.slice none (some (.decimal "bad"))]))
    "invalid" "representation.numeric-token"
  rejected .identityV01 (queryOf (.subscript (anon 1) [.index (anon 3)]))
    "invalid" "representation.parameters"
  rejected .postgres16V01 (queryOf (.subscript (anon 1) [.slice none (some (numbered 2))]))
    "unsupported" "coverage.mixed-parameters"
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    rejected profile (queryOf (deep 12)) "inconclusive" "resource.depth" 8
    count := count + 1
  pure (count + 3)

end SQLean.Tests
