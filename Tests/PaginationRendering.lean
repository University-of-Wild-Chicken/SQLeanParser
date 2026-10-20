import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import Tests.Support

/-! Hand-built pagination ASTs exercise the checked serialization boundary.
These are structural and binding witnesses, not database execution claims.
In particular, rendering NULL or a negative bound does not prove that the
selected database will execute it successfully. -/
namespace SQLean.Tests
open Advanced

private def scalar (expr : Advanced.Expr := .literal (.int 1)) : Advanced.Query :=
  {body := .select {items := [.expression expr]}}

private def anon (n : Nat) : Advanced.Expr := .parameter (.anonymous n)
private def numbered (n : Nat) : Advanced.Expr := .parameter (.numbered n)

private def deep : Nat → Advanced.Expr
  | 0 => .literal (.int 1)
  | n + 1 => .unary .pos (deep n)

private def anonymousBounds : Advanced.Query :=
  {scalar with limit := some (anon 1), offset := some (anon 2)}

/-- The independently specified domain is inhabited by parameters that occur
only in pagination; the proof does not call the parser or checked renderer. -/
example : RenderContract.Admissible anonymousBounds := by
  refine ⟨{depth := 4, parameters := [.anonymous 1, .anonymous 2]}, ?_, ?_, ?_⟩
  · unfold anonymousBounds scalar anon RenderContract.inspectQuery
    dsimp
    unfold RenderContract.inspectSelect
    dsimp
    unfold RenderContract.inspectItem RenderContract.inspectExpr
    rfl
  · decide
  · decide

private def positives : List (String × Advanced.Query × List Parameter) := [
  ("parameter only in LIMIT",
    {scalar with limit := some (numbered 1)}, [.numbered 1]),
  ("parameter only in OFFSET",
    {scalar with limit := some 10, offset := some (numbered 1)}, [.numbered 1]),
  ("same logical slot repeated across both bounds",
    {scalar with limit := some (.binary .add (numbered 2) (numbered 2)), offset := some (numbered 2)},
    [.numbered 2, .numbered 2, .numbered 2]),
  ("anonymous LIMIT then OFFSET", anonymousBounds, [.anonymous 1, .anonymous 2]),
  ("projection and ordering precede pagination",
    {scalar (anon 1) with
      orderBy := [⟨anon 2, false, none⟩]
      limit := some (.binary .add (anon 3) (anon 4))
      offset := some (anon 5)},
    [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4, .anonymous 5]),
  ("CTE and nested bound query preserve statement-wide parameter identity",
    {scalar (anon 2) with
      ctes := [⟨"c", scalar (anon 1), []⟩]
      limit := some (.binary .add (anon 3) (.scalarQuery (scalar (anon 4))))
      offset := some (anon 5)},
    [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4, .anonymous 5]),
  ("negative bound is serialized without execution-safety claim",
    {scalar with limit := some (.unary .neg 1)}, []),
  ("NULL bounds retain their AST constructors",
    {scalar with limit := some .null, offset := some .null}, []),
  ("unresolved bound name remains a serialization-only witness",
    {scalar with limit := some (.column none "missing")}, []),
  ("decimal token is retained exactly",
    {scalar with limit := some (.decimal "1.250e1")}, []),
  ("BIGINT cast and binding are retained",
    {scalar with limit := some (.cast (numbered 1) ⟨.bigInt, []⟩)}, [.numbered 1]),
  ("subtraction association in OFFSET",
    {scalar with
      limit := some 10
      offset := some (.binary .sub (numbered 1) (.binary .sub (numbered 2) 1))},
    [.numbered 1, .numbered 2])
]

private def checked (profile : RenderContract.Profile) (label : String)
    (query : Advanced.Query) (uses : List Parameter) : IO Unit := do
  let certificate ← match RenderContract.check profile query with
    | .ok certificate => pure certificate
    | .error failure => throw (IO.userError s!"pagination render rejected {label}: {reprStr failure}")
  SQLean.Tests.assert (certificate.footprint.parameters == uses)
    s!"pagination footprint lost or reordered a parameter: {label}"
  let reconstructed ← expectOk label (RenderContract.parseRendered profile certificate.sql)
  SQLean.Tests.assert (decide (reconstructed = RenderContract.expectedQuery profile query))
    s!"pagination render changed an AST field: {label}"
  let rerendered ← match RenderContract.check profile reconstructed with
    | .ok certificate => pure certificate
    | .error failure => throw (IO.userError s!"pagination rerender rejected {label}: {reprStr failure}")
  SQLean.Tests.assert (certificate.sql == rerendered.sql)
    s!"pagination canonical SQL is unstable: {label}"
  let environment : Parameter → String
    | .anonymous n => s!"anonymous-{n}"
    | .numbered n => s!"numbered-{n}"
  for parameter in uses do
    SQLean.Tests.assert
      (certificate.transport environment (RenderContract.parameterSlot parameter) == environment parameter)
      s!"pagination binding transport changed a logical value: {label}"

private def rejected (profile : RenderContract.Profile) (label : String)
    (query : Advanced.Query) (status code : String) (maxDepth : Nat := 1024) : IO Unit := do
  match RenderContract.check profile query maxDepth with
  | .ok _ => throw (IO.userError s!"pagination boundary accepted {label}")
  | .error failure =>
      SQLean.Tests.assert (failure.status == status && failure.diagnostic.code == code)
        s!"pagination boundary misclassified {label}: {reprStr failure}"

private def invalidRepresentations : List (String × Advanced.Query × String) := [
  ("injected numeric token only in LIMIT",
    {scalar with limit := some (.decimal "1; SELECT 99")}, "representation.numeric-token"),
  ("malformed numeric token only in OFFSET",
    {scalar with limit := some 1, offset := some (.decimal "1e+")}, "representation.numeric-token"),
  ("NUL text only in LIMIT",
    {scalar with limit := some (.literal (.text (String.singleton (Char.ofNat 0))))},
    "representation.text-nul"),
  ("empty bound column identifier",
    {scalar with limit := some 1, offset := some (.column none "")}, "representation.empty-name"),
  ("FILTER attached to a non-aggregate only in LIMIT",
    {scalar with limit := some (.filteredAggregate 1 (.literal (.bool true)))},
    "representation.filter"),
  ("zero parameter index only in LIMIT",
    {scalar with limit := some (numbered 0)}, "representation.parameters"),
  ("anonymous ordinal gap only in OFFSET",
    {scalar with limit := some 1, offset := some (anon 2)}, "representation.parameters"),
  ("same anonymous occurrence reused across bounds",
    {scalar with limit := some (anon 1), offset := some (anon 1)}, "representation.parameters")
]

def paginationRenderingTests : IO Nat := do
  let mut count := 0
  for profile in [RenderContract.Profile.identityV01, .postgres16V01, .sqliteV01] do
    for (label, query, uses) in positives do
      checked profile label query uses
      count := count + 1
    for (label, query, code) in invalidRepresentations do
      rejected profile label query "invalid" code
      count := count + 1
    rejected profile "mixed styles cross SELECT/LIMIT"
      {scalar (anon 1) with limit := some (numbered 1)}
      "unsupported" "coverage.mixed-parameters"
    rejected profile "mixed styles only in bounds"
      {scalar with limit := some (numbered 1), offset := some (anon 2)}
      "unsupported" "coverage.mixed-parameters"
    rejected profile "LIMIT expression alone exceeds budget"
      {scalar with limit := some (deep 80)} "inconclusive" "resource.depth" 16
    rejected profile "OFFSET expression alone exceeds budget"
      {scalar with limit := some 1, offset := some (deep 80)}
      "inconclusive" "resource.depth" 16
    checked profile "deep bound keeps every node" {scalar with limit := some (deep 80)} []
    count := count + 5
  let ilike : Advanced.Expr := .pattern (.literal (.text "a")) (.literal (.text "A")) true
  rejected .sqliteV01 "SQLite ILIKE hidden only in LIMIT"
    {scalar with limit := some (.cast ilike ⟨.int, []⟩)}
    "unsupported" "coverage.sqlite.ILIKE"
  let lateral : Advanced.Query := {
    body := .select {items := [.expression 1], source := some (.derived (scalar) "d" [] true)}}
  rejected .sqliteV01 "SQLite LATERAL hidden in OFFSET subquery"
    {scalar with limit := some 1, offset := some (.scalarQuery lateral)}
    "unsupported" "coverage.sqlite.LATERAL"
  rejected .postgres16V01 "PostgreSQL oversized slot only in LIMIT"
    {scalar with limit := some (numbered 65536)}
    "unsupported" "coverage.parameter-slot"
  rejected .sqliteV01 "SQLite oversized slot only in OFFSET"
    {scalar with limit := some 1, offset := some (numbered 32767)}
    "unsupported" "coverage.parameter-slot"
  checked .identityV01 "identity retains large pagination slot"
    {scalar with limit := some (numbered 65536)} [.numbered 65536]
  checked .postgres16V01 "PostgreSQL OFFSET without LIMIT retains the expression"
    {scalar with offset := some (.binary .add (numbered 1) 1)} [.numbered 1]
  rejected .sqliteV01 "SQLite OFFSET still requires LIMIT"
    {scalar with offset := some (numbered 1)}
    "unsupported" "coverage.sqlite.OFFSET-without-LIMIT"
  count := count + 7
  pure count

end SQLean.Tests
