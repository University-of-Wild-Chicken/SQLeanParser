import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import Tests.Support

/-! Row-lock representation and parameter-order witnesses. These checks assert
serialization and binding preservation; they do not resolve OF targets, prove
that rows can be locked, or establish transaction/concurrency behavior. -/
namespace SQLean.Tests
open Advanced

private def anon (n : Nat) : Advanced.Expr := .parameter (.anonymous n)
private def idExpr : Advanced.Expr := .column (some "t") "id"

private def base : Advanced.Query := {
  body := .select {
    items := [.expression idExpr]
    source := some (.table "items" (some "t"))
    whereClause := some (.binary .gt idExpr (anon 1)) }
  orderBy := [⟨idExpr, false, none⟩]
  limit := some (anon 2)
  offset := some (anon 3) }

private def scalar : Advanced.Query := {body := .select {items := [.expression 1]}}
private def lock : LockingClause := ⟨.update, [], .nowait⟩
private def locked : Advanced.Query := {scalar with locking := [lock]}

/-- A constructive representation witness needs neither parsing nor rendering. -/
example : RenderContract.Admissible locked := by
  refine ⟨{depth := 4}, ?_, ?_, ?_⟩
  · unfold locked scalar lock RenderContract.inspectQuery
    dsimp
    unfold RenderContract.inspectSelect
    dsimp
    unfold RenderContract.inspectItem RenderContract.inspectExpr
    rfl
  · decide
  · decide

example (query : Advanced.Query) :
    (RenderContract.translateParameters query).locking = query.locking :=
  RenderContract.translateParameters_locking query

example (query : Advanced.Query) :
    (RenderContract.translateParameters query).offsetFirst = query.offsetFirst :=
  RenderContract.translateParameters_offsetFirst query

private def checked (profile : RenderContract.Profile) (query : Advanced.Query)
    (parameters : List Parameter := [.anonymous 1, .anonymous 2, .anonymous 3]) : IO Unit := do
  let certificate ← match RenderContract.check profile query with
    | .ok certificate => pure certificate
    | .error failure => throw (IO.userError s!"locking roundtrip failed: {reprStr failure}")
  SQLean.Tests.assert (certificate.footprint.parameters == parameters) "locking changed parameter order"
  let parsed ← expectOk "locking full reparse" (RenderContract.parseRendered profile certificate.sql)
  SQLean.Tests.assert (decide (parsed = RenderContract.expectedQuery profile query))
    "locking roundtrip changed an AST field"
  SQLean.Tests.assert (parsed.locking == query.locking && parsed.offsetFirst == query.offsetFirst)
    "locking or pagination layout was lost"
  let again ← match RenderContract.check profile parsed with
    | .ok certificate => pure certificate
    | .error failure => throw (IO.userError s!"locking canonical recheck failed: {reprStr failure}")
  SQLean.Tests.assert (certificate.sql == again.sql) "locking canonical SQL changed on second render"
  let environment : Parameter → String
    | .anonymous n => s!"anonymous-{n}"
    | .numbered n => s!"numbered-{n}"
  for parameter in parameters do
    SQLean.Tests.assert
      (certificate.transport environment (RenderContract.parameterSlot parameter) == environment parameter)
      "locking changed logical parameter binding"

private def rejected (profile : RenderContract.Profile) (query : Advanced.Query)
    (status code : String) (maxDepth : Nat := 1024) : IO Unit := do
  match RenderContract.check profile query maxDepth with
  | .ok _ => throw (IO.userError s!"locking boundary accepted a rejected query: {code}")
  | .error failure =>
      SQLean.Tests.assert (failure.status == status && failure.diagnostic.code == code)
        s!"wrong locking boundary outcome: {reprStr failure}, expected {status}/{code}"

def lockingRenderingTests : IO Nat := do
  let mut count := 0
  for strength in [LockStrength.update, .noKeyUpdate, .share, .keyShare] do
    for waitPolicy in [LockWaitPolicy.block, .nowait, .skipLocked] do
      -- Duplicate and quoted targets are representable; target resolution is
      -- intentionally a separate static-validity obligation.
      for targets in [[], ["t"], ["t", "t"], ["select", "odd\"target"]] do
        let query := {base with locking := [⟨strength, targets, waitPolicy⟩]}
        for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
          checked profile query
          count := count + 1
        rejected .sqliteV01 query "unsupported" "coverage.sqlite.row-locking"
        count := count + 1
  let clauses : List LockingClause := [
    ⟨.update, ["t"], .nowait⟩, ⟨.keyShare, ["t"], .skipLocked⟩, ⟨.share, [], .block⟩]
  let offsetFirst := {base with offset := some (anon 2), limit := some (anon 3), offsetFirst := true}
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    checked profile {base with locking := clauses}
    checked profile offsetFirst
    checked profile {offsetFirst with locking := clauses}
    checked profile {locked with body := .set .union true scalar scalar} []
    rejected profile {base with locking := [⟨.update, [""], .block⟩]}
      "invalid" "representation.empty-name"
    rejected profile {base with locking := [⟨.update, ["bad\u0000name"], .block⟩]}
      "invalid" "representation.name-nul"
    rejected profile {base with locking := [⟨.update, [String.ofList (List.replicate 64 'a')], .block⟩]}
      "invalid" "representation.name-length"
    rejected profile {base with locking := [⟨.share, [String.ofList (List.replicate 32 'é')], .block⟩]}
      "invalid" "representation.name-length"
    rejected profile {base with offsetFirst := true, limit := none}
      "invalid" "representation.pagination-order"
    rejected profile {base with offsetFirst := true, offset := none}
      "invalid" "representation.pagination-order"
    rejected profile {offsetFirst with limit := some (anon 2), offset := some (anon 3)}
      "invalid" "representation.parameters"
    rejected profile {base with locking := [lock]} "inconclusive" "resource.depth" 0
    count := count + 12
  rejected .sqliteV01 offsetFirst "unsupported" "coverage.sqlite.OFFSET-first"
  count := count + 1
  let nested : List Advanced.Query := [
    {scalar with ctes := [⟨"c", locked, []⟩]},
    {body := .select {items := [.expression 1], source := some (.derived locked "d")}},
    {body := .select {items := [.expression (.scalarQuery locked)]}},
    {body := .select {items := [.expression (.exists locked)]}},
    {body := .select {items := [.expression (.inQuery 1 locked)]}},
    {scalar with limit := some (.scalarQuery locked)},
    {scalar with orderBy := [⟨.scalarQuery locked, false, none⟩]}]
  for query in nested do
    checked .postgres16V01 query []
    rejected .sqliteV01 query "unsupported" "coverage.sqlite.row-locking"
    count := count + 2
  rejected .sqliteV01 {body := .set .union true locked scalar}
    "unsupported" "coverage.sqlite.operand-local-clauses"
  count := count + 1
  let layoutSources := [
    "SELECT id FROM items FOR UPDATE OF items NOWAIT LIMIT ? OFFSET ?",
    "SELECT id FROM items OFFSET ? LIMIT ? FOR NO KEY UPDATE SKIP LOCKED",
    "SELECT id FROM items FOR SHARE OFFSET ? LIMIT ?",
    "SELECT id FROM items LIMIT ? OFFSET ? FOR KEY SHARE OF items",
    "SELECT id FROM items OFFSET ?"]
  for source in layoutSources do
    let query ← expectOk "locking source layout" (Advanced.parseQuery source)
    let expected := if source == "SELECT id FROM items OFFSET ?" then
      [.anonymous 1] else [.anonymous 1, .anonymous 2]
    checked .identityV01 query expected
    checked .postgres16V01 query expected
    count := count + 2
  for source in [
      "SELECT 1 FOR KEY UPDATE", "SELECT 1 FOR NO UPDATE", "SELECT 1 FOR UPDATE OF",
      "SELECT 1 FOR UPDATE OF t,", "SELECT 1 FOR UPDATE NOWAIT SKIP LOCKED",
      "SELECT 1 FOR UPDATE SKIP", "SELECT 1 OFFSET ? FOR UPDATE LIMIT ?",
      "SELECT 1 FOR UPDATE LIMIT ? FOR SHARE", "SELECT 1 LIMIT ? FOR UPDATE OFFSET ?"] do
    match Advanced.parseQuery source with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError s!"invalid locking syntax accepted: {source}")
    count := count + 1
  pure count

end SQLean.Tests
