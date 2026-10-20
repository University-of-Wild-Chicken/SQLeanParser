import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import SQLean.AdvancedQueryValidation
import Tests.Support

/-! Representation witnesses for set trees, clause ownership, and lexical
bindings. These checks do not establish set-result typing or equivalence
between PostgreSQL and SQLite. SQLite intentionally retains a smaller domain. -/
namespace SQLean.Tests
open Advanced RenderContract

private def scalar (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr]}}

private def compound (op : SetOp) (all : Bool) (left right : Advanced.Query) : Advanced.Query :=
  {body := .set op all left right}

private def usesWitness : Advanced.Query :=
  compound .except true (scalar (.parameter (.anonymous 1))) (scalar (.parameter (.anonymous 2)))

private theorem inspectParameterQuery (index : Nat) :
    inspectQuery (scalar (.parameter (.anonymous index))) =
      .ok {depth := 4, parameters := [.anonymous index]} := by
  unfold scalar inspectQuery
  dsimp
  unfold inspectSelect
  dsimp
  unfold inspectItem inspectExpr
  rfl

/-- Both operands contribute once, in source order, before outer modifiers. -/
example : Admissible usesWitness := by
  refine ⟨{depth := 6, parameters := [.anonymous 1, .anonymous 2]}, ?_, ?_, ?_⟩
  · unfold usesWitness compound inspectQuery
    dsimp
    rw [inspectParameterQuery, inspectParameterQuery]
    rfl
  · decide
  · decide

private def operators : List (SetOp × Bool × String) :=
  [(.union, false, "UNION"), (.union, true, "UNION ALL"),
   (.intersect, false, "INTERSECT"), (.intersect, true, "INTERSECT ALL"),
   (.except, false, "EXCEPT"), (.except, true, "EXCEPT ALL")]

private def reconstruct (profile : RenderContract.Profile) (query : Advanced.Query)
    (uses : List Parameter := []) : IO Unit := do
  let certificate ← expectOk "set renderer" ((RenderContract.check profile query).mapError reprStr)
  let reparsed ← expectOk certificate.sql (parseRendered profile certificate.sql)
  SQLean.Tests.assert (decide (reparsed = expectedQuery profile query))
    "set renderer changed operator grouping or operand-local clauses"
  SQLean.Tests.assert (certificate.footprint.parameters == uses)
    "set renderer reordered or duplicated parameter occurrences"
  SQLean.Tests.assert (certificate.parameterMap.map (·.source) == uses.eraseDups)
    "set binding map changed source slots"
  let again ← expectOk certificate.sql ((RenderContract.check profile reparsed).mapError reprStr)
  SQLean.Tests.assert (again.sql == certificate.sql) "set canonical bytes changed"
  for parameter in uses do
    SQLean.Tests.assert
      (certificate.transport reprStr (parameterSlot parameter) == reprStr parameter)
      "set transport changed the value assigned to a driver slot"

private def boundary (query : Advanced.Query) (status code : String)
    (profile : RenderContract.Profile := .sqliteV01) (fuel : Nat := 1024) : IO Unit := do
  match RenderContract.check profile query fuel with
  | .ok _ => throw (IO.userError s!"unexpected set rendering success: {status}/{code}")
  | .error failure =>
      SQLean.Tests.assert (failure.status == status && failure.diagnostic.code == code)
        s!"set boundary changed: {reprStr failure}"

private def nested : Nat → Advanced.Query
  | 0 => scalar 1
  | n + 1 => compound .union true (scalar 1) (nested n)

def setOperationsRenderingTests : IO Nat := do
  let mut count := 0
  let a := scalar 1
  let b := scalar 2
  let c := scalar 3
  -- All 6 × 6 operator pairs, with both explicit associations and native PG
  -- precedence. Parentheses are significant even for the same operation.
  for (first, firstAll, firstSql) in operators do
    for (second, secondAll, secondSql) in operators do
      let left := compound second secondAll (compound first firstAll a b) c
      let right := compound first firstAll a (compound second secondAll b c)
      let precedenceTree := if second == .intersect && first != .intersect then right else left
      for (sql, expected) in [
          (s!"SELECT 1 {firstSql} SELECT 2 {secondSql} SELECT 3", precedenceTree),
          (s!"(SELECT 1 {firstSql} SELECT 2) {secondSql} SELECT 3", left),
          (s!"SELECT 1 {firstSql} (SELECT 2 {secondSql} SELECT 3)", right)] do
        let parsed ← expectOk sql (Advanced.parseQuery sql)
        SQLean.Tests.assert (parsed == expected) s!"PostgreSQL set precedence changed: {sql}"
        for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
          reconstruct profile parsed
          count := count + 1
  let portable := operators.filter (fun (op, all, _) => !all || op == .union)
  for (first, firstAll, firstSql) in portable do
    for (second, secondAll, secondSql) in portable do
      let sql := s!"SELECT 1 {firstSql} SELECT 2 {secondSql} SELECT 3"
      let parsed ← expectOk sql (Advanced.parseSQLiteQuery sql)
      SQLean.Tests.assert (parsed == compound second secondAll (compound first firstAll a b) c)
        "SQLite compound operators must associate left at one level"
      reconstruct .sqliteV01 parsed
      count := count + 1
  for sql in [
      "(SELECT 1 AS x ORDER BY 1 LIMIT 1) UNION ALL (SELECT 2 AS y ORDER BY 1 LIMIT 1) ORDER BY x LIMIT 2 OFFSET 0",
      "WITH c AS (SELECT 1 AS v) SELECT v AS x FROM c UNION ALL SELECT v AS y FROM c",
      "(WITH c AS (SELECT 1 AS v) SELECT v FROM c) UNION ALL (WITH c AS (SELECT 2 AS v) SELECT v FROM c)",
      "WITH a AS (SELECT 1 AS v) (WITH b AS (SELECT v FROM a) SELECT v FROM b) UNION ALL SELECT v FROM a",
      "SELECT 1 EXCEPT (SELECT 2 UNION ALL (SELECT 3 ORDER BY 1 LIMIT 1))",
      "SELECT 1 UNION ALL (WITH c AS (SELECT 2 AS v UNION ALL SELECT 3) SELECT v FROM c ORDER BY v LIMIT 1)",
      "WITH c AS (SELECT 1 AS v UNION ALL SELECT 2 ORDER BY v LIMIT 1) SELECT v FROM c",
      "(SELECT NULL ORDER BY 1) UNION ALL SELECT 1",
      "(SELECT NULL LIMIT 1) UNION ALL SELECT 1",
      "SELECT NULL UNION ALL (SELECT NULL UNION ALL SELECT 1)",
      "(SELECT NULL UNION ALL SELECT NULL) UNION ALL SELECT 1",
      "(SELECT id FROM t FOR UPDATE) UNION SELECT id FROM u",
      "SELECT id FROM t UNION (SELECT id FROM u FOR UPDATE)",
      "SELECT id FROM t UNION SELECT id FROM u FOR UPDATE"] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
      reconstruct profile query
      count := count + 1
  -- Modifier placement and deferred unknown-type resolution are distinct
  -- represented trees, even when a particular query is semantically invalid.
  let withLocalClauses ← expectOk "operand modifiers" (Advanced.parseQuery
    "(SELECT 1 ORDER BY 1 LIMIT 2) UNION ALL SELECT 3 ORDER BY 1 LIMIT 4")
  match withLocalClauses.body with
  | .set .union true left right =>
      SQLean.Tests.assert (left.limit == some 2 && withLocalClauses.limit == some 4 &&
        left.orderBy.length == 1 && withLocalClauses.orderBy.length == 1 && right.limit.isNone)
        "arm and enclosing modifiers were merged"
  | _ => throw (IO.userError "operand-local query boundary missing")
  count := count + 1
  for (sql, uses) in [
      ("SELECT ? UNION ALL SELECT ?", [.anonymous 1, .anonymous 2]),
      ("(SELECT ? OFFSET ? LIMIT ?) EXCEPT ALL (SELECT ? LIMIT ? OFFSET ?) ORDER BY ? OFFSET ? LIMIT ?",
        (List.range 9).map (fun n => Parameter.anonymous (n + 1))),
      ("WITH outer_cte AS (SELECT ?) (WITH left_cte AS (SELECT ?) SELECT ? FROM left_cte) UNION ALL (WITH right_cte AS (SELECT ?) SELECT ? FROM right_cte) LIMIT ?",
        (List.range 6).map (fun n => Parameter.anonymous (n + 1))),
      ("SELECT $3 UNION ALL (SELECT $1 EXCEPT ALL SELECT $3) LIMIT $2",
        [.numbered 3, .numbered 1, .numbered 3, .numbered 2])] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    SQLean.Tests.assert (Advanced.queryParameters 1024 query == uses)
      "expanded set walker changed source parameter order"
    for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
      reconstruct profile query uses
      count := count + 1
  for op in [SetOp.intersect, .except] do
    boundary (compound op true a b) "unsupported" "coverage.sqlite.INTERSECT-or-EXCEPT-ALL"
    count := count + 1
  for op in [SetOp.union, .intersect, .except] do
    boundary (compound op false a (compound .union false b c))
      "unsupported" "coverage.sqlite.right-nested-compound"
    count := count + 1
  for modified in [
      {a with orderBy := [⟨1, false, none⟩]},
      {a with limit := some 1},
      {a with limit := some 1, offset := some 0},
      {a with ctes := [⟨"c", b, []⟩]}] do
    for query in [compound .union true modified b, compound .union true a modified] do
      boundary query "unsupported" "coverage.sqlite.operand-local-clauses"
      count := count + 1
  boundary (compound .union true {body := .select {items := []}} b)
    "invalid" "representation.select-list" .identityV01
  boundary (compound .union true (scalar (.parameter (.anonymous 2)))
    (scalar (.parameter (.anonymous 1)))) "invalid" "representation.parameters" .identityV01
  boundary (compound .union true (scalar (.parameter (.anonymous 1)))
    (scalar (.parameter (.numbered 2)))) "unsupported" "coverage.mixed-parameters" .postgres16V01
  boundary (nested 12) "inconclusive" "resource.depth" .identityV01 8
  count := count + 4
  -- PostgreSQL 16 accepts these wrapper merges; the current typed input
  -- parser deliberately leaves them as explicit coverage gaps. This is not
  -- evidence that they are invalid native SQL.
  for sql in ["(SELECT 1 ORDER BY 1) LIMIT 1",
      "((SELECT 1 UNION SELECT 2) ORDER BY 1) LIMIT 1",
      "(SELECT 1 LIMIT 1) OFFSET 1", "(SELECT 1 OFFSET 1) LIMIT 1"] do
    expectError "documented wrapper coverage gap" (Advanced.parseQuery sql)
    count := count + 1
  pure count

end SQLean.Tests
