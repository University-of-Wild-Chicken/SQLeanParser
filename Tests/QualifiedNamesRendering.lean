import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import SQLean.RenderContract.ValidityPreservation
import SQLean.AdvancedQueryValidation
import Tests.Support

/-! Schema/name components are independent identifiers. Parameter transport
preserves these components, aliases, and the original source ordering. SQLite's
attached-database namespace is deliberately outside this PostgreSQL increment. -/
namespace SQLean.Tests
open Advanced RenderContract

private def qualifiedQuery : Advanced.Query :=
  {body := .select {
    items := [.expression (.column (some "t") "id" (some "s")),
      .expression (.parameter (.anonymous 1))]
    source := some (.table "t" none [] (some "s"))
    whereClause := some (.binary .eq (.column (some "t") "id" (some "s"))
      (.parameter (.anonymous 2)))}}

example (qualifier schema : Option Name) (name : Name) :
    translateExpr (.column qualifier name schema) = .column qualifier name schema := by
  simp only [translateExpr]

example (name : Name) (alias schema : Option Name) (columns : List Name) :
    translateSource (.table name alias columns schema) = .table name alias columns schema := by
  simp only [translateSource]

example : Admissible qualifiedQuery := by
  have ht : checkName "t" = .ok () := by
    have hs : "t".utf8ByteSize = 1 := by decide
    simp [checkName, hs]
    rfl
  have hs : checkName "s" = .ok () := by
    have hs : "s".utf8ByteSize = 1 := by decide
    simp [checkName, hs]
    rfl
  have hi : checkName "id" = .ok () := by
    have hs : "id".utf8ByteSize = 2 := by decide
    simp [checkName, hs]
    rfl
  have hc : inspectExpr (.column (some "t") "id" (some "s")) = .ok {} := by
    rw [inspectExpr]
    change (do (do checkName "t"; checkName "s"; pure PUnit.unit); checkName "id"; pure ({} : Footprint)) = .ok {}
    rw [ht, hs, hi]
    rfl
  have hf : inspectSource (.table "t" none [] (some "s")) = .ok {} := by
    rw [inspectSource]
    change (do checkName "t"; checkName "s"; pure (); pure PUnit.unit; pure ({} : Footprint)) = .ok {}
    rw [ht, hs]
    rfl
  refine ⟨{depth := 4, parameters := [.anonymous 1, .anonymous 2]}, ?_, ?_, ?_⟩
  · unfold qualifiedQuery inspectQuery
    dsimp
    unfold inspectSelect
    dsimp
    simp only [List.attach_map_val, List.map_cons, List.map_nil, List.append_nil, List.nil_append]
    unfold inspectItem
    simp only [hc, hf]
    unfold inspectExpr
    simp only [hc]
    unfold inspectExpr
    rfl
  · decide
  · decide

section StaticTransport
open SelectContract

private def baseTable : CatalogTable := {
  name := "t", schema := some "s", exposeUnqualified := false,
  columns := [{name := "id", type := ⟨.int, []⟩, nullable := some false}] }
private def row : List OutputColumn := [⟨"id", ⟨.int32, false⟩⟩]
private def baseScope : SelectContract.Scope := .ofTable baseTable.identity none row
private def source : Advanced.From := .table "t" none [] (some "s")

private theorem source_valid :
    SourceValid .basicV26 [baseTable] [] (some source) baseScope [] :=
  .table (table := baseTable) (by simp) rfl (by simp) (.cons rfl .nil)

example : SourceValid .basicV26 [baseTable] [] (some (translateSource source)) baseScope [] :=
  source_valid_translated source_valid

private theorem column_valid :
    ExprValid [] baseScope (.column (some "t") "id" (some "s"))
      (some ⟨.int32, false⟩) [] :=
  .column (column := ⟨"id", ⟨.int32, false⟩⟩) (by decide)

example : ExprValid [] baseScope
    (translateExpr (.column (some "t") "id" (some "s"))) (some ⟨.int32, false⟩) [] :=
  expr_valid_translated column_valid

/-- An explicit alias hides the schema path even if it repeats the basename. -/
example : ¬ Resolves (SelectContract.Scope.ofTable baseTable.identity (some "t") row)
    (some "t") "id" ⟨"id", ⟨.int32, false⟩⟩ (some "s") := by decide

/-- Lookup selects a namespace before a column, so disjoint column lists do
not make a repeated unqualified relation name unambiguous. -/
private def otherScope : SelectContract.Scope :=
  .ofTable ⟨some "other", "t"⟩ none [⟨"different", ⟨.text, false⟩⟩]
example : JoinAliasesDistinct baseScope otherScope := by decide
example : ¬ Resolves (baseScope ++ otherScope) (some "t") "id"
    ⟨"id", ⟨.int32, false⟩⟩ := by decide
example : Resolves (baseScope ++ otherScope) (some "t") "id"
    ⟨"id", ⟨.int32, false⟩⟩ (some "s") := by decide
end StaticTransport

private def rejected (profile : RenderContract.Profile) (query : Advanced.Query)
    (status code : String) (budget : Nat := 1024) : IO Unit := do
  match RenderContract.check profile query budget with
  | .ok _ => throw (IO.userError s!"qualified-name boundary unexpectedly accepted {status}/{code}")
  | .error failure =>
      SQLean.Tests.assert (failure.status == status && failure.diagnostic.code == code)
        s!"qualified-name classification: {reprStr failure}"

private def checkRoundTrip (sql : String) (parameters : List Parameter := []) : IO Nat := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    let certificate ← expectOk sql ((RenderContract.check profile query).mapError reprStr)
    SQLean.Tests.assert (certificate.footprint.parameters == parameters)
      "qualified-name traversal changed parameter order"
    let parsed ← expectOk certificate.sql (parseRendered profile certificate.sql)
    SQLean.Tests.assert (decide (parsed = expectedQuery profile query))
      "qualified-name roundtrip changed component boundaries"
    let again ← expectOk certificate.sql ((RenderContract.check profile parsed).mapError reprStr)
    SQLean.Tests.assert (again.sql == certificate.sql) "qualified-name canonical SQL changed"
    let environment : Parameter → String := fun parameter => reprStr parameter
    for parameter in parameters do
      SQLean.Tests.assert
        (certificate.transport environment (parameterSlot parameter) == environment parameter)
        "qualified-name query changed parameter bindings"
  SQLean.Tests.assert (Advanced.queryParameters 256 query == parameters)
    "coarse query walker lost qualified-query parameters"
  rejected .sqliteV01 query "unsupported"
    (if query.locking.isEmpty then "coverage.sqlite.schema-qualification" else "coverage.sqlite.row-locking")
  pure 4

def qualifiedNamesRenderingTests : IO Nat := do
  let mut count := 0
  for (sql, expected) in [
      ("s.t.c", Advanced.Expr.column (some "t") "c" (some "s")),
      ("s /* comment */ . t . c", .column (some "t") "c" (some "s")),
      ("s.select.from", .column (some "select") "from" (some "s")),
      ("t.select", .column (some "t") "select"),
      ("sum.t.c", .column (some "t") "c" (some "sum")),
      ("count.t.c", .column (some "t") "c" (some "count")),
      ("\"s.t\".\"c.d\"", .column (some "s.t") "c.d"),
      ("\"s.t\".\"u.v\".\"c.d\"", .column (some "u.v") "c.d" (some "s.t")),
      ("\"x\"\"y\".t.\"z\"\"w\"", .column (some "t") "z\"w" (some "x\"y")),
      ("S.T.C", .column (some "t") "c" (some "s")),
      ("s.t.c[?]", .subscript (.column (some "t") "c" (some "s"))
        [.index (.parameter (.anonymous 1))]),
      ("s.t.c::TEXT", .cast (.column (some "t") "c" (some "s")) ⟨.text, []⟩),
      ("s.select(?)", .call ["s", "select"] [.parameter (.anonymous 1)])] do
    let parsed ← expectOk sql (Advanced.parseExpression sql)
    SQLean.Tests.assert (decide (parsed = expected)) s!"qualified expression parser: {sql}"
    count := count + 1
  for sql in [
      "SELECT s.t.id FROM s.t",
      "SELECT s.t.* FROM s.t",
      "SELECT t.* FROM s.t",
      "SELECT * FROM s.t",
      "SELECT x.id FROM s.t AS x",
      "SELECT x.renamed, x.other FROM s.t AS x(renamed)",
      "SELECT x.key, x.name FROM s.t AS x(key)",
      "SELECT s.select.from FROM s.select",
      "SELECT s.select.* FROM s.select",
      "SELECT \"s.dot\".\"t.dot\".\"c.dot\" FROM \"s.dot\".\"t.dot\"",
      "SELECT \"s.dot\".\"t.dot\".* FROM \"s.dot\".\"t.dot\"",
      "SELECT \"x.y\".id FROM s.t AS \"x.y\"",
      "SELECT s.t.id FROM s.t FOR UPDATE OF t",
      "SELECT x.id FROM s.t AS x FOR NO KEY UPDATE OF x NOWAIT",
      "SELECT a.t.id, b.t.id FROM a.t INNER JOIN b.t ON a.t.id = b.t.id",
      "SELECT a.t.*, b.t.* FROM a.t FULL JOIN b.t USING (id)",
      "SELECT a.t.* FROM a.t NATURAL LEFT JOIN b.t",
      "SELECT d.id FROM (SELECT s.t.id FROM s.t) AS d",
      "WITH t AS (SELECT 1 AS id) SELECT s.t.id FROM s.t",
      "SELECT EXISTS (SELECT s.t.id FROM s.t)",
      "SELECT s.t.id FROM s.t UNION SELECT u.id FROM x.u",
      "SELECT COUNT(s.t.id) FROM s.t GROUP BY s.t.other ORDER BY s.t.other",
      "SELECT s.t.id FROM s.t WHERE s.t.id IN (SELECT x.u.id FROM x.u)",
      "SELECT s.t.id FROM s.t ORDER BY s.t.id NULLS LAST LIMIT 2"] do
    count := count + (← checkRoundTrip sql)
  count := count + (← checkRoundTrip
    "SELECT ?, s.t.id FROM s.t WHERE s.t.id = ? ORDER BY ? LIMIT ? OFFSET ?"
    [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4, .anonymous 5])
  count := count + (← checkRoundTrip
    "WITH q AS (SELECT $3 AS id) SELECT $2, s.t.id FROM s.t WHERE s.t.id = $2"
    [.numbered 3, .numbered 2, .numbered 2])
  count := count + (← checkRoundTrip
    "SELECT ? FROM (SELECT ? AS id FROM s.t) AS x WHERE x.id = ?"
    [.anonymous 1, .anonymous 2, .anonymous 3])
  for sql in [
      "SELECT db.s.t.c FROM s.t", "SELECT * FROM db.s.t",
      "SELECT db.s.t.* FROM s.t", "SELECT s.*.* FROM s.t",
      "SELECT s..c FROM s.t", "SELECT s.t. FROM s.t",
      "SELECT select.t.c FROM s.t", "SELECT * FROM s.t.u.v",
      "SELECT authorization.t.c FROM s.t", "SELECT authorization.t.* FROM s.t",
      "SELECT * FROM authorization.t",
      "SELECT * FROM s.*", "SELECT * FROM s.t FOR UPDATE OF s.t"] do
    expectError sql (Advanced.parseQuery sql)
    count := count + 1
  let invalidColumn : Advanced.Query :=
    {body := .select {items := [.expression (.column none "id" (some "s"))]}}
  let invalidStar : Advanced.Query :=
    {body := .select {items := [.all none (some "s")]}}
  for query in [invalidColumn, invalidStar] do
    rejected .identityV01 query "invalid" "representation.schema-qualifier"
    count := count + 1
  for (schema, code) in [
      ("", "representation.empty-name"), ("s\x00x", "representation.name-nul"),
      (String.ofList (List.replicate 64 's'), "representation.name-length")] do
    let query : Advanced.Query :=
      {body := .select {items := [.all], source := some (.table "t" none [] (some schema))}}
    rejected .postgres16V01 query "invalid" code
    count := count + 1
  for sql in [
      "SELECT \"t.dot\".\"id\" FROM \"t.dot\"",
      "SELECT \"t.dot\".* FROM \"t.dot\"",
      "SELECT \"a.b\".id FROM \"t.dot\" AS \"a.b\""] do
    let query ← expectOk sql (Advanced.parseSQLiteQuery sql)
    let _ ← expectOk sql ((RenderContract.check .sqliteV01 query).mapError reprStr)
    count := count + 1
  let names := [String.ofList (List.replicate 63 's'), "x\"; SELECT ?; --", "s.dot", "模式"]
  for schema in names do
    let query : Advanced.Query := {body := .select {
      items := [.expression (.column (some "t") "id" (some schema))]
      source := some (.table "t" none [] (some schema))}}
    let _ ← expectOk schema ((RenderContract.check .postgres16V01 query).mapError reprStr)
    count := count + 1
  for sql in ["SELECT s.t.id FROM s.t", "SELECT s.t.* FROM t", "SELECT * FROM s.t"] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    expectError "coarse namespace typing must fail closed" (Advanced.checkQuery [] [] query)
    count := count + 1
  expectError "mixed qualified query"
    (Advanced.parseQuery "SELECT ?, s.t.id FROM s.t WHERE s.t.id = $1")
  let mixed : Advanced.Query := {body := .select {
    items := [.expression (.parameter (.anonymous 1)),
      .expression (.column (some "t") "id" (some "s"))]
    source := some (.table "t" none [] (some "s"))
    whereClause := some (.binary .eq (.column (some "t") "id" (some "s"))
      (.parameter (.numbered 1)))}}
  rejected .postgres16V01 mixed "unsupported" "coverage.mixed-parameters"
  rejected .postgres16V01 qualifiedQuery "inconclusive" "resource.depth" 0
  SQLean.Tests.assert
    ((Advanced.Expr.column (some "t") "id" (some "s")).toSql == "\"s\".\"t\".\"id\"")
    "schema and relation components were flattened"
  pure (count + 4)

end SQLean.Tests
