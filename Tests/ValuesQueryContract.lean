import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import SQLean.RenderContract.TranslationProofs
import Tests.ContractSupport

/-! VALUES constructor-only witnesses and simultaneous type/coercion controls.
These witnesses do not invoke an executable query checker. -/
namespace SQLean.Tests
open SelectContract

private def valuesOne : Advanced.Query := {body := .values [[.literal (.int 1)]]}
private def valuesIntCell := valuesCell (.literal (.int 1)) (some ⟨.int32, false⟩) .none

private theorem valuesOne_valid : QueryValid .basicV36 [] [] [] valuesOne
    [⟨"column1", ⟨.int32, false⟩, none⟩] [] := by
  apply QueryValid.values (cteUses := []) (visible := []) (rowUses := [])
    (cells := [[valuesIntCell]]) (limitUses := []) (offsetUses := [])
  · decide
  · exact .nil
  · rfl
  · exact .cons (.cons (.int (by decide)) (.atom (.int (by decide)) .int) .nil) .nil
  · exact .cons (cells := [valuesIntCell]) (base := .int32) (derivation := .none) rfl rfl rfl .nil
  · simp
  · exact .nil
  · exact .absent
  · exact .absent

private theorem valuesOne_select_valid : SelectValid .basicV36 [] [] valuesOne
    [⟨"column1", ⟨.int32, false⟩, none⟩] := by
  apply SelectValid.certified (uses := [])
  · decide
  · decide
  · decide
  · exact valuesOne_valid
  · decide

example : SelectValid .basicV36 [] [] (RenderContract.translateParameters valuesOne)
    [⟨"column1", ⟨.int32, false⟩, none⟩] :=
  RenderContract.translateParameters_valid valuesOne_select_valid

/-- All-unknown initial rows must wait for the later integer input. A sequence
of independently finalized SELECT leaves would instead choose TEXT too soon. -/
example : conditionalBase [.unknown true, .unknown true, .known ⟨.int32, false⟩] = some .int32 := rfl
example : conditionalBase [.unknown false, .known ⟨.varchar [5], false⟩] = some (.varchar []) := rfl
example : conditionalBase [.known ⟨.varchar [5], false⟩, .known ⟨.varchar [5], false⟩] = some (.varchar [5]) := rfl
example : conditionalBase [.known ⟨.numeric [5, 2], false⟩, .known ⟨.numeric [7, 2], false⟩] = some (.numeric []) := rfl
example : (Scope.ofAnonymousOutput [⟨"column1", ⟨.int32, false⟩, none⟩]).columns none =
    [⟨"column1", ⟨.int32, false⟩, none⟩] := rfl
example : (Scope.ofAnonymousOutput [⟨"column1", ⟨.int32, false⟩, none⟩]).matchingRelations "" = [] := rfl
example : (Scope.ofAnonymousOutput [⟨"column1", ⟨.int32, false⟩, none⟩]).matchingRelations "unnamed_subquery" = [] := rfl
example : valuesShape [] = false := rfl
example : valuesShape [[]] = false := rfl
example : valuesShape [[.null], [.null, .null]] = false := rfl


private def valuesParams : SelectContract.ParameterEnv := [⟨1, ⟨.int, []⟩, false⟩]
private def valuesParamExpr : Advanced.Expr := .parameter (.anonymous 1)
private def valuesParam : Advanced.Query := {body := .values [[valuesParamExpr]]}
private def valuesParamColumn : OutputColumn := ⟨"column1", ⟨.int32, false⟩, none⟩

private theorem valuesParam_valid : QueryValid .basicV36 [] valuesParams [] valuesParam [valuesParamColumn] [.anonymous 1] := by
  have typed : ExprValidCore (QueryValid .basicV36 [] valuesParams) valuesParams [] .empty
      valuesParamExpr (some ⟨.int32, false⟩) [.anonymous 1] :=
    .parameter (binding := ⟨1, ⟨.int, []⟩, false⟩) (by simp [valuesParams]) rfl rfl
  have collation : ExprCollationValidCore (QueryValid .basicV36 [] valuesParams) .basicV36
      valuesParams [] .empty valuesParamExpr (some ⟨.int32, false⟩) .none :=
    .parameter (binding := ⟨1, ⟨.int, []⟩, false⟩) (by simp [valuesParams]) rfl rfl
  apply QueryValid.values (cteUses := []) (visible := []) (rowUses := [.anonymous 1])
    (cells := [[valuesCell valuesParamExpr (some ⟨.int32, false⟩) .none]]) (limitUses := []) (offsetUses := [])
  · decide
  · exact .nil
  · rfl
  · exact .cons (.cons typed collation .nil) .nil
  · exact .cons (cells := [valuesCell valuesParamExpr (some ⟨.int32, false⟩) .none])
      (base := .int32) (derivation := .none) rfl rfl rfl .nil
  · simp
  · exact .nil
  · exact .absent
  · exact .absent

private def valuesAnonParam : Advanced.Query :=
  {body := .select {items := [.all none], source := some (.derivedAnonymous valuesParam)}}

/-- The anonymous namespace, its exposed star columns, and actual parameter
occurrence are justified using constructors only, without a parser/checker. -/
private theorem valuesAnonParam_valid : QueryValid .basicV36 [] valuesParams [] valuesAnonParam
    [valuesParamColumn] [.anonymous 1] := by
  apply QueryValid.basic (cteUses := []) (visible := []) (scope := Scope.ofAnonymousOutput [valuesParamColumn])
    (sourceUses := [.anonymous 1]) (selectUses := []) (whereUses := []) (orderUses := [])
    (limitUses := []) (offsetUses := [])
  · decide
  · exact .nil
  · exact .derivedAnonymous valuesParam_valid rfl
  · exact .all rfl (by decide) .nil
  · exact .all rfl (by decide) .nil
  · simp
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact .absent
  · exact .nil
  · exact .nil
  · exact .absent
  · exact .absent
  · exact .nil
  · rfl
  · rfl
  · rfl

example : QueryValid .basicV36 [] valuesParams [] (RenderContract.translateParameters valuesAnonParam)
    [valuesParamColumn] [.numbered 1] :=
  RenderContract.query_valid_translated valuesAnonParam_valid

private def valuesOutput (sql : String) (types : String := "") : IO (List OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let params ← expectOk types (Assurance.parseContractParameterTypes types)
  let checked ← expectOk sql ((SelectContract.checkQuery .basicV36 [] params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid checked.valid
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    let rendered ← expectOk sql ((RenderContract.check profile query).mapError reprStr)
    let parsed ← expectOk rendered.sql (RenderContract.parseRendered profile rendered.sql)
    SQLean.Tests.assert (decide (parsed = RenderContract.expectedQuery profile query))
      "VALUES roundtrip changed rows, query ownership, anonymous namespace or parameters"
    let checkedAgain ← expectOk rendered.sql ((SelectContract.checkQuery .basicV36 [] params parsed).mapError reprStr)
    SQLean.Tests.assert (checkedAgain.output == checked.output) "VALUES exact output changed"
  pure checked.output

private def valuesRejected (sql : String) (kind code : String) : IO Unit := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  match SelectContract.checkQuery .basicV36 [] [] query with
  | .ok _ => throw (IO.userError s!"unexpected VALUES acceptance: {sql}")
  | .error failure =>
    let (actualKind, diagnostic) := match failure with
      | .invalid d => ("invalid", d) | .unsupported d => ("unsupported", d)
      | .inconclusive d => ("inconclusive", d)
    SQLean.Tests.assert (actualKind == kind && diagnostic.code == code)
      s!"wrong VALUES classification: {sql}: {reprStr failure}"

def valuesQueryContractTests : IO Nat := do
  let mut count := 0
  for (sql, type, nullable, collation) in [
      ("VALUES (NULL),(NULL),(1)", ScalarType.int32, true, none),
      ("VALUES ('a'),('b')", .text, false, some .databaseDefault),
      ("VALUES (NULL),(NULL)", .text, true, some .databaseDefault),
      ("VALUES ('x'::VARCHAR(5)),('y'::VARCHAR(5))", .varchar [5], false, some .databaseDefault),
      ("VALUES ('x'::VARCHAR(5)),('y'::VARCHAR(7))", .varchar [], false, some .databaseDefault),
      ("VALUES (NULL),('x'::VARCHAR(5))", .varchar [], true, some .databaseDefault),
      ("VALUES (1::NUMERIC(5,2)),(2::NUMERIC(7,2))", .numeric [], false, none),
      ("VALUES (1::SMALLINT),(2::BIGINT)", .int64, false, none),
      ("VALUES (ARRAY[1]),(ARRAY[2::BIGINT])", .array .int64, false, none)] do
    let output ← valuesOutput sql
    SQLean.Tests.assert (output == [⟨"column1", ⟨type, nullable⟩, collation⟩])
      s!"VALUES simultaneous column metadata changed: {sql}: {reprStr output}"
    count := count + 1
  for sql in [
      "SELECT * FROM (VALUES (1))", "SELECT column1 FROM (VALUES (1))",
      "WITH t AS (VALUES (1)) SELECT * FROM t", "VALUES (1) UNION ALL SELECT 2",
      "SELECT 1 WHERE 1 IN (VALUES (1),(2))", "SELECT 1 WHERE EXISTS(VALUES (1))",
      "SELECT 1 WHERE 1 < ALL(VALUES (2),(3))", "VALUES ((SELECT 1))",
      "VALUES (1) ORDER BY column1", "VALUES (1) ORDER BY 1 LIMIT 1 OFFSET 0",
      "WITH RECURSIVE t(n) AS (VALUES (1) UNION ALL SELECT n+1 FROM t WHERE n<3) SELECT n FROM t",
      "SELECT t.x FROM (VALUES (1)), (SELECT 2 AS x)t"] do
    let output ← valuesOutput sql
    SQLean.Tests.assert (output.length == 1) s!"VALUES contextual width changed: {sql}"
    count := count + 1
  let duplicates ← valuesOutput "SELECT * FROM (VALUES (1)), (VALUES (2))"
  SQLean.Tests.assert (duplicates.map OutputColumn.name == ["column1", "column1"])
    "anonymous derived sources must retain ordered duplicate unqualified labels"
  count := count + 1
  for (sql, kind, code) in [
      ("VALUES (1),(1,2)", "invalid", "values_arity"),
      ("VALUES (1),(TRUE)", "invalid", "values_common_type"),
      ("VALUES ('x' COLLATE \"C\"),('y' COLLATE \"POSIX\")", "invalid", "collation_conflict"),
      ("VALUES (1) FOR UPDATE", "invalid", "locking_values"),
      ("SELECT column1 FROM (VALUES (1)), (VALUES (2))", "invalid", "column_binding"),
      ("SELECT unnamed_subquery.column1 FROM (VALUES (1))", "invalid", "relation_reference"),
      ("SELECT \"*SELECT*\".column1 FROM (VALUES (1))", "invalid", "relation_reference"),
      ("SELECT \"*VALUES*\".column1 FROM (VALUES (1))", "invalid", "relation_reference"),
      ("SELECT * FROM LATERAL (VALUES (1))", "unsupported", "lateral_source"),
      ("SELECT * FROM (VALUES (1)) FOR UPDATE", "unsupported", "derived_locking"),
      ("SELECT * FROM (VALUES (1)) FOR UPDATE OF unnamed_subquery", "invalid", "locking_target")] do
    valuesRejected sql kind code
    count := count + 1
  let catalog : Advanced.Catalog := [{name := "base_table", columns := [{name := "x", type := ⟨.int, []⟩, nullable := some false}]}]
  for sql in ["SELECT * FROM (SELECT x FROM base_table) FOR UPDATE",
      "SELECT * FROM base_table LEFT JOIN (SELECT x FROM base_table) ON TRUE FOR UPDATE"] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV36 catalog [] query with
    | .error (.unsupported diagnostic) =>
      SQLean.Tests.assert (diagnostic.code == "derived_locking") "anonymous row-lock provenance was lost"
    | _ => throw (IO.userError s!"anonymous derived base locking must remain Unsupported: {sql}")
    count := count + 1
  let parameterSQL := "VALUES (?,?),(?,?) OFFSET ? LIMIT ?"
  let query ← expectOk parameterSQL (Advanced.parseQuery parameterSQL)
  let expected : List Advanced.Parameter := [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4, .anonymous 5, .anonymous 6]
  SQLean.Tests.assert (Advanced.queryParameters 1024 query == expected) "VALUES row-major lexical parameter order changed"
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    let rendered ← expectOk parameterSQL ((RenderContract.check profile query).mapError reprStr)
    SQLean.Tests.assert (rendered.footprint.parameters == expected) "VALUES renderer parameter order changed"
    let environment : Advanced.Parameter → String := reprStr
    for parameter in expected do
      SQLean.Tests.assert
        (rendered.transport environment (RenderContract.parameterSlot parameter) == environment parameter)
        "VALUES parameter transport changed the bound value"
  let _ ← valuesOutput parameterSQL "INTEGER,INTEGER,INTEGER,INTEGER,INTEGER,INTEGER"
  count := count + 1
  match RenderContract.check .sqliteV01 valuesOne with
  | .error (.unsupported diagnostic) =>
    SQLean.Tests.assert (diagnostic.code == "coverage.sqlite.VALUES-query") "wrong SQLite VALUES boundary"
  | _ => throw (IO.userError "SQLite VALUES must remain explicitly unsupported")
  pure (count + 1)

end SQLean.Tests
