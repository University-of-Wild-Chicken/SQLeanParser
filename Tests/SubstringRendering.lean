import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import SQLean.RenderContract.ValidityPreservation
import SQLean.AdvancedQueryValidation
import Tests.Support

/-! SUBSTRING's special syntax stores lexical argument order. In particular,
FOR ... FROM ... is not normalized by moving anonymous parameters. The
independent static rules separately describe its function-argument order. -/
namespace SQLean.Tests
open Advanced SelectContract RenderContract

private def anon (n : Nat) : Advanced.Expr := .parameter (.anonymous n)
private def numbered (n : Nat) : Advanced.Expr := .parameter (.numbered n)
private def col (name : String) : Advanced.Expr := .column none name
private def text (value : String) : Advanced.Expr := .literal (.text value)
private def queryOf (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr]}}

example (form : SubstringForm) (args : List Advanced.Expr) :
    translateExpr (.substring form args) = .substring form (args.map translateExpr) := by
  rw [translateExpr]
  simp only [List.attach_map_val]

example : Admissible (queryOf (.substring .forFrom [anon 1, anon 2, anon 3])) := by
  refine ⟨{depth := 5, parameters := [.anonymous 1, .anonymous 2, .anonymous 3]}, ?_, ?_, ?_⟩
  · unfold queryOf inspectQuery
    dsimp
    unfold inspectSelect
    dsimp
    unfold inspectItem inspectExpr
    simp only [SubstringForm.arity]
    unfold inspectExpr
    rfl
  · decide
  · decide

section StaticTransport
private def params : SelectContract.ParameterEnv :=
  [⟨1, ⟨.text, []⟩, false⟩, ⟨2, ⟨.int, []⟩, false⟩, ⟨3, ⟨.int, []⟩, false⟩]

private theorem for_first_valid :
    ExprValid params Scope.empty (.substring .forFrom [anon 1, anon 2, anon 3])
      (some ⟨.text, false⟩) [.anonymous 1, .anonymous 2, .anonymous 3] :=
  .substring (params := params) (scope := Scope.empty)
    (es := [anon 1, anon 2, anon 3]) (selected := ⟨[.text, .int32, .int32], .text⟩)
    (.cons (.parameter (binding := ⟨1, ⟨.text, []⟩, false⟩) (by simp [params]) rfl rfl)
      (.cons (.parameter (binding := ⟨2, ⟨.int, []⟩, false⟩) (by simp [params]) rfl rfl)
        (.cons (.parameter (binding := ⟨3, ⟨.int, []⟩, false⟩) (by simp [params]) rfl rfl)
          .nil)))
    .forFrom (by decide)

example :
    ExprValid params Scope.empty (.substring .forFrom [numbered 1, numbered 2, numbered 3])
      (some ⟨.text, false⟩) [.numbered 1, .numbered 2, .numbered 3] := by
  simpa [translateExpr, translateParameter, anon, numbered] using
    expr_valid_translated for_first_valid

/-- FOR-only carries an explicit conversion, including known BOOLEAN lengths;
ordinary positional arguments do not gain that conversion rule. -/
private theorem for_only_valid :
    ExprValid [] Scope.empty (.substring .forOnly [text "abc", .literal (.bool true)])
      (some ⟨.text, false⟩) [] :=
  .substring (params := []) (scope := Scope.empty)
    (es := [text "abc", .literal (.bool true)]) (selected := ⟨[.text, .int32, .int32], .text⟩)
    (.cons .text (.cons .bool .nil))
    (.forOnly (.known (by decide) rfl)) (by decide)

example :
    ExprValid [] Scope.empty
      (translateExpr (.substring .forOnly [text "abc", .literal (.bool true)]))
      (some ⟨.text, false⟩) [] := by
  simpa using expr_valid_translated for_only_valid

example (form : SubstringForm) (args : List Advanced.Expr) :
    outputLabel (translateExpr (.cast (.substring form args) ⟨.text, []⟩)) =
      (2, "substring") := by
  simp [translateExpr, outputLabel]
end StaticTransport

private def rejected (profile : RenderContract.Profile) (query : Advanced.Query)
    (status code : String) (budget : Nat := 1024) : IO Unit := do
  match RenderContract.check profile query budget with
  | .ok _ => throw (IO.userError s!"SUBSTRING unexpectedly accepted {status}/{code}")
  | .error failure =>
    SQLean.Tests.assert (failure.status == status && failure.diagnostic.code == code)
      s!"SUBSTRING classification: {reprStr failure}"

private def checkExpr (form : SubstringForm) (args : List Advanced.Expr)
    (parameters : List Parameter) : IO Nat := do
  let expr := Advanced.Expr.substring form args
  let query := queryOf expr
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    let certificate ← expectOk "SUBSTRING" ((RenderContract.check profile query).mapError reprStr)
    SQLean.Tests.assert (certificate.footprint.parameters == parameters)
      "SUBSTRING changed lexical parameter occurrence order"
    let parsed ← expectOk certificate.sql (parseRendered profile certificate.sql)
    SQLean.Tests.assert (decide (parsed = expectedQuery profile query))
      "SUBSTRING roundtrip changed its grammar form or expressions"
    let again ← expectOk "SUBSTRING stability" ((RenderContract.check profile parsed).mapError reprStr)
    SQLean.Tests.assert (again.sql == certificate.sql) "SUBSTRING canonical SQL changed"
    let environment : Parameter → String := fun p => reprStr p
    for parameter in parameters do
      SQLean.Tests.assert
        (certificate.transport environment (parameterSlot parameter) == environment parameter)
        "SUBSTRING changed the value assigned to a parameter"
  SQLean.Tests.assert (Advanced.expressionParameters 128 expr == parameters)
    "coarse expression walker lost SUBSTRING parameters"
  expectError "coarse tier requires exact SUBSTRING normalization" (Advanced.checkQuery [] [] query)
  rejected .sqliteV01 query "unsupported" "coverage.sqlite.substring"
  pure 5

private def deep : Nat → Advanced.Expr
  | 0 => anon 1
  | n + 1 => .substring .from [deep n, 1]

def substringRenderingTests : IO Nat := do
  let mut count := 0
  let forms := [SubstringForm.from, .fromFor, .forFrom, .forOnly, .similar]
  for form in forms do
    let args := (List.range form.arity).map (fun n => anon (n + 1))
    let parameters := (List.range form.arity).map (fun n => Parameter.anonymous (n + 1))
    count := count + (← checkExpr form args parameters)
    let args := (List.range form.arity).map (fun n => numbered (7 - n))
    let parameters := (List.range form.arity).map (fun n => Parameter.numbered (7 - n))
    count := count + (← checkExpr form args parameters)
    count := count + (← checkExpr form (List.replicate form.arity (numbered 3))
      (List.replicate form.arity (.numbered 3)))
    for arity in List.range 5 do
      if arity != form.arity then
        rejected .identityV01 (queryOf (.substring form (List.replicate arity .null)))
          "invalid" "representation.substring-arity"
        count := count + 1
  for (form, args, parameters) in [
      (SubstringForm.forFrom,
        [text "abcdef", .coalesce [anon 1, anon 2], .cast (anon 3) ⟨.int, []⟩],
        [.anonymous 1, .anonymous 2, .anonymous 3]),
      (.from, [.substring .forOnly [anon 1, anon 2], anon 3],
        [.anonymous 1, .anonymous 2, .anonymous 3]),
      (.similar, [text "'); SELECT $99; -- ?", anon 1, text "'"],
        [.anonymous 1]),
      (.fromFor, [.scalarQuery (queryOf (anon 1)), anon 2, anon 3],
        [.anonymous 1, .anonymous 2, .anonymous 3]),
      (.forOnly, [text "abcdef", .caseExpr none [(.isNull (anon 1), anon 2)] (some (anon 3))],
        [.anonymous 1, .anonymous 2, .anonymous 3])] do
    count := count + (← checkExpr form args parameters)
  let a := col "a"
  let b := col "b"
  let c := col "c"
  for (sql, expected) in [
      ("SUBSTRING(a FROM b)", Advanced.Expr.substring .from [a, b]),
      ("SUBSTRING(a FROM b FOR c)", .substring .fromFor [a, b, c]),
      ("SUBSTRING(a FOR b FROM c)", .substring .forFrom [a, b, c]),
      ("SUBSTRING(a FOR b)", .substring .forOnly [a, b]),
      ("SUBSTRING(a SIMILAR b ESCAPE c)", .substring .similar [a, b, c]),
      ("substring(? /* length */ FOR ? FROM ?)", .substring .forFrom [anon 1, anon 2, anon 3]),
      ("SUBSTRING(a FROM b + c)", .substring .from [a, .binary .add b c]),
      ("SUBSTRING(a FROM b AND c)", .substring .from [a, .binary .and b c]),
      ("SUBSTRING(a FOR b OR c)", .substring .forOnly [a, .binary .or b c]),
      ("SUBSTRING(a SIMILAR b ESCAPE c OR a)", .substring .similar [a, b, .binary .or c a]),
      ("SUBSTRING(a FOR (b + c) FROM c)", .substring .forFrom [a, .binary .add b c, c]),
      ("SUBSTRING(a FROM b)::TEXT", .cast (.substring .from [a, b]) ⟨.text, []⟩),
      ("(SUBSTRING(a FROM b))[1]", .subscript (.substring .from [a, b]) [.index 1]),
      ("SUBSTRING(a FROM (SELECT ?))", .substring .from [a, .scalarQuery (queryOf (anon 1))]),
      ("SUBSTRING()", .call ["substring"] []),
      ("SUBSTRING(a)", .call ["substring"] [a]),
      ("SUBSTRING(a, b)", .call ["substring"] [a, b]),
      ("SUBSTRING(a, b, c)", .call ["substring"] [a, b, c]),
      ("\"substring\"(a, b)", .call ["substring"] [a, b]),
      ("pg_catalog.substring(a, b)", .call ["pg_catalog", "substring"] [a, b]),
      ("substring", col "substring"),
      ("t.substring", .column (some "t") "substring")] do
    let parsed ← expectOk sql (Advanced.parseExpression sql)
    SQLean.Tests.assert (decide (parsed = expected)) s!"SUBSTRING parser boundary: {sql}"
    count := count + 1
  SQLean.Tests.assert
    ((Advanced.Expr.substring .forFrom [anon 1, anon 2, anon 3]).toSql ==
      "SUBSTRING(? FOR ? FROM ?)")
    "FOR-first canonical rendering must preserve lexical order"
  SQLean.Tests.assert
    ((Advanced.Expr.substring .forFrom [anon 1, anon 2, anon 3]).toSql true ==
      "SUBSTRING($1 FOR $2 FROM $3)")
    "PostgreSQL translation changed lexical parameter ordinals"
  count := count + 2
  for sql in [
      "SUBSTRING(FROM a)", "SUBSTRING(a FROM)", "SUBSTRING(a FOR)",
      "SUBSTRING(a SIMILAR b)", "SUBSTRING(a ESCAPE c)", "SUBSTRING(a SIMILAR b ESCAPE)",
      "SUBSTRING(a FROM b, c)", "SUBSTRING(a, b FOR c)", "SUBSTRING(a FOR b FOR c)",
      "SUBSTRING(a FROM b FOR c FROM a)", "SUBSTRING(a SIMILAR b ESCAPE c FOR a)",
      "SUBSTRING(a FROM b)[1]", "\"substring\"(a FROM b)", "pg_catalog.substring(a FROM b)"] do
    expectError sql (Advanced.parseExpression sql)
    count := count + 1
  for sql in ["SELECT SUBSTRING(? FROM ?)", "SELECT SUBSTRING(? FOR ? FROM ?)",
      "SELECT SUBSTRING(? SIMILAR ? ESCAPE ?)"] do
    expectError "SQLite special SUBSTRING input" (Advanced.parseSQLiteQuery sql)
    count := count + 1
  let _ ← expectOk "SQLite ordinary substring call"
    (Advanced.parseSQLiteQuery "SELECT substring(?, ?, ?)")
  rejected .postgres16V01 (queryOf (.substring .from [anon 1, .decimal "bad"]))
    "invalid" "representation.numeric-token"
  rejected .postgres16V01 (queryOf (.substring .from [anon 1, numbered 2]))
    "unsupported" "coverage.mixed-parameters"
  rejected .identityV01 (queryOf (.substring .forFrom [anon 1, anon 3, anon 2]))
    "invalid" "representation.parameters"
  for profile in [RenderContract.Profile.identityV01, .postgres16V01, .sqliteV01] do
    rejected profile (queryOf (deep 12)) "inconclusive" "resource.depth" 8
    count := count + 1
  pure (count + 4)

end SQLean.Tests
