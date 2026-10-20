import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import SQLean.RenderContract.ValidityPreservation
import SQLean.AdvancedQueryValidation
import Tests.Support

/-! The same question character has distinct parser roles. Infix operators do
not allocate binding slots, including after numbered parameters. Alternatives
restore all counters. The native maximal-operator policy is retained except
for the explicitly supported primary anonymous-template spelling. -/
namespace SQLean.Tests
open Advanced RenderContract

private def anon (n : Nat) : Advanced.Expr := .parameter (.anonymous n)
private def numbered (n : Nat) : Advanced.Expr := .parameter (.numbered n)
private def text (s : String) : Advanced.Expr := .literal (.text s)
private def col (s : String) : Advanced.Expr := .column none s
private def queryOf (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr]}}

example (op : JsonExistenceOp) (arg keys : Advanced.Expr) :
    translateExpr (.jsonExistence op arg keys) =
      .jsonExistence op (translateExpr arg) (translateExpr keys) := by
  rw [translateExpr]

example : Admissible (queryOf (.jsonExistence .key (anon 1) (anon 2))) := by
  refine ⟨{depth := 5, parameters := [.anonymous 1, .anonymous 2]}, ?_, ?_, ?_⟩
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
open SelectContract
private def params : SelectContract.ParameterEnv :=
  [⟨1, ⟨.jsonb, []⟩, false⟩, ⟨2, ⟨.text, []⟩, true⟩]

private theorem exists_valid :
    ExprValid params Scope.empty (.jsonExistence .key (anon 1) (anon 2))
      (some ⟨.bool, true⟩) [.anonymous 1, .anonymous 2] :=
  .jsonExistence (selected := ⟨[.jsonb, .text], .bool⟩)
    (.parameter (binding := ⟨1, ⟨.jsonb, []⟩, false⟩) (by simp [params]) rfl rfl)
    (.parameter (binding := ⟨2, ⟨.text, []⟩, true⟩) (by simp [params]) rfl rfl)
    (by decide)

example : ExprValid params Scope.empty (.jsonExistence .key (numbered 1) (numbered 2))
    (some ⟨.bool, true⟩) [.numbered 1, .numbered 2] := by
  simpa [translateExpr, translateParameter, anon, numbered] using
    expr_valid_translated exists_valid
end StaticTransport

private def rejected (profile : RenderContract.Profile) (query : Advanced.Query)
    (status code : String) (budget : Nat := 1024) : IO Unit := do
  match RenderContract.check profile query budget with
  | .ok _ => throw (IO.userError s!"JSON existence unexpectedly accepted {status}/{code}")
  | .error failure =>
    SQLean.Tests.assert (failure.status == status && failure.diagnostic.code == code)
      s!"JSON existence classification: {reprStr failure}"

private def checkQuery (query : Advanced.Query) (parameters : List Parameter)
    (sqlite : Bool := true) : IO Nat := do
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    let certificate ← expectOk "JSON existence" ((RenderContract.check profile query).mapError reprStr)
    SQLean.Tests.assert (certificate.footprint.parameters == parameters)
      "question operator consumed a binding or reordered occurrences"
    let parsed ← expectOk certificate.sql (parseRendered profile certificate.sql)
    SQLean.Tests.assert (decide (parsed = expectedQuery profile query))
      "JSON existence canonical SQL changed exact structure"
    let again ← expectOk "JSON canonical stability" ((RenderContract.check profile parsed).mapError reprStr)
    SQLean.Tests.assert (again.sql == certificate.sql) "JSON existence canonical bytes changed"
    let environment : Parameter → String := reprStr
    for parameter in parameters do
      SQLean.Tests.assert
        (certificate.transport environment (parameterSlot parameter) == environment parameter)
        "JSON existence changed a bound value"
  SQLean.Tests.assert (Advanced.queryParameters 256 query == parameters)
    "coarse AST walk lost JSON existence parameters"
  if sqlite then rejected .sqliteV01 query "unsupported" "coverage.sqlite.json-existence"
  pure (if sqlite then 3 else 2)

private def deep : Nat → Advanced.Expr
  | 0 => anon 1
  | n + 1 => .jsonExistence .key (deep n) (text "x")

def jsonExistenceRenderingTests : IO Nat := do
  let mut count := 0
  for (op, spelling) in [(JsonExistenceOp.key, "?"), (.any, "?|"), (.all, "?&")] do
    let expr := Advanced.Expr.jsonExistence op (anon 1) (anon 2)
    count := count + (← checkQuery (queryOf expr) [.anonymous 1, .anonymous 2])
    SQLean.Tests.assert (expr.toSql == "(? " ++ spelling ++ " ?)") "existence operator identity"
    let parsed ← expectOk spelling (Advanced.parseExpression ("? " ++ spelling ++ " ?"))
    SQLean.Tests.assert (decide (parsed = expr)) "infix question allocated a parameter"
    count := count + 2
    for (arg, keys, uses) in [
        (text "{\"?\":null,\"?|\":1}", text "? O'Brien ?&", []),
        (.null, .null, []),
        (numbered 7, .array [numbered 2, numbered 7], [.numbered 7, .numbered 2, .numbered 7]),
        (.jsonAccess .field (anon 1) (anon 2), anon 3, [.anonymous 1, .anonymous 2, .anonymous 3]),
        (.scalarQuery (queryOf (anon 1)), anon 2, [.anonymous 1, .anonymous 2]),
        (.substring .forFrom [anon 1, anon 2, anon 3], anon 4,
          [.anonymous 1, .anonymous 2, .anonymous 3, .anonymous 4])] do
      count := count + (← checkQuery (queryOf (.jsonExistence op arg keys)) uses)
  let a := col "a"
  let b := col "b"
  let c := col "c"
  for (source, expected) in [
      ("a?b", Advanced.Expr.jsonExistence .key a b),
      ("a?1", .jsonExistence .key a 1),
      ("a?|b", .jsonExistence .any a b),
      ("a?&b", .jsonExistence .all a b),
      ("a?b||c", .concat (.jsonExistence .key a b) c),
      ("a||b?c", .jsonExistence .key (.concat a b) c),
      ("a->b?c", .jsonExistence .key (.jsonAccess .field a b) c),
      ("a?b->c", .jsonAccess .field (.jsonExistence .key a b) c),
      ("a?b=c", .binary .eq (.jsonExistence .key a b) c),
      ("a=b?c", .binary .eq a (.jsonExistence .key b c)),
      ("a?b+c", .jsonExistence .key a (.binary .add b c)),
      ("NOT a?b", .unary .not (.jsonExistence .key a b)),
      ("a?/* ? $7 /* ? */ */b", .jsonExistence .key a b),
      ("a?|-- ? $7\nb", .jsonExistence .any a b),
      ("?+?", .binary .add (anon 1) (anon 2)),
      ("?||?", .concat (anon 1) (anon 2)),
      ("?&&?", .overlap (anon 1) (anon 2)),
      ("id+?", .binary .add (col "id") (anon 1)),
      ("1=?", .binary .eq 1 (anon 1)),
      ("+-?", .unary .pos (.unary .neg (anon 1))),
      ("? ? ?", .jsonExistence .key (anon 1) (anon 2)),
      ("CAST(? AS JSONB)??", .jsonExistence .key (.cast (anon 1) ⟨.jsonb, []⟩) (anon 2)),
      ("$2 ? $1", .jsonExistence .key (numbered 2) (numbered 1))] do
    let parsed ← expectOk source (Advanced.parseExpression source)
    SQLean.Tests.assert (decide (parsed = expected)) s!"question role/precedence: {source}"
    count := count + 1
  for (sql, n) in [
      ("SELECT DISTINCT ON (?) ? ? ?", 3),
      ("SELECT CASE WHEN ? THEN ?::jsonb ? ? ELSE ? END", 4),
      ("WITH c AS (SELECT ?) SELECT ? ? ? FROM c WHERE ?", 4),
      ("SELECT ? ? (SELECT ?)", 2),
      ("SELECT ? FROM ((SELECT ? AS x) q JOIN t ON q.x = ?)", 3),
      ("SELECT ? IN ((SELECT ?), ?) OR ? ? ?", 5),
      ("SELECT ? FROM t WHERE ? ? ? ORDER BY ? OFFSET ? LIMIT ?", 6),
      ("SELECT SUBSTRING(? FOR ? FROM ?) ? ?", 4)] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    let uses := (List.range n).map fun i => Parameter.anonymous (i + 1)
    count := count + (← checkQuery query uses false)
  for source in ["a?-b", "a?+b", "a?!b", "a|?b", "a?||b", "a?&&b", "a?|-b",
      "a||-b", "a&&-b", "?|a", "?&a", "SELECT ?1", "SELECT ?0",
      "SELECT ?::jsonb ? $1", "SELECT $1::jsonb ? ?", "SELECT ?1, ?"] do
    expectError source (if source.startsWith "SELECT" then Advanced.parseQuery source |>.map fun _ => ()
      else Advanced.parseExpression source |>.map fun _ => ())
    count := count + 1
  let declarations ← expectOk "nullable declarations are not bindings"
    (Advanced.parseParameterDeclarations "jsonb?, text?, text[]?")
  SQLean.Tests.assert (declarations.map Prod.snd == [true, true, true]) "nullable suffix changed roles"
  count := count + 1
  let sqlite ← expectOk "SQLite numbered bindings" (Advanced.parseSQLiteQuery "SELECT ?2, ?1, ?2")
  SQLean.Tests.assert (Advanced.queryParameters 256 sqlite == [.numbered 2, .numbered 1, .numbered 2])
    "SQLite numbered identity changed"
  expectError "SQLite mixed binding styles" (Advanced.parseSQLiteQuery "SELECT ?1, ?")
  count := count + 2
  for sql in ["SELECT j ? 'a' FROM t", "SELECT j ?| k FROM t", "SELECT j ?& k FROM t"] do
    let query ← expectOk sql (Advanced.parseSQLiteQuery sql)
    rejected .sqliteV01 query "unsupported" "coverage.sqlite.json-existence"
    expectError "coarse tier cannot erase exact existence typing" (Advanced.checkQuery [] [] query)
    count := count + 2
  for expr in [Advanced.Expr.jsonExistence .key (.decimal "bad") (anon 1),
      .jsonExistence .all (anon 1) (.array [.decimal "bad"])] do
    rejected .postgres16V01 (queryOf expr) "invalid" "representation.numeric-token"
    count := count + 1
  rejected .identityV01 (queryOf (.jsonExistence .key (anon 2) (anon 1)))
    "invalid" "representation.parameters"
  rejected .postgres16V01 (queryOf (.jsonExistence .key (anon 1) (numbered 2)))
    "unsupported" "coverage.mixed-parameters"
  rejected .postgres16V01 (queryOf (deep 12)) "inconclusive" "resource.depth" 8
  let dense := String.intercalate "+" (List.replicate 100 "?")
  let parsed ← expectOk "dense operator run retains source-sized fuel" (Advanced.parseExpression dense)
  SQLean.Tests.assert
    (Advanced.expressionParameters 256 parsed == (List.range 100).map (fun i => .anonymous (i + 1)))
    "dense anonymous operator run lost slots"
  pure (count + 4)

end SQLean.Tests
