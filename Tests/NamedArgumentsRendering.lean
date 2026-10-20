import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import SQLean.RenderContract.ValidityPreservation
import SQLean.AdvancedQueryValidation
import Tests.Support

/-! Named call syntax retains lexical order, decoded name identity, and both
assignment spellings. Defaults and argument binding belong to the independent
validity judgment, not to structural rendering. -/
namespace SQLean.Tests
open Advanced RenderContract

private def queryOf (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr]}}
private def anon (n : Nat) : Advanced.Expr := .parameter (.anonymous n)
private def num (n : Nat) : Advanced.Expr := .parameter (.numbered n)
private def named (name : Name) (expr : Advanced.Expr)
    (spelling : NamedArgumentNotation := .arrow) : CallArgument := .named name expr spelling

example (name : Name) (value : Advanced.Expr) (spelling : NamedArgumentNotation) :
    (translateCallArgument (.named name value spelling)).name? = some name := by
  rw [translateCallArgument_name]
  rfl

example (args : List CallArgument) :
    (args.map translateCallArgument).map CallArgument.expression =
      (args.map CallArgument.expression).map translateExpr := translated_call_expressions args

example (args : List CallArgument) :
    translateExpr (translateExpr (.namedCall ["make_interval"] args)) =
      translateExpr (.namedCall ["make_interval"] args) :=
  translateExpr_idempotent _

private def roundTrip (expr : Advanced.Expr) (uses : List Parameter) : IO Nat := do
  let query := queryOf expr
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    let cert ← expectOk "named argument rendering" ((RenderContract.check profile query).mapError reprStr)
    SQLean.Tests.assert (cert.footprint.parameters == uses) "named arguments reordered or lost bindings"
    let parsed ← expectOk cert.sql (parseRendered profile cert.sql)
    SQLean.Tests.assert (decide (parsed = expectedQuery profile query))
      "argument identity, spelling or lexical order changed"
    let again ← expectOk "named call canonical" ((RenderContract.check profile parsed).mapError reprStr)
    SQLean.Tests.assert (again.sql == cert.sql) "named call canonical bytes changed"
    for parameter in uses do
      SQLean.Tests.assert (cert.transport reprStr (parameterSlot parameter) == reprStr parameter)
        "named call value transport changed a logical parameter"
  SQLean.Tests.assert (Advanced.queryParameters 256 query == uses) "expanded parameter traversal dropped arguments"
  pure 2

private def parsed (source : String) (expected : Advanced.Expr) : IO Unit := do
  let expr ← expectOk source (Advanced.parseExpression source)
  SQLean.Tests.assert (decide (expr = expected)) s!"named argument AST mismatch: {source}"

private def rejectedRepresentation (expr : Advanced.Expr) (code : String) : IO Unit := do
  match RenderContract.check .identityV01 (queryOf expr) with
  | .error (.invalid diagnostic) =>
      SQLean.Tests.assert (diagnostic.code == code) s!"wrong named-call representation boundary: {diagnostic.code}"
  | result => throw (IO.userError s!"malformed named-call AST admitted: {reprStr (result.map (·.sql))}")

def namedArgumentsRenderingTests : IO Nat := do
  let mut count := 0
  for (source, expected) in [
      ("make_interval()", Advanced.Expr.call ["make_interval"] []),
      ("make_interval(1, 2)", .call ["make_interval"] [1, 2]),
      ("make_interval(days => 2)", .namedCall ["make_interval"] [named "days" 2]),
      ("make_interval(days := 2)", .namedCall ["make_interval"] [named "days" 2 .assignment]),
      ("make_interval(1, days => 2, secs := 3)", .namedCall ["make_interval"]
        [.positional 1, named "days" 2, named "secs" 3 .assignment]),
      ("make_interval(secs=>?,days:=?)", .namedCall ["make_interval"]
        [named "secs" (anon 1), named "days" (anon 2) .assignment]),
      ("make_interval(secs=>$2,days:=$1)", .namedCall ["make_interval"]
        [named "secs" (num 2), named "days" (num 1) .assignment]),
      ("make_interval(secs=>-1)", .namedCall ["make_interval"] [named "secs" (.unary .neg 1)]),
      ("make_interval(secs:=+?)", .namedCall ["make_interval"] [named "secs" (.unary .pos (anon 1)) .assignment]),
      ("f(KEY => 1, current_schema := 2)", .namedCall ["f"]
        [named "key" 1, named "current_schema" 2 .assignment]),
      ("\"F\"(\"Select\"=>1,\"a.b\":=2)", .namedCall ["F"]
        [named "Select" 1, named "a.b" 2 .assignment]),
      ("s.f(x=>1)", .namedCall ["s", "f"] [named "x" 1]),
      ("current_schema(x=>1)", .namedCall ["current_schema"] [named "x" 1]),
      ("substring(string=>'abc',start=>1)", .namedCall ["substring"]
        [named "string" (.literal (.text "abc")), named "start" 1]),
      ("sum(x=>1)", .namedCall ["sum"] [named "x" 1]),
      ("make_interval(days=>1,days:=2)", .namedCall ["make_interval"]
        [named "days" 1, named "days" 2 .assignment]),
      ("make_interval(days=>1,2)", .namedCall ["make_interval"] [named "days" 1, .positional 2]),
      ("f(x/*?*/=>/*?*/?,y:=f(z=>?))", .namedCall ["f"]
        [named "x" (anon 1), named "y" (.namedCall ["f"] [named "z" (anon 2)]) .assignment])
      ] do
    parsed source expected
    count := count + 1 + (← roundTrip expected (Advanced.expressionParameters 256 expected))
  -- Retain ordinary aggregate and substring paths after speculative named parsing.
  parsed "SUM(?)" (.aggregate .sum (anon 1))
  parsed "SUBSTRING(? FOR ? FROM ?)" (.substring .forFrom [anon 1, anon 2, anon 3])
  parsed "current_schema()" (.call ["current_schema"] [])
  count := count + 3
  for spelling in [NamedArgumentNotation.arrow, .assignment] do
    for value in [anon 1, .caseExpr none [(.literal (.bool true), anon 1)] (some (anon 2)),
        .substring .forFrom [anon 1, anon 2, anon 3],
        .jsonExistence .key (anon 1) (anon 2),
        .subscript (anon 1) [.slice (some (anon 2)) (some (anon 3))],
        .namedCall ["inner"] [named "a" (anon 1), named "b" (anon 2) spelling]] do
      let expr := Advanced.Expr.namedCall ["outer"] [named "value" value spelling]
      count := count + (← roundTrip expr (Advanced.expressionParameters 256 expr))
  for source in ["f(=>1)", "f(:=1)", "f(x=>)", "f(x:=)", "f(x=>1,)", "f(,x=>1)",
      "f(x=>1 y=>2)", "f(x=>1,,y=>2)", "f(x.y=>1)", "f('x'=>1)",
      "f(select=>1)", "f(between=>1)", "f(x= >1)", "f(x: =1)", "f(x=>>1)",
      "f(x=>-?)", "f(x=>?!)", "COALESCE(x=>1)", "CAST(x=>1 AS INTEGER)"] do
    expectError source (Advanced.parseExpression source)
    count := count + 1
  rejectedRepresentation (.namedCall ["f"] []) "representation.named-call"
  rejectedRepresentation (.namedCall ["f"] [.positional 1]) "representation.named-call"
  rejectedRepresentation (.namedCall [] [named "x" 1]) "representation.function-name"
  rejectedRepresentation (.namedCall ["a","b","c","d"] [named "x" 1]) "representation.function-name"
  count := count + 4
  for expr in [Advanced.Expr.namedCall ["f"] [named "x" 1],
      .namedCall ["f"] [named "x" (anon 1) .assignment]] do
    match RenderContract.check .sqliteV01 (queryOf expr) with
    | .error (.unsupported diagnostic) =>
        SQLean.Tests.assert (diagnostic.code == "coverage.sqlite.named-function-arguments")
          "SQLite named-call boundary changed"
    | other => throw (IO.userError s!"SQLite admitted named notation: {reprStr (other.map (·.sql))}")
    count := count + 1
  for source in ["SELECT f(x=>1)", "SELECT f(x:=?)"] do
    expectError source (Advanced.parseSQLiteQuery source)
    count := count + 1
  let query := queryOf (.namedCall ["f"] [named "x" (anon 1)])
  match RenderContract.check .identityV01 query 0 with
  | .error (.inconclusive _) => pure ()
  | other => throw (IO.userError s!"named call ignored depth budget: {reprStr (other.map (·.sql))}")
  count := count + 1
  pure count

end SQLean.Tests
