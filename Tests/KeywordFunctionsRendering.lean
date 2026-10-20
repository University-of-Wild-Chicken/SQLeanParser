import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import SQLean.RenderContract.ValidityPreservation
import SQLean.SelectContract.Checker
import SQLean.AdvancedQueryValidation
import Tests.Support

/-! PostgreSQL's TYPE_FUNC_NAME_KEYWORD category is a function-head permission,
not a blanket permission for column or schema names. LEFT/RIGHT retain the
ordinary call node; unknown keyword routines remain structurally renderable. -/
namespace SQLean.Tests
open Advanced RenderContract

private def queryOf (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr]}}
private def anon (n : Nat) : Advanced.Expr := .parameter (.anonymous n)
private def text (value : String) : Advanced.Expr := .literal (.text value)

example (name : List Name) (args : List Advanced.Expr) :
    translateExpr (.call name args) = .call name (args.map translateExpr) := by
  simp only [translateExpr, List.attach_map_val]

private def roundTrip (expr : Advanced.Expr) (uses : List Parameter) : IO Nat := do
  let query := queryOf expr
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    let cert ← expectOk "keyword function rendering" ((RenderContract.check profile query).mapError reprStr)
    SQLean.Tests.assert (cert.footprint.parameters == uses) "keyword function changed lexical binding order"
    let parsed ← expectOk cert.sql (parseRendered profile cert.sql)
    SQLean.Tests.assert (decide (parsed = expectedQuery profile query))
      "keyword function lost decoded name identity or argument order"
    let again ← expectOk "keyword function canonical" ((RenderContract.check profile parsed).mapError reprStr)
    SQLean.Tests.assert (again.sql == cert.sql) "keyword function canonical spelling changed"
    for parameter in uses do
      SQLean.Tests.assert (cert.transport reprStr (parameterSlot parameter) == reprStr parameter)
        "keyword function transport changed a parameter"
  SQLean.Tests.assert (Advanced.queryParameters 256 query == uses) "expanded keyword-call traversal lost bindings"
  pure 2

private def parsed (source : String) (expected : Advanced.Expr) : IO Unit := do
  let expr ← expectOk source (Advanced.parseExpression source)
  SQLean.Tests.assert (decide (expr = expected)) s!"keyword function AST mismatch: {source}"

private def unsupported (expr : Advanced.Expr) : IO Unit := do
  match SelectContract.checkQuery .basicV28 [] [] (queryOf expr) with
  | .error (.unsupported _) => pure ()
  | result => throw (IO.userError s!"unknown keyword function acquired static validity: {reprStr (result.map (·.output))}")

/-- Exact pinned PG16 TYPE_FUNC_NAME_KEYWORD population. CURRENT_SCHEMA also
has a distinct bare SQL value form; every other bare member remains invalid. -/
private def keywordHeads : List String :=
  ["authorization", "binary", "collation", "concurrently", "cross", "current_schema",
   "freeze", "full", "ilike", "inner", "is", "isnull", "join", "left", "like", "natural",
   "notnull", "outer", "overlaps", "right", "similar", "tablesample", "verbose"]

def keywordFunctionsRenderingTests : IO Nat := do
  let mut count := 0
  for name in keywordHeads do
    SQLean.Tests.assert ((SQLean.PostgresGrammar.Generated.keyword name).any
      (fun keyword => keyword.category == "TYPE_FUNC_NAME_KEYWORD")) "pinned keyword category drift"
    parsed (name ++ "(1)") (.call [name] [1])
    parsed (name.toUpper ++ " /*gap*/ (1)") (.call [name] [1])
    parsed ("\"" ++ name ++ "\"(1)") (.call [name] [1])
    parsed ("pg_catalog." ++ name ++ "(1)") (.call ["pg_catalog", name] [1])
    parsed ("\"" ++ name ++ "\".f(1)") (.call [name, "f"] [1])
    parsed ("t." ++ name) (.column (some "t") name)
    count := count + 7 + (← roundTrip (.call [name] [1]) [])
    if name != "current_schema" then
      expectError ("bare " ++ name) (Advanced.parseExpression name)
      count := count + 1
    for source in [name ++ ".f(1)", name ++ ".x", name ++ "[1]"] do
      expectError source (Advanced.parseExpression source)
      count := count + 1
    if name != "current_schema" && name != "left" && name != "right" then
      unsupported (.call [name] [1])
      count := count + 1
  parsed "CURRENT_SCHEMA" (.contextValue .currentSchema)
  parsed "CURRENT_SCHEMA()" (.call ["current_schema"] [])
  count := count + 2
  for name in ["left", "right"] do
    for args in [[text "aλbc", 2], [text "", .unary .neg 2], [.null, 1],
        [anon 1, anon 2], [.call ["left"] [anon 1, anon 2], anon 3]] do
      let expr := Advanced.Expr.call [name] args
      count := count + (← roundTrip expr (Advanced.expressionParameters 256 expr))
    for callee in [[name], ["pg_catalog", name]] do
      let expr := Advanced.Expr.call callee [text "abcdef", 2]
      let cert ← expectOk "LEFT/RIGHT exact validity" ((SelectContract.checkQuery .basicV28 [] [] (queryOf expr)).mapError reprStr)
      SQLean.Tests.assert (cert.output == [⟨name, ⟨.text, false⟩⟩]) "keyword function label/type changed"
      count := count + 1
    let uppercase := name.toUpper
    parsed ("\"" ++ uppercase ++ "\"('abc',1)") (.call [uppercase] [text "abc", 1])
    unsupported (.call [uppercase] [text "abc", 1])
    unsupported (.call ["custom", name] [text "abc", 1])
    count := count + 3 + (← roundTrip (.call [uppercase] [text "abc", 1]) [])
    for source in [name ++ "(,)", name ++ "('x',)", name ++ "('x' 1)", name ++ "(*)"] do
      expectError source (Advanced.parseExpression source)
      count := count + 1
    parsed (name ++ "(x=>?)") (.namedCall [name] [.named "x" (anon 1)])
    match SelectContract.checkQuery .basicV28 [] []
        (queryOf (.namedCall [name] [.named "x" (text "abc")])) with
    | .error (.unsupported _) => pure ()
    | result => throw (IO.userError s!"keyword named call bypassed explicit signature metadata: {reprStr (result.map (·.output))}")
    count := count + 2
    match RenderContract.check .sqliteV01 (queryOf (.call [name] [text "abc", 1])) with
    | .error (.unsupported diagnostic) =>
        SQLean.Tests.assert (diagnostic.code == "coverage.sqlite.scalar-function-signatures")
          "SQLite silently acquired PostgreSQL keyword functions"
    | result => throw (IO.userError s!"SQLite keyword function admitted: {reprStr (result.map (·.sql))}")
    count := count + 1
  -- Clause keywords retain native roles after keyword function parsing.
  for source in ["SELECT left('abc',1) AS v FROM users WHERE id = 1",
      "SELECT right('abc',1) FROM users LEFT JOIN teams ON users.id = teams.id",
      "SELECT left('abc',1) AS left", "SELECT right('abc',1) right"] do
    let _ ← expectOk source (Advanced.parseQuery source)
    count := count + 1
  for source in ["SELECT left FROM users", "SELECT right.x FROM users",
      "SELECT 1 FROM left", "SELECT 1 FROM right AS r"] do
    expectError source (Advanced.parseQuery source)
    count := count + 1
  pure count

end SQLean.Tests
