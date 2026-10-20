import SQLean.RenderContract.Checker
import SQLean.RenderContract.TranslationProofs
import SQLean.RenderContract.ValidityPreservation
import SQLean.AdvancedQueryValidation
import Tests.Support

/-! Bare context values retain their native keyword and output label. Ordinary
calls retain quoted component identity, including forms that are syntactically
valid but have no builtin overload. NAME remains an exact type, never TEXT. -/
namespace SQLean.Tests
open Advanced RenderContract

private def queryOf (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr]}}
private def anon (n : Nat) : Advanced.Expr := .parameter (.anonymous n)

example (value : ContextValue) : translateExpr (.contextValue value) = .contextValue value := by
  rw [translateExpr]

example : Admissible (queryOf (.contextValue .currentSchema)) := by
  refine ⟨{depth := 4}, ?_, ?_, ?_⟩
  · unfold queryOf inspectQuery
    dsimp
    unfold inspectSelect
    dsimp
    unfold inspectItem inspectExpr
    rfl
  · decide
  · decide

example (value : ContextValue) :
    SelectContract.ExprValid params scope (translateExpr (.contextValue value))
      (some (SelectContract.contextValueType value)) [] := by
  simpa only [List.map_nil] using
    expr_valid_translated (SelectContract.ExprValid.contextValue (value := value)
      (params := params) (scope := scope))

private def roundTrip (expr : Advanced.Expr) (uses : List Parameter) : IO Nat := do
  let query := queryOf expr
  for profile in [RenderContract.Profile.identityV01, .postgres16V01] do
    let cert ← expectOk "context rendering" ((RenderContract.check profile query).mapError reprStr)
    SQLean.Tests.assert (cert.footprint.parameters == uses) "context value allocated or lost bindings"
    let parsed ← expectOk cert.sql (parseRendered profile cert.sql)
    SQLean.Tests.assert (decide (parsed = expectedQuery profile query))
      "context value or NAME identity changed during canonical rendering"
    let again ← expectOk "context canonical" ((RenderContract.check profile parsed).mapError reprStr)
    SQLean.Tests.assert (again.sql == cert.sql) "context canonical bytes changed"
    for parameter in uses do
      SQLean.Tests.assert
        (cert.transport reprStr (parameterSlot parameter) == reprStr parameter)
        "context query parameter transport changed its value"
  SQLean.Tests.assert (Advanced.queryParameters 256 query == uses) "coarse context parameter traversal"
  pure 2

private def parsed (sql : String) (expected : Advanced.Expr) : IO Unit := do
  let expr ← expectOk sql (Advanced.parseExpression sql)
  SQLean.Tests.assert (decide (expr = expected)) s!"context expression shape: {sql}"

private def sqliteExcluded (expr : Advanced.Expr) (code : String) : IO Unit := do
  match RenderContract.check .sqliteV01 (queryOf expr) with
  | .error (.unsupported diagnostic) =>
      SQLean.Tests.assert (diagnostic.code == code) s!"SQLite context boundary: {diagnostic.code}"
  | other => throw (IO.userError s!"SQLite context unexpectedly admitted: {reprStr (other.map (·.sql))}")

def contextValuesRenderingTests : IO Nat := do
  let mut count := 0
  let values := [(ContextValue.currentSchema, "CURRENT_SCHEMA"), (.currentCatalog, "CURRENT_CATALOG"),
    (.currentUser, "CURRENT_USER"), (.user, "USER"), (.currentRole, "CURRENT_ROLE"),
    (.sessionUser, "SESSION_USER"), (.systemUser, "SYSTEM_USER")]
  for (value, keyword) in values do
    let expr := Advanced.Expr.contextValue value
    parsed keyword expr
    parsed keyword.toLower expr
    SQLean.Tests.assert (expr.toSql == keyword) "bare context keyword was printed as a function/column"
    count := count + 3 + (← roundTrip expr [])
    sqliteExcluded expr "coverage.sqlite.context-value"
    count := count + 1
    for source in [s!"SELECT 1 AS {keyword}", s!"SELECT 1 {keyword}"] do
      let query ← expectOk source (Advanced.parseQuery source)
      SQLean.Tests.assert (decide (query = {body := .select {
        items := [.expression 1 (some keyword.toLower)]}}))
        "native keyword output alias was rejected or mistaken for a value"
      count := count + 1
    parsed ("\"" ++ keyword.toLower ++ "\"") (.column none keyword.toLower)
    parsed ("t." ++ keyword.toLower) (.column (some "t") keyword.toLower)
    count := count + 2
    for expr in [Advanced.Expr.concat (.cast expr ⟨.text, []⟩) (anon 1),
        .caseExpr none [(.literal (.bool true), anon 1)] (some expr),
        .binary .eq expr (anon 1)] do
      count := count + (← roundTrip expr [.anonymous 1])
  for (sql, names, args) in [
      ("current_schema()", ["current_schema"], []),
      ("current_schema(1)", ["current_schema"], [Advanced.Expr.literal (.int 1)]),
      ("current_database()", ["current_database"], []),
      ("current_schemas(TRUE)", ["current_schemas"], [.literal (.bool true)]),
      ("\"current_user\"()", ["current_user"], []),
      ("\"session_user\"()", ["session_user"], []),
      ("\"system_user\"()", ["system_user"], []),
      ("\"user\"()", ["user"], []),
      ("\"current_role\"()", ["current_role"], []),
      ("\"current_catalog\"()", ["current_catalog"], []),
      ("\"CURRENT_SCHEMA\"()", ["CURRENT_SCHEMA"], []),
      ("pg_catalog.current_schema()", ["pg_catalog", "current_schema"], []),
      ("\"pg_catalog\".\"current_user\"()", ["pg_catalog", "current_user"], [])] do
    parsed sql (.call names args)
    count := count + 1 + (← roundTrip (.call names args) [])
  for source in ["CURRENT_CATALOG()", "CURRENT_USER()", "USER()", "CURRENT_ROLE()",
      "SESSION_USER()", "SYSTEM_USER()", "CURRENT_SCHEMA(,)", "CURRENT_SCHEMA.x",
      "CURRENT_SCHEMA[1]", "CURRENT_SCHEMA(*)"] do
    expectError source (Advanced.parseExpression source)
    count := count + 1
  expectError "FROM context value is a separate native table-function form"
    (Advanced.parseQuery "SELECT 1 FROM CURRENT_SCHEMA")
  count := count + 1
  for (source, type) in [("NAME", DataType.mk .name []),
      ("NAME[]", ⟨.array .name, []⟩), ("NAME[][]", ⟨.array (.array .name), []⟩)] do
    let actual ← expectOk source (Advanced.parseDataType source)
    SQLean.Tests.assert (actual == type) "NAME declaration or array rank lost"
    SQLean.Tests.assert (actual.toSql == source) "NAME rendered as a different type"
    count := count + 2 + (← roundTrip (.cast (anon 1) type) [.anonymous 1])
    sqliteExcluded (.cast (anon 1) type)
      (if type.name.isArray then "coverage.sqlite.array-type" else "coverage.sqlite.PostgreSQL-type")
    count := count + 1
  parsed "NAME 'O''Brien'" (.cast (.literal (.text "O'Brien")) ⟨.name, []⟩)
  parsed "name" (.column none "name")
  for source in ["NAME(1)", "NAME(63)", "NAME(1)[]"] do
    expectError source (Advanced.parseDataType source)
  let declarations ← expectOk "NAME parameter declarations"
    (Advanced.parseParameterDeclarations "name?, name[], text")
  SQLean.Tests.assert (declarations == [(⟨.name, []⟩, true), (⟨.array .name, []⟩, false),
    (⟨.text, []⟩, false)]) "NAME metadata was collapsed to TEXT"
  SQLean.Tests.assert (DataType.ofSqlType (.opaque .pgName) == ⟨.name, []⟩)
    "compatibility catalog erased NAME"
  let malformed := queryOf (.cast (.contextValue .currentUser) ⟨.name, [3]⟩)
  match RenderContract.check .postgres16V01 malformed with
  | .error (.invalid diagnostic) =>
      SQLean.Tests.assert (diagnostic.code == "representation.type-modifiers") "NAME invalid modifiers"
  | _ => throw (IO.userError "NAME modifiers unexpectedly admitted")
  pure (count + 8)

end SQLean.Tests
