import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

namespace SQLean.Tests

example : SelectContract.ExprValid [] .empty (.contextValue .currentSchema)
    (some ⟨.name, true⟩) [] := .contextValue
example : SelectContract.ExprValid [] .empty (.contextValue .currentUser)
    (some ⟨.name, false⟩) [] := .contextValue
example : SelectContract.ExprValid [] .empty (.contextValue .systemUser)
    (some ⟨.text, true⟩) [] := .contextValue
example : SelectContract.implicitCast .name .text = true := rfl
example : SelectContract.implicitCast .name (.varchar []) = false := rfl
example : SelectContract.implicitCast (.varchar [3]) .name = true := rfl
example : SelectContract.concreteType ⟨.array (.array .name), []⟩ = some (.array .name) := rfl
example : SelectContract.callSignature ["current_schema"] [] = some ⟨.name, true⟩ := rfl
example : SelectContract.callSignature ["system_user"] [] = some ⟨.text, true⟩ := rfl
example : SelectContract.conditionalBase [.known ⟨.name, false⟩, .known ⟨.text, false⟩] =
    some .name := rfl
example : SelectContract.conditionalBase [.known ⟨.text, false⟩, .known ⟨.name, false⟩] =
    some .text := rfl

private def contextField (id : String) (record : Lean.Json) (field : String) : IO String :=
  expectOk s!"{id}: {field}" ((record.getObjVal? field) >>= Lean.Json.getStr?)

private def contextCertificate (query : Advanced.Query)
    (params : SelectContract.ParameterEnv := []) (catalog : Advanced.Catalog := []) :
    IO (List SelectContract.OutputColumn) := do
  let certificate ← expectOk "context-value SELECT"
    ((SelectContract.checkQuery .basicV31 catalog params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let identity ← expectOk "context identity renderer"
    ((RenderContract.check .identityV01 query).mapError reprStr)
  let postgres ← expectOk "context PostgreSQL renderer"
    ((RenderContract.check .postgres16V01 query).mapError reprStr)
  have _identity : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
  have _postgres : Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
    postgres.roundTrip
  pure certificate.output

private def contextOutput (sql : String) (parameterTypes : String := "") :
    IO (List SelectContract.OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let params ← expectOk sql (Assurance.parseContractParameterTypes parameterTypes)
  contextCertificate query params

private def contextType (text : String) : IO SelectContract.ScalarType := do
  if text == "bpchar" then pure (.char [])
  else
    let declaration ← expectOk text (Advanced.parseDataType text)
    match SelectContract.concreteType declaration with
    | some base => pure base.unmodified
    | none => throw (IO.userError s!"unknown context inventory type {text}")

private def contextInventoryTests : IO Nat := do
  let functions ← expectOk "context function inventory"
    ((Lean.Json.parse (← IO.FS.readFile "fixtures/context_values/function_signatures.json")) >>= Lean.Json.getArr?)
  SQLean.Tests.assert (functions.size == 6) "six fixed context functions required"
  let mut observedFunctions : List (String × SelectContract.FunctionOverload) := []
  for record in functions do
    let name ← contextField "function" record "name"
    let inputs ← expectOk name ((record.getObjVal? "inputs") >>= Lean.Json.getArr?)
    let inputs ← inputs.toList.mapM fun input => do
      contextType (← expectOk name input.getStr?)
    let output ← contextType (← contextField name record "output")
    let selected : SelectContract.FunctionOverload := ⟨inputs, output⟩
    SQLean.Tests.assert (SelectContract.contextFunctionCatalog name == [selected] &&
      SelectContract.resolveOverload (SelectContract.functionCatalog name)
        (inputs.map fun base => .known ⟨base, false⟩) == some selected)
      s!"{name}: exact context function inputs/output"
    for nullable in [false, true] do
      let args := inputs.map fun base => SelectContract.ScalarInput.known ⟨base, nullable⟩
      let expected := name == "current_schema" || name == "system_user" || (!inputs.isEmpty && nullable)
      SQLean.Tests.assert (SelectContract.callSignature ["pg_catalog", name] args ==
        some ⟨output, expected⟩) s!"{name}: context nullability"
    observedFunctions := (name, selected) :: observedFunctions
  let expectedFunctions := SelectContract.contextFunctionNames.flatMap fun name =>
    (SelectContract.contextFunctionCatalog name).map (name, ·)
  SQLean.Tests.assert (decide observedFunctions.Nodup && expectedFunctions.all observedFunctions.contains &&
    observedFunctions.all expectedFunctions.contains) "exact context function inventory differs"
  let casts ← expectOk "NAME cast inventory"
    ((Lean.Json.parse (← IO.FS.readFile "fixtures/context_values/cast_signatures.json")) >>= Lean.Json.getArr?)
  SQLean.Tests.assert (casts.size == 6) "six NAME casts required"
  let mut observedCasts : List (SelectContract.ScalarType × SelectContract.ScalarType) := []
  for record in casts do
    let source ← contextType (← contextField "cast" record "source")
    let target ← contextType (← contextField "cast" record "target")
    let context ← contextField "cast" record "context"
    let function ← contextField "cast" record "function"
    let expectedContext := if source == .name && target != .text then "assignment" else "implicit"
    let expectedFunction := match target with
      | .name => "name" | .text => "text" | .char _ => "bpchar" | .varchar _ => "varchar" | _ => ""
    SQLean.Tests.assert (context == expectedContext && function == expectedFunction &&
      SelectContract.implicitCast source target == (context == "implicit") &&
      SelectContract.explicitCastAllowed source target &&
      SelectContract.implicitCast source.asArray target.asArray == (context == "implicit"))
      "NAME cast direction must distinguish implicit and assignment-only coercion"
    observedCasts := (source, target) :: observedCasts
  let expectedCasts : List (SelectContract.ScalarType × SelectContract.ScalarType) :=
    [(.name, .text), (.name, .char []), (.name, .varchar []),
     (.text, .name), (.char [], .name), (.varchar [], .name)]
  SQLean.Tests.assert (decide observedCasts.Nodup && expectedCasts.all observedCasts.contains &&
    observedCasts.all expectedCasts.contains) "NAME cast inventory differs"
  let operators ← expectOk "NAME operator inventory"
    ((Lean.Json.parse (← IO.FS.readFile "fixtures/context_values/operator_signatures.json")) >>= Lean.Json.getArr?)
  SQLean.Tests.assert (operators.size == 26) "eighteen comparisons and eight pattern declarations required"
  let mut observedOperators : List (String × SelectContract.ScalarType × SelectContract.ScalarType) := []
  for record in operators do
    let spelling ← contextField "operator" record "operator"
    let left ← contextType (← contextField spelling record "left")
    let right ← contextType (← contextField spelling record "right")
    let output ← contextType (← contextField spelling record "output")
    let function ← contextField spelling record "function"
    let selected : SelectContract.FunctionOverload := ⟨[left, right], .bool⟩
    SQLean.Tests.assert (output == .bool) "NAME operators return BOOLEAN"
    let op : Option Advanced.ComparisonOp := match spelling with
      | "=" => some .eq | "<>" => some .ne | "<" => some .lt | "<=" => some .le
      | ">" => some .gt | ">=" => some .ge | _ => none
    match op with
    | some op =>
        SQLean.Tests.assert (SelectContract.comparisonOverload op (.known ⟨left, false⟩)
          (.known ⟨right, false⟩) == some selected && SelectContract.rowBtreeCompatible selected &&
          SelectContract.quantifiedComparisonSignature op (.known ⟨left, false⟩)
            (.known ⟨right.asArray, false⟩) == some selected) "NAME exact comparison/row/quantified declaration"
        let stem := match op with | .eq => "eq" | .ne => "ne" | .lt => "lt" | .le => "le" | .gt => "gt" | .ge => "ge"
        let expected := if left == .name then "name" ++ stem ++ (if right == .text then "text" else "")
          else "text" ++ stem ++ "name"
        SQLean.Tests.assert (function == expected) "NAME comparison native identity"
    | none =>
        SQLean.Tests.assert (left == .name && right == .text) "NAME pattern declared arguments"
        let expected ← match spelling with
          | "~~" => pure "namelike"
          | "!~~" => pure "namenlike"
          | "!~~*" => pure "nameicnlike"
          | _ =>
              match SelectContract.stringMatchOperators.find? (·.toSql == spelling) with
              | none => throw (IO.userError s!"unknown NAME operator {spelling}")
              | some op =>
                  SQLean.Tests.assert (SelectContract.stringMatchSignature (.known ⟨left, false⟩)
                    (.known ⟨right, false⟩) == some selected) "NAME exact pattern signature"
                  match op.nativeFunctionName left with
                  | some function => pure function
                  | none => throw (IO.userError "unsupported pattern family")
        SQLean.Tests.assert (function == expected &&
          SelectContract.patternSignature (some ⟨left, false⟩) (some ⟨right, false⟩) ==
            some (some ⟨.bool, false⟩)) "NAME native pattern identity and Boolean result"
    observedOperators := (spelling, left, right) :: observedOperators
  let pairs : List (SelectContract.ScalarType × SelectContract.ScalarType) :=
    [(.name, .name), (.name, .text), (.text, .name)]
  let expectedOperators := (["=", "<>", "<", "<=", ">", ">="].flatMap fun op =>
    pairs.map fun (left, right) => (op, left, right)) ++
    ["~~", "!~~", "~~*", "!~~*", "~", "~*", "!~", "!~*"].map (·, .name, .text)
  SQLean.Tests.assert (decide observedOperators.Nodup && expectedOperators.all observedOperators.contains &&
    observedOperators.all expectedOperators.contains) "NAME operator fixture coverage differs"
  SQLean.Tests.assert (SelectContract.arrayPredicateSignature (.known ⟨.array .name, false⟩)
    (.known ⟨.array .name, false⟩) == some ⟨[.array .name, .array .name], .bool⟩)
    "NAME equality enables exact NAME-array predicates"
  pure (functions.size + casts.size + operators.size + 1)

def contextValuesContractTests : IO Nat := do
  let mut count ← contextInventoryTests
  let forms : List (String × String × SelectContract.ScalarType × Bool) := [
    ("CURRENT_SCHEMA", "current_schema", .name, true),
    ("CURRENT_SCHEMA()", "current_schema", .name, true),
    ("CURRENT_CATALOG", "current_catalog", .name, false),
    ("current_database()", "current_database", .name, false),
    ("CURRENT_USER", "current_user", .name, false), ("USER", "user", .name, false),
    ("CURRENT_ROLE", "current_role", .name, false), ("SESSION_USER", "session_user", .name, false),
    ("SYSTEM_USER", "system_user", .text, true),
    ("current_schemas(TRUE)", "current_schemas", .array .name, false),
    ("current_schemas(NULL)", "current_schemas", .array .name, true),
    ("pg_catalog.current_user()", "current_user", .name, false),
    ("\"session_user\"()", "session_user", .name, false),
    ("pg_catalog.system_user()", "system_user", .text, true)]
  for (expr, label, base, nullable) in forms do
    for projected in [expr, s!"CAST({expr} AS {base.dataType.toSql})",
        s!"CASE WHEN TRUE THEN {expr} ELSE {expr} END"] do
      SQLean.Tests.assert ((← contextOutput s!"SELECT {projected}") == [⟨label, ⟨base, nullable⟩⟩])
        s!"context exact native label/type/nullability: {projected}"
      count := count + 1
  let cases : List (String × SelectContract.ScalarType × Bool) := [
    ("COALESCE(CURRENT_SCHEMA, 'fallback')", .name, false),
    ("COALESCE('fallback', CURRENT_SCHEMA)", .name, false),
    ("COALESCE(CURRENT_SCHEMA, 'fallback'::TEXT)", .name, false),
    ("COALESCE('fallback'::TEXT, CURRENT_SCHEMA)", .text, false),
    ("COALESCE('a'::NAME, 'b'::CHAR(5))", .name, false),
    ("COALESCE('a'::CHAR(5), 'b'::NAME)", .name, false),
    ("ARRAY[CURRENT_SCHEMA, 'fallback'::TEXT]", .array .name, false),
    ("ARRAY['fallback'::TEXT, CURRENT_SCHEMA]", .array .text, false),
    ("ARRAY['a'::CHAR(5), CURRENT_SCHEMA]", .array .name, false),
    ("NULLIF(CURRENT_USER, 'x')", .name, true),
    ("NULLIF(CURRENT_USER, 'x'::TEXT)", .name, true),
    ("GREATEST(CURRENT_SCHEMA, 'fallback')", .name, false),
    ("CURRENT_SCHEMA || 1", .text, true),
    ("1 || CURRENT_USER", .text, false),
    ("length(CURRENT_USER)", .int32, false),
    ("length('abc'::BYTEA, 'UTF8'::NAME)", .int32, false),
    ("length(NULL::BYTEA, 'UTF8'::NAME)", .int32, true),
    ("'{}'::JSONB ? CURRENT_SCHEMA", .bool, true),
    ("'{}'::JSONB ?& ARRAY[CURRENT_SCHEMA]", .bool, false),
    ("'{}'::JSONB #> ARRAY[CURRENT_USER]", .jsonb, true),
    ("(current_schemas(FALSE))[1]", .name, true),
    ("(current_schemas(FALSE))[1:2]", .array .name, true),
    ("ARRAY[CURRENT_USER] || ARRAY['fallback'::TEXT]", .array .name, false),
    ("ARRAY['fallback'::TEXT] || ARRAY[CURRENT_USER]", .array .text, false)]
  for (expr, base, nullable) in cases do
    SQLean.Tests.assert ((← contextOutput s!"SELECT {expr} AS v") == [⟨"v", ⟨base, nullable⟩⟩])
      s!"NAME composition exact result: {expr}"
    count := count + 1
  for left in ["CURRENT_USER", "CURRENT_SCHEMA", "CAST(NULL AS NAME)"] do
    for right in ["'a'", "CAST('a' AS NAME)", "CAST('a' AS TEXT)", "CAST('a' AS CHAR(3))",
        "CAST('a' AS VARCHAR(3))", "NULL"] do
      for op in ["=", "<>", "<", "<=", ">", ">=", "LIKE", "NOT LIKE", "ILIKE", "NOT ILIKE", "~", "~*", "!~", "!~*"] do
        let expected := left != "CURRENT_USER" || right == "NULL"
        SQLean.Tests.assert ((← contextOutput s!"SELECT {left} {op} {right} AS v") ==
          [⟨"v", ⟨.bool, expected⟩⟩]) s!"NAME comparison/pattern composition: {left} {op} {right}"
        count := count + 1
  for (expr, params, base, nullable) in [
      ("$1", "NAME", SelectContract.ScalarType.name, false),
      ("$1", "NAME?", .name, true),
      ("$1", "NAME[][]", .array .name, false),
      ("COALESCE(CURRENT_SCHEMA, ?)", "NAME", .name, false),
      ("? || CURRENT_USER || ?", "NAME,TEXT", .text, false),
      ("current_schemas(?)", "BOOLEAN?", .array .name, true),
      ("ARRAY[CURRENT_USER, ?] @> ARRAY[?]", "NAME,NAME", .bool, false),
      ("ROW(CURRENT_USER, $2) = ROW($1, $2)", "NAME,INTEGER", .bool, true),
      ("CURRENT_USER = ANY($1)", "NAME[]", .bool, true),
      ("CURRENT_USER = ANY($1)", "TEXT[]", .bool, true)] do
    SQLean.Tests.assert ((← contextOutput s!"SELECT {expr} AS v" params) == [⟨"v", ⟨base, nullable⟩⟩])
      s!"NAME exact binding and lexical parameter transport: {expr}"
    count := count + 1
  for sql in ["SELECT CURRENT_USER + 1", "SELECT current_schemas(1)",
      "SELECT pg_catalog.current_schema(1)", "SELECT pg_catalog.system_user(TRUE)",
      "SELECT CURRENT_USER = 1", "SELECT CURRENT_USER ~ 1",
      "SELECT ARRAY[CURRENT_USER] = ARRAY['x'::TEXT]",
      "SELECT ARRAY[CURRENT_USER] @> ARRAY['x'::TEXT]"] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV31 [] [] query with
    | .error (.invalid _) => pure ()
    | other => throw (IO.userError s!"expected Invalid for concrete incompatible NAME query {sql}: {reprStr (other.map (fun _ => ())) }")
    count := count + 1
  for sql in ["SELECT application.current_schema()", "SELECT current_setting('role')",
      "SELECT version()", "SELECT CURRENT_USER = (SELECT CURRENT_USER)"] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV31 [] [] query with
    | .error (.unsupported _) => pure ()
    | _ => throw (IO.userError s!"unmodeled context dependency must remain Unsupported: {sql}")
    count := count + 1
  for modifiers in [[1], [0], [1, 2]] do
    let query : Advanced.Query := {body := .select {items := [.expression (.cast .null ⟨.name, modifiers⟩)]}}
    match SelectContract.checkQuery .basicV31 [] [] query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError "NAME never admits declaration modifiers")
    count := count + 1
  let catalog : Advanced.Catalog := [{name := "names", columns := [
    {name := "n", type := ⟨.name, []⟩, nullable := some false},
    {name := "ns", type := ⟨.array .name, []⟩}]}]
  let query ← expectOk "NAME source columns" (Advanced.parseQuery
    "SELECT n, ns, n = CURRENT_USER AS equal_user FROM names")
  SQLean.Tests.assert ((← contextCertificate query [] catalog) ==
    [⟨"n", ⟨.name, false⟩⟩, ⟨"ns", ⟨.array .name, true⟩⟩, ⟨"equal_user", ⟨.bool, false⟩⟩])
    "exact NAME catalog columns remain distinct from TEXT"
  let bare : Advanced.Query := {body := .select {items := [.expression (.contextValue .currentUser)]}}
  match SelectContract.checkQuery .basicV31 [] [] bare 0 with
  | .error (.inconclusive _) => pure ()
  | _ => throw (IO.userError "context resource exhaustion must remain Inconclusive")
  pure (count + 2)

private def contextOutputLabel (base : SelectContract.ScalarType) : String :=
  match base with
  | .int32 => "int32" | .bool => "bool" | .text => "text" | .char [] => "bpchar"
  | .array element => contextOutputLabel element ++ "[]"
  | base => base.dataType.toSql.toLower.replace ", " ","

def contextValuesCorpusTests : IO Nat := do
  let records ← expectOk "context synthetic records"
    ((Lean.Json.parse (← IO.FS.readFile "fixtures/context_values/synthetic.json")) >>= Lean.Json.getArr?)
  SQLean.Tests.assert (records.size == 50) "expected fifty authored context queries"
  let mut ids : List String := []
  let mut statements : List String := []
  for record in records do
    let id ← contextField "synthetic" record "id"
    let sql ← contextField id record "sql"
    SQLean.Tests.assert ((← contextField id record "source_kind") == "synthetic") s!"{id}: population"
    let parameters ← contextField id record "parameter_types"
    let expected ← expectOk id ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
    let expected ← expected.toList.mapM fun column => do
      let name ← contextField id column "name"
      let type ← contextField id column "type"
      let nullable ← expectOk id ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
      pure (name, type, nullable)
    let actual ← contextOutput sql parameters
    let labels := actual.map fun column =>
      (column.name, contextOutputLabel column.type.base, column.type.nullable)
    SQLean.Tests.assert (labels == expected) s!"{id}: exact context output {reprStr labels}; expected {reprStr expected}"
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (decide ids.Nodup && decide statements.Nodup) "duplicate context fixture identities or SQL"
  pure records.size

/-- Eligibility and output metadata are authored before running the checker.
Thirteen closed source queries obtain full certificates; the other thirty-seven
retain rendering certificates without invented schemas/session-helper contracts. -/
def contextValuesConcreteContractTests : IO Nat := do
  let registered : List (String × List SelectContract.OutputColumn) := [
    ("context_values:postgres:src/test/regress/sql/expressions.sql:statement-12", [⟨"?column?", ⟨.bool, false⟩⟩]),
    ("context_values:postgres:src/test/regress/sql/expressions.sql:statement-13", [⟨"current_schema", ⟨.name, true⟩⟩]),
    ("context_values:postgres:src/test/regress/sql/guc.sql:statement-156", [⟨"?column?", ⟨.bool, false⟩⟩]),
    ("context_values:postgres:src/test/regress/sql/privileges.sql:statement-150", [⟨"session_user", ⟨.name, false⟩⟩, ⟨"current_user", ⟨.name, false⟩⟩]),
    ("context_values:postgres:src/test/regress/sql/temp.sql:statement-160", [⟨"is_temp_schema", ⟨.bool, true⟩⟩]),
    ("context_values:materialize:test/sqllogictest/current_database.slt:sqllogic-query-12", [⟨"current_database", ⟨.name, false⟩⟩]),
    ("context_values:materialize:test/sqllogictest/schemas.slt:sqllogic-query-41", [⟨"current_schema", ⟨.name, true⟩⟩]),
    ("context_values:duckdb:test/sql/pg_catalog/system_functions.test:sqllogic-query-6", [⟨"current_user", ⟨.name, false⟩⟩]),
    ("context_values:duckdb:test/sql/pg_catalog/system_functions.test:sqllogic-query-11", [⟨"current_catalog", ⟨.name, false⟩⟩]),
    ("context_values:duckdb:test/sql/pg_catalog/system_functions.test:sqllogic-query-26", [⟨"user", ⟨.name, false⟩⟩]),
    ("context_values:duckdb:test/sql/pg_catalog/system_functions.test:sqllogic-query-31", [⟨"session_user", ⟨.name, false⟩⟩]),
    ("context_values:pgweb:pkg/client/client.go:go-string-15103", [⟨"current_user", ⟨.name, false⟩⟩, ⟨"current_database", ⟨.name, false⟩⟩]),
    ("context_values:river:riverdriver/riverpgxv5/river_pgx_v5_driver.go:go-string-44649", [⟨"coalesce", ⟨.name, false⟩⟩])]
  let expectedIds : List String := [
    "context_values:postgres:contrib/pg_stat_statements/sql/user_activity.sql:statement-15",
    "context_values:postgres:contrib/postgres_fdw/sql/postgres_fdw.sql:statement-1828",
    "context_values:postgres:contrib/postgres_fdw/sql/postgres_fdw.sql:statement-1831",
    "context_values:postgres:src/test/regress/sql/expressions.sql:statement-12",
    "context_values:postgres:src/test/regress/sql/expressions.sql:statement-13",
    "context_values:postgres:src/test/regress/sql/guc.sql:statement-156",
    "context_values:postgres:src/test/regress/sql/privileges.sql:statement-100",
    "context_values:postgres:src/test/regress/sql/privileges.sql:statement-116",
    "context_values:postgres:src/test/regress/sql/privileges.sql:statement-150",
    "context_values:postgres:src/test/regress/sql/privileges.sql:statement-696",
    "context_values:postgres:src/test/regress/sql/privileges.sql:statement-697",
    "context_values:postgres:src/test/regress/sql/privileges.sql:statement-698",
    "context_values:postgres:src/test/regress/sql/privileges.sql:statement-699",
    "context_values:postgres:src/test/regress/sql/privileges.sql:statement-700",
    "context_values:postgres:src/test/regress/sql/privileges.sql:statement-701",
    "context_values:postgres:src/test/regress/sql/privileges.sql:statement-702",
    "context_values:postgres:src/test/regress/sql/privileges.sql:statement-709",
    "context_values:postgres:src/test/regress/sql/privileges.sql:statement-710",
    "context_values:postgres:src/test/regress/sql/privileges.sql:statement-711",
    "context_values:postgres:src/test/regress/sql/privileges.sql:statement-712",
    "context_values:postgres:src/test/regress/sql/privileges.sql:statement-713",
    "context_values:postgres:src/test/regress/sql/privileges.sql:statement-714",
    "context_values:postgres:src/test/regress/sql/privileges.sql:statement-715",
    "context_values:postgres:src/test/regress/sql/privileges.sql:statement-721",
    "context_values:postgres:src/test/regress/sql/privileges.sql:statement-722",
    "context_values:postgres:src/test/regress/sql/privileges.sql:statement-723",
    "context_values:postgres:src/test/regress/sql/privileges.sql:statement-724",
    "context_values:postgres:src/test/regress/sql/privileges.sql:statement-725",
    "context_values:postgres:src/test/regress/sql/privileges.sql:statement-726",
    "context_values:postgres:src/test/regress/sql/privileges.sql:statement-727",
    "context_values:postgres:src/test/regress/sql/rules.sql:statement-128",
    "context_values:postgres:src/test/regress/sql/temp.sql:statement-160",
    "context_values:river:riverdriver/riverpgxv5/internal/dbsqlc/pg_misc.sql.go:pGNotifyMany",
    "context_values:river:riverdriver/riverpgxv5/internal/dbsqlc/schema.sql.go:columnExists",
    "context_values:river:riverdriver/riverpgxv5/internal/dbsqlc/schema.sql.go:indexExists",
    "context_values:materialize:test/sqllogictest/current_database.slt:sqllogic-query-12",
    "context_values:materialize:test/sqllogictest/schemas.slt:sqllogic-query-41",
    "context_values:duckdb:test/sql/pg_catalog/system_functions.test:sqllogic-query-6",
    "context_values:duckdb:test/sql/pg_catalog/system_functions.test:sqllogic-query-11",
    "context_values:duckdb:test/sql/pg_catalog/system_functions.test:sqllogic-query-26",
    "context_values:duckdb:test/sql/pg_catalog/system_functions.test:sqllogic-query-31",
    "context_values:risingwave:e2e_test/batch/keyword/user.slt:sqllogic-query-10",
    "context_values:pgweb:pkg/client/client.go:go-string-15103",
    "context_values:pgweb:pkg/statements/sql.go:go-string-946",
    "context_values:pgweb:pkg/statements/sql.go:go-string-1028",
    "context_values:pgweb:pkg/statements/sql.go:go-string-1207",
    "context_values:pgweb:pkg/statements/sql.go:go-string-1931",
    "context_values:pgweb:pkg/statements/sql/info.sql:whole-file",
    "context_values:pgweb:pkg/statements/sql/info_simple.sql:whole-file",
    "context_values:river:riverdriver/riverpgxv5/river_pgx_v5_driver.go:go-string-44649"]
  SQLean.Tests.assert (registered.length == 13 && expectedIds.length == 50 &&
    decide expectedIds.Nodup && decide (registered.map Prod.fst).Nodup)
    "fixed context source registry must be unique"
  let source ← IO.FS.readFile "fixtures/context_values/concrete.jsonl"
  let lines := (source.splitOn "\n").filter (fun line => !line.trimAscii.toString.isEmpty)
  SQLean.Tests.assert (lines.length == 50) "expected fifty original context queries"
  let mut ids : List String := []
  let mut statements : List String := []
  let mut certified := 0
  let mut positions := 0
  for line in lines do
    let record ← expectOk "context source" (Lean.Json.parse line)
    let id ← contextField "source" record "id"
    let sql ← contextField id record "sql"
    SQLean.Tests.assert (expectedIds.contains id &&
      (← contextField id record "raw_sql") == sql) s!"{id}: unregistered or changed source"
    let query ← expectOk id (Advanced.parseQuery sql)
    let slots ← expectOk id ((record.getObjVal? "observed_parameter_slots") >>= Lean.Json.getArr?)
    let slots ← slots.toList.mapM fun slot => expectOk id slot.getNat?
    let expectedSlots : List Nat :=
      if id.endsWith ":pGNotifyMany" then [1, 2, 3]
      else if id.endsWith ":columnExists" || id.endsWith ":indexExists" then [1, 2]
      else []
    SQLean.Tests.assert (slots == expectedSlots &&
      (Advanced.queryParameters 1024 query).all (fun parameter => match parameter with
        | .numbered n => expectedSlots.contains n | .anonymous _ => false) &&
      expectedSlots.all (fun n => (Advanced.queryParameters 1024 query).contains (.numbered n)))
      s!"{id}: source parameter inventory changed"
    match registered.find? (fun entry => entry.1 == id) with
    | some (_, expected) =>
        let observations ← expectOk id (record.getObjVal? "observed_syntax")
        let sourceFree ← expectOk id ((observations.getObjVal? "source_free") >>= Lean.Json.getBool?)
        SQLean.Tests.assert (sourceFree && query.ctes.isEmpty && expectedSlots.isEmpty)
          s!"{id}: fixed closed source scope changed"
        match query.body with
        | .select select => SQLean.Tests.assert select.source.isNone s!"{id}: closed source acquired FROM"
        | _ => throw (IO.userError s!"{id}: closed source body changed")
        SQLean.Tests.assert ((← contextCertificate query) == expected)
          s!"{id}: exact original-source full certificate"
        certified := certified + 1
        positions := positions + expected.length
    | none =>
        let identity ← expectOk id ((RenderContract.check .identityV01 query).mapError reprStr)
        let postgres ← expectOk id ((RenderContract.check .postgres16V01 query).mapError reprStr)
        have _identity := identity.roundTrip
        have _postgres := postgres.roundTrip
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (certified == 13 && positions == 15 && decide ids.Nodup &&
    decide statements.Nodup && expectedIds.all ids.contains)
    "all registered original sources and fifteen certified columns must be present exactly once"
  pure certified

end SQLean.Tests
