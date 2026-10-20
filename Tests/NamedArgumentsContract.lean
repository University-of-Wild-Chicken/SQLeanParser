import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

namespace SQLean.Tests

example : SelectContract.ArgumentAssignments ["first", "second"] 0 false
    [some "second", some "first"] [.unknown false, .unknown true]
    [(1, .unknown false), (0, .unknown true)] :=
  .named rfl (.named rfl .nil)

example : SelectContract.ArgumentAssignments ["first", "second"] 0 false
    [none, some "second"] [.unknown false, .unknown true]
    [(0, .unknown false), (1, .unknown true)] :=
  .positional (by decide) (.named rfl .nil)

example : SelectContract.ArgumentSlot [] 0
    ⟨"years", .int32, some .intZero⟩ (.known ⟨.int32, false⟩) := .defaulted (value := .intZero) rfl rfl

example : SelectContract.makeIntervalSignature
    (SelectContract.makeIntervalParameters.map fun parameter =>
      .known ⟨parameter.type, false⟩) = some ⟨.interval [], false⟩ := rfl

private def defaultIntervalInputs : List SelectContract.ScalarInput :=
  [.known ⟨.int32, false⟩, .known ⟨.int32, false⟩, .known ⟨.int32, false⟩,
   .known ⟨.int32, false⟩, .known ⟨.int32, false⟩, .known ⟨.int32, false⟩,
   .known ⟨.doublePrecision, false⟩]

private theorem defaultIntervalBinding : SelectContract.ArgumentsBound
    SelectContract.makeIntervalParameters [] [] defaultIntervalInputs :=
  .intro .nil (by decide)
    (.cons (.defaulted (value := .intZero) rfl rfl)
      (.cons (.defaulted (value := .intZero) rfl rfl)
        (.cons (.defaulted (value := .intZero) rfl rfl)
          (.cons (.defaulted (value := .intZero) rfl rfl)
            (.cons (.defaulted (value := .intZero) rfl rfl)
              (.cons (.defaulted (value := .intZero) rfl rfl)
                (.cons (.defaulted (value := .floatZero) rfl rfl) .nil)))))))

example : SelectContract.ExprValid [] .empty (.call ["make_interval"] [])
    (some ⟨.interval [], false⟩) [] :=
  .defaultCall .nil rfl defaultIntervalBinding rfl

private theorem namedIntervalBinding : SelectContract.ArgumentsBound
    SelectContract.makeIntervalParameters [some "days"] [.known ⟨.int32, false⟩]
    defaultIntervalInputs :=
  .intro (.named (index := 3) rfl .nil) (by decide)
    (.cons (.defaulted (value := .intZero) rfl rfl)
      (.cons (.defaulted (value := .intZero) rfl rfl)
        (.cons (.defaulted (value := .intZero) rfl rfl)
          (.cons (.supplied rfl)
            (.cons (.defaulted (value := .intZero) rfl rfl)
              (.cons (.defaulted (value := .intZero) rfl rfl)
                (.cons (.defaulted (value := .floatZero) rfl rfl) .nil)))))))

example : SelectContract.ExprValid [] .empty
    (.namedCall ["make_interval"] [.named "days" (.literal (.int 1))])
    (some ⟨.interval [], false⟩) [] :=
  .namedCall (.cons (.int (by decide)) .nil) rfl namedIntervalBinding rfl

private def namedField (id : String) (record : Lean.Json) (field : String) : IO String :=
  expectOk s!"{id}: {field}" ((record.getObjVal? field) >>= Lean.Json.getStr?)

private def namedCertificate (query : Advanced.Query)
    (params : SelectContract.ParameterEnv := []) : IO (List SelectContract.OutputColumn) := do
  let certificate ← expectOk "named/default SELECT"
    ((SelectContract.checkQuery .basicV26 [] params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let identity ← expectOk "named identity renderer"
    ((RenderContract.check .identityV01 query).mapError reprStr)
  let postgres ← expectOk "named PostgreSQL renderer"
    ((RenderContract.check .postgres16V01 query).mapError reprStr)
  have _identity : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
  have _postgres : Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
    postgres.roundTrip
  pure certificate.output

private def namedOutput (sql : String) (parameterTypes : String := "") :
    IO (List SelectContract.OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let params ← expectOk sql (Assurance.parseContractParameterTypes parameterTypes)
  namedCertificate query params

private def namedInventoryTests : IO Nat := do
  let records ← expectOk "named function declaration"
    ((Lean.Json.parse (← IO.FS.readFile "fixtures/named_arguments/function_signatures.json")) >>= Lean.Json.getArr?)
  SQLean.Tests.assert (records.size == 1) "one admitted defaulted named function declaration"
  let record := records[0]!
  let name ← namedField "inventory" record "name"
  let strings := fun field => do
    let values ← expectOk field ((record.getObjVal? field) >>= Lean.Json.getArr?)
    values.toList.mapM fun value => expectOk field value.getStr?
  let names ← strings "names"
  let inputNames ← strings "inputs"
  let defaults ← strings "defaults"
  let outputName ← namedField name record "output"
  let parseType := fun text => do
    let declaration ← expectOk text (Advanced.parseDataType text)
    match SelectContract.concreteType declaration with
    | some base => pure base.unmodified
    | none => throw (IO.userError s!"unsupported named declaration type: {text}")
  let inputs ← inputNames.mapM parseType
  let output ← parseType outputName
  SQLean.Tests.assert (name == "make_interval" && names ==
    ["years", "months", "weeks", "days", "hours", "mins", "secs"] &&
    defaults == ["0", "0", "0", "0", "0", "0", "0.0"] &&
    SelectContract.makeIntervalParameters.map SelectContract.FunctionParameter.name == names &&
    SelectContract.makeIntervalParameters.map SelectContract.FunctionParameter.type == inputs &&
    SelectContract.makeIntervalCatalog == [⟨inputs, output⟩] &&
    SelectContract.functionCatalog name == [⟨inputs, output⟩])
    "exact parameter names, declared inputs, defaults and output must match native inventory"
  let expectedDefaults : List SelectContract.FunctionDefault :=
    [.intZero, .intZero, .intZero, .intZero, .intZero, .intZero, .floatZero]
  SQLean.Tests.assert (SelectContract.makeIntervalParameters.map
    SelectContract.FunctionParameter.defaultValue == expectedDefaults.map some)
    "each omitted argument must have its exact typed-zero default"
  let bound ← expectOk "all defaults" ((SelectContract.checkArguments
    SelectContract.makeIntervalParameters [] []).mapError reprStr)
  have _bound := bound.property
  SQLean.Tests.assert (bound.val == expectedDefaults.map SelectContract.FunctionDefault.input &&
    SelectContract.makeIntervalSignature bound.val == some ⟨.interval [], false⟩)
    "default-only call has nonnullable INTERVAL"
  pure 1

def namedArgumentsContractTests : IO Nat := do
  let mut count ← namedInventoryTests
  let names := ["years", "months", "weeks", "days", "hours", "mins", "secs"]
  -- All 128 omission subsets, both notations and both lexical orders.
  for mask in List.range 128 do
    let indices := (List.range 7).filter fun index => mask / (2 ^ index) % 2 == 1
    for reverse in [false, true] do
      let indices := if reverse then indices.reverse else indices
      for spelling in ["=>", ":="] do
        let arguments := indices.map fun index =>
          s!"{names[index]!} {spelling} {index + 1}"
        let sql := "SELECT make_interval(" ++ String.intercalate ", " arguments ++ ") AS v"
        SQLean.Tests.assert ((← namedOutput sql) == [⟨"v", ⟨.interval [], false⟩⟩])
          s!"default omission/lexical mapping: {sql}"
        count := count + 1
  let declarations : List (String × Bool × Bool) := [
    ("SMALLINT", true, true), ("INTEGER", true, true), ("BIGINT", false, true),
    ("NUMERIC(8,2)", false, true), ("REAL", false, true), ("DOUBLE PRECISION", false, true),
    ("TEXT", false, false), ("VARCHAR(5)", false, false), ("CHAR(5)", false, false),
    ("NAME", false, false), ("BOOLEAN", false, false), ("DATE", false, false),
    ("TIME", false, false), ("TIMESTAMP", false, false), ("INTERVAL", false, false),
    ("UUID", false, false), ("JSON", false, false), ("JSONB", false, false),
    ("BYTEA", false, false), ("INTEGER[]", false, false), ("TEXT[]", false, false)]
  for name in names do
    for (declaration, integerSlot, secondsSlot) in declarations do
      for nullable in [false, true] do
        let sql := s!"SELECT make_interval({name} => $1) AS v"
        let query ← expectOk sql (Advanced.parseQuery sql)
        let params ← expectOk declaration (Assurance.parseContractParameterTypes
          (declaration ++ (if nullable then "?" else "")))
        if (if name == "secs" then secondsSlot else integerSlot) then
          SQLean.Tests.assert ((← namedCertificate query params) ==
            [⟨"v", ⟨.interval [], nullable⟩⟩]) s!"named exact implicit argument coercion: {name}, {declaration}"
        else match SelectContract.checkQuery .basicV26 [] params query with
          | .error (.invalid diagnostic) =>
              SQLean.Tests.assert (diagnostic.code == "function_signature") "known argument type must fail coercion"
          | _ => throw (IO.userError s!"incompatible declared make_interval argument accepted: {name}, {declaration}")
        count := count + 1
  for length in List.range 8 do
    let args := (List.range length).map fun n => toString (n + 1)
    SQLean.Tests.assert ((← namedOutput ("SELECT make_interval(" ++ String.intercalate "," args ++ ")")) ==
      [⟨"make_interval", ⟨.interval [], false⟩⟩]) "positional prefix and omitted defaults"
    count := count + 1
  for (sql, params, nullable) in [
      ("SELECT make_interval(secs => ?, days => ?, years => ?) AS v", "DOUBLE PRECISION,INTEGER,INTEGER", false),
      ("SELECT make_interval(?, secs := ?, months => ?) AS v", "INTEGER,DOUBLE PRECISION,INTEGER", false),
      ("SELECT make_interval(days => $2, secs => $1, years => $2) AS v", "DOUBLE PRECISION,INTEGER", false),
      ("SELECT make_interval(secs => $1, days => $2) AS v", "DOUBLE PRECISION?,INTEGER", true),
      ("SELECT make_interval(\"years\" := 1, \"secs\" => 1.5) AS v", "", false),
      ("SELECT pg_catalog.make_interval(days => 1) AS v", "", false),
      ("SELECT make_interval(days => 'not an integer') AS v", "", false),
      ("SELECT make_interval(secs => 'Infinity'::DOUBLE PRECISION) AS v", "", false),
      ("SELECT make_interval(years => NULL, secs => 'Infinity'::DOUBLE PRECISION) AS v", "", true)] do
    SQLean.Tests.assert ((← namedOutput sql params) == [⟨"v", ⟨.interval [], nullable⟩⟩])
      s!"named lexical bindings and runtime-value boundary: {sql}"
    count := count + 1
  for expr in ["make_interval(days=>1)", "CAST(make_interval(days=>1) AS INTERVAL)",
      "CASE WHEN TRUE THEN make_interval(days=>1) ELSE make_interval() END"] do
    SQLean.Tests.assert ((← namedOutput s!"SELECT {expr}") ==
      [⟨"make_interval", ⟨.interval [], false⟩⟩]) "default strong function label"
    count := count + 1
  for (sql, expectedCode) in [
      ("SELECT make_interval(days=>1,2)", "named_argument_order"),
      ("SELECT make_interval(days=>1,days=>2)", "duplicate_argument"),
      ("SELECT make_interval(1,years=>2)", "duplicate_argument"),
      ("SELECT make_interval(1,2,months=>3)", "duplicate_argument"),
      ("SELECT make_interval(day=>1)", "named_argument_name"),
      ("SELECT make_interval(\"Years\"=>1)", "named_argument_name"),
      ("SELECT make_interval(1,2,3,4,5,6,7,8)", "function_arity")] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV26 [] [] query with
    | .error (.invalid diagnostic) =>
        SQLean.Tests.assert (diagnostic.code == expectedCode) s!"exact named-binding failure: {sql}"
    | _ => throw (IO.userError s!"malformed argument binding acquired a certificate: {sql}")
    count := count + 1
  for sql in ["SELECT application.make_interval(days=>1)", "SELECT f(a=>1)",
      "SELECT abs(x=>1)", "SELECT make_date(year=>2024,month=>1,day=>2)",
      "SELECT make_interval(days=>(SELECT 1))"] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV26 [] [] query with
    | .error (.unsupported _) => pure ()
    | _ => throw (IO.userError s!"unregistered named routine/dependency must remain Unsupported: {sql}")
    count := count + 1
  let required : List SelectContract.FunctionParameter := [⟨"required", .int32, none⟩]
  match SelectContract.checkArguments required [] [] with
  | .error (.invalid diagnostic) =>
      SQLean.Tests.assert (diagnostic.code == "missing_argument")
        "missing required slot cannot manufacture a default"
  | _ => throw (IO.userError "missing required slot accepted")
  let query ← expectOk "named fuel" (Advanced.parseQuery "SELECT make_interval(days=>1)")
  match SelectContract.checkQuery .basicV26 [] [] query 1 with
  | .error (.inconclusive _) => pure ()
  | _ => throw (IO.userError "named resource exhaustion must remain Inconclusive")
  let args := [Advanced.CallArgument.named "secs" (.parameter (.anonymous 2)),
    .named "days" (.parameter (.anonymous 1))]
  let query : Advanced.Query := {body := .select {items := [.expression (.namedCall ["make_interval"] args)]}}
  let params ← expectOk "named parameter declarations"
    (Assurance.parseContractParameterTypes "INTEGER,DOUBLE PRECISION")
  match SelectContract.checkQuery .basicV26 [] params query with
  | .error (.invalid diagnostic) =>
      SQLean.Tests.assert (diagnostic.code == "parameter_notation")
        "declaration-slot order cannot override anonymous lexical order"
  | _ => throw (IO.userError "slot binding reordered anonymous occurrences")
  pure (count + 3)

private def namedTypeLabel (base : SelectContract.ScalarType) : String :=
  match base with
  | .bool => "bool" | .int32 => "int32" | .text => "text"
  | base => base.dataType.toSql.toLower.replace ", " ","

def namedArgumentsCorpusTests : IO Nat := do
  let records ← expectOk "named synthetic records"
    ((Lean.Json.parse (← IO.FS.readFile "fixtures/named_arguments/synthetic.json")) >>= Lean.Json.getArr?)
  SQLean.Tests.assert (records.size == 50) "fifty authored named/default calls required"
  let mut ids : List String := []
  let mut statements : List String := []
  for record in records do
    let id ← namedField "synthetic" record "id"
    let sql ← namedField id record "sql"
    SQLean.Tests.assert ((← namedField id record "source_kind") == "synthetic") s!"{id}: source population"
    let parameters ← namedField id record "parameter_types"
    let expected ← expectOk id ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
    let expected ← expected.toList.mapM fun column => do
      let name ← namedField id column "name"
      let type ← namedField id column "type"
      let nullable ← expectOk id ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
      pure (name, type, nullable)
    let actual ← namedOutput sql parameters
    let labels := actual.map fun column =>
      (column.name, namedTypeLabel column.type.base, column.type.nullable)
    SQLean.Tests.assert (labels == expected) s!"{id}: exact named output {reprStr labels}; expected {reprStr expected}"
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (decide ids.Nodup && decide statements.Nodup) "duplicate authored named queries"
  pure records.size

/-- The five closed PostgreSQL queries and two pinned SQLC interfaces form
an explicit eligibility registry. The latter certificates are conditional on
registered nonnullable FLOAT8/INT32 bindings, not observations of source values. -/
def namedArgumentsConcreteContractTests : IO Nat := do
  let expectedIds : List String := [
    "named_arguments:postgres:src/test/regress/sql/interval.sql:statement-320",
    "named_arguments:postgres:src/test/regress/sql/interval.sql:statement-321",
    "named_arguments:postgres:src/test/regress/sql/interval.sql:statement-322",
    "named_arguments:postgres:src/test/regress/sql/interval.sql:statement-323",
    "named_arguments:postgres:src/test/regress/sql/interval.sql:statement-324",
    "named_arguments:postgres:src/test/regress/sql/polymorphism.sql:statement-330",
    "named_arguments:postgres:src/test/regress/sql/polymorphism.sql:statement-331",
    "named_arguments:postgres:src/test/regress/sql/polymorphism.sql:statement-332",
    "named_arguments:postgres:src/test/regress/sql/polymorphism.sql:statement-333",
    "named_arguments:postgres:src/test/regress/sql/polymorphism.sql:statement-334",
    "named_arguments:postgres:src/test/regress/sql/polymorphism.sql:statement-335",
    "named_arguments:postgres:src/test/regress/sql/polymorphism.sql:statement-336",
    "named_arguments:postgres:src/test/regress/sql/polymorphism.sql:statement-338",
    "named_arguments:postgres:src/test/regress/sql/polymorphism.sql:statement-340",
    "named_arguments:postgres:src/test/regress/sql/polymorphism.sql:statement-341",
    "named_arguments:postgres:src/test/regress/sql/polymorphism.sql:statement-342",
    "named_arguments:postgres:src/test/regress/sql/polymorphism.sql:statement-343",
    "named_arguments:postgres:src/test/regress/sql/polymorphism.sql:statement-344",
    "named_arguments:postgres:src/test/regress/sql/polymorphism.sql:statement-345",
    "named_arguments:postgres:src/test/regress/sql/polymorphism.sql:statement-346",
    "named_arguments:postgres:src/test/regress/sql/polymorphism.sql:statement-347",
    "named_arguments:postgres:src/test/regress/sql/polymorphism.sql:statement-349",
    "named_arguments:postgres:src/test/regress/sql/polymorphism.sql:statement-351",
    "named_arguments:postgres:src/test/regress/sql/polymorphism.sql:statement-352",
    "named_arguments:postgres:src/test/regress/sql/polymorphism.sql:statement-353",
    "named_arguments:postgres:src/test/regress/sql/polymorphism.sql:statement-354",
    "named_arguments:postgres:src/test/regress/sql/polymorphism.sql:statement-355",
    "named_arguments:sqlc:internal/endtoend/testdata/func_args/pgx/v5/query.sql:statement-0",
    "named_arguments:sqlc:internal/endtoend/testdata/func_args/pgx/v5/query.sql:statement-1",
    "named_arguments:sqlc:internal/endtoend/testdata/func_args/pgx/v5/query.sql:statement-2",
    "named_arguments:sqlc:internal/endtoend/testdata/func_args/pgx/v5/query.sql:statement-4",
    "named_arguments:sqlc:internal/endtoend/testdata/sql_syntax_calling_funcs/postgresql/pgx/v5/query.sql:statement-2",
    "named_arguments:sqlc:internal/endtoend/testdata/sql_syntax_calling_funcs/postgresql/pgx/v5/query.sql:statement-3",
    "named_arguments:sqlc:internal/endtoend/testdata/sql_syntax_calling_funcs/postgresql/pgx/v5/query.sql:statement-4",
    "named_arguments:sqlc:internal/endtoend/testdata/sql_syntax_calling_funcs/postgresql/pgx/v5/query.sql:statement-5",
    "named_arguments:postgres:src/test/regress/sql/jsonb.sql:statement-825",
    "named_arguments:postgres:src/test/regress/sql/jsonb.sql:statement-826",
    "named_arguments:postgres:src/test/regress/sql/jsonb.sql:statement-827",
    "named_arguments:postgres:src/test/regress/sql/name.sql:statement-25",
    "named_arguments:postgres:src/test/regress/sql/jsonb_jsonpath.sql:statement-404",
    "named_arguments:postgres:src/test/regress/sql/jsonb_jsonpath.sql:statement-405",
    "named_arguments:postgres:src/test/regress/sql/jsonb_jsonpath.sql:statement-407",
    "named_arguments:postgres:src/test/regress/sql/jsonb_jsonpath.sql:statement-411",
    "named_arguments:postgres:src/test/regress/sql/jsonb_jsonpath.sql:statement-412",
    "named_arguments:postgres:src/test/regress/sql/jsonb_jsonpath.sql:statement-418",
    "named_arguments:postgres:src/test/regress/sql/jsonb_jsonpath.sql:statement-419",
    "named_arguments:postgres:src/test/regress/sql/jsonb_jsonpath.sql:statement-422",
    "named_arguments:postgres:src/test/regress/sql/jsonb_jsonpath.sql:statement-423",
    "named_arguments:postgres:src/test/regress/sql/jsonb_jsonpath.sql:statement-424",
    "named_arguments:postgres:src/test/regress/sql/jsonb_jsonpath.sql:statement-425"]
  let pgId := fun (n : Nat) => s!"named_arguments:postgres:src/test/regress/sql/interval.sql:statement-{n}"
  let sqlcId := fun (n : Nat) => s!"named_arguments:sqlc:internal/endtoend/testdata/func_args/pgx/v5/query.sql:statement-{n}"
  let certifiedIds := ([320, 321, 322, 323, 324] : List Nat).map pgId ++ [sqlcId 1, sqlcId 2]
  SQLean.Tests.assert (expectedIds.length == 50 && certifiedIds.length == 7 &&
    decide expectedIds.Nodup && decide certifiedIds.Nodup) "fixed named source identities"
  let source ← IO.FS.readFile "fixtures/named_arguments/concrete.jsonl"
  let lines := (source.splitOn "\n").filter (fun line => !line.trimAscii.toString.isEmpty)
  SQLean.Tests.assert (lines.length == 50) "fifty original named source statements required"
  let mut ids : List String := []
  let mut statements : List String := []
  let mut certified := 0
  for line in lines do
    let record ← expectOk "named source" (Lean.Json.parse line)
    let id ← namedField "source" record "id"
    let sql ← namedField id record "sql"
    SQLean.Tests.assert (expectedIds.contains id && (← namedField id record "raw_sql") == sql)
      s!"{id}: original source identity or bytes changed"
    let expectedSlots : List Nat := if id == sqlcId 0 then [2, 1]
      else if [sqlcId 1, sqlcId 2, sqlcId 4].contains id then [1] else []
    let slots ← expectOk id ((record.getObjVal? "observed_parameter_slots") >>= Lean.Json.getArr?)
    let slots ← slots.toList.mapM fun slot => expectOk id slot.getNat?
    let query ← expectOk id (Advanced.parseQuery sql)
    SQLean.Tests.assert (slots == expectedSlots &&
      Advanced.queryParameters 1024 query == expectedSlots.map Advanced.Parameter.numbered)
      s!"{id}: exact lexical source parameter order"
    if certifiedIds.contains id then
      let observations ← expectOk id (record.getObjVal? "observed_syntax")
      let sourceFree ← expectOk id ((observations.getObjVal? "source_free") >>= Lean.Json.getBool?)
      SQLean.Tests.assert (sourceFree == expectedSlots.isEmpty && query.ctes.isEmpty)
        s!"{id}: certified source structure changed"
      match query.body with
      | .select select => SQLean.Tests.assert select.source.isNone s!"{id}: certified source acquired FROM"
      | _ => throw (IO.userError s!"{id}: certified query body changed")
      let parameterTypes := if id == sqlcId 1 then "double precision"
        else if id == sqlcId 2 then "integer" else ""
      if parameterTypes.isEmpty then
        SQLean.Tests.assert ((← expectOk id (record.getObjVal? "parameter_types")) == Lean.Json.null)
          s!"{id}: literal source must not acquire invented declarations"
      else
        SQLean.Tests.assert ((← namedField id record "parameter_types") == parameterTypes)
          s!"{id}: pinned interface input type changed"
        let provenance ← expectOk id (record.getObjVal? "parameter_type_provenance")
        SQLean.Tests.assert ((← namedField id provenance "kind") == "pinned-generated-sqlc-interface" &&
          (← namedField id provenance "postgres_type") == parameterTypes &&
          (← namedField id provenance "go_type") == (if id == sqlcId 1 then "float64" else "int32") &&
          (← namedField id provenance "method") == (if id == sqlcId 1 then "MakeIntervalSecs" else "MakeIntervalDays") &&
          (← namedField id provenance "sha256") == "625c536dc7ea795ca784ceaad0dc0e0f9175cb6df1a9a838c1dd37bb8abd78e2")
          s!"{id}: registered interface provenance changed"
      let params ← expectOk id (Assurance.parseContractParameterTypes parameterTypes)
      let expected : List SelectContract.OutputColumn := if id == pgId 323 then
        [⟨"?column?", ⟨.bool, false⟩⟩] else [⟨"make_interval", ⟨.interval [], false⟩⟩]
      SQLean.Tests.assert ((← namedCertificate query params) == expected)
        s!"{id}: exact complete source certificate"
      certified := certified + 1
    else
      SQLean.Tests.assert ((← expectOk id (record.getObjVal? "parameter_types")) == Lean.Json.null)
        s!"{id}: rendering-only source must retain unspecified declarations"
      let identity ← expectOk id ((RenderContract.check .identityV01 query).mapError reprStr)
      let postgres ← expectOk id ((RenderContract.check .postgres16V01 query).mapError reprStr)
      have _identity := identity.roundTrip
      have _postgres := postgres.roundTrip
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (certified == 7 && decide ids.Nodup && decide statements.Nodup &&
    expectedIds.all ids.contains) "complete named source registry must be replayed exactly once"
  pure certified

end SQLean.Tests
