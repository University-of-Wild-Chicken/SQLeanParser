import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

namespace SQLean.Tests

example : SelectContract.extractSignature (.unknown false) = none := rfl

example : SelectContract.extractSignature (.known ⟨.time [3], false⟩) =
    some ⟨[.text, .time []], .numeric []⟩ := rfl

example : SelectContract.extractNullable (.known ⟨.date, false⟩) = true := rfl

example : SelectContract.ExprValid [⟨1, ⟨.time, [3]⟩, false⟩] .empty
    (.extract "second" (.parameter (.anonymous 1)))
    (some ⟨.numeric [], false⟩) [.anonymous 1] :=
  .extract (selected := ⟨[.text, .time []], .numeric []⟩)
    (.parameter (binding := ⟨1, ⟨.time, [3]⟩, false⟩) (base := .time [3])
      (by simp) rfl rfl) rfl

private def extractField (id : String) (record : Lean.Json) (name : String) : IO String :=
  expectOk s!"{id}: {name}" ((record.getObjVal? name) >>= Lean.Json.getStr?)

private def extractCertificate (query : Advanced.Query)
    (params : SelectContract.ParameterEnv := []) :
    IO (List SelectContract.OutputColumn) := do
  let certificate ← expectOk "EXTRACT SELECT"
    ((SelectContract.checkQuery .basicV21 [] params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let identity ← expectOk "EXTRACT identity renderer"
    ((RenderContract.check .identityV01 query).mapError reprStr)
  let postgres ← expectOk "EXTRACT PostgreSQL renderer"
    ((RenderContract.check .postgres16V01 query).mapError reprStr)
  have _identity : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
  have _postgres : Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
    postgres.roundTrip
  pure certificate.output

private def extractOutput (sql : String) (parameterTypes : String := "") :
    IO (List SelectContract.OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let params ← expectOk sql (Assurance.parseContractParameterTypes parameterTypes)
  extractCertificate query params

private def extractInventoryTests : IO Nat := do
  let json ← expectOk "EXTRACT catalog JSON"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/extract/function_signatures.json"))
  let records ← expectOk "EXTRACT catalog records" json.getArr?
  SQLean.Tests.assert (records.size == 6) "expected six EXTRACT declarations"
  let mut observed : List SelectContract.FunctionOverload := []
  for record in records do
    SQLean.Tests.assert ((← extractField "catalog" record "name") == "extract")
      "EXTRACT catalog function name"
    let inputJson ← expectOk "EXTRACT inputs" ((record.getObjVal? "inputs") >>= Lean.Json.getArr?)
    let inputs ← inputJson.toList.mapM fun value => do
      let name ← expectOk "EXTRACT input name" value.getStr?
      let declaration ← expectOk name (Advanced.parseDataType name)
      match SelectContract.concreteType declaration with
      | some base => pure base.unmodified
      | none => throw (IO.userError s!"unsupported EXTRACT catalog type {name}")
    let outputName ← extractField "catalog" record "output"
    let declaration ← expectOk outputName (Advanced.parseDataType outputName)
    let output ← match SelectContract.concreteType declaration with
      | some base => pure base.unmodified
      | none => throw (IO.userError "unsupported EXTRACT catalog output")
    let signature : SelectContract.FunctionOverload := ⟨inputs, output⟩
    match inputs with
    | [.text, temporal] =>
        SQLean.Tests.assert (SelectContract.extractSignature (.known ⟨temporal, false⟩) == some signature)
          "EXTRACT exact native declaration must be selected by the independent resolver"
    | _ => throw (IO.userError "EXTRACT must have TEXT field and one temporal input")
    observed := signature :: observed
  SQLean.Tests.assert (decide observed.Nodup && observed.all SelectContract.extractCatalog.contains &&
      SelectContract.extractCatalog.all observed.contains) "EXTRACT catalog inventory differs"
  pure records.size

def extractContractTests : IO Nat := do
  let mut count ← extractInventoryTests
  let declarations : List (String × Bool × Bool) := [
    ("SMALLINT", false, false), ("INTEGER", false, false), ("BIGINT", false, false),
    ("NUMERIC(8,2)", false, false), ("REAL", false, false), ("DOUBLE PRECISION", false, false),
    ("TEXT", false, false), ("VARCHAR(5)", false, false), ("CHAR(5)", false, false),
    ("BOOLEAN", false, false), ("DATE", true, true), ("TIME(3)", true, false),
    ("TIME(3) WITH TIME ZONE", true, false), ("TIMESTAMP(3)", true, true),
    ("TIMESTAMP(3) WITH TIME ZONE", true, true), ("INTERVAL(3)", true, false),
    ("UUID", false, false), ("JSON", false, false), ("JSONB", false, false), ("BYTEA", false, false)]
  for (declaration, temporal, infinityNullable) in declarations do
    for array in [false, true] do
      for nullable in [false, true] do
        let parameter := declaration ++ (if array then "[]" else "") ++ (if nullable then "?" else "")
        let sql := "SELECT EXTRACT('year' FROM $1) AS v"
        let query ← expectOk sql (Advanced.parseQuery sql)
        let params ← expectOk parameter (Assurance.parseContractParameterTypes parameter)
        if temporal && !array then
          SQLean.Tests.assert ((← extractCertificate query params) ==
              [⟨"v", ⟨.numeric [], nullable || infinityNullable⟩⟩])
            s!"EXTRACT exact temporal result: {parameter}"
        else match SelectContract.checkQuery .basicV21 [] params query with
        | .error (.invalid diagnostic) =>
            SQLean.Tests.assert (diagnostic.code == "extract_signature")
              s!"EXTRACT concrete invalid signature: {parameter}"
        | _ => throw (IO.userError s!"EXTRACT invalid type accepted: {parameter}")
        count := count + 1
  let fields := ["year", "years", "month", "day", "hour", "minute", "second", "epoch",
    "microseconds", "milliseconds", "timezone", "isodow", "julian", "foo", "", "YEAR",
    "field with spaces", "x'y", "? $1"];
  for (declaration, infinityNullable) in [
      ("DATE", true), ("TIME(3)", false), ("TIME(3) WITH TIME ZONE", false),
      ("TIMESTAMP(3)", true), ("TIMESTAMP(3) WITH TIME ZONE", true), ("INTERVAL(3)", false)] do
    for field in fields do
      let params ← expectOk declaration (Assurance.parseContractParameterTypes declaration)
      let query : Advanced.Query :=
        {body := .select {items := [.expression (.extract field (.parameter (.anonymous 1))) none]}}
      SQLean.Tests.assert ((← extractCertificate query params) ==
          [⟨"extract", ⟨.numeric [], infinityNullable⟩⟩])
        s!"EXTRACT field is a runtime unit obligation: {field}, {declaration}"
      count := count + 1
  for arg in ["NULL", "'2024-01-01'", "'12:34:56'", "''", "'1 day'",
      "1", "TRUE", "CAST('2024-01-01' AS TEXT)", "ARRAY[DATE '2024-01-01']",
      "EXTRACT(year FROM DATE '2024-01-01')"] do
    let sql := s!"SELECT EXTRACT(year FROM {arg})"
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV21 [] [] query with
    | .error (.invalid diagnostic) =>
        SQLean.Tests.assert (diagnostic.code == "extract_signature") s!"EXTRACT invalid input: {sql}"
    | _ => throw (IO.userError s!"EXTRACT invalid/ambiguous input accepted: {sql}")
    count := count + 1
  for sql in [
      "SELECT EXTRACT(year FROM (SELECT DATE '2024-01-01'))",
      "SELECT EXTRACT(year FROM unregistered_temporal_function())"] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV21 [] [] query with
    | .error (.unsupported _) => pure ()
    | _ => throw (IO.userError s!"EXTRACT unsupported child must retain its status: {sql}")
    count := count + 1
  for (sql, nullable) in [
      ("SELECT EXTRACT(day FROM DATE 'infinity')", true),
      ("SELECT EXTRACT(epoch FROM DATE 'infinity')", true),
      ("SELECT EXTRACT('foo' FROM NULL::DATE)", true),
      ("SELECT EXTRACT('foo' FROM DATE '2024-01-01')", true),
      ("SELECT EXTRACT(year FROM TIME '12:34:56')", false),
      ("SELECT EXTRACT('' FROM INTERVAL '1 day')", false),
      ("SELECT EXTRACT(hour FROM NULL::TIME)", true),
      ("SELECT EXTRACT(year FROM CAST('not a date' AS DATE))", true),
      ("SELECT EXTRACT(hour FROM CAST('not a time' AS TIME))", false)] do
    SQLean.Tests.assert ((← extractOutput sql) == [⟨"extract", ⟨.numeric [], nullable⟩⟩])
      s!"EXTRACT analysis/runtime and infinity boundary: {sql}"
    count := count + 1
  for sql in [
      "SELECT EXTRACT(second FROM TIME '12:34:56.789')",
      "SELECT CAST(EXTRACT(second FROM TIME '12:34:56.789') AS NUMERIC)",
      "SELECT CASE WHEN TRUE THEN 1 ELSE EXTRACT(second FROM TIME '12:34:56.789') END"] do
    SQLean.Tests.assert ((← extractOutput sql) == [⟨"extract", ⟨.numeric [], false⟩⟩])
      s!"EXTRACT strong default label: {sql}"
    count := count + 1
  for (sql, types) in [
      ("SELECT EXTRACT('?$2' FROM ?), EXTRACT(second FROM ?)", "DATE,TIME"),
      ("SELECT EXTRACT(second FROM $2), EXTRACT(year FROM $1), EXTRACT(hour FROM $2)", "DATE,TIME"),
      ("SELECT EXTRACT(second FROM CASE WHEN ? THEN ? ELSE ? END)", "BOOLEAN,TIME,TIME?"),
      ("SELECT EXTRACT(second FROM COALESCE(?, ?))", "TIME?,TIME")] do
    discard <| extractOutput sql types
    count := count + 1
  let query ← expectOk "EXTRACT fuel query" (Advanced.parseQuery "SELECT EXTRACT(second FROM $1)")
  let params ← expectOk "EXTRACT parameter" (Assurance.parseContractParameterTypes "TIME")
  match SelectContract.checkQuery .basicV21 [] params query 0 with
  | .error (.inconclusive _) => pure ()
  | _ => throw (IO.userError "EXTRACT fuel exhaustion must be Inconclusive")
  count := count + 1
  expectError "EXTRACT mixed placeholder syntax"
    (Advanced.parseQuery "SELECT EXTRACT(year FROM ?), EXTRACT(hour FROM $1)")
  count := count + 1
  let mixed : Advanced.Query := {body := .select {items := [
    .expression (.extract "second" (.parameter (.anonymous 1))) none,
    .expression (.extract "hour" (.parameter (.numbered 1))) none]}}
  match SelectContract.checkQuery .basicV21 [] params mixed with
  | .error (.invalid _) => pure ()
  | _ => throw (IO.userError "Hand-built EXTRACT AST must not bypass mixed placeholder rejection")
  count := count + 1
  for sql in ["SELECT EXTRACT(year FROM $2)"] do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV21 [] params query with
    | .error (.invalid _) => pure ()
    | _ => throw (IO.userError s!"EXTRACT malformed parameter usage must be Invalid: {sql}")
    count := count + 1
  pure count

def extractCorpusTests : IO Nat := do
  let json ← expectOk "EXTRACT synthetic JSON"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/extract/synthetic.json"))
  let records ← expectOk "EXTRACT synthetic records" json.getArr?
  SQLean.Tests.assert (records.size == 50) "expected fifty EXTRACT synthetic queries"
  let mut ids : List String := []
  let mut statements : List String := []
  for record in records do
    let id ← extractField "synthetic" record "id"
    let sql ← extractField id record "sql"
    SQLean.Tests.assert ((← extractField id record "source_kind") == "synthetic")
      s!"{id}: synthetic population"
    let parameters ← extractField id record "parameter_types"
    let expected ← expectOk id ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
    let expected ← expected.toList.mapM fun column => do
      let name ← extractField id column "name"
      let type ← extractField id column "type"
      let nullable ← expectOk id ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
      pure (name, type, nullable)
    let actual ← extractOutput sql parameters
    let labels := actual.map fun column =>
      (column.name, if column.type.base == .numeric [] then "numeric" else "unexpected",
        column.type.nullable)
    SQLean.Tests.assert (labels == expected)
      s!"{id}: exact EXTRACT output {reprStr labels}; expected {reprStr expected}"
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (decide ids.Nodup && decide statements.Nodup)
    "duplicate EXTRACT synthetic identities or SQL"
  pure records.size

/-- Every registered authentic source is a source-free temporal literal.
No catalog or parameter assumptions are invented, and no failed check is
silently moved into a weaker assurance population. -/
def extractConcreteContractTests : IO Nat := do
  let registrations : List (String × List Nat × Advanced.TypeName × Bool) := [
    ("date", [176,177,187,194,206,207,208,213,215,216,217,219,221,226,242,251,
      178,179,180,181,182,183], .date, true),
    ("time", [31,32,33,34,35,39], .time, false),
    ("timetz", [35,36,37,38,39,42,43,44,45], .timeTZ, false),
    ("timestamp", [134,135], .timestamp, true),
    ("timestamptz", [154,155], .timestampTZ, true),
    ("interval", [333,334,335,336,337,338,339,340,342], .interval, false)]
  let expected := registrations.flatMap fun (file, numbers, type, nullable) =>
    numbers.map fun number =>
      (s!"extract:postgres:src/test/regress/sql/{file}.sql:statement-{number}", type, nullable)
  SQLean.Tests.assert (expected.length == 50 && decide (expected.map (·.1)).Nodup)
    "EXTRACT concrete identities must be complete and unique"
  let source ← IO.FS.readFile "fixtures/extract/concrete.jsonl"
  let lines := (source.splitOn "\n").filter fun line => !line.trimAscii.toString.isEmpty
  SQLean.Tests.assert (lines.length == 50) "expected fifty unchanged EXTRACT sources"
  let mut observed : List String := []
  let mut statements : List String := []
  for line in lines do
    let record ← expectOk "EXTRACT concrete" (Lean.Json.parse line)
    let id ← extractField "concrete" record "id"
    let registered ← match expected.find? (fun entry => entry.1 == id) with
      | some entry => pure entry
      | none => throw (IO.userError s!"unregistered EXTRACT concrete identity {id}")
    let sql ← extractField id record "sql"
    SQLean.Tests.assert ((← extractField id record "raw_sql") == sql &&
        (← extractField id record "source") == "postgres")
      s!"{id}: unchanged source/provenance required"
    let observations ← expectOk id (record.getObjVal? "observed_syntax")
    SQLean.Tests.assert (← expectOk id ((observations.getObjVal? "source_free") >>= Lean.Json.getBool?))
      s!"{id}: fixed source-free population"
    let slots ← expectOk id ((record.getObjVal? "observed_parameter_slots") >>= Lean.Json.getArr?)
    let query ← expectOk id (Advanced.parseQuery sql)
    SQLean.Tests.assert (slots.isEmpty && query.ctes.isEmpty &&
        Advanced.queryParameters 1024 query == []) s!"{id}: genuinely empty query environment"
    match query.body with
    | .select select =>
        SQLean.Tests.assert select.source.isNone s!"{id}: source-free AST required"
        match select.items with
        | [.expression (.extract _ (.cast (.literal (.text _)) target)) none] =>
            SQLean.Tests.assert (target.name == registered.2.1)
              s!"{id}: registered exact temporal source type"
        | _ => throw (IO.userError s!"{id}: registered temporal-literal expression changed")
    | _ => throw (IO.userError s!"{id}: registered SELECT structure changed")
    SQLean.Tests.assert ((← extractCertificate query) ==
        [⟨"extract", ⟨.numeric [], registered.2.2⟩⟩]) s!"{id}: exact concrete EXTRACT output"
    observed := id :: observed
    statements := sql :: statements
  SQLean.Tests.assert (decide observed.Nodup && decide statements.Nodup &&
      expected.all (fun entry => observed.contains entry.1))
    "EXTRACT concrete certificates must cover every registered identity exactly once"
  pure observed.length

end SQLean.Tests
