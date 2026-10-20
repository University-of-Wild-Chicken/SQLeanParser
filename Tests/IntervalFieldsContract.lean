import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support
import Lean.Data.Json

namespace SQLean.Tests

example : SelectContract.ExprValid [] .empty
    (.cast (.literal (.text "1")) ⟨.intervalRange .year, []⟩)
    (some ⟨.intervalRange .year [], false⟩) [] :=
  .cast .text rfl trivial rfl trivial

example : SelectContract.ExprValid
    [⟨1, ⟨.array (.intervalRange .dayToSecond), [2]⟩, false⟩] .empty
    (.parameter (.anonymous 1)) (some ⟨.array (.interval []), false⟩) [.anonymous 1] :=
  .parameter
    (binding := ⟨1, ⟨.array (.intervalRange .dayToSecond), [2]⟩, false⟩)
    (base := .array (.intervalRange .dayToSecond [2])) (by simp) rfl rfl

example : SelectContract.extractSignature
    (.known ⟨.intervalRange .minuteToSecond [2], false⟩) =
    some ⟨[.text, .interval []], .numeric []⟩ := rfl

private def intervalField (id : String) (record : Lean.Json) (name : String) : IO String :=
  expectOk s!"{id}: {name}" ((record.getObjVal? name) >>= Lean.Json.getStr?)

private def intervalProjection (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr (some "v")]}}

private def intervalCertificate (query : Advanced.Query)
    (catalog : Advanced.Catalog := []) (params : SelectContract.ParameterEnv := []) :
    IO (List SelectContract.OutputColumn) := do
  let certificate ← expectOk "interval fields SELECT"
    ((SelectContract.checkQuery .basicV25 catalog params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  let identity ← expectOk "interval fields identity renderer"
    ((RenderContract.check .identityV01 query).mapError reprStr)
  let postgres ← expectOk "interval fields PostgreSQL renderer"
    ((RenderContract.check .postgres16V01 query).mapError reprStr)
  have _identity : Advanced.parseQuery identity.sql = .ok query := identity.roundTrip
  have _postgres : Advanced.parseQuery postgres.sql = .ok (RenderContract.translateParameters query) :=
    postgres.roundTrip
  pure certificate.output

private def intervalOutput (sql : String) (parameterTypes : String := "") :
    IO (List SelectContract.OutputColumn) := do
  let query ← expectOk sql (Advanced.parseQuery sql)
  let params ← expectOk sql (Assurance.parseContractParameterTypes parameterTypes)
  intervalCertificate query [] params

def intervalFieldsContractTests : IO Nat := do
  let mut count := 0
  let ranges : List (Advanced.IntervalFields × String) := [
    (.year, "YEAR"), (.month, "MONTH"), (.day, "DAY"), (.hour, "HOUR"),
    (.minute, "MINUTE"), (.second, "SECOND"), (.yearToMonth, "YEAR TO MONTH"),
    (.dayToHour, "DAY TO HOUR"), (.dayToMinute, "DAY TO MINUTE"),
    (.dayToSecond, "DAY TO SECOND"), (.hourToMinute, "HOUR TO MINUTE"),
    (.hourToSecond, "HOUR TO SECOND"), (.minuteToSecond, "MINUTE TO SECOND")]
  SQLean.Tests.assert (ranges.map (·.1) == Advanced.IntervalFields.all)
    "all thirteen interval ranges must be registered"
  for (fields, spelling) in ranges do
    let precisions := [[]] ++ (if fields.allowsPrecision then (List.range 7).map (fun p => [p]) else [])
    for modifiers in precisions do
      let scalar : SelectContract.ScalarType := .intervalRange fields modifiers
      let declaration : Advanced.DataType := ⟨.intervalRange fields, modifiers⟩
      let sqlType := "INTERVAL " ++ spelling ++
        (if modifiers.isEmpty then "" else "(" ++ toString (modifiers.headD 0) ++ ")")
      SQLean.Tests.assert ((← expectOk sqlType (Advanced.parseDataType sqlType)) == declaration &&
          decide (SelectContract.DataTypeWellFormed declaration) &&
          SelectContract.concreteType declaration == some scalar)
        s!"interval qualifier identity: {sqlType}"
      count := count + 1
      for rank in [0, 1, 2] do
        let target : Advanced.DataType :=
          ⟨(List.range rank).foldl (fun typeName _ => .array typeName) declaration.name, modifiers⟩
        let exact := if rank == 0 then scalar else scalar.asArray
        let erased := if rank == 0 then SelectContract.ScalarType.interval []
          else .array (.interval [])
        for nullable in [false, true] do
          let arg : Advanced.Expr := if nullable then .null else
            .literal (.text (if rank == 0 then "1 year 2 mons 3 days 04:05:06.789"
              else "{1 day 04:05:06.789,NULL}"))
          SQLean.Tests.assert ((← intervalCertificate (intervalProjection (.cast arg target))) ==
              [⟨"v", ⟨exact, nullable⟩⟩])
            s!"exact cast interval typmod: {reprStr target}"
          let catalog : Advanced.Catalog := [{
            name := "durations", columns := [{name := "v", type := target, nullable := some nullable}]
          }]
          let fromTable : Advanced.Query :=
            {body := .select {items := [.all], source := some (.table "durations")}}
          SQLean.Tests.assert ((← intervalCertificate fromTable catalog) ==
              [⟨"v", ⟨exact, nullable⟩⟩]) "interval catalog preserves exact range and precision"
          let params : SelectContract.ParameterEnv := [⟨1, target, nullable⟩]
          SQLean.Tests.assert ((← intervalCertificate
              (intervalProjection (.parameter (.anonymous 1))) [] params) ==
              [⟨"v", ⟨erased, nullable⟩⟩]) "interval parameter must erase all typmods"
          SQLean.Tests.assert ((← intervalCertificate
              (intervalProjection (.cast (.parameter (.anonymous 1)) target)) [] params) ==
              [⟨"v", ⟨exact, nullable⟩⟩]) "explicit cast restores interval parameter typmods"
          count := count + 4
      for expr in [
          s!"INTERVAL '1 year 2 mons 3 days 04:05:06.789' {spelling}" ++
            (if modifiers.isEmpty then "" else "(" ++ toString (modifiers.headD 0) ++ ")"),
          s!"CAST('1 year 2 mons 3 days 04:05:06.789' AS {sqlType})"] do
        SQLean.Tests.assert ((← intervalOutput ("SELECT " ++ expr)) ==
            [⟨"interval", ⟨scalar, false⟩⟩]) "typed literal and CAST retain interval label and exact typmod"
        count := count + 1
      SQLean.Tests.assert ((← intervalOutput s!"SELECT EXTRACT(second FROM CAST($1 AS {sqlType})) AS v"
          "INTERVAL") == [⟨"v", ⟨.numeric [], false⟩⟩])
        "qualified interval uses the existing exact EXTRACT declaration"
      count := count + 1
    for modifiers in [[7], [1,2]] ++ (if fields.allowsPrecision then [] else [[0], [2], [6]]) do
      let target : Advanced.DataType := ⟨.intervalRange fields, modifiers⟩
      SQLean.Tests.assert (!(decide (SelectContract.DataTypeWellFormed target)))
        "noncanonical interval metadata must fail well-formedness"
      let precisionGap := fields.allowsPrecision && modifiers == [7]
      match SelectContract.checkQuery .basicV25 [] [] (intervalProjection (.cast .null target)) with
      | .error (.unsupported diagnostic) =>
          SQLean.Tests.assert (precisionGap && diagnostic.code == "interval_precision")
            "native precision clamping is an unsupported canonical boundary"
      | .error (.invalid diagnostic) =>
          SQLean.Tests.assert (!precisionGap && diagnostic.code == "type_declaration")
            "interval cast metadata diagnosis"
      | _ => throw (IO.userError "invalid interval cast metadata acquired a certificate")
      let params : SelectContract.ParameterEnv := [⟨1, target, false⟩]
      match SelectContract.checkQuery .basicV25 [] params
          (intervalProjection (.parameter (.numbered 1))) with
      | .error (.unsupported diagnostic) =>
          SQLean.Tests.assert (precisionGap && diagnostic.code == "interval_precision")
            "parameter precision clamping is an unsupported canonical boundary"
      | .error (.invalid _) =>
          SQLean.Tests.assert (!precisionGap) "supported declaration syntax must not be labeled native-invalid"
      | _ => throw (IO.userError "invalid interval parameter metadata acquired a certificate")
      count := count + 2
  for (leftFields, leftSpelling) in ranges do
    for (rightFields, rightSpelling) in ranges do
      let left := s!"CAST('1 year 2 mons 3 days 04:05:06.789' AS INTERVAL {leftSpelling})"
      let right := s!"CAST(NULL AS INTERVAL {rightSpelling})"
      let common := if leftFields == rightFields then
        SelectContract.ScalarType.intervalRange leftFields [] else .interval []
      SQLean.Tests.assert ((← intervalOutput s!"SELECT COALESCE({left}, {right}) AS v") ==
          [⟨"v", ⟨common, false⟩⟩]) "interval conditional common typmods"
      SQLean.Tests.assert ((← intervalOutput s!"SELECT ARRAY[{left}, {right}] AS v") ==
          [⟨"v", ⟨common.asArray, false⟩⟩]) "interval array element common typmods"
      count := count + 2
    let typed := s!"CAST('1 year 2 mons 3 days 04:05:06.789' AS INTERVAL {leftSpelling})"
    for (expr, expected) in [
        (s!"NULLIF({typed}, INTERVAL '0')",
          SelectContract.ExactType.mk (.intervalRange leftFields []) true),
        (s!"CAST({typed} AS INTERVAL)", ⟨.interval [], false⟩),
        (s!"{typed} + INTERVAL '0'", ⟨.interval [], false⟩),
        (s!"-{typed}", ⟨.interval [], false⟩),
        (s!"ARRAY[{typed}] || ARRAY[INTERVAL '0']", ⟨.array (.interval []), false⟩),
        (s!"ARRAY[{typed}] @> ARRAY[INTERVAL '0']", ⟨.bool, false⟩),
        (s!"(ARRAY[{typed}])[1]", ⟨.intervalRange leftFields [], true⟩)] do
      SQLean.Tests.assert ((← intervalOutput s!"SELECT {expr} AS v") == [⟨"v", expected⟩])
        s!"interval expression modifier behavior: {expr}"
      count := count + 1
  for fields in [.second, .dayToSecond, .hourToSecond, .minuteToSecond] do
    for (leftPrecision, rightPrecision) in [(0, 6), (2, 3), (6, 6)] do
      let left : Advanced.Expr := .cast (.literal (.text "1.234")) ⟨.intervalRange fields, [leftPrecision]⟩
      let right : Advanced.Expr := .cast .null ⟨.intervalRange fields, [rightPrecision]⟩
      let common := if leftPrecision == rightPrecision then
        SelectContract.ScalarType.intervalRange fields [leftPrecision] else .interval []
      SQLean.Tests.assert ((← intervalCertificate (intervalProjection (.coalesce [left, right]))) ==
          [⟨"v", ⟨common, false⟩⟩]) "interval precision participates in common typmod identity"
      count := count + 1
  let query ← expectOk "qualified interval fuel"
    (Advanced.parseQuery "SELECT INTERVAL '1' YEAR")
  match SelectContract.checkQuery .basicV25 [] [] query 0 with
  | .error (.inconclusive _) => pure ()
  | _ => throw (IO.userError "qualified interval fuel exhaustion must be Inconclusive")
  count := count + 1
  let unsupportedType : Advanced.DataType := ⟨.intervalRange .second, [7]⟩
  for typeName in [unsupportedType.name, .array unsupportedType.name] do
    let catalog : Advanced.Catalog := [{
      name := "durations", columns := [{name := "v", type := ⟨typeName, [7]⟩}]
    }]
    match SelectContract.checkQuery .basicV25 catalog [] query with
    | .error (.unsupported diagnostic) =>
        SQLean.Tests.assert (diagnostic.code == "interval_precision")
          "catalog precision clamping is outside canonical coverage"
    | _ => throw (IO.userError "excess catalog precision must be Unsupported")
    count := count + 1
  match SelectContract.checkPaginationBounds .basicV25 [⟨1, unsupportedType, false⟩] query with
  | .error (.unsupported diagnostic) =>
      SQLean.Tests.assert (diagnostic.code == "interval_precision")
        "bounds-only certificates retain the same exact metadata coverage"
  | _ => throw (IO.userError "bounds-only API must not certify unsupported parameter metadata")
  count := count + 1
  let duplicateParams : SelectContract.ParameterEnv :=
    [⟨1, unsupportedType, false⟩, ⟨1, ⟨.interval, []⟩, false⟩]
  match SelectContract.checkQuery .basicV25 [] duplicateParams query with
  | .error (.invalid diagnostic) =>
      SQLean.Tests.assert (diagnostic.code == "invalid_environment")
        "unrelated invalid metadata must not be hidden by an unsupported precision"
  | _ => throw (IO.userError "precision boundary masked duplicate parameters")
  count := count + 1
  let badCatalog : Advanced.Catalog := [{
    name := "durations", columns := [
      {name := "v", type := unsupportedType}, {name := "v", type := ⟨.interval, []⟩}]
  }]
  match SelectContract.checkQuery .basicV25 badCatalog [] query with
  | .error (.invalid diagnostic) =>
      SQLean.Tests.assert (diagnostic.code == "invalid_environment")
        "precision coverage must retain unrelated catalog invalidity"
  | _ => throw (IO.userError "precision boundary masked duplicate catalog names")
  pure (count + 1)

def intervalFieldsCorpusTests : IO Nat := do
  let json ← expectOk "interval fields synthetic JSON"
    (Lean.Json.parse (← IO.FS.readFile "fixtures/interval_fields/synthetic.json"))
  let records ← expectOk "interval fields synthetic records" json.getArr?
  SQLean.Tests.assert (records.size == 50) "expected fifty interval fields synthetic queries"
  let mut ids : List String := []
  let mut statements : List String := []
  for record in records do
    let id ← intervalField "synthetic" record "id"
    let sql ← intervalField id record "sql"
    SQLean.Tests.assert ((← intervalField id record "source_kind") == "synthetic")
      s!"{id}: synthetic population"
    let parameters ← intervalField id record "parameter_types"
    let expected ← expectOk id ((record.getObjVal? "output_columns") >>= Lean.Json.getArr?)
    let expected ← expected.toList.mapM fun column => do
      let name ← intervalField id column "name"
      let type ← intervalField id column "type"
      let nullable ← expectOk id ((column.getObjVal? "nullable") >>= Lean.Json.getBool?)
      pure (name, type, nullable)
    let actual ← intervalOutput sql parameters
    let labels := actual.map fun column =>
      (column.name, if column.type.base == .bool then "bool" else
        column.type.base.dataType.toSql.toLower.replace ", " ",", column.type.nullable)
    SQLean.Tests.assert (labels == expected)
      s!"{id}: exact interval output {reprStr labels}; expected {reprStr expected}"
    ids := id :: ids
    statements := sql :: statements
  SQLean.Tests.assert (decide ids.Nodup && decide statements.Nodup)
    "duplicate interval fields synthetic identities or SQL"
  pure records.size

/-- Exact source identities and range/precision expectations are registered
before checking. All fifty original statements are literal source-free SELECTs. -/
def intervalFieldsConcreteContractTests : IO Nat := do
  let groups : List (Advanced.IntervalFields × List Nat × List Nat) := [
    (.second, [], [92,102,134]), (.minute, [], [93,101]), (.hour, [], [94,100]),
    (.day, [], [95,99]), (.month, [], [96,98]), (.year, [], [97]),
    (.yearToMonth, [], [103,104]), (.dayToHour, [], [105,106,107,127]),
    (.dayToMinute, [], [108,109,110]), (.dayToSecond, [], [111,112,113]),
    (.hourToMinute, [], [114,115,116]), (.hourToSecond, [], [117,118,119]),
    (.minuteToSecond, [], [120,121,122,123,124,125,126]),
    (.minuteToSecond, [2], [133,143,144,145]), (.second, [2], [135]),
    (.dayToSecond, [2], [136,137,138,139]), (.hourToSecond, [2], [140,141,142])]
  let expected : List (String × Advanced.IntervalFields × List Nat) :=
    (groups.flatMap fun (fields, precision, numbers) =>
    numbers.map fun number =>
      (s!"interval_fields:postgres:src/test/regress/sql/interval.sql:statement-{number}",
        fields, precision)) ++ [
      ("interval_fields:duckdb:test/sql/types/interval/test_interval.test:sqllogic-query-158",
        .day, [])]
  SQLean.Tests.assert (expected.length == 50 && decide (expected.map (·.1)).Nodup)
    "interval concrete identities must be complete and unique"
  let source ← IO.FS.readFile "fixtures/interval_fields/concrete.jsonl"
  let lines := (source.splitOn "\n").filter fun line => !line.trimAscii.toString.isEmpty
  SQLean.Tests.assert (lines.length == 50) "expected fifty unchanged interval fields sources"
  let mut observed : List String := []
  let mut statements : List String := []
  for line in lines do
    let record ← expectOk "interval concrete" (Lean.Json.parse line)
    let id ← intervalField "concrete" record "id"
    let registered ← match expected.find? (fun entry => entry.1 == id) with
      | some entry => pure entry
      | none => throw (IO.userError s!"unregistered interval concrete identity {id}")
    let sql ← intervalField id record "sql"
    let origin ← intervalField id record "source"
    SQLean.Tests.assert ((← intervalField id record "raw_sql") == sql &&
        (id.splitOn ":").getD 1 "" == origin) s!"{id}: unchanged source/provenance required"
    let observations ← expectOk id (record.getObjVal? "observed_syntax")
    SQLean.Tests.assert (← expectOk id ((observations.getObjVal? "source_free") >>= Lean.Json.getBool?))
      s!"{id}: fixed source-free population"
    let slots ← expectOk id ((record.getObjVal? "observed_parameter_slots") >>= Lean.Json.getArr?)
    let query ← expectOk id (Advanced.parseQuery sql)
    SQLean.Tests.assert (slots.isEmpty && query.ctes.isEmpty &&
        Advanced.queryParameters 1024 query == []) s!"{id}: genuinely empty query environment"
    let target : Advanced.DataType := ⟨.intervalRange registered.2.1, registered.2.2⟩
    match query.body with
    | .select select =>
        SQLean.Tests.assert select.source.isNone s!"{id}: source-free AST required"
        match select.items with
        | [.expression (.cast (.literal (.text _)) actual) none] =>
            SQLean.Tests.assert (actual == target) s!"{id}: registered exact interval mask/precision"
        | _ => throw (IO.userError s!"{id}: registered interval literal expression changed")
    | _ => throw (IO.userError s!"{id}: registered SELECT structure changed")
    let scalar : SelectContract.ScalarType := .intervalRange registered.2.1 registered.2.2
    SQLean.Tests.assert ((← intervalCertificate query) ==
        [⟨"interval", ⟨scalar, false⟩⟩]) s!"{id}: exact concrete interval output"
    observed := id :: observed
    statements := sql :: statements
  SQLean.Tests.assert (decide observed.Nodup && decide statements.Nodup &&
      expected.all (fun entry => observed.contains entry.1))
    "interval concrete certificates must cover every registered identity exactly once"
  pure observed.length

end SQLean.Tests
