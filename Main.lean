import SQLean
import SQLean.SchemaJson
import SQLean.PostgresGrammar.Report
import Lean.Data.Json

open SQLean
open Lean (toJson)

private def usage : String :=
  "Usage: sqlean [--ast] [--schema schema.json] [--param-types int,text] [--postgres] [--assurance contract|checked|syntax] [--render-assurance identity|postgres|sqlite] [--max-depth N] [--file query.sql | SQL]\n\
   Parse one SELECT, INSERT, UPDATE, or DELETE, or CREATE/ALTER/DROP TABLE.\n\
   With no SQL or --file, read stdin.\n\
   --ast                  Print the public Lean AST\n\
   --schema schema.json   Also certify table/column resolution and types\n\
   --param-types TYPES    Parameter types in position order (int,text,bool,real; suffix ? permits NULL)\n\
   --postgres             Render anonymous ? parameters as PostgreSQL $n\n\
   --postgres-grammar     Emit a pinned PostgreSQL 16 grammar certificate report\n\
   --max-transitions N    PostgreSQL grammar LR transition budget (default 1000000)\n\
   --assurance LEVEL      Emit a JSON assurance report (contract, checked, or syntax)\n\
   --render-assurance MODE  Emit checked SELECT serialization and parameter-map JSON\n\
   --max-depth N          SELECT assurance depth budget (default 1024; zero is inconclusive)\n\
   --help                 Show this help\n"

private structure Options where
  ast : Bool := false
  schemaFile : Option String := none
  queryFile : Option String := none
  source : Option String := none
  help : Bool := false
  parameterTypes : Option String := none
  postgres : Bool := false
  assurance : Option Assurance.Level := none
  renderAssurance : Option RenderContract.Profile := none
  maxDepth : Option Nat := none
  postgresGrammar : Bool := false
  maxTransitions : Option Nat := none

private def parseArgs : List String → Options → Except String Options
  | [], options => pure options
  | "--help" :: rest, options => parseArgs rest { options with help := true }
  | "--ast" :: rest, options => parseArgs rest { options with ast := true }
  | "--postgres" :: rest, options => parseArgs rest { options with postgres := true }
  | "--postgres-grammar" :: rest, options => parseArgs rest { options with postgresGrammar := true }
  | "--max-transitions" :: value :: rest, options => do
      if options.maxTransitions.isSome then throw "--max-transitions may only be specified once"
      let some fuel := value.toNat? | throw "--max-transitions requires a nonnegative integer"
      parseArgs rest { options with maxTransitions := some fuel }
  | "--render-assurance" :: mode :: rest, options => do
      if options.renderAssurance.isSome then throw "--render-assurance may only be specified once"
      let profile ← match mode with
        | "identity" => pure RenderContract.Profile.identityV01
        | "postgres" => pure .postgres16V01
        | "sqlite" => pure .sqliteV01
        | _ => throw "--render-assurance requires identity, postgres, or sqlite"
      parseArgs rest { options with renderAssurance := some profile }
  | "--assurance" :: level :: rest, options => do
      if options.assurance.isSome then throw "--assurance may only be specified once"
      let level ← match level with
        | "contract" => pure Assurance.Level.declarative
        | "checked" => pure .executable
        | "syntax" => pure .syntax
        | _ => throw "--assurance requires contract, checked, or syntax"
      parseArgs rest { options with assurance := some level }
  | "--max-depth" :: value :: rest, options => do
      if options.maxDepth.isSome then throw "--max-depth may only be specified once"
      let some depth := value.toNat? | throw "--max-depth requires a nonnegative integer"
      parseArgs rest { options with maxDepth := some depth }
  | "--param-types" :: types :: rest, options =>
      if options.parameterTypes.isSome then throw "--param-types may only be specified once"
      else parseArgs rest { options with parameterTypes := some types }
  | "--schema" :: path :: rest, options =>
      if options.schemaFile.isSome then throw "--schema may only be specified once"
      else parseArgs rest { options with schemaFile := some path }
  | "--file" :: path :: rest, options =>
      if options.queryFile.isSome || options.source.isSome then
        throw "supply exactly one SQL argument or --file"
      else parseArgs rest { options with queryFile := some path }
  | "--schema" :: [], _ => throw "--schema requires a path"
  | "--assurance" :: [], _ => throw "--assurance requires contract, checked, or syntax"
  | "--render-assurance" :: [], _ => throw "--render-assurance requires identity, postgres, or sqlite"
  | "--max-depth" :: [], _ => throw "--max-depth requires a nonnegative integer"
  | "--max-transitions" :: [], _ => throw "--max-transitions requires a nonnegative integer"
  | "--param-types" :: [], _ => throw "--param-types requires comma-separated types"
  | "--file" :: [], _ => throw "--file requires a path"
  | arg :: rest, options =>
      if arg.startsWith "--" then throw s!"unknown option: {arg}"
      else if options.source.isSome || options.queryFile.isSome then
        throw "supply one quoted SQL argument or --file"
      else parseArgs rest { options with source := some arg }

private def validateOptions (options : Options) : Except String Options := do
  if options.postgresGrammar &&
      (options.ast || options.postgres || options.assurance.isSome || options.renderAssurance.isSome ||
       options.schemaFile.isSome || options.parameterTypes.isSome || options.maxDepth.isSome) then
    throw "--postgres-grammar is a separate grammar/source report; incompatible validation/output option"
  if options.maxTransitions.isSome && !options.postgresGrammar then
    throw "--max-transitions requires --postgres-grammar"
  if options.renderAssurance.isSome &&
      (options.assurance.isSome || options.ast || options.postgres ||
       options.schemaFile.isSome || options.parameterTypes.isSome) then
    throw "--render-assurance cannot be combined with validation or other output modes"
  if options.assurance.isSome && (options.ast || options.postgres) then
    throw "--assurance emits JSON and cannot be combined with --ast or --postgres"
  if options.maxDepth.isSome && options.renderAssurance.isNone &&
      (options.assurance.isNone || options.assurance == some .syntax) then
    throw "--max-depth requires --assurance contract/checked or --render-assurance"
  pure options

private def bindingMapJson (entry : RenderContract.BindingMapEntry) : Lean.Json :=
  let (style, index) := match entry.source with
    | .numbered n => ("numbered", n) | .anonymous n => ("anonymous", n)
  Lean.Json.mkObj [
    ("source", Lean.Json.mkObj [("style", toJson style), ("index", toJson index)]),
    ("target", toJson entry.target)]

private def reportRender (profile : RenderContract.Profile) (status : String)
    (sql : Option String := none) (parameterMap : List RenderContract.BindingMapEntry := [])
    (diagnostic : Option RenderContract.Diagnostic := none) : IO UInt32 := do
  let mut fields := [
    ("assurance", toJson "checked-roundtrip"), ("profile", toJson profile.name),
    ("mode", toJson profile.mode), ("status", toJson status),
    ("evidence", toJson (if status == "rendered" then "checked-instance" else "none")),
    ("rendererVersion", toJson "0.2"),
    ("semanticPreservation", toJson false),
    ("assumptions", toJson profile.assumptions),
    ("trustedFoundations", toJson ["Lean kernel", "propext", "Classical.choice", "Quot.sound",
      "Lean compiler/runtime for executable reports"]),
    ("scope", toJson "SELECT AST serialization; independent target semantics not established")]
  if let some sql := sql then
    fields := fields ++ [
      ("sql", toJson sql), ("parameterMap", .arr (parameterMap.map bindingMapJson).toArray),
      ("theorems", toJson ["SQLean.RenderContract.check_roundTrip",
        "SQLean.RenderContract.check_admissible", "SQLean.RenderContract.check_canonical",
        "SQLean.RenderContract.render_expected_stable",
        "SQLean.RenderContract.Certificate.parameter_slots_injective",
        "SQLean.RenderContract.Certificate.parameter_map_complete",
        "SQLean.RenderContract.Certificate.transport_preserves"])]
  if let some diagnostic := diagnostic then
    fields := fields ++ [("diagnostic", Lean.Json.mkObj [
      ("code", toJson diagnostic.code), ("message", toJson diagnostic.message)])]
  IO.println (Lean.Json.mkObj fields).compress
  pure (match status with
    | "rendered" => 0 | "unsupported" => 3 | "inconclusive" => 4 | _ => 1)

private def runRenderAssurance (options : Options) (profile : RenderContract.Profile)
    (source : String) : IO UInt32 := do
  let parsed := if profile == .sqliteV01 then Advanced.parseSQLite source else Advanced.parse source
  let statement ← match parsed with
    | .ok statement => pure statement
    | .error error =>
        return ← reportRender profile "invalid" none [] (some ⟨"input.parse", toString error⟩)
  match statement with
  | .query query =>
    match RenderContract.check profile query (options.maxDepth.getD 1024) with
    | .ok certificate => reportRender profile "rendered" (some certificate.sql) certificate.parameterMap
    | .error failure => reportRender profile failure.status none [] (some failure.diagnostic)
  | _ => reportRender profile "unsupported" none [] (some ⟨"coverage.statement", "the rendering contract covers SELECT statements"⟩)

private def diagnosticJson (diagnostic : SelectContract.Diagnostic) : Lean.Json :=
  Lean.Json.mkObj [("code", toJson diagnostic.code), ("message", toJson diagnostic.message)]

-- Unmodified bpchar is different from the declaration CHAR (which implies
-- length one). Output metadata must preserve that distinction recursively.
private def contractSqlTypeName : SelectContract.ScalarType → String
  | .char [] => "bpchar"
  | .array element => contractSqlTypeName element ++ "[]"
  | type => type.dataType.toSql.toLower.replace ", " ","

private def contractColumnJson (column : SelectContract.OutputColumn) : Lean.Json :=
  let name := match column.type.base with
    | .int32 => "int32" | .text => "text" | .bool => "bool"
    | type => contractSqlTypeName type
  Lean.Json.mkObj [("name", toJson column.name), ("type", toJson name),
    ("nullable", toJson column.type.nullable)]

private def expandedTypeName : SqlType → String
  | .int => "int" | .text => "text" | .bool => "bool" | .real => "real"
  | .opaque name => name.name
  | .nullable base => expandedTypeName base
  | .array element => expandedTypeName element ++ "[]"

private def expandedColumnJson (column : ColumnDef) : Lean.Json :=
  let name := expandedTypeName column.type.base
  Lean.Json.mkObj [("name", toJson column.name), ("type", toJson name),
    ("nullable", toJson column.type.isNullable)]

private def report (level : Assurance.Level) (status : String)
    (columns : Option (List Lean.Json) := none) (diagnostic : Option SelectContract.Diagnostic := none)
    (catalogUnchanged : Bool := false) : IO UInt32 := do
  let profile := match level with
    | .declarative => SelectContract.Profile.basicV21.name
    | .executable => "sqlean-expanded-v0"
    | .syntax => "sqlean-syntax-v0"
  let evidence := match status with
    | "valid" => "declarative-derivation" | "checked" => "checker-acceptance"
    | "parsed" => "parsed-ast" | _ => "none"
  let mut fields := [("assurance", toJson level.name), ("status", toJson status),
    ("profile", toJson profile), ("evidence", toJson evidence)]
  if let some columns := columns then
    fields := fields ++ [("outputColumns", .arr columns.toArray),
      ("typePrecision", toJson (if level == .declarative then "exact" else "family"))]
  if let some diagnostic := diagnostic then fields := fields ++ [("diagnostic", diagnosticJson diagnostic)]
  if catalogUnchanged then fields := fields ++ [("catalogUnchanged", toJson true)]
  IO.println (Lean.Json.mkObj fields).compress
  pure (match status with
    | "valid" | "checked" | "parsed" => 0
    | "unsupported" => 3 | "inconclusive" => 4 | _ => 1)

private def runAssurance (options : Options) (level : Assurance.Level) (source : String) : IO UInt32 := do
  let statement ← match Advanced.parse source with
    | .ok statement => pure statement
    | .error error => throw (IO.userError s!"parse error: {error}")
  if level == .syntax then return ← report level "parsed"
  let schemaSource ← match options.schemaFile with
    | some path => IO.FS.readFile path
    | none => pure "{\"tables\":[]}"
  let catalog ← match Advanced.decodeCatalogJson schemaSource with
    | .ok catalog => pure catalog
    | .error error =>
      return ← report level (if level == .declarative then "invalid" else "rejected") none
        (some ⟨"environment.decode", error⟩)
  let fuel := options.maxDepth.getD 1024
  if level == .declarative then
    let params ← match Assurance.parseContractParameterTypes (options.parameterTypes.getD "") with
      | .ok params => pure params
      | .error error => return ← report level "invalid" none (some ⟨"environment.parameters", error⟩)
    match statement with
    | .query query =>
      match Assurance.checkContract .basicV21 catalog params query fuel with
      | .valid certificate => report level "valid" (some (certificate.output.map contractColumnJson)) none true
      | .invalid diagnostic => report level "invalid" none (some diagnostic)
      | .unsupported diagnostic => report level "unsupported" none (some diagnostic)
      | .inconclusive diagnostic => report level "inconclusive" none (some diagnostic)
    | _ => report level "unsupported" none (some ⟨"coverage.statement", "this contract covers SELECT statements"⟩)
  else
    let params ← match Advanced.parseParameterTypes (options.parameterTypes.getD "") with
      | .ok params => pure params
      | .error error => return ← report level "rejected" none (some ⟨"environment.parameters", error⟩)
    match statement with
    | .query query =>
      match Assurance.checkExpanded catalog params query fuel with
      | .checked certificate => report level "checked" (some (certificate.output.map expandedColumnJson)) none true
      | .rejected diagnostic => report level "rejected" none (some diagnostic)
      | .inconclusive diagnostic => report level "inconclusive" none (some diagnostic)
    | _ =>
      if options.maxDepth.isSome then
        return ← report level "unsupported" none
          (some ⟨"coverage.statement-budget", "custom --max-depth is available for SELECT only"⟩)
      match Advanced.checkStatementDetailed catalog params statement with
      | .ok result =>
        report level "checked" (some (result.outputTypes.map (fun type => expandedColumnJson ⟨"", type⟩)))
      | .error error =>
          if error.message == "advanced validation depth exhausted" then
            report level "inconclusive" none (some ⟨"resource.depth", error.message⟩)
          else report level "rejected" none (some ⟨"expanded.rejected", error.message⟩)

private def readStdin : IO String := do
  let stdin ← IO.getStdin
  let mut chunks : Array String := #[]
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    chunks := chunks.push line
  pure (String.join chunks.toList)

private def runPostgresGrammar (options : Options) (source : String) : IO UInt32 := do
  let (report, code) := PostgresGrammar.report source (options.maxTransitions.getD 1000000)
  IO.println report.compress
  pure code

private def run (options : Options) : IO UInt32 := do
  let source ← match options.source, options.queryFile with
    | some source, _ => pure source
    | _, some path => IO.FS.readFile path
    | _, _ => readStdin
  if options.postgresGrammar then return ← runPostgresGrammar options source
  if let some profile := options.renderAssurance then return ← runRenderAssurance options profile source
  if let some level := options.assurance then return ← runAssurance options level source
  let statement ← match parseStatement source with
    | .ok statement => pure statement
    | .error error => throw (IO.userError s!"parse error: {error}")
  if options.schemaFile.isSome || options.parameterTypes.isSome then
    let schemaSource ← match options.schemaFile with
      | some path => IO.FS.readFile path
      | none => pure "{\"tables\":[]}"
    let catalog ← match Advanced.parseCatalogJson schemaSource with
      | .ok catalog => pure catalog
      | .error error => throw (IO.userError s!"schema error: {error}")
    let params ← match Advanced.parseParameterTypes (options.parameterTypes.getD "") with
      | .ok params => pure params
      | .error error => throw (IO.userError s!"parameter error: {error}")
    let advanced : Bool := match statement with
      | .extended _ => true
      | _ => options.parameterTypes.isSome || catalog.any (fun table =>
        !table.keys.isEmpty || table.columns.any (fun column =>
          column.defaultValue.isSome || column.sqlType.isNullable || column.type.sqlType == .real))
    if advanced then
      let checked ← match parseAndValidateAdvanced catalog params source with
        | .ok checked => pure checked
        | .error error => throw (IO.userError (toString error))
      match checked.statement with
      | .query _ => IO.println s!"Valid query. Output types: {String.intercalate ", " (checked.result.outputTypes.map toSql)}"
      | .insert query =>
          if query.returning.isEmpty then IO.println "Valid INSERT statement."
          else IO.println s!"Valid query. Output types: {String.intercalate ", " (checked.result.outputTypes.map toSql)}"
      | .update query =>
          if query.returning.isEmpty then IO.println "Valid UPDATE statement."
          else IO.println s!"Valid query. Output types: {String.intercalate ", " (checked.result.outputTypes.map toSql)}"
      | .delete query =>
          if query.returning.isEmpty then IO.println "Valid DELETE statement."
          else IO.println s!"Valid query. Output types: {String.intercalate ", " (checked.result.outputTypes.map toSql)}"
      | _ => IO.println s!"Valid DDL statement. Catalog tables: {checked.result.catalog.length}"
    else match certifyStatement catalog.toSchema statement with
    | .ok certificate =>
      match statement with
      | .select _ | .relational _ | .returning _ _ =>
        IO.println s!"Valid query. Output types: {String.intercalate ", " (certificate.outputTypes.map toSql)}"
      | .insert _ => IO.println "Valid INSERT statement."
      | .update _ => IO.println "Valid UPDATE statement."
      | .delete _ => IO.println "Valid DELETE statement."
      | .extended _ => IO.println "Valid extended statement."
    | .error error => throw (IO.userError s!"validation error: {error}")
  if options.ast then IO.println (reprStr statement)
  else if options.postgres then
    match Advanced.parse source with
    | .ok statement => IO.println (Advanced.renderPostgres statement)
    | .error error => throw (IO.userError s!"parse error: {error}")
  else IO.println (toSql statement)
  pure 0

def main (args : List String) : IO UInt32 := do
  match (parseArgs args {}) >>= validateOptions with
  | .error error =>
    (← IO.getStderr).putStrLn s!"{error}\n{usage}"
    pure 2
  | .ok options =>
    if options.help then
      IO.print usage
      pure 0
    else
      try run options
      catch error =>
        (← IO.getStderr).putStrLn (toString error)
        pure 1
