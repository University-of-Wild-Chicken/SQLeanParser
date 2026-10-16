import SQLean
import SQLean.SchemaJson

open SQLean

private def usage : String :=
  "Usage: sqlean [--ast] [--schema schema.json] [--param-types int,text] [--postgres] [--file query.sql | SQL]\n\
   Parse one SELECT, INSERT, UPDATE, or DELETE, or CREATE/ALTER/DROP TABLE.\n\
   With no SQL or --file, read stdin.\n\
   --ast                  Print the public Lean AST\n\
   --schema schema.json   Also certify table/column resolution and types\n\
   --param-types TYPES    Parameter types in position order (int,text,bool,real; suffix ? permits NULL)\n\
   --postgres             Render anonymous ? parameters as PostgreSQL $n\n\
   --help                 Show this help\n"

private structure Options where
  ast : Bool := false
  schemaFile : Option String := none
  queryFile : Option String := none
  source : Option String := none
  help : Bool := false
  parameterTypes : Option String := none
  postgres : Bool := false

private def parseArgs : List String → Options → Except String Options
  | [], options => pure options
  | "--help" :: rest, options => parseArgs rest { options with help := true }
  | "--ast" :: rest, options => parseArgs rest { options with ast := true }
  | "--postgres" :: rest, options => parseArgs rest { options with postgres := true }
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
  | "--param-types" :: [], _ => throw "--param-types requires comma-separated types"
  | "--file" :: [], _ => throw "--file requires a path"
  | arg :: rest, options =>
      if arg.startsWith "--" then throw s!"unknown option: {arg}"
      else if options.source.isSome || options.queryFile.isSome then
        throw "supply one quoted SQL argument or --file"
      else parseArgs rest { options with source := some arg }

private def readStdin : IO String := do
  let stdin ← IO.getStdin
  let mut chunks : Array String := #[]
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    chunks := chunks.push line
  pure (String.join chunks.toList)

private def run (options : Options) : IO UInt32 := do
  let source ← match options.source, options.queryFile with
    | some source, _ => pure source
    | _, some path => IO.FS.readFile path
    | _, _ => readStdin
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
  match parseArgs args {} with
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
