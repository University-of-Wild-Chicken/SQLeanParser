import SQLean
import SQLean.SchemaJson

open SQLean

private def usage : String :=
  "Usage: sqlean [--ast] [--schema schema.json] [--file query.sql | SQL]\n\
   Parse one SELECT, INSERT, UPDATE, or DELETE. SELECT supports WITH RECURSIVE and UNION.\n\
   With no SQL or --file, read stdin.\n\
   --ast                  Print the public Lean AST\n\
   --schema schema.json   Also certify table/column resolution and types\n\
   --help                 Show this help\n"

private structure Options where
  ast : Bool := false
  schemaFile : Option String := none
  queryFile : Option String := none
  source : Option String := none
  help : Bool := false

private def parseArgs : List String → Options → Except String Options
  | [], options => pure options
  | "--help" :: rest, options => parseArgs rest { options with help := true }
  | "--ast" :: rest, options => parseArgs rest { options with ast := true }
  | "--schema" :: path :: rest, options =>
      if options.schemaFile.isSome then throw "--schema may only be specified once"
      else parseArgs rest { options with schemaFile := some path }
  | "--file" :: path :: rest, options =>
      if options.queryFile.isSome || options.source.isSome then
        throw "supply exactly one SQL argument or --file"
      else parseArgs rest { options with queryFile := some path }
  | "--schema" :: [], _ => throw "--schema requires a path"
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
  if let some path := options.schemaFile then
    let schemaSource ← IO.FS.readFile path
    let schema ← match parseSchemaJson schemaSource with
      | .ok schema => pure schema
      | .error error => throw (IO.userError s!"schema error: {error}")
    match certifyStatement schema statement with
    | .ok certificate =>
      match statement with
      | .select _ | .relational _ =>
        IO.println s!"Valid query. Output types: {String.intercalate ", " (certificate.outputTypes.map toSql)}"
      | .insert _ => IO.println "Valid INSERT statement."
      | .update _ => IO.println "Valid UPDATE statement."
      | .delete _ => IO.println "Valid DELETE statement."
    | .error error => throw (IO.userError s!"validation error: {error}")
  if options.ast then IO.println (reprStr statement)
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
