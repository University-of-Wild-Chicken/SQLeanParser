import SQLean.PostgresGrammar.Report

private def readStdin : IO String := do
  let input ← IO.getStdin
  let mut chunks := #[]
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    chunks := chunks.push line
  pure (String.join chunks.toList)

private def batch (fuel : Nat) : IO UInt32 := do
  let input ← IO.getStdin
  let mut result : UInt32 := 0
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let decoded := do
      let json ← Lean.Json.parse line
      let id ← json.getObjValAs? String "id"
      let sql ← json.getObjValAs? String "sql"
      pure (id, sql)
    match decoded with
    | .error error =>
        IO.println (Lean.Json.mkObj [
          ("status", Lean.toJson "invalid-request"), ("diagnostic", Lean.toJson error)]).compress
        result := 2
    | .ok (id, sql) =>
        let (report, code) := SQLean.PostgresGrammar.report sql fuel
        IO.println (Lean.Json.mkObj [
          ("id", Lean.toJson id), ("result", report)]).compress
        if result == 0 && code != 0 then result := code
  pure result

def main (args : List String) : IO UInt32 := do
  let (fuel, args) ← match args with
    | "--max-transitions" :: amount :: rest =>
        match amount.toNat? with
        | some fuel => pure (fuel, rest)
        | none => throw (IO.userError "--max-transitions requires a nonnegative integer")
    | _ => pure (1000000, args)
  if args == ["--jsonl"] then return ← batch fuel
  if args == ["--help"] then
    IO.println "Usage: sqlean_pg_grammar [--max-transitions N] [--jsonl | --file PATH | SQL]\nWith no SQL, read stdin. --jsonl reads {id,sql} per line. This API certifies grammar derivations and exact source preservation, not SQL static validity or C semantic actions."
    return 0
  let source ← match args with
    | [] => readStdin
    | ["--file", path] => IO.FS.readFile path
    | [source] => pure source
    | _ => throw (IO.userError "expected one SQL argument, --file PATH, or --jsonl")
  let (report, code) := SQLean.PostgresGrammar.report source fuel
  IO.println report.compress
  pure code
