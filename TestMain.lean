import Tests

def main : IO UInt32 := do
  try
    SQLean.Tests.run
    pure 0
  catch error =>
    (← IO.getStderr).putStrLn s!"FAIL: {error}"
    pure 1
