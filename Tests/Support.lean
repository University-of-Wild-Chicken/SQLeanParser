import SQLean.AST

namespace SQLean.Tests

def assert (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def expectOk {ε α : Type} [ToString ε] (label : String) (result : Except ε α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: unexpected error: {error}")

def expectError {ε α : Type} (label : String) (result : Except ε α) : IO Unit :=
  match result with
  | .ok _ => throw (IO.userError s!"{label}: unexpectedly accepted")
  | .error _ => pure ()

end SQLean.Tests
