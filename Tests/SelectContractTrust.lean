import SQLean.SelectContract.Checker
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! CI guard: every declaration in the new contract namespace must depend only
on Lean's standard logical axioms. This rejects sorryAx, native_decide axioms,
and custom assumptions, including dependencies through helper declarations. -/
open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let contractNamespace : Name := `SQLean.SelectContract
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in environment.constants.toList do
    if contractNamespace.isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "SELECT contract declaration {name} depends on disallowed axiom {axiomName}"
