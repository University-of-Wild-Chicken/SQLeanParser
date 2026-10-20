import SQLean.ScopeContract.Embedding
import Tests.ScopeContract
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command in
run_cmd do
  let environment ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in environment.constants.toList do
    if (`SQLean.ScopeContract).isPrefixOf name ||
        (`SQLean.Tests.ScopeContract).isPrefixOf name then
      for axiomName in (← collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "Scope contract declaration {name} depends on {axiomName}"
