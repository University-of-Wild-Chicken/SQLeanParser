import Lean.Util.CollectAxioms
import Lean.Elab.Command
import Lean.Compiler.Old

/-! Project-wide declaration audit, invoked after importing every project module
by scripts/check_lean_trust.py. Ownership is determined from the originating
module, so private declarations and declarations outside SQLean namespaces are
covered. The three explicitly reported foundational axioms are Lean's standard
logical foundations; this project adds no axioms to that allowlist.

Lean generates executable `_unsafe_rec` helpers for recursive definitions and
opaque derived BEq functions. Only those helpers with a corresponding safe
kernel declaration in the same module are permitted; their axiom dependencies
are still checked, and they are counted in the report. Opaque runtime helpers
are not kernel reduction rules and cannot supply a proof by native computation.
The source guard complements this dependency audit by rejecting bypass syntax
before elaboration. This is a trust-boundary check, not a semantic SQL theorem.
-/

namespace SQLean.Tests.Trust

open Lean Elab Command

/-- Run after the caller has imported the complete project module inventory. -/
def auditProjectDeclarations (projectModules : Array Name) : CommandElabM Unit := do
  let environment ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  if projectModules.isEmpty then
    throwError "Project trust audit requires an explicit nonempty source-module inventory"
  for moduleName in projectModules do
    unless (environment.getModuleIdx? moduleName).isSome do
      throwError "Project trust audit did not import inventoried module {moduleName}"
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut compilerHelpers : Nat := 0
  for (name, info) in environment.constants.toList do
    let some moduleIndex := environment.getModuleIdxFor? name | continue
    let some moduleName := environment.allImportedModuleNames[moduleIndex.toNat]? | continue
    if projectModules.contains moduleName then
      declarations := declarations + 1
      if info.isUnsafe then
        throwError "Project declaration {name} in {moduleName} is unsafe"
      if info.isPartial then
        match Compiler.isUnsafeRecName? name with
        | some parent =>
            let safeParent := match environment.find? parent with
              | some (.defnInfo definition) => definition.safety == .safe
              | some (.opaqueInfo definition) => !definition.isUnsafe
              | _ => false
            if safeParent && environment.getModuleIdxFor? parent == some moduleIndex then
              compilerHelpers := compilerHelpers + 1
            else throwError "Partial helper {name} in {moduleName} has no safe kernel declaration in its module"
        | none => throwError "Project declaration {name} in {moduleName} is partial"
      match info with
      | .axiomInfo _ => throwError "Project declaration {name} in {moduleName} is a custom axiom"
      | .thmInfo _ => theorems := theorems + 1
      | _ => pure ()
      for dependency in (← collectAxioms name) do
        unless allowed.contains dependency do
          throwError "Project declaration {name} in {moduleName} depends on disallowed axiom {dependency}"
  if declarations == 0 || theorems == 0 then
    throwError "Project trust audit found no declarations or no theorems; import the project before auditing"
  logInfo m!"PASS: trust audit checked {declarations} project declarations, including {theorems} theorems and {compilerHelpers} generated executable recursion helpers; allowed foundations: propext, Classical.choice, Quot.sound"

end SQLean.Tests.Trust
