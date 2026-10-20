import SQLean.SelectContract.Checker
import SQLean.AdvancedParser
import SQLean.AdvancedValidation

/-! Explicit SELECT assurance tiers. A successful expanded executable check is
never promoted to an independent SELECT-contract derivation. The compatibility
APIs and all existing syntax remain available unchanged. -/
namespace SQLean.Assurance

inductive Level where
  | syntax | executable | declarative
  deriving Repr, BEq, DecidableEq

def Level.name : Level → String
  | .syntax => "syntax"
  | .executable => "executable"
  | .declarative => "declarative"

/-- Four contract outcomes, with a derivation only in the `valid` branch. -/
inductive ContractOutcome (profile : SelectContract.Profile) (catalog : Advanced.Catalog)
    (params : SelectContract.ParameterEnv) (query : Advanced.Query) where
  | valid (certificate : SelectContract.Certificate profile catalog params query)
  | invalid (diagnostic : SelectContract.Diagnostic)
  | unsupported (diagnostic : SelectContract.Diagnostic)
  | inconclusive (diagnostic : SelectContract.Diagnostic)

def checkContract (profile : SelectContract.Profile) (catalog : Advanced.Catalog)
    (params : SelectContract.ParameterEnv) (query : Advanced.Query) (fuel : Nat := 1024) :
    ContractOutcome profile catalog params query :=
  match SelectContract.checkQuery profile catalog params query fuel with
  | .ok certificate => .valid certificate
  | .error (.invalid diagnostic) => .invalid diagnostic
  | .error (.unsupported diagnostic) => .unsupported diagnostic
  | .error (.inconclusive diagnostic) => .inconclusive diagnostic

/-- Each successful contract outcome carries the independent specification proof. -/
theorem contract_valid_sound (certificate : SelectContract.Certificate profile catalog params query) :
    SelectContract.SelectValid profile catalog params query certificate.output :=
  certificate.valid

structure ParsedContract (profile : SelectContract.Profile) (catalog : Advanced.Catalog)
    (params : SelectContract.ParameterEnv) where
  query : Advanced.Query
  outcome : ContractOutcome profile catalog params query

/-- Parsing failure is separate from the four AST-level contract outcomes. -/
def parseContract (profile : SelectContract.Profile) (catalog : Advanced.Catalog)
    (params : SelectContract.ParameterEnv) (source : String) (fuel : Nat := 1024) :
    Except ParseError (ParsedContract profile catalog params) := do
  let query ← Advanced.parseQuery source
  pure ⟨query, checkContract profile catalog params query fuel⟩

/-- The existing expanded check, exposed with an explicit resource bound and
ordered output names. Its result types are the older coarse SqlType families. -/
def expandedCheck (catalog : Advanced.Catalog) (params : Advanced.ParameterEnv)
    (query : Advanced.Query) (fuel : Nat) : Except ValidationError (List ColumnDef) := do
  Advanced.checkCatalogDefaults catalog
  Advanced.checkParameterEnv params
  -- Type traversal must finish before consulting the fuel-bounded collector:
  -- a truncated list of anonymous parameters is not a notation violation.
  let output ← Advanced.checkQueryFuel fuel catalog.toSchema params [] query
  Advanced.checkParameterUses (Advanced.queryParameters fuel query)
  pure output

structure ExpandedCertificate (catalog : Advanced.Catalog) (params : Advanced.ParameterEnv)
    (query : Advanced.Query) (fuel : Nat) where
  output : List ColumnDef
  accepted : expandedCheck catalog params query fuel = .ok output

/-- `checked` deliberately differs from contract `valid`; `rejected` is an
implementation result, not a proof that the independent contract is violated. -/
inductive ExpandedOutcome (catalog : Advanced.Catalog) (params : Advanced.ParameterEnv)
    (query : Advanced.Query) (fuel : Nat) where
  | checked (certificate : ExpandedCertificate catalog params query fuel)
  | rejected (diagnostic : SelectContract.Diagnostic)
  | inconclusive (diagnostic : SelectContract.Diagnostic)

def checkExpanded (catalog : Advanced.Catalog) (params : Advanced.ParameterEnv)
    (query : Advanced.Query) (fuel : Nat := 1024) : ExpandedOutcome catalog params query fuel :=
  match h : expandedCheck catalog params query fuel with
  | .ok output => .checked ⟨output, h⟩
  | .error error =>
      -- The compatibility checker predates typed diagnostics. This bridge maps
      -- its one resource-exhaustion diagnostic without changing its old API.
      if error.message == "advanced validation depth exhausted" then
        .inconclusive ⟨"resource.depth", error.message⟩
      else .rejected ⟨"expanded.rejected", error.message⟩

/-- Exact parameter declarations for the contract API, including precision,
scale, lengths, and nullable suffixes. No numeric-family conversion occurs. -/
def parseContractParameterTypes (source : String) : Except String SelectContract.ParameterEnv := do
  let declarations ← (Advanced.parseParameterDeclarations source).mapError toString
  pure (declarations.zipIdx.map fun ((type, nullable), index) =>
    { index := index + 1, type, nullable })

end SQLean.Assurance
