import SQLean.AdvancedSyntax

/-! Versioned serialization profiles. These are representation conditions, not
catalog/type checks and not a definition of PostgreSQL execution semantics. -/
namespace SQLean.RenderContract
open Advanced

deriving instance ReflBEq, LawfulBEq for Parameter

inductive Profile where
  /-- SQLean's PostgreSQL-shaped syntax with identity-preserving `?` markers. -/
  | identityV01
  /-- PostgreSQL 16 with anonymous markers translated to numbered slots. -/
  | postgres16V01
  /-- SQLite 3.39+ syntax with explicit numeric ?NNN binding slots. -/
  | sqliteV01
  deriving Repr, BEq, DecidableEq, Inhabited

def Profile.name : Profile → String
  | .identityV01 => "sqlean-select-render-v0.1"
  | .postgres16V01 => "postgresql-16-select-render-v0.1"
  | .sqliteV01 => "sqlite-3.39-select-render-v0.1"

def Profile.postgres : Profile → Bool
  | .identityV01 => false
  | .postgres16V01 => true
  | .sqliteV01 => false

def Profile.translate (profile : Profile) : Bool :=
  profile != .identityV01

def Profile.mode (profile : Profile) : String :=
  match profile with
  | .identityV01 => "identity" | .postgres16V01 => "postgres" | .sqliteV01 => "sqlite"

/-- Target assumptions are explicit. The SQLite profile keeps the common
63-byte name restriction and uses native SQLite binding and type behavior. -/
def Profile.assumptions : Profile → List String
  | .sqliteV01 =>
    ["SQLite>=3.39.0", "UTF8 input", "SQLITE_LIMIT_VARIABLE_NUMBER>=32766",
     "profile identifier limit=63 UTF8 bytes", "same database, namespace, and collation settings",
     "SQLite native types, NULL behavior and identifier rules; no PostgreSQL semantic equivalence"]
  | _ =>
    ["server_encoding=UTF8", "client_encoding=UTF8", "standard_conforming_strings=on",
     "max_identifier_length=63", "same catalog, search_path, and namespace interpretation"]

structure Diagnostic where
  code : String
  message : String
  deriving Repr, BEq, DecidableEq

inductive Failure where
  | invalid (diagnostic : Diagnostic)
  | unsupported (diagnostic : Diagnostic)
  | inconclusive (diagnostic : Diagnostic)
  /-- An implementation disagreement, never reclassified as bad user syntax. -/
  | mismatch (diagnostic : Diagnostic)
  deriving Repr, BEq, DecidableEq

def Failure.diagnostic : Failure → Diagnostic
  | .invalid d | .unsupported d | .inconclusive d | .mismatch d => d

def Failure.status : Failure → String
  | .invalid _ => "invalid" | .unsupported _ => "unsupported"
  | .inconclusive _ => "inconclusive" | .mismatch _ => "mismatch"

inductive ParameterStyle where
  | numbered | anonymous
  deriving Repr, BEq, DecidableEq

def parameterStyle : Parameter → ParameterStyle
  | .numbered _ => .numbered | .anonymous _ => .anonymous

def parameterSlot : Parameter → Nat
  | .numbered n | .anonymous n => n

/-- Database binding profiles have finite target-slot ranges. Identity
serialization does not impose a database transport limit. -/
def ProfileParameters (profile : Profile) (parameters : List Parameter) : Prop :=
  match profile with
  | .identityV01 => True
  | .postgres16V01 => parameters.all (fun p => parameterSlot p ≤ 65535) = true
  | .sqliteV01 => parameters.all (fun p => parameterSlot p ≤ 32766) = true

instance (profile : Profile) (parameters : List Parameter) :
    Decidable (ProfileParameters profile parameters) :=
  match profile with
  | .identityV01 => inferInstanceAs (Decidable True)
  | .postgres16V01 => inferInstanceAs (Decidable (_ = true))
  | .sqliteV01 => inferInstanceAs (Decidable (_ = true))

structure BindingMapEntry where
  source : Parameter
  target : Nat
  deriving Repr, BEq, DecidableEq

/-- Each referenced logical binding appears once, in first-occurrence order.
The slot identity is also used for declared types and separately supplied values. -/
def bindingMap (parameters : List Parameter) : List BindingMapEntry :=
  parameters.eraseDups.map fun p => ⟨p, parameterSlot p⟩

/-- Transport a separately supplied environment; no SQL literal substitution.
Polymorphism allows the same operation for values and concrete declared types. -/
def transport {α : Type} (style : ParameterStyle) (environment : Parameter → α)
    (slot : Nat) : α :=
  environment (match style with | .numbered => .numbered slot | .anonymous => .anonymous slot)

theorem transport_preserves {α : Type} (environment : Parameter → α)
    (parameter : Parameter) :
    transport (parameterStyle parameter) environment (parameterSlot parameter) =
      environment parameter := by
  cases parameter <;> rfl

theorem slot_injective_within_style (a b : Parameter)
    (sameStyle : parameterStyle a = parameterStyle b)
    (sameSlot : parameterSlot a = parameterSlot b) : a = b := by
  cases a <;> cases b <;> simp_all [parameterStyle, parameterSlot]

end SQLean.RenderContract
