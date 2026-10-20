import SQLean.RenderContract.Admissibility
import SQLean.RenderContract.SQLiteAdmissibility
import SQLean.RenderContract.Translation
import SQLean.AdvancedEquality
import SQLean.AdvancedParser
import SQLean.AdvancedPretty
import SQLean.SQLitePretty
import SQLean.RenderContract.SerializationProofs
import SQLean.RenderContract.SQLiteSerializationProofs

/-! Checked serialization with proof-carrying *instance* round trips. This is
not a proof that every admissible AST passes the check, nor an independent
PostgreSQL grammar/semantics theorem. Rejection by the independent admissibility
boundary, resource limits, and implementation disagreement are distinct. -/
namespace SQLean.RenderContract
open Advanced

def expectedQuery (profile : Profile) (query : Advanced.Query) : Advanced.Query :=
  if profile.translate then translateParameters query else query

def renderQuery (profile : Profile) (query : Advanced.Query) : String :=
  match profile with
  | .identityV01 => query.toSql
  | .postgres16V01 => query.toSql true
  | .sqliteV01 => query.toSQLite

def renderSql (profile : Profile) (query : Advanced.Query) : String :=
  renderQuery profile query ++ ";"

def parseRendered (profile : Profile) (sql : String) : Except ParseError Advanced.Query :=
  match profile with
  | .sqliteV01 => Advanced.parseSQLiteQuery sql
  | _ => Advanced.parseQuery sql

def checkDialect (profile : Profile) (query : Advanced.Query) : Except Failure Unit :=
  match profile with
  | .sqliteV01 => checkSQLiteQuery query
  | _ => .ok ()

/-- A general byte-preservation law, independent of admissibility, successful
parsing, budgets, and test corpora. Canonical parameter translation cannot
change the selected renderer's output. -/
theorem render_expected_stable (profile : Profile) (query : Advanced.Query) :
    renderSql profile (expectedQuery profile query) = renderSql profile query := by
  cases profile with
  | identityV01 => rfl
  | postgres16V01 => exact renderPostgres_translateParameters query
  | sqliteV01 => exact renderSQLite_translateParameters query

def selectedStyle (parameters : List Parameter) : ParameterStyle :=
  parameterStyle (parameters.headD (.numbered 1))

def StyleMatches (parameters : List Parameter) (style : ParameterStyle) : Prop :=
  ∀ p ∈ parameters, parameterStyle p = style

instance (parameters : List Parameter) (style : ParameterStyle) :
    Decidable (StyleMatches parameters style) :=
  inferInstanceAs (Decidable (∀ p ∈ parameters, _))

/-- Indexed by the exact original query and profile. Equality is Lean equality
over all fields, not the existing unchecked Boolean equality instance. -/
structure Certificate (profile : Profile) (query : Advanced.Query) where
  footprint : Footprint
  inspected : inspectQuery query = .ok footprint
  parameterDiscipline : ParameterDiscipline footprint.parameters
  profileParameters : ProfileParameters profile footprint.parameters
  dialectCoverage : checkDialect profile query = .ok ()
  uniformStyle : UniformStyle footprint.parameters
  styleMatches : StyleMatches footprint.parameters (selectedStyle footprint.parameters)
  sql : String
  serialized : sql = renderSql profile query
  roundTrip : parseRendered profile sql = .ok (expectedQuery profile query)
  canonical : renderSql profile (expectedQuery profile query) = sql

theorem Certificate.admissible (certificate : Certificate profile query) : Admissible query :=
  ⟨certificate.footprint, certificate.inspected, certificate.parameterDiscipline,
    certificate.uniformStyle⟩

def Certificate.parameterMap (certificate : Certificate profile query) : List BindingMapEntry :=
  bindingMap certificate.footprint.parameters

def Certificate.style (certificate : Certificate profile query) : ParameterStyle :=
  selectedStyle certificate.footprint.parameters

/-- Use this same transport for values and type declarations. Gaps in numbered
slots remain gaps; callers must respect the target driver's binding interface. -/
def Certificate.transport {α : Type} (certificate : Certificate profile query)
    (environment : Parameter → α) : Nat → α :=
  RenderContract.transport certificate.style environment

theorem Certificate.transport_preserves {α : Type} (certificate : Certificate profile query)
    (environment : Parameter → α) (parameter : Parameter)
    (referenced : parameter ∈ certificate.footprint.parameters) :
    certificate.transport environment (parameterSlot parameter) = environment parameter := by
  unfold Certificate.transport Certificate.style
  rw [← certificate.styleMatches parameter referenced]
  exact RenderContract.transport_preserves environment parameter

theorem Certificate.parameter_slots_injective (certificate : Certificate profile query)
    (a b : Parameter) (ha : a ∈ certificate.footprint.parameters)
    (hb : b ∈ certificate.footprint.parameters)
    (sameSlot : parameterSlot a = parameterSlot b) : a = b :=
  slot_injective_within_style a b (certificate.uniformStyle a ha b hb) sameSlot

/-- All referenced bindings occur in the explicit returned map. -/
theorem Certificate.parameter_map_complete (certificate : Certificate profile query)
    (parameter : Parameter) (referenced : parameter ∈ certificate.footprint.parameters) :
    (⟨parameter, parameterSlot parameter⟩ : BindingMapEntry) ∈ certificate.parameterMap := by
  simp only [Certificate.parameterMap, bindingMap, List.mem_map]
  exact ⟨parameter, (List.mem_eraseDups).mpr referenced, rfl⟩

theorem Certificate.one_terminator (certificate : Certificate profile query) :
    certificate.sql = renderQuery profile query ++ ";" := by
  rw [certificate.serialized]
  rfl

/-- Input inspection is total. The depth cap bounds entry into serialization
and full reparsing; it is not an operating-system memory or time guarantee. -/
def check (profile : Profile) (query : Advanced.Query) (maxDepth : Nat := 1024) :
    Except Failure (Certificate profile query) := do
  match inspected : inspectQuery query with
  | .error error => throw error
  | .ok footprint =>
    if footprint.depth > maxDepth then
      throw (.inconclusive ⟨"resource.depth", "AST exceeds the requested rendering/reparse depth budget"⟩)
    else if profileParameters : ProfileParameters profile footprint.parameters then
      if styles : StyleMatches footprint.parameters (selectedStyle footprint.parameters) then
        have uniform : UniformStyle footprint.parameters :=
          fun p hp q hq => (styles p hp).trans (styles q hq).symm
        if discipline : ParameterDiscipline footprint.parameters then
          match coverage : checkDialect profile query with
          | .error failure => throw failure
          | .ok () =>
            let sql := renderSql profile query
            match parsed : parseRendered profile sql with
            | .error error =>
                throw (.mismatch ⟨"roundtrip.parse", s!"renderer output did not fully reparse: {error}"⟩)
            | .ok actual =>
              if same : actual = expectedQuery profile query then
                pure {
                  footprint, inspected, parameterDiscipline := discipline, profileParameters
                  dialectCoverage := coverage, uniformStyle := uniform
                  styleMatches := styles, sql, serialized := rfl
                  roundTrip := by rw [parsed, same]
                  canonical := render_expected_stable profile query
                }
              else throw (.mismatch ⟨"roundtrip.ast", "full reparsing changed an AST field"⟩)
        else throw (.invalid ⟨"representation.parameters",
          "numbered slots must be positive; anonymous ordinals must be exactly 1..N in statement order"⟩)
      else throw (.unsupported ⟨"coverage.mixed-parameters",
        "mixed numbered and anonymous bindings need a separate collision-free mapping contract"⟩)
    else throw (.unsupported ⟨"coverage.parameter-slot",
        "parameter slot exceeds the selected target binding limit"⟩)

/-- Success implies exact full reconstruction of this instance. It does not
assert success for every admissible input or target-language semantics. -/
theorem check_roundTrip (certificate : Certificate profile query) :
    parseRendered profile certificate.sql = .ok (expectedQuery profile query) :=
  certificate.roundTrip

theorem check_admissible (certificate : Certificate profile query) : Admissible query :=
  certificate.admissible

theorem check_canonical (certificate : Certificate profile query) :
    renderSql profile (expectedQuery profile query) = certificate.sql :=
  certificate.canonical

end SQLean.RenderContract
