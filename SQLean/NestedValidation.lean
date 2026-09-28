import SQLean.RelationalValidation

/-! Recursive certificates for nonrecursive CTEs and non-lateral derived tables.
Each child query is validated in its lexical schema before its named output is
introduced into the enclosing query. The resulting flat query uses the existing
relational typing/grouping rules. -/
namespace SQLean

/-- Names of outputs: aliases override natural column names; computed expressions
remain unnamed until an explicit alias or CTE column list supplies a name. -/
def relOutputNames (schema : Schema) (query : RelQuery) :
    Except ValidationError (List (Option Name)) := do
  let scope ← certifyRelFrom schema query
  let items ← expandRelProjection scope.val query.selectList
  pure (items.map fun item => item.alias.orElse fun _ =>
    match item.expr with | .column _ name => some name | _ => none)

/-- Materialize only well-named relation outputs. This rejects ambiguous duplicate
columns and unaliased computed outputs at a derived-table/CTE boundary. -/
def materializeRelTable (name : Name) (overrides : List Name) (types : List SqlType)
    (names : List (Option Name)) : Except ValidationError TableDef := do
  let resolved ← if overrides.isEmpty then
    names.mapM (fun name => match name with
      | some name => pure name
      | none => .error ⟨"derived tables and CTEs require aliases for computed output columns"⟩)
    else pure overrides
  if resolved.length ≠ types.length then
    throw ⟨"CTE column list does not match query output arity"⟩
  let table : TableDef := ⟨name, (resolved.zip types).map fun pair => ⟨pair.1, pair.2⟩⟩
  if WellFormedTable table then pure table
  else throw ⟨"virtual relation needs distinct nonempty output names and at least one column"⟩

/-- A lexical CTE shadows an equally named outer relation. -/
def withRelTable (schema : Schema) (table : TableDef) : Schema :=
  table :: schema.filter (fun previous => previous.name != table.name)

/-- Internal derived-table names are longer than every currently visible name. -/
def freshRelName (schema : Schema) : Name :=
  String.ofList (List.replicate (schema.foldl (fun n table => max n table.name.length) 0 + 1) '$')

def flatRelQuery (query : RelQuery) (source : TableRef) (joins : List Join) : RelQuery :=
  { query with source, joins, ctes := [] }

mutual
  /-- Full nested validity records every child derivation and the flat core proof. -/
  inductive NestedRelValid : Schema → RelQuery → List SqlType → List (Option Name) → Prop where
    | intro (schemaValid : WellFormedSchema schema)
        (ctes : RelCTEsValid schema query.ctes lexical)
        (source : RelSourceValid lexical lexical query.source withSource sourceRef)
        (joins : RelJoinsExpanded lexical withSource query.joins effective joinsOut)
        (core : ValidRelQueryCore effective (flatRelQuery query sourceRef joinsOut) types)
        (names : relOutputNames effective (flatRelQuery query sourceRef joinsOut) = .ok outputNames)
        (arity : outputNames.length = types.length) :
        NestedRelValid schema query types outputNames

  inductive RelCTEsValid : Schema → List CTE → Schema → Prop where
    | nil : RelCTEsValid schema [] schema
    | cons (nonempty : cte.name ≠ "")
        (unique : ∀ other ∈ rest, other.name ≠ cte.name)
        (child : NestedRelValid schema cte.query types names)
        (table : materializeRelTable cte.name cte.columns types names = .ok definition)
        (tail : RelCTEsValid (withRelTable schema definition) rest output) :
        RelCTEsValid schema (cte :: rest) output

  inductive RelSourceValid : Schema → Schema → TableRef → Schema → TableRef → Prop where
    | named (plain : source.derived = none)
        (found : (lexical.findTable source.name).isSome = true) :
        RelSourceValid lexical working source working source
    | derived (nested : source.derived = some query)
        (emptyName : source.name = "")
        (aliasValid : ∃ alias, source.alias = some alias ∧ alias ≠ "")
        (child : NestedRelValid lexical query types names)
        (table : materializeRelTable (freshRelName working) [] types names = .ok definition) :
        RelSourceValid lexical working source (definition :: working)
          { name := definition.name, alias := source.alias }

  inductive RelJoinsExpanded : Schema → Schema → List Join → Schema → List Join → Prop where
    | nil : RelJoinsExpanded lexical working [] working []
    | cons (source : RelSourceValid lexical working join.table next table)
        (tail : RelJoinsExpanded lexical next rest output joins) :
        RelJoinsExpanded lexical working (join :: rest) output ({ join with table } :: joins)
end

/-- Public validity hides output naming details but retains all nested proofs. -/
def ValidRelQuery (schema : Schema) (query : RelQuery) (types : List SqlType) : Prop :=
  ∃ names, NestedRelValid schema query types names

structure CertifiedRelQuery (schema : Schema) (query : RelQuery) where
  outputTypes : List SqlType
  outputNames : List (Option Name)
  derivation : NestedRelValid schema query outputTypes outputNames

theorem CertifiedRelQuery.valid (checked : CertifiedRelQuery schema query) :
    ValidRelQuery schema query checked.outputTypes := ⟨checked.outputNames, checked.derivation⟩

private structure CertifiedCTEs (inputSchema : Schema) (ctes : List CTE) where
  schema : Schema
  valid : RelCTEsValid inputSchema ctes schema

private structure CertifiedSource (lexical working : Schema) (source : TableRef) where
  schema : Schema
  ref : TableRef
  valid : RelSourceValid lexical working source schema ref

private structure CertifiedJoins (lexical working : Schema) (inputJoins : List Join) where
  schema : Schema
  joins : List Join
  valid : RelJoinsExpanded lexical working inputJoins schema joins

private def require (proposition : Prop) [Decidable proposition] (message : String) :
    Except ValidationError (PLift proposition) :=
  if proof : proposition then .ok ⟨proof⟩ else .error ⟨message⟩

private structure NamedOutputs (schema : Schema) (query : RelQuery) where
  names : List (Option Name)
  proof : relOutputNames schema query = .ok names

private def certifyNames (schema : Schema) (query : RelQuery) : Except ValidationError (NamedOutputs schema query) :=
  match h : relOutputNames schema query with
  | .error error => .error error
  | .ok names => .ok ⟨names, h⟩

private structure Materialized (name : Name) (overrides : List Name) (types : List SqlType)
    (names : List (Option Name)) where
  table : TableDef
  proof : materializeRelTable name overrides types names = .ok table

private def certifyMaterialization (name : Name) (overrides : List Name) (types : List SqlType)
    (names : List (Option Name)) : Except ValidationError (Materialized name overrides types names) :=
  match h : materializeRelTable name overrides types names with
  | .error error => .error error
  | .ok table => .ok ⟨table, h⟩

mutual
  /-- Certify nested SELECTs without a fixed nesting-depth limit. -/
  def certifyRelQuery (schema : Schema) (query : RelQuery) :
      Except ValidationError (CertifiedRelQuery schema query) := do
    let schemaValid ← checkSchema schema
    let ctes ← certifyRelCTEs schema query.ctes
    let source ← certifyRelSource ctes.schema ctes.schema query.source
    let joins ← certifyRelJoinSources ctes.schema source.schema query.joins
    let core ← certifyRelQueryCore joins.schema (flatRelQuery query source.ref joins.joins)
    let names ← certifyNames joins.schema (flatRelQuery query source.ref joins.joins)
    let arity ← require (names.names.length = core.outputTypes.length) "inconsistent output naming arity"
    pure ⟨core.outputTypes, names.names,
      .intro schemaValid.down ctes.valid source.valid joins.valid core.valid names.proof arity.down⟩
  termination_by sizeOf query
  decreasing_by all_goals cases query; simp_all; omega

  private def certifyRelCTEs (schema : Schema) (ctes : List CTE) :
      Except ValidationError (CertifiedCTEs schema ctes) :=
    match ctes with
    | [] => pure ⟨schema, .nil⟩
    | cte :: rest => do
      let nonempty ← require (cte.name ≠ "") "empty CTE name"
      let unique ← require (∀ other ∈ rest, other.name ≠ cte.name) "duplicate CTE name"
      let child ← certifyRelQuery schema cte.query
      let table ← certifyMaterialization cte.name cte.columns child.outputTypes child.outputNames
      let tail ← certifyRelCTEs (withRelTable schema table.table) rest
      pure ⟨tail.schema, .cons nonempty.down unique.down child.derivation table.proof tail.valid⟩
  termination_by sizeOf ctes
  decreasing_by all_goals simp_all; cases cte <;> simp_all <;> omega

  private def certifyRelSource (lexical working : Schema) (source : TableRef) :
      Except ValidationError (CertifiedSource lexical working source) :=
    match h : source.derived with
    | none => do
      let found ← require ((lexical.findTable source.name).isSome = true) s!"unknown table '{source.name}'"
      pure ⟨working, source, .named h found.down⟩
    | some query => do
      let emptyName ← require (source.name = "") "a derived source cannot also name a physical table"
      let aliasValid ← require (source.alias.isSome = true ∧ source.alias ≠ some "") "derived table requires a nonempty alias"
      let aliasProof : ∃ alias, source.alias = some alias ∧ alias ≠ "" := by
        have hvalid := aliasValid.down
        cases ha : source.alias with
        | none => simp [ha] at hvalid
        | some alias => exact ⟨alias, rfl, by simpa [ha] using hvalid.2⟩
      let child ← certifyRelQuery lexical query
      let table ← certifyMaterialization (freshRelName working) [] child.outputTypes child.outputNames
      pure ⟨table.table :: working, { name := table.table.name, alias := source.alias },
        .derived h emptyName.down aliasProof child.derivation table.proof⟩
  termination_by sizeOf source
  decreasing_by all_goals cases source; simp_all; omega

  private def certifyRelJoinSources (lexical working : Schema) (joins : List Join) :
      Except ValidationError (CertifiedJoins lexical working joins) :=
    match joins with
    | [] => pure ⟨working, [], .nil⟩
    | join :: rest => do
      let source ← certifyRelSource lexical working join.table
      let tail ← certifyRelJoinSources lexical source.schema rest
      pure ⟨tail.schema, { join with table := source.ref } :: tail.joins, .cons source.valid tail.valid⟩
  termination_by sizeOf joins
  decreasing_by all_goals simp_all; cases join <;> simp_all <;> omega
end

/-- Selected result types, retaining proofs in the certificate API. -/
def checkRelQuery (schema : Schema) (query : RelQuery) : Except ValidationError (List SqlType) :=
  (certifyRelQuery schema query).map CertifiedRelQuery.outputTypes

theorem checkRelQuery_sound (success : checkRelQuery schema query = .ok types) :
    ValidRelQuery schema query types := by
  unfold checkRelQuery at success
  cases checked : certifyRelQuery schema query with
  | error error => simp [checked, Except.map] at success
  | ok result =>
      simp [checked, Except.map] at success
      exact success ▸ result.valid

private theorem require_complete (proof : proposition) [Decidable proposition] (message : String) :
    require proposition message = .ok ⟨proof⟩ := by
  simp [require, proof]

private theorem certifyNames_complete (proof : relOutputNames schema query = .ok names) :
    certifyNames schema query = .ok ⟨names, proof⟩ := by
  unfold certifyNames
  split
  · simp_all
  · rename_i names' proof'
    have same := Except.ok.inj (proof'.symm.trans proof)
    subst names'
    rfl

private theorem certifyMaterialization_complete
    (proof : materializeRelTable name overrides types names = .ok table) :
    certifyMaterialization name overrides types names = .ok ⟨table, proof⟩ := by
  unfold certifyMaterialization
  split
  · simp_all
  · rename_i table' proof'
    have same := Except.ok.inj (proof'.symm.trans proof)
    subst table'
    rfl

/-- Every derivation of recursive relational validity receives its exact certificate. -/
theorem certifyRelQuery_complete (valid : NestedRelValid schema query types names) :
    certifyRelQuery schema query = .ok ⟨types, names, valid⟩ := by
  refine NestedRelValid.rec
    (motive_1 := fun schema query types names valid =>
      certifyRelQuery schema query = .ok ⟨types, names, valid⟩)
    (motive_2 := fun schema ctes output valid =>
      certifyRelCTEs schema ctes = .ok ⟨output, valid⟩)
    (motive_3 := fun lexical working source output ref valid =>
      certifyRelSource lexical working source = .ok ⟨output, ref, valid⟩)
    (motive_4 := fun lexical working joins output result valid =>
      certifyRelJoinSources lexical working joins = .ok ⟨output, result, valid⟩)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ valid
  · intro schema lexical withSource sourceRef effective joinsOut query types names
      schemaValid ctes source joins core namesProof arity ihCTEs ihSource ihJoins
    simp [certifyRelQuery, checkSchema, schemaValid, ihCTEs, ihSource, ihJoins,
      certifyRelQueryCore_complete core, certifyNames_complete namesProof, require_complete arity,
      pure, bind, Except.bind, Except.pure]
  · intro schema
    simp [certifyRelCTEs, pure, Except.pure]
  · intro rest schema types names definition output cte nonempty unique child table tail ihChild ihTail
    simp [certifyRelCTEs, require_complete nonempty, require_complete unique, ihChild,
      certifyMaterialization_complete table, ihTail, pure, bind, Except.bind, Except.pure]
  · intro lexical working source plain found
    simp only [certifyRelSource]
    split
    · simp [require_complete found, pure, bind, Except.bind, Except.pure]
    · rename_i query contradiction
      cases plain.symm.trans contradiction
  · intro query lexical types names working definition source nested emptyName aliasValid child table ihChild
    have aliasCondition : source.alias.isSome = true ∧ source.alias ≠ some "" := by
      obtain ⟨alias, equality, nonempty⟩ := aliasValid
      simp [equality, nonempty]
    simp only [certifyRelSource]
    split
    · rename_i contradiction
      cases contradiction.symm.trans nested
    · rename_i query' nested'
      have same := Option.some.inj (nested'.symm.trans nested)
      subst query'
      simp [require_complete emptyName, require_complete aliasCondition, ihChild,
        certifyMaterialization_complete table, pure, bind, Except.bind, Except.pure]
  · intro lexical working
    simp [certifyRelJoinSources, pure, Except.pure]
  · intro lexical working next table rest output joins join source tail ihSource ihTail
    simp [certifyRelJoinSources, ihSource, ihTail, pure, bind, Except.bind, Except.pure]

/-- Soundness and completeness for the full static contract, including all child queries. -/
theorem checkRelQuery_iff : checkRelQuery schema query = .ok types ↔ ValidRelQuery schema query types := by
  constructor
  · exact checkRelQuery_sound
  · rintro ⟨names, valid⟩
    simp [checkRelQuery, certifyRelQuery_complete valid, Except.map]

end SQLean
