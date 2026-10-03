import SQLean.RelationalValidation

/-! Structural certificates for derived tables, compound queries, and portable
recursive CTEs. Each child is checked in its lexical schema. Recursive CTEs check
an independent anchor, materialize its output schema, then check the recursive
step against that schema. UNION arms must have identical type vectors. The
contract establishes static scope, shape, and type consistency; it does not
establish execution termination, cycle safety, or runtime result equivalence. -/
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


/-- Drop the enclosing WITH and compound-query envelope before core typing. -/
def flatRelQuery (query : RelQuery) (source : TableRef) (joins : List Join) : RelQuery :=
  { query with
    source := source
    joins := joins
    ctes := []
    recursive := false
    unions := []
    orderBy := if query.unions.isEmpty then query.orderBy else []
    limit := if query.unions.isEmpty then query.limit else none
    offset := if query.unions.isEmpty then query.offset else none }

/-- Recursive WITH reserves its current and future relation names. -/
def cteInputSchema (schema : Schema) (recursive : Bool) (ctes : List CTE) : Schema :=
  if recursive then schema.filter (fun table => !(ctes.any fun cte => cte.name == table.name))
  else schema

mutual
  /-- Free relation references respect nested WITH bindings. An ordinary binding
  shadows its name after its own RHS; recursive local bindings shadow throughout. -/
  def relReferences (name : Name) (query : RelQuery) : Bool :=
    let shadowed := query.ctes.any (fun cte => cte.name == name)
    if query.recursive && shadowed then false
    else ctesReferences name query.ctes || (!shadowed &&
      (sourceReferences name query.source || joinsReferences name query.joins ||
        unionsReferences name query.unions))
  termination_by sizeOf query
  decreasing_by all_goals cases query; simp_all <;> omega

  def sourceReferences (name : Name) (source : TableRef) : Bool :=
    source.name == name || match _h : source.derived with
      | none => false
      | some query => relReferences name query
  termination_by sizeOf source
  decreasing_by all_goals cases source; simp_all; omega

  def joinsReferences (name : Name) (joins : List Join) : Bool :=
    match joins with
    | [] => false
    | join :: rest => sourceReferences name join.table || joinsReferences name rest
  termination_by sizeOf joins
  decreasing_by all_goals simp_all; cases join <;> simp_all <;> omega

  def ctesReferences (name : Name) (ctes : List CTE) : Bool :=
    match ctes with
    | [] => false
    | cte :: rest => relReferences name cte.query || (cte.name != name && ctesReferences name rest)
  termination_by sizeOf ctes
  decreasing_by all_goals simp_all; cases cte <;> simp_all <;> omega

  def unionsReferences (name : Name) (unions : List UnionBranch) : Bool :=
    match unions with
    | [] => false
    | branch :: rest => relReferences name branch.query || unionsReferences name rest
  termination_by sizeOf unions
  decreasing_by all_goals simp_all; cases branch <;> simp_all <;> omega
end

def relAnchor (query : RelQuery) : RelQuery := { query with unions := [] }

private theorem relAnchor_size (query : RelQuery) : sizeOf (relAnchor query) ≤ sizeOf query := by
  cases query
  rename_i source selectList joins whereClause groupBy having distinct orderBy limit offset ctes recursive unions
  cases unions <;> simp [relAnchor] <;> omega

private theorem unionQuery_size (query : RelQuery) (branch : UnionBranch)
    (shape : query.unions = [branch]) : sizeOf branch.query < sizeOf query := by
  cases query
  cases branch
  simp_all
  omega

/-- Portable compound arms keep their ordering/pagination on the whole compound. -/
def RelUnionArmShape (query : RelQuery) : Prop :=
  query.ctes = [] ∧ query.recursive = false ∧ query.unions = [] ∧
  query.orderBy = [] ∧ query.limit = none ∧ query.offset = none

instance (query : RelQuery) : Decidable (RelUnionArmShape query) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Compound ORDER BY binds only first-arm output names or positive ordinals. -/
def RelCompoundOrderKey (names : List (Option Name)) (expr : RelExpr) : Prop :=
  match expr with
  | .literal (.int ordinal) => 0 < ordinal ∧ ordinal ≤ names.length
  | .column none name => (names.filter (· == some name)).length = 1
  | _ => False

instance (names : List (Option Name)) (expr : RelExpr) : Decidable (RelCompoundOrderKey names expr) := by
  unfold RelCompoundOrderKey
  split <;> infer_instance

def RelCompoundOptions (query : RelQuery) (names : List (Option Name)) : Prop :=
  (query.recursive = true → query.ctes ≠ []) ∧
  (query.unions ≠ [] → (query.offset ≠ none → query.limit ≠ none) ∧
    ∀ order ∈ query.orderBy, RelCompoundOrderKey names order.expr)

instance (query : RelQuery) (names : List (Option Name)) : Decidable (RelCompoundOptions query names) :=
  inferInstanceAs (Decidable ((_ → _) ∧ (_ → (_ → _) ∧ _)))

/-- A conservative common recursive term: one direct reference, ordinary inner
or cross joins, no aggregates, grouping, nested sources, or query modifiers. -/
def RelRecursiveStepShape (name : Name) (query : RelQuery) : Prop :=
  RelUnionArmShape query ∧ query.distinct = false ∧ query.groupBy = [] ∧ query.having = none ∧
  query.source.derived = none ∧
  ((if query.source.name == name then 1 else 0) +
    (query.joins.filter (fun join => join.table.name == name)).length = 1) ∧
  (∀ join ∈ query.joins, join.table.derived = none ∧ (join.kind = .inner ∨ join.kind = .cross)) ∧
  (query.selectList.all (fun item => match item with
    | .all _ => true | .expression expr _ => !expr.hasAggregate)) = true

instance (name : Name) (query : RelQuery) : Decidable (RelRecursiveStepShape name query) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def RelRecursiveAnchorShape (name : Name) (query : RelQuery) : Prop :=
  query.ctes = [] ∧ query.recursive = false ∧ query.orderBy = [] ∧
  query.limit = none ∧ query.offset = none ∧ relReferences name (relAnchor query) = false

instance (name : Name) (query : RelQuery) : Decidable (RelRecursiveAnchorShape name query) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

mutual
  /-- Full relational validity exposes structural typing of each compound arm and
recursive anchor/step. It deliberately makes no execution termination claim. -/
  inductive NestedRelValid : Schema → RelQuery → List SqlType → List (Option Name) → Prop where
    | intro (schemaValid : WellFormedSchema schema)
        (ctes : RelCTEsValid query.recursive (cteInputSchema schema query.recursive query.ctes) query.ctes lexical)
        (source : RelSourceValid lexical lexical query.source withSource sourceRef)
        (joins : RelJoinsExpanded lexical withSource query.joins effective joinsOut)
        (core : ValidRelQueryCore effective (flatRelQuery query sourceRef joinsOut) types)
        (names : relOutputNames effective (flatRelQuery query sourceRef joinsOut) = .ok outputNames)
        (arity : outputNames.length = types.length)
        (unions : RelUnionsValid lexical types query.unions)
        (options : RelCompoundOptions query outputNames) :
        NestedRelValid schema query types outputNames

  inductive RelCTEsValid : Bool → Schema → List CTE → Schema → Prop where
    | nil : RelCTEsValid recursive schema [] schema
    | cons (nonempty : cte.name ≠ "")
        (unique : ∀ other ∈ rest, other.name ≠ cte.name)
        (ordinary : (recursive && relReferences cte.name cte.query) = false)
        (child : NestedRelValid schema cte.query types names)
        (table : materializeRelTable cte.name cte.columns types names = .ok definition)
        (tail : RelCTEsValid recursive (withRelTable schema definition) rest output) :
        RelCTEsValid recursive schema (cte :: rest) output
    | recursive (nonempty : cte.name ≠ "")
        (unique : ∀ other ∈ rest, other.name ≠ cte.name)
        (enabled : (recursive && relReferences cte.name cte.query) = true)
        (shape : cte.query.unions = [branch])
        (anchorShape : RelRecursiveAnchorShape cte.name cte.query)
        (stepShape : RelRecursiveStepShape cte.name branch.query)
        (anchor : NestedRelValid schema (relAnchor cte.query) types names)
        (table : materializeRelTable cte.name cte.columns types names = .ok definition)
        (step : NestedRelValid (withRelTable schema definition) branch.query types stepNames)
        (tail : RelCTEsValid recursive (withRelTable schema definition) rest output) :
        RelCTEsValid recursive schema (cte :: rest) output

  inductive RelSourceValid : Schema → Schema → TableRef → Schema → TableRef → Prop where
    | absent (plain : source.derived = none) (emptyName : source.name = "")
        (unaliased : source.alias = none) : RelSourceValid lexical working source working source
    | named (plain : source.derived = none) (nonempty : source.name ≠ "")
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

  /-- This portable subset requires identical type vectors, including nullability. -/
  inductive RelUnionsValid : Schema → List SqlType → List UnionBranch → Prop where
    | nil : RelUnionsValid schema types []
    | cons (shape : RelUnionArmShape branch.query)
        (child : NestedRelValid schema branch.query types names)
        (tail : RelUnionsValid schema types rest) : RelUnionsValid schema types (branch :: rest)
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

private structure CertifiedCTEs (recursive : Bool) (inputSchema : Schema) (ctes : List CTE) where
  schema : Schema
  valid : RelCTEsValid recursive inputSchema ctes schema

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
    let ctes ← certifyRelCTEs query.recursive (cteInputSchema schema query.recursive query.ctes) query.ctes
    let source ← certifyRelSource ctes.schema ctes.schema query.source
    let joins ← certifyRelJoinSources ctes.schema source.schema query.joins
    let core ← certifyRelQueryCore joins.schema (flatRelQuery query source.ref joins.joins)
    let names ← certifyNames joins.schema (flatRelQuery query source.ref joins.joins)
    let arity ← require (names.names.length = core.outputTypes.length) "inconsistent output naming arity"
    let unions ← certifyRelUnions ctes.schema core.outputTypes query.unions
    let options ← require (RelCompoundOptions query names.names) "invalid compound ORDER BY, pagination, or recursive modifier"
    pure ⟨core.outputTypes, names.names,
      .intro schemaValid.down ctes.valid source.valid joins.valid core.valid names.proof arity.down unions.down options.down⟩
  termination_by sizeOf query
  decreasing_by all_goals cases query; simp_all <;> omega

  private def certifyRelCTEs (recursive : Bool) (schema : Schema) (ctes : List CTE) :
      Except ValidationError (CertifiedCTEs recursive schema ctes) :=
    match ctes with
    | [] => pure ⟨schema, .nil⟩
    | cte :: rest => do
      let nonempty ← require (cte.name ≠ "") "empty CTE name"
      let unique ← require (∀ other ∈ rest, other.name ≠ cte.name) "duplicate CTE name"
      if enabled : (recursive && relReferences cte.name cte.query) = true then
        match shape : cte.query.unions with
        | [branch] => do
          let anchorShape ← require (RelRecursiveAnchorShape cte.name cte.query)
            "recursive CTE needs a nonrecursive anchor without WITH, ORDER BY, or pagination"
          let stepShape ← require (RelRecursiveStepShape cte.name branch.query)
            "recursive step needs exactly one direct self-reference and no grouping, nested query, or outer join"
          let anchor ← certifyRelQuery schema (relAnchor cte.query)
          let table ← certifyMaterialization cte.name cte.columns anchor.outputTypes anchor.outputNames
          let step ← certifyRelQuery (withRelTable schema table.table) branch.query
          let equalTypes ← require (step.outputTypes = anchor.outputTypes)
            "recursive anchor and step need identical output arity and types, including nullability"
          let tail ← certifyRelCTEs recursive (withRelTable schema table.table) rest
          pure ⟨tail.schema, .recursive nonempty.down unique.down enabled shape anchorShape.down stepShape.down
            anchor.derivation table.proof (equalTypes.down ▸ step.derivation) tail.valid⟩
        | _ => .error ⟨"recursive CTE needs exactly one anchor and one UNION/UNION ALL step"⟩
      else
        let ordinary : (recursive && relReferences cte.name cte.query) = false := by
          cases h : recursive && relReferences cte.name cte.query <;> simp_all
        let child ← certifyRelQuery schema cte.query
        let table ← certifyMaterialization cte.name cte.columns child.outputTypes child.outputNames
        let tail ← certifyRelCTEs recursive (withRelTable schema table.table) rest
        pure ⟨tail.schema, .cons nonempty.down unique.down ordinary child.derivation table.proof tail.valid⟩
  termination_by sizeOf ctes
  decreasing_by
    all_goals have hanchor := relAnchor_size cte.query
    all_goals try have hbranch := unionQuery_size cte.query branch shape
    all_goals cases cte <;> simp_all <;> omega

  private def certifyRelSource (lexical working : Schema) (source : TableRef) :
      Except ValidationError (CertifiedSource lexical working source) :=
    match h : source.derived with
    | none => do
      if emptyName : source.name = "" then
        let unaliased ← require (source.alias = none) "absent FROM cannot have an alias"
        pure ⟨working, source, .absent h emptyName unaliased.down⟩
      else
        let found ← require ((lexical.findTable source.name).isSome = true) s!"unknown table '{source.name}'"
        pure ⟨working, source, .named h emptyName found.down⟩
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

  private def certifyRelUnions (schema : Schema) (types : List SqlType) (unions : List UnionBranch) :
      Except ValidationError (PLift (RelUnionsValid schema types unions)) :=
    match unions with
    | [] => pure ⟨.nil⟩
    | branch :: rest => do
      let shape ← require (RelUnionArmShape branch.query) "UNION arm modifiers require a derived query"
      let child ← certifyRelQuery schema branch.query
      let equalTypes ← require (child.outputTypes = types) "UNION arms need identical output arity and types, including nullability"
      let tail ← certifyRelUnions schema types rest
      pure ⟨.cons shape.down (equalTypes.down ▸ child.derivation) tail.down⟩
  termination_by sizeOf unions
  decreasing_by all_goals simp_all; cases branch <;> simp_all <;> omega
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

/-- Every structural derivation receives its exact certificate. -/
theorem certifyRelQuery_complete (valid : NestedRelValid schema query types names) :
    certifyRelQuery schema query = .ok ⟨types, names, valid⟩ := by
  refine NestedRelValid.rec
    (motive_1 := fun schema query types names valid =>
      certifyRelQuery schema query = .ok ⟨types, names, valid⟩)
    (motive_2 := fun recursive schema ctes output valid =>
      certifyRelCTEs recursive schema ctes = .ok ⟨output, valid⟩)
    (motive_3 := fun lexical working source output ref valid =>
      certifyRelSource lexical working source = .ok ⟨output, ref, valid⟩)
    (motive_4 := fun lexical working joins output result valid =>
      certifyRelJoinSources lexical working joins = .ok ⟨output, result, valid⟩)
    (motive_5 := fun schema types unions valid =>
      certifyRelUnions schema types unions = .ok ⟨valid⟩)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ valid
  · intro schema lexical withSource sourceRef effective joinsOut query types names
      schemaValid ctes source joins core namesProof arity unions options ihCTEs ihSource ihJoins ihUnions
    simp [certifyRelQuery, checkSchema, schemaValid, ihCTEs, ihSource, ihJoins,
      certifyRelQueryCore_complete core, certifyNames_complete namesProof, require_complete arity,
      ihUnions, require_complete options, pure, bind, Except.bind, Except.pure]
  · intro recursive schema
    simp [certifyRelCTEs, pure, Except.pure]
  · intro rest recursive schema types names definition output cte nonempty unique ordinary child table tail ihChild ihTail
    simp [certifyRelCTEs, require_complete nonempty, require_complete unique, ordinary, ihChild,
      certifyMaterialization_complete table, ihTail, pure, bind, Except.bind, Except.pure]
  · intro rest recursive branch schema types names definition stepNames output cte
      nonempty unique enabled shape anchorShape stepShape anchor table step tail ihAnchor ihStep ihTail
    simp only [certifyRelCTEs, require_complete nonempty, require_complete unique, enabled,
      dite_true, bind, Except.bind]
    split
    · rename_i branch' shape'
      have same : branch' = branch := by simpa using shape'.symm.trans shape
      subst branch'
      simp [require_complete anchorShape, require_complete stepShape, ihAnchor,
        certifyMaterialization_complete table, ihStep, require_complete (rfl : types = types), ihTail,
        pure, Except.pure]
    · rename_i other shape' mismatch
      exact False.elim (mismatch branch shape)

  · intro lexical working source plain emptyName unaliased
    simp only [certifyRelSource]
    split
    · simp [emptyName, require_complete unaliased, pure, bind, Except.bind, Except.pure]
    · rename_i query contradiction
      cases plain.symm.trans contradiction
  · intro lexical working source plain nonempty found
    simp only [certifyRelSource]
    split
    · simp [nonempty, require_complete found, pure, bind, Except.bind, Except.pure]
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
  · intro schema types
    simp [certifyRelUnions, pure, Except.pure]
  · intro schema types names rest branch shape child tail ihChild ihTail
    simp [certifyRelUnions, require_complete shape, ihChild, require_complete (rfl : types = types), ihTail,
      pure, bind, Except.bind, Except.pure]

/-- Soundness and completeness for the full static contract, including all child queries. -/
theorem checkRelQuery_iff : checkRelQuery schema query = .ok types ↔ ValidRelQuery schema query types := by
  constructor
  · exact checkRelQuery_sound
  · rintro ⟨names, valid⟩
    simp [checkRelQuery, certifyRelQuery_complete valid, Except.map]

end SQLean
