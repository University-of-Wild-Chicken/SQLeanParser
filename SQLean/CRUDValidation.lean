import SQLean.Validation

/-! Declarative static validity and executable certificates for the CRUD subset.
Mutation certificates establish column resolution, value typing, arity, and
boolean filters. They do not establish execution, data constraints, or ACID.
-/

namespace SQLean

/-- The established expression checker makes declarative typing decidable. -/
instance (columns : List ColumnDef) (expr : Expr) (type : SqlType) :
    Decidable (HasType columns expr type) := by
  cases checked : inferType columns expr with
  | error error =>
      exact isFalse (by
        intro typed
        have success := (inferType_iff columns expr type).mpr typed
        simp [checked] at success)
  | ok inferred =>
      if equal : inferred = type then
        exact isTrue (by subst inferred; exact inferType_sound columns expr type checked)
      else
        exact isFalse (by
          intro typed
          have success := (inferType_iff columns expr type).mpr typed
          simp [checked] at success
          exact equal success)

/-- A target column exists and accepts the value in the supplied expression scope. -/
def ColumnValueTyped (targets scope : List ColumnDef) (name : Name) (value : Expr) : Prop :=
  ∃ column ∈ targets, column.name = name ∧ HasType scope value column.type

instance (targets scope : List ColumnDef) (name : Name) (value : Expr) :
    Decidable (ColumnValueTyped targets scope name value) :=
  inferInstanceAs (Decidable (∃ column ∈ targets, _))

/-- INSERT without a target list uses the schema's column order. -/
def InsertQuery.targetNames (columns : List ColumnDef) (query : InsertQuery) : List Name :=
  query.columns.getD (columns.map ColumnDef.name)

/-- Since this subset has no defaults or NULL, INSERT must supply every column once. -/
def InsertTargetsValid (columns : List ColumnDef) (names : List Name) : Prop :=
  names ≠ [] ∧ names.Pairwise (· ≠ ·) ∧
  (∀ name ∈ names, ∃ column ∈ columns, column.name = name) ∧
  (∀ column ∈ columns, column.name ∈ names)

instance (columns : List ColumnDef) (names : List Name) :
    Decidable (InsertTargetsValid columns names) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Each row has exactly one value per target and contains no table-column references. -/
def InsertRowValid (columns : List ColumnDef) (names : List Name) (row : List Expr) : Prop :=
  row.length = names.length ∧
  ∀ pair ∈ row.zip names, ColumnValueTyped columns [] pair.2 pair.1

instance (columns : List ColumnDef) (names : List Name) (row : List Expr) :
    Decidable (InsertRowValid columns names row) :=
  inferInstanceAs (Decidable (_ ∧ _))

def InsertValid (columns : List ColumnDef) (query : InsertQuery) : Prop :=
  InsertTargetsValid columns (query.targetNames columns) ∧ query.rows ≠ [] ∧
  ∀ row ∈ query.rows, InsertRowValid columns (query.targetNames columns) row

instance (columns : List ColumnDef) (query : InsertQuery) : Decidable (InsertValid columns query) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- UPDATE values are typed against the original table schema. -/
def AssignmentsValid (columns : List ColumnDef) (assignments : List Assignment) : Prop :=
  assignments ≠ [] ∧
  assignments.Pairwise (fun left right => left.column ≠ right.column) ∧
  ∀ assignment ∈ assignments, ColumnValueTyped columns columns assignment.column assignment.value

instance (columns : List ColumnDef) (assignments : List Assignment) :
    Decidable (AssignmentsValid columns assignments) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- The projection determines the ordered result-column types. -/
inductive ProjectionTyped (columns : List ColumnDef) : Projection → List SqlType → Prop where
  | all : ProjectionTyped columns .all (columns.map ColumnDef.type)
  | expressions (nonempty : exprs ≠ []) (typed : HasTypes columns exprs types) :
      ProjectionTyped columns (.expressions exprs) types

/-- All supported primitive types can be sort keys. -/
def OrderValid (columns : List ColumnDef) (order : OrderBy) : Prop :=
  HasType columns order.expr .int ∨ HasType columns order.expr .text ∨
  HasType columns order.expr .bool

instance (columns : List ColumnDef) (order : OrderBy) : Decidable (OrderValid columns order) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

def Projection.expressionsFor (columns : List ColumnDef) : Projection → List Expr
  | .all => columns.map (fun column => .column column.name)
  | .expressions items => items

/-- Bare signed integer sort keys denote result-column positions. -/
def orderOrdinal : Expr → Option Int
  | .literal (.int value) => some (Int.ofNat value)
  | .unary .pos arg => orderOrdinal arg
  | .unary .neg arg => (orderOrdinal arg).map Neg.neg
  | _ => none

def SelectOrderValid (columns : List ColumnDef) (query : SelectQuery) (order : OrderBy) : Prop :=
  match orderOrdinal order.expr with
  | some ordinal => 0 < ordinal ∧ ordinal ≤ (query.projection.expressionsFor columns).length
  | none => OrderValid columns order ∧
      (query.distinct = false ∨
        ∃ expression ∈ query.projection.expressionsFor columns, order.expr = expression)

instance (columns : List ColumnDef) (query : SelectQuery) (order : OrderBy) :
    Decidable (SelectOrderValid columns query order) := by
  unfold SelectOrderValid
  split <;> infer_instance

/-- For DISTINCT, sort expressions must occur in the result projection. -/
def SelectOptionsValid (columns : List ColumnDef) (query : SelectQuery) : Prop :=
  (∀ order ∈ query.orderBy, SelectOrderValid columns query order) ∧
  (query.offset ≠ none → query.limit ≠ none)

instance (columns : List ColumnDef) (query : SelectQuery) :
    Decidable (SelectOptionsValid columns query) :=
  inferInstanceAs (Decidable (_ ∧ _))

inductive SelectValid (columns : List ColumnDef) (query : SelectQuery)
    (outputTypes : List SqlType) : Prop where
  | intro (projection : ProjectionTyped columns query.projection outputTypes)
      (filter : WhereValid columns query.whereClause)
      (options : SelectOptionsValid columns query) : SelectValid columns query outputTypes

/-- Schema-aware static CRUD validity, independent of the implementation of the checker. -/
inductive ValidStatement (schema : Schema) : Statement → List SqlType → Prop where
  | select (schemaValid : WellFormedSchema schema)
      (found : schema.findTable query.table = some table)
      (valid : SelectValid table.columns query types) :
      ValidStatement schema (.select query) types
  | insert (schemaValid : WellFormedSchema schema)
      (found : schema.findTable query.table = some table)
      (valid : InsertValid table.columns query) :
      ValidStatement schema (.insert query) []
  | update (schemaValid : WellFormedSchema schema)
      (found : schema.findTable query.table = some table)
      (assignments : AssignmentsValid table.columns query.assignments)
      (filter : WhereValid table.columns query.whereClause) :
      ValidStatement schema (.update query) []
  | delete (schemaValid : WellFormedSchema schema)
      (found : schema.findTable query.table = some table)
      (filter : WhereValid table.columns query.whereClause) :
      ValidStatement schema (.delete query) []

structure CertifiedStatement (schema : Schema) (statement : Statement) where
  outputTypes : List SqlType
  valid : ValidStatement schema statement outputTypes

private def require (proposition : Prop) [Decidable proposition] (message : String) :
    Except ValidationError (PLift proposition) :=
  if proof : proposition then .ok ⟨proof⟩ else .error ⟨message⟩

private theorem require_complete (proof : proposition) [Decidable proposition] (message : String) :
    require proposition message = .ok ⟨proof⟩ := by
  simp [require, proof]

private structure LocatedTable (schema : Schema) (name : Name) where
  val : TableDef
  property : schema.findTable name = some val

private def certifyTable (schema : Schema) (name : Name) :
    Except ValidationError (LocatedTable schema name) :=
  match found : schema.findTable name with
  | none => .error ⟨s!"unknown table '{name}'"⟩
  | some table => .ok ⟨table, found⟩

private theorem certifyTable_complete (found : schema.findTable name = some table) :
    certifyTable schema name = .ok ⟨table, found⟩ := by
  unfold certifyTable
  split
  · simp_all
  · rename_i table' found'
    have same := Option.some.inj (found'.symm.trans found)
    subst table'
    rfl

def certifyProjection (columns : List ColumnDef) (projection : Projection) :
    Except ValidationError {types : List SqlType // ProjectionTyped columns projection types} :=
  match projection with
  | .all => .ok ⟨columns.map ColumnDef.type, .all⟩
  | .expressions exprs => do
      let nonempty ← require (exprs ≠ []) "SELECT needs at least one expression"
      let typed ← certifyExprs columns exprs
      pure ⟨typed.val, .expressions nonempty.down typed.property⟩

theorem certifyProjection_complete (typed : ProjectionTyped columns projection types) :
    certifyProjection columns projection = .ok ⟨types, typed⟩ := by
  cases typed with
  | all => rfl
  | expressions nonempty typed =>
      simp [certifyProjection, require_complete nonempty, certifyExprs_complete typed,
        pure, bind, Except.bind, Except.pure]

/-- Infer result types and construct a Lean proof for a CRUD statement. -/
def certifyStatement (schema : Schema) (statement : Statement) :
    Except ValidationError (CertifiedStatement schema statement) :=
  match statement with
  | .select query => do
      let schemaValid ← checkSchema schema
      let table ← certifyTable schema query.table
      let projection ← certifyProjection table.val.columns query.projection
      let filter ← checkWhere table.val.columns query.whereClause
      let options ← require (SelectOptionsValid table.val.columns query)
        "invalid SELECT options: check sort types and positions, DISTINCT projection, and LIMIT before OFFSET"
      pure ⟨projection.val, .select schemaValid.down table.property
        (.intro projection.property filter.down options.down)⟩
  | .insert query => do
      let schemaValid ← checkSchema schema
      let table ← certifyTable schema query.table
      let valid ← require (InsertValid table.val.columns query)
        "invalid INSERT: supply every column once, nonempty rows, and matching value types and arity"
      pure ⟨[], .insert schemaValid.down table.property valid.down⟩
  | .update query => do
      let schemaValid ← checkSchema schema
      let table ← certifyTable schema query.table
      let assignments ← require (AssignmentsValid table.val.columns query.assignments)
        "invalid UPDATE: assignments must be nonempty, target distinct known columns, and match their types"
      let filter ← checkWhere table.val.columns query.whereClause
      pure ⟨[], .update schemaValid.down table.property assignments.down filter.down⟩
  | .delete query => do
      let schemaValid ← checkSchema schema
      let table ← certifyTable schema query.table
      let filter ← checkWhere table.val.columns query.whereClause
      pure ⟨[], .delete schemaValid.down table.property filter.down⟩

/-- SELECT yields its projection types; INSERT, UPDATE, and DELETE yield no columns. -/
def checkStatement (schema : Schema) (statement : Statement) : Except ValidationError (List SqlType) :=
  (certifyStatement schema statement).map CertifiedStatement.outputTypes

theorem checkStatement_sound (schema : Schema) (statement : Statement) (types : List SqlType)
    (success : checkStatement schema statement = .ok types) : ValidStatement schema statement types := by
  unfold checkStatement at success
  cases checked : certifyStatement schema statement with
  | error error => simp [checked, Except.map] at success
  | ok result =>
      simp [checked, Except.map] at success
      exact success ▸ result.valid

/-- Every statement satisfying the declarative rules receives a certificate. -/
theorem certifyStatement_complete (valid : ValidStatement schema statement types) :
    certifyStatement schema statement = .ok ⟨types, valid⟩ := by
  cases valid with
  | select schemaValid found valid =>
      cases valid with
      | intro projection filter options =>
        simp [certifyStatement, checkSchema, schemaValid, certifyTable_complete found,
          certifyProjection_complete projection, checkWhere_complete filter, require_complete options,
          pure, bind, Except.bind, Except.pure]
  | insert schemaValid found valid =>
      simp [certifyStatement, checkSchema, schemaValid, certifyTable_complete found,
        require_complete valid, pure, bind, Except.bind, Except.pure]
  | update schemaValid found assignments filter =>
      simp [certifyStatement, checkSchema, schemaValid, certifyTable_complete found,
        require_complete assignments, checkWhere_complete filter, pure, bind, Except.bind, Except.pure]
  | delete schemaValid found filter =>
      simp [certifyStatement, checkSchema, schemaValid, certifyTable_complete found,
        checkWhere_complete filter, pure, bind, Except.bind, Except.pure]

/-- Soundness and completeness for the entire supported static CRUD contract. -/
theorem checkStatement_iff (schema : Schema) (statement : Statement) (types : List SqlType) :
    checkStatement schema statement = .ok types ↔ ValidStatement schema statement types := by
  constructor
  · exact checkStatement_sound schema statement types
  · intro valid
    simp [checkStatement, certifyStatement_complete valid, Except.map]

end SQLean
