import SQLean.AST

/-!
Schema-aware expression typing and proof-carrying SELECT validation.

`HasType`, `HasTypes`, and `ValidQuery` describe validity independently of
the checker. The checker constructs inhabitants of those relations.
This is static validation, not query execution or a division-safety proof.
-/

namespace SQLean

structure ValidationError where
  message : String
  deriving Repr, BEq, DecidableEq, Inhabited

instance : ToString ValidationError where
  toString error := error.message

private def invalid {α : Type} (message : String) : Except ValidationError α :=
  .error ⟨message⟩

/-- SQL's non-null primitive operator signatures in this supported subset. -/
def binaryResult : BinOp → SqlType → SqlType → Option SqlType
  | .eq, left, right | .ne, left, right => if left = right then some .bool else none
  | .lt, .int, .int | .le, .int, .int | .gt, .int, .int | .ge, .int, .int => some .bool
  | .and, .bool, .bool | .or, .bool, .bool => some .bool
  | .add, .int, .int | .sub, .int, .int | .mul, .int, .int | .div, .int, .int => some .int
  | _, _, _ => none

/-- Unary signs preserve integers; logical negation requires a boolean. -/
def unaryResult : UnOp → SqlType → Option SqlType
  | .pos, .int | .neg, .int => some .int
  | .not, .bool => some .bool
  | _, _ => none

/-- Declarative, syntax-directed expression typing. -/
inductive HasType (columns : List ColumnDef) : Expr → SqlType → Prop where
  | literal (value : Value) : HasType columns (.literal value) value.type
  | column (found : columns.find? (fun c => c.name == name) = some column) :
      HasType columns (.column name) column.type
  | binary (leftTyped : HasType columns left leftType)
      (rightTyped : HasType columns right rightType)
      (signature : binaryResult op leftType rightType = some result) :
      HasType columns (.binary op left right) result
  | unary (argTyped : HasType columns arg argType)
      (signature : unaryResult op argType = some result) :
      HasType columns (.unary op arg) result

/-- Infer an expression type together with a kernel-checked typing derivation. -/
def certifyExpr (columns : List ColumnDef) (expr : Expr) :
    Except ValidationError {type : SqlType // HasType columns expr type} :=
  match expr with
  | .literal value => pure ⟨value.type, .literal value⟩
  | .column name =>
      match h : columns.find? (fun c => c.name == name) with
      | none => invalid s!"unknown column '{name}'"
      | some column => pure ⟨column.type, .column h⟩
  | .binary op left right => do
      let leftResult ← certifyExpr columns left
      let rightResult ← certifyExpr columns right
      match h : binaryResult op leftResult.val rightResult.val with
      | none => invalid s!"incompatible operand types for {repr op}"
      | some type => pure ⟨type, .binary leftResult.property rightResult.property h⟩
  | .unary op arg => do
      let argResult ← certifyExpr columns arg
      match h : unaryResult op argResult.val with
      | none => invalid s!"incompatible operand type for {repr op}"
      | some type => pure ⟨type, .unary argResult.property h⟩

def inferType (columns : List ColumnDef) (expr : Expr) : Except ValidationError SqlType :=
  (certifyExpr columns expr).map Subtype.val

def expectType (columns : List ColumnDef) (expr : Expr) (expected : SqlType) :
    Except ValidationError (PLift (HasType columns expr expected)) := do
  let result ← certifyExpr columns expr
  if h : result.val = expected then
    pure ⟨h ▸ result.property⟩
  else
    invalid s!"expected {repr expected}, found {repr result.val}"

/-- A table has a nonempty name, at least one column, and distinct nonempty column names. -/
def WellFormedTable (table : TableDef) : Prop :=
  table.name ≠ "" ∧ table.columns ≠ [] ∧
  table.columns.Pairwise (fun left right => left.name ≠ right.name) ∧
  ∀ column ∈ table.columns, column.name ≠ ""

instance (table : TableDef) : Decidable (WellFormedTable table) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- A schema has distinct table names and well-formed table definitions. -/
def WellFormedSchema (schema : Schema) : Prop :=
  schema.Pairwise (fun left right => left.name ≠ right.name) ∧
  ∀ table ∈ schema, WellFormedTable table

instance (schema : Schema) : Decidable (WellFormedSchema schema) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Validate an externally supplied schema before checking a query. -/
def checkSchema (schema : Schema) : Except ValidationError (PLift (WellFormedSchema schema)) :=
  if h : WellFormedSchema schema then pure ⟨h⟩
  else invalid "invalid schema: table and column names must be nonempty and unique, and tables must have columns"

inductive WhereValid (columns : List ColumnDef) : Option Expr → Prop where
  | absent : WhereValid columns none
  | present (typed : HasType columns expr .bool) : WhereValid columns (some expr)

def checkWhere (columns : List ColumnDef) (whereClause : Option Expr) :
    Except ValidationError (PLift (WhereValid columns whereClause)) :=
  match whereClause with
  | none => pure ⟨.absent⟩
  | some expr => do
      let typed ← expectType columns expr .bool
      pure ⟨.present typed.down⟩

/-- Ordered result-column typing, with one type for each selected expression. -/
inductive HasTypes (columns : List ColumnDef) : List Expr → List SqlType → Prop where
  | nil : HasTypes columns [] []
  | cons (head : HasType columns expr type) (tail : HasTypes columns exprs types) :
      HasTypes columns (expr :: exprs) (type :: types)

def certifyExprs (columns : List ColumnDef) (exprs : List Expr) :
    Except ValidationError {types : List SqlType // HasTypes columns exprs types} :=
  match exprs with
  | [] => pure ⟨[], .nil⟩
  | expr :: exprs => do
      let head ← certifyExpr columns expr
      let tail ← certifyExprs columns exprs
      pure ⟨head.val :: tail.val, .cons head.property tail.property⟩

/-- Declarative SELECT validity: the schema is well formed, the table exists,
selected expressions are typed, and any filter has boolean type. -/
inductive ValidQuery (schema : Schema) (query : Query) (outputTypes : List SqlType) : Prop where
  | intro (schemaValid : WellFormedSchema schema)
      (found : schema.findTable query.table = some table)
      (nonempty : query.selectList ≠ [])
      (selected : HasTypes table.columns query.selectList outputTypes)
      (whereValid : WhereValid table.columns query.whereClause) :
      ValidQuery schema query outputTypes

/-- The proof is checked by Lean's kernel and erased from compiled programs. -/
structure CertifiedQuery (schema : Schema) (query : Query) where
  outputTypes : List SqlType
  valid : ValidQuery schema query outputTypes

/-- Validate a query against an explicit schema and return its typing certificate. -/
def certifyQuery (schema : Schema) (query : Query) :
    Except ValidationError (CertifiedQuery schema query) := do
  let schemaValid ← checkSchema schema
  match h : schema.findTable query.table with
  | none => invalid s!"unknown table '{query.table}'"
  | some table =>
      if nonempty : query.selectList ≠ [] then
        let selected ← certifyExprs table.columns query.selectList
        let whereValid ← checkWhere table.columns query.whereClause
        pure ⟨selected.val, .intro schemaValid.down h nonempty selected.property whereValid.down⟩
      else invalid "SELECT needs at least one expression"

/-- Convenience API returning just the ordered output types. -/
def checkQuery (schema : Schema) (query : Query) : Except ValidationError (List SqlType) :=
  (certifyQuery schema query).map CertifiedQuery.outputTypes

/-- Every inferred expression type has a derivation in the declarative relation. -/
theorem inferType_sound (columns : List ColumnDef) (expr : Expr) (type : SqlType)
    (success : inferType columns expr = .ok type) : HasType columns expr type := by
  unfold inferType at success
  cases checked : certifyExpr columns expr with
  | error error => simp [checked, Except.map] at success
  | ok result =>
      simp [checked, Except.map] at success
      exact success ▸ result.property

/-- Every successful convenience check has a declarative query-validity proof. -/
theorem checkQuery_sound (schema : Schema) (query : Query) (types : List SqlType)
    (success : checkQuery schema query = .ok types) : ValidQuery schema query types := by
  unfold checkQuery at success
  cases checked : certifyQuery schema query with
  | error error => simp [checked, Except.map] at success
  | ok result =>
      simp [checked, Except.map] at success
      exact success ▸ result.valid

/-- A selected expression contributes exactly one output column. -/
theorem HasTypes.length_eq (typed : HasTypes columns exprs types) : exprs.length = types.length := by
  induction typed with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Certified output schemas have exactly the query's number of selected expressions. -/
theorem ValidQuery.output_arity (valid : ValidQuery schema query types) :
    query.selectList.length = types.length := by
  cases valid with
  | intro _ _ _ selected _ => exact selected.length_eq

/-- Expression types are unique, even before requiring a well-formed schema. -/
theorem HasType.unique (first : HasType columns expr firstType)
    (second : HasType columns expr secondType) : firstType = secondType := by
  induction first generalizing secondType with
  | literal value => cases second; rfl
  | column found =>
      cases second with
      | column found' => simp_all
  | binary leftTyped rightTyped signature leftIH rightIH =>
      cases second with
      | binary leftTyped' rightTyped' signature' =>
          have leftEq := leftIH leftTyped'
          have rightEq := rightIH rightTyped'
          simp_all
  | unary argTyped signature argIH =>
      cases second with
      | unary argTyped' signature' =>
          have argEq := argIH argTyped'
          simp_all

/-- The expression checker accepts every expression in the declarative typing relation. -/
theorem certifyExpr_complete (typed : HasType columns expr type) :
    certifyExpr columns expr = .ok ⟨type, typed⟩ := by
  induction typed with
  | literal value => rfl
  | column found =>
      simp only [certifyExpr]
      split
      · simp_all
      · rename_i column found'
        have same := Option.some.inj (found'.symm.trans found)
        subst column
        rfl
  | binary leftTyped rightTyped signature leftIH rightIH =>
      simp only [certifyExpr, leftIH, rightIH, Except.bind, pure, bind]
      split
      · simp_all
      · rename_i result signature'
        have same := Option.some.inj (signature'.symm.trans signature)
        subst result
        rfl
  | unary argTyped signature argIH =>
      simp only [certifyExpr, argIH, Except.bind, pure, bind]
      split
      · simp_all
      · rename_i result signature'
        have same := Option.some.inj (signature'.symm.trans signature)
        subst result
        rfl

/-- Soundness and completeness characterize the executable expression checker. -/
theorem inferType_iff (columns : List ColumnDef) (expr : Expr) (type : SqlType) :
    inferType columns expr = .ok type ↔ HasType columns expr type := by
  constructor
  · exact inferType_sound columns expr type
  · intro typed
    simp [inferType, certifyExpr_complete typed, Except.map]

theorem certifyExprs_complete (typed : HasTypes columns exprs types) :
    certifyExprs columns exprs = .ok ⟨types, typed⟩ := by
  induction typed with
  | nil => rfl
  | cons head tail ih =>
      simp [certifyExprs, certifyExpr_complete head, ih, pure, bind, Except.bind, Except.pure]

theorem expectType_complete (typed : HasType columns expr type) :
    expectType columns expr type = .ok ⟨typed⟩ := by
  simp [expectType, certifyExpr_complete typed, pure, bind, Except.bind, Except.pure]

theorem checkWhere_complete (valid : WhereValid columns whereClause) :
    checkWhere columns whereClause = .ok ⟨valid⟩ := by
  cases valid with
  | absent => rfl
  | present typed =>
      simp [checkWhere, expectType_complete typed, pure, bind, Except.bind, Except.pure]

/-- Every declaratively valid query receives a certificate. -/
theorem certifyQuery_complete (valid : ValidQuery schema query types) :
    certifyQuery schema query = .ok ⟨types, valid⟩ := by
  cases valid with
  | intro schemaValid found nonempty selected whereValid =>
      simp only [certifyQuery, checkSchema, dite_eq_left schemaValid, pure, bind, Except.bind,
        Except.pure]
      split
      · simp_all
      · rename_i table found'
        have same := Option.some.inj (found'.symm.trans found)
        subst table
        simp [nonempty, certifyExprs_complete selected, checkWhere_complete whereValid]

/-- The public query check is both sound and complete for `ValidQuery`. -/
theorem checkQuery_iff (schema : Schema) (query : Query) (types : List SqlType) :
    checkQuery schema query = .ok types ↔ ValidQuery schema query types := by
  constructor
  · exact checkQuery_sound schema query types
  · intro valid
    simp [checkQuery, certifyQuery_complete valid, Except.map]

end SQLean
