import SQLean.Validation

/-! Static certificates for relation scopes, nullable expression types, joins and
aggregation. Name/alias elaboration is explicit; typing and grouping are separate
structural rules. This module does not model SQL execution or data constraints. -/
namespace SQLean

structure RelColumn where
  qualifier : Name
  name : Name
  type : SqlType
  deriving Repr, BEq, DecidableEq, Inhabited

abbrev RelScope := List RelColumn

def SqlType.base : SqlType → SqlType
  | .nullable type => type.base
  | type => type

def SqlType.isNullable : SqlType → Bool
  | .nullable _ => true
  | _ => false

def SqlType.asNullable (type : SqlType) : SqlType := .nullable type.base

def SqlType.numeric (type : SqlType) : Bool := type.base == .int || type.base == .real

private def numericResult (left right : SqlType) : Option SqlType :=
  if left.numeric && right.numeric then
    some (if left.base == .real || right.base == .real then .real else .int)
  else none

def relBinaryResult (op : BinOp) (left right : SqlType) : Option SqlType :=
  let result : Option SqlType := match op with
    | .add | .sub | .mul | .div => numericResult left right
    | .and | .or => if left.base == SqlType.bool && right.base == SqlType.bool then some .bool else none
    | .eq | .ne =>
        if left.base == right.base || (left.numeric && right.numeric) then some .bool else none
    | .lt | .le | .gt | .ge =>
        if (left.numeric && right.numeric) || (left.base == SqlType.text && right.base == SqlType.text)
        then some .bool else none
  result.map (fun type => if left.isNullable || right.isNullable then type.asNullable else type)

def relUnaryResult (op : UnOp) (arg : SqlType) : Option SqlType :=
  match op with
  | .pos | .neg => if arg.numeric then some arg else none
  | .not => if arg.base == .bool then some arg else none

def aggregateResult (fn : AggregateFn) (arg : SqlType) : Option SqlType :=
  match fn with
  | .count => some .int
  | .sum => if arg.numeric then some arg.asNullable else none
  | .avg => if arg.numeric then some (.nullable .real) else none
  | .min | .max =>
      if arg.numeric || arg.base == .text then some arg.asNullable else none

def matchingRelColumns (scope : RelScope) (qualifier : Option Name) (name : Name) : RelScope :=
  scope.filter (fun column => column.name == name &&
    (qualifier.isNone || qualifier == some column.qualifier))

/-- Exactly one visible binding is required, including for unqualified names. -/
def resolveRelColumn (scope : RelScope) (qualifier : Option Name) (name : Name) : Option RelColumn :=
  match matchingRelColumns scope qualifier name with
  | [column] => some column
  | _ => none

/-- Aggregates are only legal in aggregate-enabled contexts; arguments cannot
contain aggregates. Outer-join nullability follows operator signatures. -/
inductive RelHasType (scope : RelScope) : Bool → RelExpr → SqlType → Prop where
  | literal (value : Value) : RelHasType scope aggregates (.literal value) value.type
  | column (resolved : resolveRelColumn scope qualifier name = some column) :
      RelHasType scope aggregates (.column qualifier name) column.type
  | binary (leftTyped : RelHasType scope aggregates left leftType)
      (rightTyped : RelHasType scope aggregates right rightType)
      (signature : relBinaryResult op leftType rightType = some result) :
      RelHasType scope aggregates (.binary op left right) result
  | unary (argTyped : RelHasType scope aggregates arg argType)
      (signature : relUnaryResult op argType = some result) :
      RelHasType scope aggregates (.unary op arg) result
  | countAll (allowed : aggregates = true) : RelHasType scope aggregates .countAll .int
  | aggregate (allowed : aggregates = true) (argTyped : RelHasType scope false arg argType)
      (signature : aggregateResult fn argType = some result) :
      RelHasType scope aggregates (.aggregate fn arg distinct) result
  | isNull (argTyped : RelHasType scope aggregates arg argType) :
      RelHasType scope aggregates (.isNull arg negated) .bool

private def invalid {α : Type} (message : String) : Except ValidationError α := .error ⟨message⟩

private def require (proposition : Prop) [Decidable proposition] (message : String) :
    Except ValidationError (PLift proposition) :=
  if proof : proposition then .ok ⟨proof⟩ else invalid message

private theorem require_complete (proof : proposition) [Decidable proposition] (message : String) :
    require proposition message = .ok ⟨proof⟩ := by simp [require, proof]

def certifyRelExpr (scope : RelScope) (aggregates : Bool) (expr : RelExpr) :
    Except ValidationError {type : SqlType // RelHasType scope aggregates expr type} :=
  match expr with
  | .literal value => pure ⟨value.type, .literal value⟩
  | .column qualifier name =>
      match h : resolveRelColumn scope qualifier name with
      | none => invalid s!"unknown or ambiguous column '{qualifier.getD ""}.{name}'"
      | some column => pure ⟨column.type, .column h⟩
  | .binary op left right => do
      let left ← certifyRelExpr scope aggregates left
      let right ← certifyRelExpr scope aggregates right
      match h : relBinaryResult op left.val right.val with
      | none => invalid s!"incompatible operand types for {repr op}"
      | some type => pure ⟨type, .binary left.property right.property h⟩
  | .unary op arg => do
      let arg ← certifyRelExpr scope aggregates arg
      match h : relUnaryResult op arg.val with
      | none => invalid s!"incompatible operand type for {repr op}"
      | some type => pure ⟨type, .unary arg.property h⟩
  | .countAll => do
      let allowed ← require (aggregates = true) "aggregate forbidden in this clause or nested aggregate"
      pure ⟨.int, .countAll allowed.down⟩
  | .aggregate fn arg _distinct => do
      let allowed ← require (aggregates = true) "aggregate forbidden in this clause or nested aggregate"
      let arg ← certifyRelExpr scope false arg
      match h : aggregateResult fn arg.val with
      | none => invalid s!"incompatible argument type for aggregate {repr fn}"
      | some type => pure ⟨type, .aggregate allowed.down arg.property h⟩
  | .isNull arg _negated => do
      let arg ← certifyRelExpr scope aggregates arg
      pure ⟨.bool, .isNull arg.property⟩

theorem certifyRelExpr_complete (typed : RelHasType scope aggregates expr type) :
    certifyRelExpr scope aggregates expr = .ok ⟨type, typed⟩ := by
  induction typed with
  | literal value => rfl
  | column resolved =>
      simp only [certifyRelExpr]
      split
      · simp_all
      · rename_i column resolved'
        have same := Option.some.inj (resolved'.symm.trans resolved)
        subst column
        rfl
  | binary left right signature ihLeft ihRight =>
      simp only [certifyRelExpr, ihLeft, ihRight, Except.bind, pure, bind]
      split
      · simp_all
      · rename_i result signature'
        have same := Option.some.inj (signature'.symm.trans signature)
        subst result
        rfl
  | unary arg signature ih =>
      simp only [certifyRelExpr, ih, Except.bind, pure, bind]
      split
      · simp_all
      · rename_i result signature'
        have same := Option.some.inj (signature'.symm.trans signature)
        subst result
        rfl
  | countAll allowed => simp [certifyRelExpr, require_complete allowed, pure, bind, Except.bind, Except.pure]
  | aggregate allowed arg signature ih =>
      simp only [certifyRelExpr, require_complete allowed, ih, Except.bind, pure, bind]
      split
      · simp_all
      · rename_i result signature'
        have same := Option.some.inj (signature'.symm.trans signature)
        subst result
        rfl
  | isNull arg ih => simp [certifyRelExpr, ih, pure, bind, Except.bind, Except.pure]

def inferRelType (scope : RelScope) (aggregates : Bool) (expr : RelExpr) : Except ValidationError SqlType :=
  (certifyRelExpr scope aggregates expr).map Subtype.val

theorem inferRelType_sound (success : inferRelType scope aggregates expr = .ok type) :
    RelHasType scope aggregates expr type := by
  unfold inferRelType at success
  cases checked : certifyRelExpr scope aggregates expr with
  | error error => simp [checked, Except.map] at success
  | ok result =>
      simp [checked, Except.map] at success
      exact success ▸ result.property

theorem inferRelType_iff : inferRelType scope aggregates expr = .ok type ↔
    RelHasType scope aggregates expr type := by
  constructor
  · exact inferRelType_sound
  · intro typed; simp [inferRelType, certifyRelExpr_complete typed, Except.map]

/-- The relational type rules determine a unique type. -/
theorem RelHasType.unique (first : RelHasType scope aggregates expr firstType)
    (second : RelHasType scope aggregates expr secondType) : firstType = secondType := by
  have left := inferRelType_iff.mpr first
  have right := inferRelType_iff.mpr second
  exact Except.ok.inj (left.symm.trans right)

inductive RelHasTypes (scope : RelScope) (aggregates : Bool) : List RelExpr → List SqlType → Prop where
  | nil : RelHasTypes scope aggregates [] []
  | cons (head : RelHasType scope aggregates expr type) (tail : RelHasTypes scope aggregates exprs types) :
      RelHasTypes scope aggregates (expr :: exprs) (type :: types)

/-- Every selected or expanded expression contributes one result column. -/
theorem RelHasTypes.length_eq (typed : RelHasTypes scope aggregates exprs types) :
    exprs.length = types.length := by
  induction typed with
  | nil => rfl
  | cons _ _ ih => simp [ih]

def certifyRelExprs (scope : RelScope) (aggregates : Bool) (exprs : List RelExpr) :
    Except ValidationError {types : List SqlType // RelHasTypes scope aggregates exprs types} :=
  match exprs with
  | [] => pure ⟨[], .nil⟩
  | expr :: exprs => do
      let head ← certifyRelExpr scope aggregates expr
      let tail ← certifyRelExprs scope aggregates exprs
      pure ⟨head.val :: tail.val, .cons head.property tail.property⟩

theorem certifyRelExprs_complete (typed : RelHasTypes scope aggregates exprs types) :
    certifyRelExprs scope aggregates exprs = .ok ⟨types, typed⟩ := by
  induction typed with
  | nil => rfl
  | cons head tail ih => simp [certifyRelExprs, certifyRelExpr_complete head, ih,
      pure, bind, Except.bind, Except.pure]

inductive RelPredicateValid (scope : RelScope) (aggregates : Bool) : Option RelExpr → Prop where
  | absent : RelPredicateValid scope aggregates none
  | present (typed : RelHasType scope aggregates expr type) (boolean : type.base = .bool) :
      RelPredicateValid scope aggregates (some expr)

def certifyRelPredicate (scope : RelScope) (aggregates : Bool) (predicate : Option RelExpr) :
    Except ValidationError (PLift (RelPredicateValid scope aggregates predicate)) :=
  match predicate with
  | none => pure ⟨.absent⟩
  | some expr => do
      let typed ← certifyRelExpr scope aggregates expr
      let boolean ← require (typed.val.base = .bool) "predicate must have boolean type"
      pure ⟨.present typed.property boolean.down⟩

theorem certifyRelPredicate_complete (valid : RelPredicateValid scope aggregates predicate) :
    certifyRelPredicate scope aggregates predicate = .ok ⟨valid⟩ := by
  cases valid with
  | absent => rfl
  | present typed boolean => simp [certifyRelPredicate, certifyRelExpr_complete typed,
      require_complete boolean, pure, bind, Except.bind, Except.pure]

def TableRef.visibleName (table : TableRef) : Name := table.alias.getD table.name

def bindRelTable (table : TableDef) (ref : TableRef) : RelScope :=
  table.columns.map (fun column => ⟨ref.visibleName, column.name, column.type⟩)

def nullableScope (scope : RelScope) : RelScope :=
  scope.map (fun column => { column with type := column.type.asNullable })

def joinOutputScope (kind : JoinKind) (left right : RelScope) : RelScope :=
  match kind with
  | .inner | .cross => left ++ right
  | .left => left ++ nullableScope right
  | .right => nullableScope left ++ right
  | .full => nullableScope left ++ nullableScope right

def JoinShapeValid (join : Join) : Prop :=
  if join.kind = .cross then join.on = none else join.on ≠ none

instance (join : Join) : Decidable (JoinShapeValid join) := by unfold JoinShapeValid; infer_instance

/-- The ON scope contains only preceding relations and the current relation. -/
inductive RelJoinChain (schema : Schema) : RelScope → List Join → RelScope → Prop where
  | nil : RelJoinChain schema scope [] scope
  | cons (found : schema.findTable join.table.name = some table)
      (nameValid : join.table.visibleName ≠ "")
      (fresh : ∀ column ∈ scope, column.qualifier ≠ join.table.visibleName)
      (shape : JoinShapeValid join)
      (condition : RelPredicateValid (scope ++ bindRelTable table join.table) false join.on)
      (tail : RelJoinChain schema (joinOutputScope join.kind scope (bindRelTable table join.table)) joins finalScope) :
      RelJoinChain schema scope (join :: joins) finalScope

private structure LocatedTable (schema : Schema) (name : Name) where
  val : TableDef
  property : schema.findTable name = some val

private def certifyTable (schema : Schema) (name : Name) : Except ValidationError (LocatedTable schema name) :=
  match found : schema.findTable name with
  | none => invalid s!"unknown table '{name}'"
  | some table => pure ⟨table, found⟩

private theorem certifyTable_complete (found : schema.findTable name = some table) :
    certifyTable schema name = .ok ⟨table, found⟩ := by
  unfold certifyTable
  split
  · simp_all
  · rename_i table' found'
    have same := Option.some.inj (found'.symm.trans found)
    subst table'
    rfl

def certifyRelJoins (schema : Schema) (scope : RelScope) (joins : List Join) :
    Except ValidationError {finalScope : RelScope // RelJoinChain schema scope joins finalScope} :=
  match joins with
  | [] => pure ⟨scope, .nil⟩
  | join :: joins => do
      let table ← certifyTable schema join.table.name
      let nameValid ← require (join.table.visibleName ≠ "") "empty relation alias"
      let fresh ← require (∀ column ∈ scope, column.qualifier ≠ join.table.visibleName)
        s!"duplicate relation alias '{join.table.visibleName}'"
      let shape ← require (JoinShapeValid join) "JOIN requires ON; CROSS JOIN forbids ON"
      let condition ← certifyRelPredicate (scope ++ bindRelTable table.val join.table) false join.on
      let tail ← certifyRelJoins schema (joinOutputScope join.kind scope (bindRelTable table.val join.table)) joins
      pure ⟨tail.val, .cons table.property nameValid.down fresh.down shape.down condition.down tail.property⟩

theorem certifyRelJoins_complete (valid : RelJoinChain schema scope joins finalScope) :
    certifyRelJoins schema scope joins = .ok ⟨finalScope, valid⟩ := by
  induction valid with
  | nil => rfl
  | cons found nameValid fresh shape condition tail ih =>
      simp [certifyRelJoins, certifyTable_complete found, require_complete nameValid,
        require_complete fresh, require_complete shape, certifyRelPredicate_complete condition, ih,
        pure, bind, Except.bind, Except.pure]

inductive RelFromValid (schema : Schema) (query : RelQuery) (scope : RelScope) : Prop where
  | absent (emptyName : query.source.name = "")
      (plain : query.source.derived = none) (unaliased : query.source.alias = none)
      (noJoins : query.joins = []) (emptyScope : scope = []) : RelFromValid schema query scope
  | intro (nonempty : query.source.name ≠ "")
      (found : schema.findTable query.source.name = some table)
      (nameValid : query.source.visibleName ≠ "")
      (joins : RelJoinChain schema (bindRelTable table query.source) query.joins scope) :
      RelFromValid schema query scope

def certifyRelFrom (schema : Schema) (query : RelQuery) :
    Except ValidationError {scope : RelScope // RelFromValid schema query scope} := do
  if emptyName : query.source.name = "" then
    let plain ← require (query.source.derived = none) "unexpected derived source in flat query"
    let unaliased ← require (query.source.alias = none) "SELECT without FROM cannot have a source alias"
    let noJoins ← require (query.joins = []) "JOIN requires FROM"
    pure ⟨[], .absent emptyName plain.down unaliased.down noJoins.down rfl⟩
  else
    let table ← certifyTable schema query.source.name
    let nameValid ← require (query.source.visibleName ≠ "") "empty relation alias"
    let joins ← certifyRelJoins schema (bindRelTable table.val query.source) query.joins
    pure ⟨joins.val, .intro emptyName table.property nameValid.down joins.property⟩

theorem certifyRelFrom_complete (valid : RelFromValid schema query scope) :
    certifyRelFrom schema query = .ok ⟨scope, valid⟩ := by
  cases valid with
  | absent emptyName plain unaliased noJoins emptyScope =>
      subst scope
      simp [certifyRelFrom, emptyName, require_complete plain, require_complete unaliased,
        require_complete noJoins, pure, bind, Except.bind, Except.pure]
  | intro nonempty found nameValid joins => simp [certifyRelFrom, nonempty, certifyTable_complete found,
      require_complete nameValid, certifyRelJoins_complete joins, pure, bind, Except.bind, Except.pure]

/-- Normalize each column to its unique visible relation name. This makes
`id` and `u.id` denote the same grouping key when both resolve to `u.id`. -/
def canonicalRelExpr (scope : RelScope) : RelExpr → Except ValidationError RelExpr
  | .literal value => pure (.literal value)
  | .column qualifier name =>
      match resolveRelColumn scope qualifier name with
      | none => invalid s!"unknown or ambiguous column '{qualifier.getD ""}.{name}'"
      | some column => pure (.column (some column.qualifier) column.name)
  | .binary op left right => do
      return .binary op (← canonicalRelExpr scope left) (← canonicalRelExpr scope right)
  | .unary op arg => do return .unary op (← canonicalRelExpr scope arg)
  | .countAll => pure .countAll
  | .aggregate fn arg distinct => do return .aggregate fn (← canonicalRelExpr scope arg) distinct
  | .isNull arg negated => do return .isNull (← canonicalRelExpr scope arg) negated

structure ExpandedRelItem where
  expr : RelExpr
  alias : Option Name
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Expand wildcards in visible FROM/JOIN order. Explicit aliases are retained
for GROUP BY and ORDER BY name lookup, and are required to be nonempty. -/
def expandRelProjection (scope : RelScope) : List SelectItem → Except ValidationError (List ExpandedRelItem)
  | [] => pure []
  | .expression expr alias :: items => do
      let _ ← require (alias ≠ some "") "empty result alias"
      let expr ← canonicalRelExpr scope expr
      let tail ← expandRelProjection scope items
      pure (⟨expr, alias⟩ :: tail)
  | .all qualifier :: items => do
      let columns := scope.filter (fun column => qualifier.isNone || qualifier == some column.qualifier)
      let _ ← require (columns ≠ []) "unknown relation qualifier in wildcard"
      let tail ← expandRelProjection scope items
      pure (columns.map (fun column => ⟨.column (some column.qualifier) column.name, none⟩) ++ tail)

def relOrderOrdinal : RelExpr → Option Int
  | .literal (.int value) => some (Int.ofNat value)
  | .unary .pos arg => relOrderOrdinal arg
  | .unary .neg arg => (relOrderOrdinal arg).map Neg.neg
  | _ => none

private def resolveOutputAlias (items : List ExpandedRelItem) (name : Name) :
    Except ValidationError RelExpr :=
  match items.filter (fun item => item.alias == some name) with
  | [item] => pure item.expr
  | [] => invalid s!"unknown output alias '{name}'"
  | _ => invalid s!"ambiguous output alias '{name}'"

/-- SQL clause precedence: GROUP BY prefers input names; ORDER BY prefers
output aliases. Bare signed integers are checked 1-based projection ordinals.
Aliases are accepted as whole keys, not interpolated inside expressions. -/
def elaborateRelKey (scope : RelScope) (items : List ExpandedRelItem) (order : Bool)
    (expr : RelExpr) : Except ValidationError RelExpr := do
  match relOrderOrdinal expr with
  | some ordinal =>
      if ordinal > 0 then
        match items[ordinal.toNat - 1]? with
        | some item => pure item.expr
        | none => invalid "GROUP BY/ORDER BY ordinal is outside the result projection"
      else invalid "GROUP BY/ORDER BY ordinal must be positive"
  | none =>
      match expr with
      | .column none name =>
          let aliases := items.filter (fun item => item.alias == some name)
          let source := matchingRelColumns scope none name
          if order && !aliases.isEmpty then resolveOutputAlias items name
          else if !source.isEmpty then canonicalRelExpr scope expr
          else if !aliases.isEmpty then resolveOutputAlias items name
          else canonicalRelExpr scope expr
      | _ => canonicalRelExpr scope expr

structure ElaboratedRelQuery where
  selected : List RelExpr
  groupKeys : List RelExpr
  having : Option RelExpr
  orderKeys : List RelExpr
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Syntactic elaboration resolves bindings, expands stars, and substitutes
whole-clause aliases/ordinals. The certificate records this exact elaboration. -/
def elaborateRelQuery (scope : RelScope) (query : RelQuery) : Except ValidationError ElaboratedRelQuery := do
  let items ← expandRelProjection scope query.selectList
  let groups ← query.groupBy.mapM (elaborateRelKey scope items false)
  let having ← query.having.mapM (canonicalRelExpr scope)
  let orders ← query.orderBy.mapM (fun order => elaborateRelKey scope items true order.expr)
  pure ⟨items.map ExpandedRelItem.expr, groups, having, orders⟩

def RelExpr.hasAggregate : RelExpr → Bool
  | .literal _ | .column _ _ => false
  | .binary _ left right => left.hasAggregate || right.hasAggregate
  | .unary _ arg | .isNull arg _ => arg.hasAggregate
  | .countAll | .aggregate _ _ _ => true

/-- A grouped result may use complete grouping keys, constants, aggregate
results, or expressions built from them. No functional dependencies are assumed. -/
def GroupCompatible (keys : List RelExpr) : RelExpr → Prop
  | .literal value => (∃ key ∈ keys, RelExpr.literal value = key) ∨ True
  | .column qualifier name => (∃ key ∈ keys, RelExpr.column qualifier name = key) ∨ False
  | .countAll => (∃ key ∈ keys, RelExpr.countAll = key) ∨ True
  | .aggregate fn arg distinct => (∃ key ∈ keys, RelExpr.aggregate fn arg distinct = key) ∨ True
  | .binary op left right => (∃ key ∈ keys, RelExpr.binary op left right = key) ∨
      (GroupCompatible keys left ∧ GroupCompatible keys right)
  | .unary op arg => (∃ key ∈ keys, RelExpr.unary op arg = key) ∨ GroupCompatible keys arg
  | .isNull arg negated => (∃ key ∈ keys, RelExpr.isNull arg negated = key) ∨ GroupCompatible keys arg

instance groupCompatibleDecidable (keys : List RelExpr) (expr : RelExpr) :
    Decidable (GroupCompatible keys expr) :=
  match expr with
  | .literal _ | .column _ _ | .countAll | .aggregate _ _ _ =>
      inferInstanceAs (Decidable (_ ∨ _))
  | .binary _ left right =>
      let _ := groupCompatibleDecidable keys left
      let _ := groupCompatibleDecidable keys right
      inferInstanceAs (Decidable (_ ∨ _))
  | .unary _ arg | .isNull arg _ =>
      let _ := groupCompatibleDecidable keys arg
      inferInstanceAs (Decidable (_ ∨ _))

def ElaboratedRelQuery.isGrouped (query : ElaboratedRelQuery) : Bool :=
  !query.groupKeys.isEmpty || query.having.isSome ||
  (query.selected ++ query.orderKeys).any RelExpr.hasAggregate

def RelGroupingValid (query : ElaboratedRelQuery) : Prop :=
  query.isGrouped = true →
    ∀ expr ∈ query.selected ++ query.orderKeys ++ query.having.toList,
      GroupCompatible query.groupKeys expr

instance (query : ElaboratedRelQuery) : Decidable (RelGroupingValid query) :=
  inferInstanceAs (Decidable (_ → _))

def RelOptionsValid (query : RelQuery) (elaborated : ElaboratedRelQuery) : Prop :=
  elaborated.selected ≠ [] ∧
  (query.offset ≠ none → query.limit ≠ none) ∧
  (query.distinct = true → ∀ expr ∈ elaborated.orderKeys, ∃ selected ∈ elaborated.selected, expr = selected)

instance (query : RelQuery) (elaborated : ElaboratedRelQuery) : Decidable (RelOptionsValid query elaborated) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Nested sources are handled by `NestedValidation`; the flat checker never
silently drops a WITH binding or derived-table query. -/
def FlatRelQuery (query : RelQuery) : Prop :=
  query.ctes.isEmpty = true ∧ query.recursive = false ∧ query.unions.isEmpty = true ∧
  query.source.derived.isNone = true ∧ ∀ join ∈ query.joins, join.table.derived.isNone = true

instance (query : RelQuery) : Decidable (FlatRelQuery query) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Independent static contract: a well-formed schema, sequential join scope,
explicit name elaboration, structurally typed clauses, aggregate placement,
SQL grouping rules and bounded projection ordinals. -/
inductive ValidRelQueryCore (schema : Schema) (query : RelQuery) (outputTypes : List SqlType) : Prop where
  | intro (schemaValid : WellFormedSchema schema)
      (flat : FlatRelQuery query)
      (fromValid : RelFromValid schema query scope)
      (elaboration : elaborateRelQuery scope query = .ok elaborated)
      (selected : RelHasTypes scope true elaborated.selected outputTypes)
      (filter : RelPredicateValid scope false query.whereClause)
      (groups : RelHasTypes scope false elaborated.groupKeys groupTypes)
      (having : RelPredicateValid scope true elaborated.having)
      (orders : RelHasTypes scope true elaborated.orderKeys orderTypes)
      (grouping : RelGroupingValid elaborated)
      (options : RelOptionsValid query elaborated) : ValidRelQueryCore schema query outputTypes

structure CertifiedRelQueryCore (schema : Schema) (query : RelQuery) where
  outputTypes : List SqlType
  valid : ValidRelQueryCore schema query outputTypes

private structure CertifiedElaboration (scope : RelScope) (query : RelQuery) where
  val : ElaboratedRelQuery
  property : elaborateRelQuery scope query = .ok val

private def certifyElaboration (scope : RelScope) (query : RelQuery) :
    Except ValidationError (CertifiedElaboration scope query) :=
  match h : elaborateRelQuery scope query with
  | .error error => .error error
  | .ok result => .ok ⟨result, h⟩

private theorem certifyElaboration_complete (h : elaborateRelQuery scope query = .ok result) :
    certifyElaboration scope query = .ok ⟨result, h⟩ := by
  unfold certifyElaboration
  split
  · simp_all
  · rename_i result' h'
    have same := Except.ok.inj (h'.symm.trans h)
    subst result'
    rfl

def certifyRelQueryCore (schema : Schema) (query : RelQuery) :
    Except ValidationError (CertifiedRelQueryCore schema query) := do
  let schemaValid ← checkSchema schema
  let flat ← require (FlatRelQuery query) "nested query requires certifyRelQuery"
  let source ← certifyRelFrom schema query
  let elaborated ← certifyElaboration source.val query
  let selected ← certifyRelExprs source.val true elaborated.val.selected
  let filter ← certifyRelPredicate source.val false query.whereClause
  let groups ← certifyRelExprs source.val false elaborated.val.groupKeys
  let having ← certifyRelPredicate source.val true elaborated.val.having
  let orders ← certifyRelExprs source.val true elaborated.val.orderKeys
  let grouping ← require (RelGroupingValid elaborated.val)
    "ungrouped column: SELECT, HAVING and ORDER BY must use grouping keys or aggregates"
  let options ← require (RelOptionsValid query elaborated.val)
    "invalid SELECT options: empty projection, OFFSET without LIMIT, or DISTINCT order outside projection"
  pure ⟨selected.val, .intro schemaValid.down flat.down source.property elaborated.property selected.property
    filter.down groups.property having.down orders.property grouping.down options.down⟩

def checkRelQueryCore (schema : Schema) (query : RelQuery) : Except ValidationError (List SqlType) :=
  (certifyRelQueryCore schema query).map CertifiedRelQueryCore.outputTypes

theorem checkRelQueryCore_sound (success : checkRelQueryCore schema query = .ok types) :
    ValidRelQueryCore schema query types := by
  unfold checkRelQueryCore at success
  cases checked : certifyRelQueryCore schema query with
  | error error => simp [checked, Except.map] at success
  | ok result =>
      simp [checked, Except.map] at success
      exact success ▸ result.valid

theorem certifyRelQueryCore_complete (valid : ValidRelQueryCore schema query types) :
    certifyRelQueryCore schema query = .ok ⟨types, valid⟩ := by
  cases valid with
  | intro schemaValid flat fromValid elaboration selected filter groups having orders grouping options =>
      simp [certifyRelQueryCore, checkSchema, schemaValid, require_complete flat, certifyRelFrom_complete fromValid,
        certifyElaboration_complete elaboration, certifyRelExprs_complete selected,
        certifyRelPredicate_complete filter, certifyRelExprs_complete groups,
        certifyRelPredicate_complete having, certifyRelExprs_complete orders,
        require_complete grouping, require_complete options, pure, bind, Except.bind, Except.pure]

theorem checkRelQueryCore_iff : checkRelQueryCore schema query = .ok types ↔ ValidRelQueryCore schema query types := by
  constructor
  · exact checkRelQueryCore_sound
  · intro valid; simp [checkRelQueryCore, certifyRelQueryCore_complete valid, Except.map]

/-- A core certificate binds its output arity to the exact elaborated projection. -/
theorem ValidRelQueryCore.output_arity (valid : ValidRelQueryCore schema query types) :
    ∃ scope elaborated, RelFromValid schema query scope ∧
      elaborateRelQuery scope query = .ok elaborated ∧ elaborated.selected.length = types.length := by
  cases valid with
  | intro _ _ fromValid elaboration selected _ _ _ _ _ _ =>
      exact ⟨_, _, fromValid, elaboration, selected.length_eq⟩

end SQLean
