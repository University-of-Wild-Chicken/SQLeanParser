import SQLean.SelectContract.CollationRules

/-! Independent query, source, and namespace judgments. Scalar typing and
collation derivations are separate prerequisites of every expression context. -/
namespace SQLean.SelectContract
open Advanced

/-- Constructor-derived labels survive explicit cast chains. -/
def arrayOrigin : Advanced.Expr → Bool
  | .array _ => true
  | .cast arg _ => arrayOrigin arg
  | _ => false

/-- Built-in names used by PostgreSQL's raw TypeName after grammar aliases
are normalized. Array suffixes and modifiers do not change the label. -/
def typeNameLabel : Advanced.TypeName → Name
  | .smallInt => "int2" | .int => "int4" | .bigInt => "int8"
  | .name => "name" | .text => "text" | .varchar => "varchar" | .char => "bpchar"
  | .bool => "bool" | .real => "float4" | .doublePrecision => "float8"
  | .numeric => "numeric" | .date => "date" | .time => "time"
  | .timeTZ => "timetz" | .timestamp => "timestamp" | .timestampTZ => "timestamptz"
  | .interval | .intervalRange _ => "interval" | .uuid => "uuid" | .json => "json"
  | .jsonb => "jsonb" | .bytea => "bytea"
  | .array element => typeNameLabel element

/-- PostgreSQL FigureColnameInternal's strength distinction for the covered
expression forms: 0 is absent, 1 is a weak cast/CASE name, and 2 is inherited.
A cast replaces a weak name but retains a column/function/constructor name. -/
def outputLabel : Advanced.Expr → Nat × Name
  | .column _ name _ => (2, name)
  | .call name _ | .namedCall name _ => (2, name.getLastD "?column?")
  | .contextValue value => (2, contextValueLabel value)
  | .array _ => (2, "array")
  | .row _ => (2, "row")
  | .extract .. => (2, "extract")
  | .substring .. => (2, "substring")
  | .cast arg target =>
      let inherited := outputLabel arg
      if inherited.1 ≤ 1 then (1, typeNameLabel target.name) else inherited
  | .subscript arg _ | .collate arg _ => outputLabel arg
  | .caseExpr _ _ otherwise =>
      let inherited := match otherwise with
        | none => (0, "?column?")
        | some expr => outputLabel expr
      if inherited.1 ≤ 1 then (1, "case") else inherited
  | .coalesce .. => (2, "coalesce")
  | .nullIf .. => (2, "nullif")
  | .greatest .. => (2, "greatest")
  | .least .. => (2, "least")
  | _ => (0, "?column?")

/-- Labels are independent of expression typing. Duplicate labels remain
ordered outputs, and an explicit alias overrides every inferred label. -/
def outputName (expr : Advanced.Expr) (alias : Option Name) : Name :=
  alias.getD (outputLabel expr).2

inductive ItemsValid (profile : Profile) (params : ParameterEnv) (scope : Scope) :
    List Advanced.SelectItem → List OutputColumn → List Parameter → Prop where
  | nil : ItemsValid profile params scope [] [] []
  | expression (typed : ExprValid params scope expr type uses)
      (collation : ExprCollationValid profile params scope expr type derivation)
      (aliasValid : ∀ name ∈ alias, name ≠ "")
      (tail : ItemsValid profile params scope items output remaining) :
      ItemsValid profile params scope (.expression expr alias :: items)
        (⟨outputName expr alias, projectedType type, projectedCollation expr type derivation⟩ :: output) (uses ++ remaining)
  | all (bindings : scope.columns qualifier schema = selected)
      (nonempty : selected ≠ [])
      (tail : ItemsValid profile params scope items output uses) :
      ItemsValid profile params scope (.all qualifier schema :: items) (selected ++ output) uses

/-- A set operand retains raw unknown literal inputs until its containing
binary set operation selects a type. Complete derived/CTE outputs are known. -/
structure PendingColumn where
  name : Name
  input : ScalarInput
  derivation : CollationDerivation := .none
  origin : PendingOrigin := .known
  sortKey : Option UnknownSortValue := none
  deriving Repr, BEq, DecidableEq

def knownColumns (output : List OutputColumn) : List PendingColumn :=
  output.map fun column => ⟨column.name, .known column.type, .stored column.collation, .known, none⟩

inductive ItemsInputValid (profile : Profile) (params : ParameterEnv) (scope : Scope) :
    List Advanced.SelectItem → List PendingColumn → List Parameter → Prop where
  | nil : ItemsInputValid profile params scope [] [] []
  | expression (typed : ExprValid params scope expr type uses)
      (collation : ExprCollationValid profile params scope expr type derivation)
      (aliasValid : ∀ name ∈ alias, name ≠ "")
      (tail : ItemsInputValid profile params scope items output remaining) :
      ItemsInputValid profile params scope (.expression expr alias :: items)
        (⟨outputName expr alias, scalarInput expr type, derivation, pendingOrigin expr type, unknownCollationSortKey profile expr⟩ :: output) (uses ++ remaining)
  | all (bindings : scope.columns qualifier schema = selected)
      (nonempty : selected ≠ [])
      (tail : ItemsInputValid profile params scope items output uses) :
      ItemsInputValid profile params scope (.all qualifier schema :: items)
        (knownColumns selected ++ output) uses

inductive PredicateValid (profile : Profile) (params : ParameterEnv) (scope : Scope) : Option Advanced.Expr → List Parameter → Prop where
  | absent : PredicateValid profile params scope none []
  | present (typed : ExprValid params scope expr type uses)
      (collation : ExprCollationValid profile params scope expr type derivation) (boolean : acceptsBase .bool type = true) :
      PredicateValid profile params scope (some expr) uses

/-- Outer joins add possible NULL rows without changing names, order, concrete
types, or declaration modifiers. Existing nullability is retained. -/
def nullableColumn (column : OutputColumn) : OutputColumn :=
  { column with type := { column.type with nullable := true } }

def nullableScope (scope : Scope) : Scope :=
  ⟨scope.relations.map (fun relation =>
      {relation with columns := relation.columns.map nullableColumn, nullable := true}),
    scope.output.map nullableColumn⟩

def joinScope (kind : JoinKind) (left right : Scope) : Scope :=
  (if kind == .right || kind == .full then nullableScope left else left) ++
  (if kind == .left || kind == .full then nullableScope right else right)

/-- Visible leaf relation names with the possibility of a NULL-extended row.
This is structural metadata, independent of column resolution or a checker. -/
def fromRelations : Advanced.From → List (Name × Bool)
  | .table name alias _ _ => [(alias.getD name, false)]
  | .derived _ alias _ _ => [(alias, false)]
  | .join kind left right _ =>
      (fromRelations left).map (fun relation =>
        (relation.1, relation.2 || kind == .right || kind == .full)) ++
      (fromRelations right).map (fun relation =>
        (relation.1, relation.2 || kind == .left || kind == .full))

def sourceRelations (source : Option Advanced.From) : List (Name × Bool) :=
  source.toList.flatMap fromRelations

def fromDerivedNames : Advanced.From → List Name
  | .table .. => []
  | .derived _ alias _ _ => [alias]
  | .join _ left right _ => fromDerivedNames left ++ fromDerivedNames right

def sourceDerivedNames (source : Option Advanced.From) : List Name :=
  source.toList.flatMap fromDerivedNames

/-- Equal visible names are legal only for distinct unaliased base relations.
Column lookup can still be ambiguous; the namespace itself remains well formed. -/
def NamespaceCompatible (left right : RelationNamespace) : Prop :=
  left.name ≠ right.name ∨
    (left.aliased = false ∧ right.aliased = false ∧
      left.origin.isBase = true ∧ right.origin.isBase = true ∧ left.origin ≠ right.origin)

instance (left right : RelationNamespace) : Decidable (NamespaceCompatible left right) := by
  unfold NamespaceCompatible
  infer_instance

def JoinAliasesDistinct (left right : Scope) : Prop :=
  ∀ l ∈ left.relations, ∀ r ∈ right.relations, NamespaceCompatible l r

instance (left right : Scope) : Decidable (JoinAliasesDistinct left right) := by
  unfold JoinAliasesDistinct
  infer_instance

/-- NATURAL discovers common names in the left exposed row's order. It does
not deduplicate names: ambiguous exposed keys must be rejected. -/
def naturalJoinKeys (left right : List OutputColumn) : List Name :=
  (left.filter (fun col => right.any (fun other => other.name == col.name))).map OutputColumn.name

/-- No equality-based nullability refinement is claimed. LEFT/RIGHT preserve
their retained side; INNER/FULL conservatively admit NULL from either input.
In particular FULL must not use COALESCE's pre-join conjunction rule. -/
def mergedKeyNullable (kind : JoinKind) (left right : ExactType) : Bool :=
  match kind with
  | .left => left.nullable
  | .right => right.nullable
  | _ => left.nullable || right.nullable

/-- Equality resolution and merged-column common-type resolution are separate
normative premises, as in PostgreSQL. Both inspect the original child types. -/
inductive JoinKeysValid (kind : JoinKind) (left right : List OutputColumn) :
    List Name → List OutputColumn → Prop where
  | nil : JoinKeysValid kind left right [] []
  | cons (leftResolved : left.filter (fun col => col.name == key) = [leftColumn])
      (rightResolved : right.filter (fun col => col.name == key) = [rightColumn])
      (equality : equalityOverload (.known leftColumn.type) (.known rightColumn.type) = some operator)
      (common : conditionalBase [.known leftColumn.type, .known rightColumn.type] = some base)
      (equalityCoercions : contextualCollations
        [.column none key, .column none key] [some leftColumn.type, some rightColumn.type]
        [.stored leftColumn.collation, .stored rightColumn.collation]
        (concreteCollationTargets operator.inputs) = some coerced)
      (equalityCollation : CollationDerivation.mergeList coerced = some inputCollation)
      (resultCollation : mergedKeyCollation kind leftColumn rightColumn base = some collation)
      (tail : JoinKeysValid kind left right keys merged) :
      JoinKeysValid kind left right (key :: keys)
        (⟨key, ⟨base, mergedKeyNullable kind leftColumn.type rightColumn.type⟩, collation⟩ :: merged)

/-- Qualified columns retain both child namespaces and their original order.
Only the exposed row is merged: keys first, then left and right nonkeys. -/
def mergedJoinScope (kind : JoinKind) (left right : Scope)
    (keys : List Name) (merged : List OutputColumn) : Scope :=
  let joined := joinScope kind left right
  ⟨joined.relations, merged ++ joined.output.filter (fun col => !keys.contains col.name)⟩

/-- An alias list renames a positional prefix; unnamed remaining columns keep
their certified labels. Repeated labels are legal and remain ambiguous when
referenced by name. The separate length premise forbids excess aliases. -/
def renameOutput : List Name → List OutputColumn → List OutputColumn
  | [], output => output
  | name :: names, column :: output => { column with name } :: renameOutput names output
  | _ :: _, [] => []

def ColumnAliasesValid (names : List Name) (output : List OutputColumn) : Prop :=
  names.length ≤ output.length ∧ ∀ name ∈ names, name ≠ ""

instance (names : List Name) (output : List OutputColumn) : Decidable (ColumnAliasesValid names output) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- PostgreSQL SQL92 sort constants retain their raw token category.
Only signed chains of integer tokens that fit the scanner's INT4 category are
ordinals. Unary plus is an operator expression; it must not be folded here. -/
inductive SortSyntax where
  | integer (position : Int)
  | numericConstant
  | otherConstant
  | expression
  deriving Repr, BEq, DecidableEq

def sortSyntax : Advanced.Expr → SortSyntax
  | .literal (.int n) =>
      if n ≤ 2147483647 then .integer (Int.ofNat n) else .numericConstant
  | .decimal _ => .numericConstant
  | .null | .literal (.text _) | .literal (.bool _) => .otherConstant
  | .unary .neg arg => match sortSyntax arg with
      | .integer n => .integer (-n)
      | .numericConstant => .numericConstant
      | _ => .expression
  | _ => .expression

/-- Constants use the SQL92 rules above. Bare output names use name resolution;
all other admitted expressions use ordinary scalar typing. -/
def SortExpression (expr : Advanced.Expr) : Prop :=
  sortSyntax expr = .expression ∧ match expr with
    | .column none _ none => False
    | _ => True

instance (expr : Advanced.Expr) : Decidable (SortExpression expr) := by
  unfold SortExpression
  split <;> infer_instance

def OrdinalOrderable (output : List OutputColumn) (n : Nat) : Prop :=
  ((output[n - 1]?).map (fun column => column.type.base.orderable)).getD false = true

instance (output : List OutputColumn) (n : Nat) : Decidable (OrdinalOrderable output n) :=
  inferInstanceAs (Decidable (_ = _))

def DistinctAllowed (distinct : Bool) (output : List OutputColumn) : Prop :=
  distinct = false ∨ ∀ column ∈ output, column.type.base.orderable = true

instance (distinct : Bool) (output : List OutputColumn) : Decidable (DistinctAllowed distinct output) :=
  inferInstanceAs (Decidable (_ ∨ _))

def projectionExpressions (items : List Advanced.SelectItem) (name : Name) : List Advanced.Expr :=
  match items with
  | [] => []
  | .expression expr alias :: rest =>
      if outputName expr alias == name then expr :: projectionExpressions rest name
      else projectionExpressions rest name
  | .all .. :: rest => projectionExpressions rest name

def pureProjection (items : List Advanced.SelectItem) : Bool :=
  items.all fun item => match item with | .expression .. => true | .all .. => false

/-- Syntactic identity and exact normalized unknown COLLATE trees justify
PostgreSQL's repeated-target-name exception. Other transformed identities
remain outside coverage. -/
def SameOutputExpressions (profile : Profile) (items : List Advanced.SelectItem) (name : Name) : Prop :=
  pureProjection items = true ∧
    match projectionExpressions items name with
    | [] => False
    | first :: rest => ∀ expr ∈ rest, expr = first ∨
        ((unknownCollationSortKey profile expr).isSome = true ∧
          unknownCollationSortKey profile expr = unknownCollationSortKey profile first)

/-- Output-name lookup takes precedence only for a bare name. Repeated names
need projection identity; compound expressions see input bindings, not aliases. -/
inductive SortValid (profile : Profile) (params : ParameterEnv) (scope : Scope) (projection : List Advanced.SelectItem) (output : List OutputColumn) (distinct : Bool) :
    Advanced.Expr → List Parameter → Prop where
  | ordinal (constant : sortSyntax expr = .integer position)
      (positive : 0 < position) (inRange : position.toNat ≤ output.length)
      (orderable : OrdinalOrderable output position.toNat) :
      SortValid profile params scope projection output distinct expr []
  | outputName (resolved : output.filter (·.name == name) = [column])
      (orderable : column.type.base.orderable = true) :
      SortValid profile params scope projection output distinct (.column none name) []
  | repeatedName (same : SameOutputExpressions profile projection name)
      (resolved : output.filter (·.name == name) = column :: remaining)
      (orderable : column.type.base.orderable = true) :
      SortValid profile params scope projection output distinct (.column none name) []
  | inputName (noOutput : output.filter (·.name == name) = []) (ordinary : distinct = false)
      (typed : ExprValid params scope (.column none name) type uses)
      (orderable : type.orderable = true) :
      SortValid profile params scope projection output distinct (.column none name) uses
  | expression (ordinary : distinct = false) (typed : ExprValid params scope expr type uses)
      (category : SortExpression expr) (orderable : type.orderable = true) :
      SortValid profile params scope projection output distinct expr uses

/-- Raw unknown identity survives until its particular target entry is sorted.
The outer option distinguishes known expressions; the inner distinguishes NULL
from an unknown string payload. -/
def unknownSortKey (profile : Profile) (expr : Advanced.Expr) : Option UnknownSortValue :=
  unknownCollationSortKey profile expr

def projectionSortKeys (profile : Profile) (items : List Advanced.SelectItem) : List (Name × Option UnknownSortValue) :=
  items.map fun item => match item with
    | .expression expr alias => (outputName expr alias, unknownSortKey profile expr)
    | .all .. => ("", none)

def firstSortIndex (keys : List (Name × Option UnknownSortValue)) (name : Name) : Option Nat :=
  match keys with
  | [] => none
  | key :: rest => if key.1 == name then some 0 else (firstSortIndex rest name).map Nat.succ

def firstExpressionSortIndex (keys : List (Name × Option UnknownSortValue))
    (resolved : List Nat) (key : UnknownSortValue) : Option Nat :=
  ((keys.zipIdx).find? fun row => row.1.2 == some key && !resolved.contains row.2).map Prod.snd

def sortTargetIndex (profile : Profile) (keys : List (Name × Option UnknownSortValue))
    (resolved : List Nat) (expr : Advanced.Expr) : Option Nat :=
  match sortSyntax expr with
  | .integer position => if 0 < position then some (position.toNat - 1) else none
  | _ => match expr with
    | .column none name none => firstSortIndex keys name
    | _ => (unknownSortKey profile expr).bind (firstExpressionSortIndex keys resolved)

/-- SQL99 matches the remaining unknown target entries after preceding sort
items have resolved earlier matches. SQL92 names and ordinals can reuse them. -/
def orderResolvedIndices (profile : Profile) (keys : List (Name × Option UnknownSortValue))
    (resolved : List Nat) : List Advanced.OrderBy → List Nat
  | [] => resolved
  | order :: rest => orderResolvedIndices profile keys
      (match sortTargetIndex profile keys resolved order.expr with
        | none => resolved | some index => index :: resolved) rest

def unknownSortGroup (keys : List (Name × Option UnknownSortValue)) (name : Name) : List Nat :=
  let matching := keys.zipIdx.filter (fun row => row.1.1 == name)
  match matching with
  | [] => []
  | first :: _ =>
    match first.1.2 with
    | none => []
    | some key =>
      if matching.all (fun row => row.1.2 == some key) then matching.map Prod.snd else []

/-- PostgreSQL processes ORDER BY entries sequentially. Resolving just one of
several identical unknown projections can make a later name ambiguous. -/
def orderSequenceSafe (profile : Profile) (keys : List (Name × Option UnknownSortValue)) (resolved : List Nat) :
    List Advanced.OrderBy → Bool
  | [] => true
  | order :: rest =>
    let safe := match order.expr with
      | .column none name none =>
        let group := unknownSortGroup keys name
        group.all resolved.contains || group.all (fun index => !resolved.contains index)
      | _ => true
    safe && orderSequenceSafe profile keys
      (match sortTargetIndex profile keys resolved order.expr with | none => resolved | some index => index :: resolved) rest

def OrderSequenceSafe (profile : Profile) (projection : List Advanced.SelectItem) (orders : List Advanced.OrderBy) : Prop :=
  pureProjection projection = false ∨ orderSequenceSafe profile (projectionSortKeys profile projection) [] orders = true

instance (profile : Profile) (projection : List Advanced.SelectItem) (orders : List Advanced.OrderBy) :
    Decidable (OrderSequenceSafe profile projection orders) :=
  inferInstanceAs (Decidable (_ ∨ _))

inductive SortListValid (profile : Profile) (params : ParameterEnv) (scope : Scope) (projection : List Advanced.SelectItem) (output : List OutputColumn) (distinct : Bool) :
    List Advanced.OrderBy → List Parameter → Prop where
  | nil : SortListValid profile params scope projection output distinct [] []
  | cons (head : SortValid profile params scope projection output distinct item.expr uses)
      (tail : SortListValid profile params scope projection output distinct items remaining) :
      SortListValid profile params scope projection output distinct (item :: items) (uses ++ remaining)

inductive OrdersValid (profile : Profile) (params : ParameterEnv) (scope : Scope) (projection : List Advanced.SelectItem)
    (output : List OutputColumn) (distinct : Bool) : List Advanced.OrderBy → List Parameter → Prop where
  | nil : OrdersValid profile params scope projection output distinct [] []
  | checked (items : SortListValid profile params scope projection output distinct orders uses)
      (sequence : OrderSequenceSafe profile projection orders) :
      OrdersValid profile params scope projection output distinct orders uses

/-- A direct sort sees the derivation of its target expression. A stored
relation column has already lost explicit/conflict strength at its query boundary. -/
inductive SortCollationValid (profile : Profile) (params : ParameterEnv) (scope : Scope)
    (pending : List PendingColumn) : Advanced.Expr → Prop where
  | ordinal (constant : sortSyntax expr = .integer position)
      (resolved : pending[position.toNat - 1]? = some column)
      (determinate : column.derivation.determinate = true) :
      SortCollationValid profile params scope pending expr
  | outputName (resolved : pending.find? (fun column => column.name == name) = some column)
      (determinate : column.derivation.determinate = true) :
      SortCollationValid profile params scope pending (.column none name)
  | inputName (noOutput : pending.find? (fun column => column.name == name) = none)
      (collation : ExprCollationValid profile params scope (.column none name) type derivation)
      (determinate : derivation.determinate = true) :
      SortCollationValid profile params scope pending (.column none name)
  | expression (category : SortExpression expr)
      (collation : ExprCollationValid profile params scope expr type derivation)
      (determinate : derivation.determinate = true) :
      SortCollationValid profile params scope pending expr

inductive OrdersCollationValid (profile : Profile) (params : ParameterEnv) (scope : Scope)
    (pending : List PendingColumn) : List Advanced.OrderBy → Prop where
  | nil : OrdersCollationValid profile params scope pending []
  | cons (head : SortCollationValid profile params scope pending item.expr)
      (tail : OrdersCollationValid profile params scope pending items) :
      OrdersCollationValid profile params scope pending (item :: items)

def DistinctCollations (distinct : Bool) (pending : List PendingColumn) : Prop :=
  distinct = false ∨ ∀ column ∈ pending, column.derivation.determinate = true

instance (distinct : Bool) (pending : List PendingColumn) :
    Decidable (DistinctCollations distinct pending) := by
  unfold DistinctCollations
  infer_instance

/-- Sorting resolves the targets selected sequentially by SQL92 or SQL99.
DISTINCT then resolves every target. Pagination alone leaves them contextual. -/
def resolveLeafInputs (profile : Profile) (distinct : Bool) (orders : List Advanced.OrderBy)
    (columns : List PendingColumn) : List PendingColumn :=
  let resolved := orderResolvedIndices profile
    (columns.map fun column => (column.name, column.sortKey)) [] orders
  columns.zipIdx.map fun (column, index) =>
    if distinct || resolved.contains index then
      match column.input with
      | .unknown nullable => ⟨column.name, .known ⟨.text, nullable⟩,
          pendingCoercion column.origin column.input column.derivation .text, .known, column.sortKey⟩
      | .known _ => column
    else column

/-- Within the admitted built-in inventory, grouping requires scalar equality,
including element equality for arrays. JSON and JSON[] fail this requirement
at set analysis, unlike the deferred JSON[] comparison execution boundary. -/
def SetGroupingAllowed (op : Advanced.SetOp) (all : Bool) (type : ScalarType) : Prop :=
  (op = .union ∧ all = true) ∨ type.orderable = true

instance (op : Advanced.SetOp) (all : Bool) (type : ScalarType) :
    Decidable (SetGroupingAllowed op all type) :=
  inferInstanceAs (Decidable (_ ∨ _))

inductive SetColumnsValid (op : Advanced.SetOp) (all : Bool) :
    List PendingColumn → List PendingColumn → List OutputColumn → Prop where
  | nil : SetColumnsValid op all [] [] []
  | cons (common : conditionalBase [left.input, right.input] = some base)
      (leftCoercion : acceptsInput left.input base = true)
      (rightCoercion : acceptsInput right.input base = true)
      (grouping : SetGroupingAllowed op all base)
      (collation : CollationDerivation.merge
        (pendingCoercion left.origin left.input left.derivation base)
        (pendingCoercion right.origin right.input right.derivation base) = some derivation)
      (determinate : (op = .union ∧ all = true) ∨ derivation.determinate = true)
      (tail : SetColumnsValid op all lefts rights output) :
      SetColumnsValid op all (left :: lefts) (right :: rights)
        (⟨left.name, ⟨base, left.input.nullable || right.input.nullable⟩, derivation.identity⟩ :: output)

/-- A compound result has no input-relation namespace for ORDER BY. -/
inductive SetSortValid (output : List OutputColumn) : Advanced.Expr → Prop where
  | ordinal (constant : sortSyntax expr = .integer position)
      (positive : 0 < position) (inRange : position.toNat ≤ output.length)
      (orderable : OrdinalOrderable output position.toNat) : SetSortValid output expr
  | outputName (resolved : output.filter (·.name == name) = [column])
      (orderable : column.type.base.orderable = true) :
      SetSortValid output (.column none name)

inductive SetOrdersValid (output : List OutputColumn) : List Advanced.OrderBy → Prop where
  | nil : SetOrdersValid output []
  | cons (head : SetSortValid output item.expr) (tail : SetOrdersValid output items) :
      SetOrdersValid output (item :: items)

/-- The pagination context supplies PostgreSQL's INT8 row-count target.
Integer widening is lossless; NUMERIC/REAL/DOUBLE use catalog assignment casts
whose rounding/range checks remain execution obligations. Unknown NULL acquires
the target type. These are contextual casts, not general operator signatures. -/
inductive RowCountCoercion : ExprType → Prop where
  | unknownNull : RowCountCoercion none
  | smallIntWiden (nullable : Bool) : RowCountCoercion (some ⟨.smallInt, nullable⟩)
  | int32Widen (nullable : Bool) : RowCountCoercion (some ⟨.int32, nullable⟩)
  | int64Identity (nullable : Bool) : RowCountCoercion (some ⟨.int64, nullable⟩)
  | numericAssignment (modifiers : List Nat) (nullable : Bool) :
      RowCountCoercion (some ⟨.numeric modifiers, nullable⟩)
  | realAssignment (nullable : Bool) : RowCountCoercion (some ⟨.real, nullable⟩)
  | doubleAssignment (nullable : Bool) : RowCountCoercion (some ⟨.doublePrecision, nullable⟩)

/-- Every successfully evaluated signed INT32 value embeds unchanged in the
signed INT8 target used by PostgreSQL pagination. This does not assert that
evaluation succeeds or that the value is nonnegative. -/
theorem int32_row_count_widening (value : Int)
    (lower : -2147483648 ≤ value) (upper : value ≤ 2147483647) :
    -9223372036854775808 ≤ value ∧ value ≤ 9223372036854775807 := by
  omega

/-- Pagination expressions have no local row or output-alias bindings.
This is a static typing judgment. Expression evaluation may still fail, and
non-NULL runtime values must satisfy PaginationValueAllowed. In PostgreSQL,
NULL LIMIT means no bound, and NULL OFFSET means zero. -/
inductive PaginationValid (profile : Profile) (params : ParameterEnv) :
    Option Advanced.Expr → List Parameter → Prop where
  | absent : PaginationValid profile params none []
  | present (typed : ExprValid params .empty expr type uses)
      (collation : ExprCollationValid profile params .empty expr type derivation)
      (coercion : RowCountCoercion type) :
      PaginationValid profile params (some expr) uses

/-- A separate execution obligation on an evaluated row count. A static
certificate does not prove this predicate or successful expression evaluation. -/
def PaginationValueAllowed (value : Option Int) : Prop :=
  ∀ count ∈ value, 0 ≤ count

/-- A pagination-only judgment is useful even when other query clauses lack
independent rules. It records occurrences separately for LIMIT and OFFSET.
The two occurrence lists belong to their named bounds; their execution/source
ordering is not asserted here. It makes no assertion about the body, catalog,
output schema, or query-wide parameter notation, which requires occurrences
from every clause and the pagination-layout flag. -/
inductive PaginationBoundsValid (profile : Profile) (params : ParameterEnv)
    (query : Advanced.Query) : List Parameter → List Parameter → Prop where
  | bounds (environment : ParametersWellFormed params)
      (collations : profile.collations.WellFormed)
      (limit : PaginationValid profile params query.limit limitUses)
      (offset : PaginationValid profile params query.offset offsetUses) :
      PaginationBoundsValid profile params query limitUses offsetUses

structure PaginationBoundsCertificate (profile : Profile) (params : ParameterEnv)
    (query : Advanced.Query) where
  limitUses : List Parameter
  offsetUses : List Parameter
  valid : PaginationBoundsValid profile params query limitUses offsetUses

/-- The remaining value condition, to be checked after successful evaluation
and widening. The certificate supplies no proof of this execution obligation. -/
def PaginationBoundsCertificate.runtimeObligation
    (_certificate : PaginationBoundsCertificate profile params query)
    (limitValue offsetValue : Option Int) : Prop :=
  PaginationValueAllowed limitValue ∧ PaginationValueAllowed offsetValue

/-- PostgreSQL OF resolves the first matching visible relation in range-table
order. This deliberately differs from unique namespace resolution for columns. -/
def LockTarget (scope : Scope) (target : Name) : Prop :=
  target ≠ "" ∧ ∃ relation ∈ scope.relations.find? (fun relation => relation.name == target),
    relation.origin.isBase = true ∧ relation.nullable = false

instance (scope : Scope) (target : Name) : Decidable (LockTarget scope target) := by
  unfold LockTarget
  infer_instance

def LockTargets (scope : Scope) (targets : List Name) : Prop :=
  if targets = [] then ∀ relation ∈ scope.relations,
    relation.origin = .cte ∨ (relation.origin.isBase = true ∧ relation.nullable = false)
  else ∀ target ∈ targets, LockTarget scope target

instance (scope : Scope) (targets : List Name) : Decidable (LockTargets scope targets) := by
  unfold LockTargets
  infer_instance

/-- This judgment checks target identity and null extension, not privileges,
lock acquisition, waits, or propagation into a selected derived relation. -/
inductive LockingValid (scope : Scope) (distinct : Bool) :
    List Advanced.LockingClause → Prop where
  | nil : LockingValid scope distinct []
  | cons (ordinary : distinct = false)
      (targets : LockTargets scope clause.targets)
      (tail : LockingValid scope distinct clauses) :
      LockingValid scope distinct (clause :: clauses)

def CTENamesValid (ctes : List Advanced.CTE) : Prop :=
  (ctes.map Advanced.CTE.name).Nodup ∧ ∀ cte ∈ ctes, cte.name ≠ ""

instance (ctes : List Advanced.CTE) : Decidable (CTENamesValid ctes) := by
  unfold CTENamesValid
  infer_instance

/-- The body of a WITH query retains all non-WITH clauses and their lexical
parameter order. -/
def withoutWith (query : Advanced.Query) : Advanced.Query :=
  {query with ctes := [], recursive := false}

mutual
  /-- Every ON predicate sees exactly its two child scopes, before this join's
  own NULL extension. Parameters are visited left source, right source, then ON.
  USING/NATURAL preserve separate qualified and exposed scopes. Non-LATERAL
  derived sources expose a certified child row without fabricating catalog metadata. -/
  inductive SourceValid (profile : Profile) (catalog : Catalog) (params : ParameterEnv) :
      CTEEnv → Option Advanced.From → Scope → List Parameter → Prop where
    | empty : SourceValid profile catalog params env none .empty []
    | table (unshadowed : schema.isSome = true ∨ env.lookup name = none)
        (present : table ∈ catalog) (resolved : table.matchesReference name schema = true)
        (aliasValid : ∀ aliasName ∈ alias, aliasName ≠ "")
        (columns : TableColumns table table.columns bindings) :
        SourceValid profile catalog params env (some (.table name alias [] schema)) (Scope.ofTable table.identity alias bindings) []
    | tableRenamed (unshadowed : schema.isSome = true ∨ env.lookup name = none)
        (present : table ∈ catalog) (resolved : table.matchesReference name schema = true)
        (aliasValid : alias ≠ "")
        (columns : TableColumns table table.columns bindings)
        (aliasesValid : ColumnAliasesValid aliases bindings) :
        SourceValid profile catalog params env (some (.table name (some alias) aliases schema))
          (Scope.ofTable table.identity (some alias) (renameOutput aliases bindings)) []
    | cte (resolved : env.lookup name = some binding)
        (aliasValid : ∀ aliasName ∈ alias, aliasName ≠ "")
        (columnsValid : ColumnAliasesValid columns binding.output)
        (aliasRequired : columns = [] ∨ alias.isSome = true) :
        SourceValid profile catalog params env (some (.table name alias columns none))
          (Scope.ofCTE name alias (renameOutput columns binding.output)) []
    | cross (leftValid : SourceValid profile catalog params env (some left) leftScope leftUses)
        (rightValid : SourceValid profile catalog params env (some right) rightScope rightUses)
        (aliases : JoinAliasesDistinct leftScope rightScope) :
        SourceValid profile catalog params env (some (.join .cross left right .none))
          (leftScope ++ rightScope) (leftUses ++ rightUses)
    | on (leftValid : SourceValid profile catalog params env (some left) leftScope leftUses)
        (rightValid : SourceValid profile catalog params env (some right) rightScope rightUses)
        (aliases : JoinAliasesDistinct leftScope rightScope)
        (kindValid : kind ≠ .cross)
        (condition : PredicateValid profile params (leftScope ++ rightScope) (some expr) onUses) :
        SourceValid profile catalog params env (some (.join kind left right (.on expr)))
          (joinScope kind leftScope rightScope) (leftUses ++ rightUses ++ onUses)
    | using (leftValid : SourceValid profile catalog params env (some left) leftScope leftUses)
        (rightValid : SourceValid profile catalog params env (some right) rightScope rightUses)
        (aliases : JoinAliasesDistinct leftScope rightScope)
        (kindValid : kind ≠ .cross) (nonempty : keys ≠ []) (unique : keys.Nodup)
        (keysValid : JoinKeysValid kind leftScope.output rightScope.output keys merged) :
        SourceValid profile catalog params env (some (.join kind left right (.using keys)))
          (mergedJoinScope kind leftScope rightScope keys merged) (leftUses ++ rightUses)
    | natural (leftValid : SourceValid profile catalog params env (some left) leftScope leftUses)
        (rightValid : SourceValid profile catalog params env (some right) rightScope rightUses)
        (aliases : JoinAliasesDistinct leftScope rightScope)
        (kindValid : kind ≠ .cross)
        (unique : (naturalJoinKeys leftScope.output rightScope.output).Nodup)
        (keysValid : JoinKeysValid kind leftScope.output rightScope.output
          (naturalJoinKeys leftScope.output rightScope.output) merged) :
        SourceValid profile catalog params env (some (.join kind left right .natural))
          (mergedJoinScope kind leftScope rightScope
            (naturalJoinKeys leftScope.output rightScope.output) merged) (leftUses ++ rightUses)
    | derived (queryValid : QueryValid profile catalog params env query output uses)
        (aliasValid : alias ≠ "") (columnsValid : ColumnAliasesValid columns output)
        (nonLateral : lateral = false) :
        SourceValid profile catalog params env (some (.derived query alias columns lateral))
          (Scope.ofOutput alias (renameOutput columns output)) uses

  /-- Internal query derivations collect complete lexical occurrences. Nested
  queries do not restart anonymous ordinals or assert global notation validity. -/
  inductive QueryValid (profile : Profile) (catalog : Catalog) (params : ParameterEnv) :
      CTEEnv → Advanced.Query → List OutputColumn → List Parameter → Prop where
    | basic {select : Advanced.Select}
        (names : CTENamesValid ctes)
        (definitions : CTEsValid profile catalog params env ctes visible cteUses)
        (source : SourceValid profile catalog params visible select.source scope sourceUses)
        (items : ItemsValid profile params scope select.items output selectUses)
        (inputs : ItemsInputValid profile params scope select.items pending selectUses)
        (nonempty : output ≠ [])
        (distinctComparable : DistinctAllowed select.distinct output)
        (distinctCollations : DistinctCollations select.distinct pending)
        (predicate : PredicateValid profile params scope select.whereClause whereUses)
        (orders : OrdersValid profile params scope select.items output select.distinct orderBy orderUses)
        (orderCollations : OrdersCollationValid profile params scope pending orderBy)
        (limitValid : PaginationValid profile params limit limitUses)
        (offsetValid : PaginationValid profile params offset offsetUses)
        (lockingValid : LockingValid scope select.distinct locking)
        (noGrouping : select.groupBy = []) (noHaving : select.having = none)
        (noDistinctOn : select.distinctOn = []) :
        QueryValid profile catalog params env
          ⟨.select select, ctes, false, orderBy, limit, offset, locking, offsetFirst⟩ output
          (cteUses ++ if offsetFirst then selectUses ++ sourceUses ++ whereUses ++ orderUses ++ offsetUses ++ limitUses
           else selectUses ++ sourceUses ++ whereUses ++ orderUses ++ limitUses ++ offsetUses)
    | set (names : CTENamesValid ctes)
        (definitions : CTEsValid profile catalog params env ctes visible cteUses)
        (leftValid : SetOperandValid profile catalog params visible left leftInputs leftUses)
        (rightValid : SetOperandValid profile catalog params visible right rightInputs rightUses)
        (leftUnlocked : left.locking = []) (rightUnlocked : right.locking = [])
        (columns : SetColumnsValid op all leftInputs rightInputs output)
        (nonempty : output ≠ [])
        (orders : SetOrdersValid output orderBy)
        (limitValid : PaginationValid profile params limit limitUses)
        (offsetValid : PaginationValid profile params offset offsetUses) :
        QueryValid profile catalog params env
          ⟨.set op all left right, ctes, false, orderBy, limit, offset, [], offsetFirst⟩ output
          (cteUses ++ leftUses ++ rightUses ++
            if offsetFirst then offsetUses ++ limitUses else limitUses ++ offsetUses)

    | recursiveWith (nonemptyDefinitions : query.ctes ≠ [])
        (names : CTENamesValid query.ctes)
        (recursiveFlag : query.recursive = true)
        (definitions : RecursiveCTEsValid profile catalog params
          (recursiveOuterEnv env query.ctes) query.ctes visible cteUses)
        (body : QueryValid profile catalog params visible (withoutWith query) output bodyUses) :
        QueryValid profile catalog params env query output (cteUses ++ bodyUses)

  /-- Contextual set operands have their own projection judgment. The ordinary
  SELECT premises remain independent of checker success; only their pending
  output treatment differs. A nested set has already selected concrete types. -/
  inductive SetOperandValid (profile : Profile) (catalog : Catalog) (params : ParameterEnv) :
      CTEEnv → Advanced.Query → List PendingColumn → List Parameter → Prop where
    | basic {select : Advanced.Select}
        (names : CTENamesValid ctes)
        (definitions : CTEsValid profile catalog params env ctes visible cteUses)
        (source : SourceValid profile catalog params visible select.source scope sourceUses)
        (items : ItemsValid profile params scope select.items output selectUses)
        (inputs : ItemsInputValid profile params scope select.items pending selectUses)
        (nonempty : output ≠ [])
        (distinctComparable : DistinctAllowed select.distinct output)
        (distinctCollations : DistinctCollations select.distinct pending)
        (predicate : PredicateValid profile params scope select.whereClause whereUses)
        (orders : OrdersValid profile params scope select.items output select.distinct orderBy orderUses)
        (orderCollations : OrdersCollationValid profile params scope pending orderBy)
        (limitValid : PaginationValid profile params limit limitUses)
        (offsetValid : PaginationValid profile params offset offsetUses)
        (lockingValid : LockingValid scope select.distinct locking)
        (noGrouping : select.groupBy = []) (noHaving : select.having = none)
        (noDistinctOn : select.distinctOn = []) :
        SetOperandValid profile catalog params env
          ⟨.select select, ctes, false, orderBy, limit, offset, locking, offsetFirst⟩
          (resolveLeafInputs profile select.distinct orderBy pending)
          (cteUses ++ if offsetFirst then selectUses ++ sourceUses ++ whereUses ++ orderUses ++ offsetUses ++ limitUses
           else selectUses ++ sourceUses ++ whereUses ++ orderUses ++ limitUses ++ offsetUses)
    | set (complete : QueryValid profile catalog params env
        ⟨.set op all left right, ctes, recursive, orderBy, limit, offset, locking, offsetFirst⟩ output uses) :
        SetOperandValid profile catalog params env
          ⟨.set op all left right, ctes, recursive, orderBy, limit, offset, locking, offsetFirst⟩
          (knownColumns output) uses
    | recursiveWith (nonemptyDefinitions : query.ctes ≠ [])
        (names : CTENamesValid query.ctes)
        (recursiveFlag : query.recursive = true)
        (definitions : RecursiveCTEsValid profile catalog params
          (recursiveOuterEnv env query.ctes) query.ctes visible cteUses)
        (body : SetOperandValid profile catalog params visible (withoutWith query) output bodyUses) :
        SetOperandValid profile catalog params env query output (cteUses ++ bodyUses)

  /-- Definitions are analyzed in order. A name becomes visible only after its
  own query is certified, allowing inherited/base lookup in its defining body.
  References reuse output metadata and never duplicate definition occurrences. -/
  inductive CTEsValid (profile : Profile) (catalog : Catalog) (params : ParameterEnv) :
      CTEEnv → List Advanced.CTE → CTEEnv → List Parameter → Prop where
    | nil : CTEsValid profile catalog params env [] env []
    | cons (body : QueryValid profile catalog params env head.query output uses)
        (aliases : ColumnAliasesValid head.columns output)
        (tail : CTEsValid profile catalog params
          (⟨head.name, renameOutput head.columns output⟩ :: env) remaining visible restUses) :
        CTEsValid profile catalog params env (head :: remaining) visible (uses ++ restUses)

  /-- The recursive binding is established from the complete anchor row, while
  UNION coercion still sees the original pending anchor inputs. Equality of the
  final concrete bases includes every typmod; nullability is conservatively
  widened on the self binding and every externally exposed recursive column. -/
  inductive RecursiveCTEValid (profile : Profile) (catalog : Catalog) (params : ParameterEnv) :
      CTEEnv → Advanced.CTE → List OutputColumn → List Parameter → Prop where
    | union (names : CTENamesValid ctes)
        (notShadowed : ∀ cte ∈ ctes, cte.name ≠ name)
        (prefixFree : (recursiveCTEReferences name false false ctes).count = 0)
        (definitions : CTEsValid profile catalog params env ctes visible prefixUses)
        (anchorFree : (recursiveReferences name false false left).count = 0)
        (stepReference : recursiveReferences name false true right = ⟨1, true⟩)
        (anchor : QueryValid profile catalog params visible left anchorOutput leftUses)
        (anchorInputs : SetOperandValid profile catalog params visible left leftInputs leftUses)
        (aliases : ColumnAliasesValid columns anchorOutput)
        (step : SetOperandValid profile catalog params
          (⟨name, recursiveOutput (renameOutput columns anchorOutput)⟩ :: visible) right rightInputs rightUses)
        (leftUnlocked : left.locking = []) (rightUnlocked : right.locking = [])
        (merged : SetColumnsValid .union all leftInputs rightInputs mergedOutput)
        (sameTypes : mergedOutput.map (fun column => column.type.base) = anchorOutput.map (fun column => column.type.base))
        (collation : mergedOutput.map OutputColumn.collation = anchorOutput.map OutputColumn.collation) :
        RecursiveCTEValid profile catalog params env
          ⟨name, ⟨.set .union all left right, ctes, false, [], none, none, [], offsetFirst⟩, columns⟩
          (recursiveOutput (renameOutput columns anchorOutput)) (prefixUses ++ leftUses ++ rightUses)

  /-- This increment accepts dependency order already present in the source.
  A forward or mutual dependency is explicit missing coverage, never a lookup
  against an inherited binding or physical table of the same name. -/
  inductive RecursiveCTEsValid (profile : Profile) (catalog : Catalog) (params : ParameterEnv) :
      CTEEnv → List Advanced.CTE → CTEEnv → List Parameter → Prop where
    | nil : RecursiveCTEsValid profile catalog params env [] env []
    | ordinary (forwardFree : NoForwardCTEReferences remaining head.query)
        (noSelf : (recursiveReferences head.name false true head.query).count = 0)
        (body : QueryValid profile catalog params env head.query output uses)
        (aliases : ColumnAliasesValid head.columns output)
        (tail : RecursiveCTEsValid profile catalog params
          (⟨head.name, renameOutput head.columns output⟩ :: env) remaining visible restUses) :
        RecursiveCTEsValid profile catalog params env (head :: remaining) visible (uses ++ restUses)
    | recursive (forwardFree : NoForwardCTEReferences remaining head.query)
        (body : RecursiveCTEValid profile catalog params env head output uses)
        (tail : RecursiveCTEsValid profile catalog params
          (⟨head.name, output⟩ :: env) remaining visible restUses) :
        RecursiveCTEsValid profile catalog params env (head :: remaining) visible (uses ++ restUses)
end

/-- The public judgment checks exact metadata and parameter notation once,
over the complete statement's occurrence list including all derived sources. -/
inductive SelectValid (profile : Profile) (catalog : Catalog) (params : ParameterEnv) :
    Advanced.Query → List OutputColumn → Prop where
  | certified (environment : WellFormedEnvironment catalog params)
      (collations : CollationEnvironment profile catalog)
      (supported : SupportedEnvironment catalog params)
      (query : QueryValid profile catalog params [] ast output uses)
      (parameterOrder : ParameterOrder uses) :
      SelectValid profile catalog params ast output

structure Certificate (profile : Profile) (catalog : Catalog) (params : ParameterEnv) (query : Advanced.Query) where
  output : List OutputColumn
  valid : SelectValid profile catalog params query output

def Certificate.outputCatalog (_certificate : Certificate profile catalog params query) : Catalog := catalog

@[simp] theorem Certificate.catalog_unchanged (certificate : Certificate profile catalog params query) :
    certificate.outputCatalog = catalog := rfl

end SQLean.SelectContract
