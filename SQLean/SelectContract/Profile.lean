import SQLean.CatalogSyntax

/-! The closed, normative PostgreSQL 16 scalar profile for the independent SELECT
contract. These tables describe the language; they do not run an expression
checker. Concrete types and declaration modifiers are retained.

Reference tables: PostgreSQL REL_16_STABLE src/include/catalog/pg_cast.dat and
pg_operator.dat; explicit string conversion follows find_coercion_pathway in
src/backend/parser/parse_coerce.c. This finite signature inventory is not a
formalization of PostgreSQL's general overload-resolution algorithm. -/
namespace SQLean.SelectContract

inductive Profile where
  | basicV22
  deriving Repr, BEq, DecidableEq, Inhabited

def Profile.name : Profile → String
  | .basicV22 => "sqlean-basic-select-v0.22"

/-- Concrete PostgreSQL built-ins. Modifiers are retained on declarations and
casts; operator-result types deliberately discard modifiers. Bare CHAR denotes
CHAR(1). The exact source spelling remains in the indexed catalog/query. -/
inductive ScalarType where
  | smallInt | int32 | int64 | text | bool | real | doublePrecision
  | numeric (modifiers : List Nat := [])
  | varchar (modifiers : List Nat := [])
  | char (modifiers : List Nat := [])
  | date
  | time (modifiers : List Nat := [])
  | timeTZ (modifiers : List Nat := [])
  | timestamp (modifiers : List Nat := [])
  | timestampTZ (modifiers : List Nat := [])
  | interval (modifiers : List Nat := [])
  /-- Explicit interval field masks are exact typmods, not distinct base OIDs. -/
  | intervalRange (fields : Advanced.IntervalFields) (modifiers : List Nat := [])
  | uuid | json | jsonb | bytea
  | array (element : ScalarType)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Array rank is syntax/value information, not a PostgreSQL type identity.
Certified array types contain precisely one wrapper around a scalar leaf. -/
def ScalarType.arrayElement : ScalarType → ScalarType
  | .array element => element.arrayElement
  | type => type

def ScalarType.asArray (type : ScalarType) : ScalarType := .array type.arrayElement

def ScalarType.isArray : ScalarType → Bool
  | .array _ => true
  | _ => false

@[simp] theorem ScalarType.arrayElement_not_array (type : ScalarType) :
    type.arrayElement.isArray = false := by
  induction type <;> simp_all [arrayElement, isArray]

@[simp] theorem ScalarType.arrayElement_idempotent (type : ScalarType) :
    type.arrayElement.arrayElement = type.arrayElement := by
  induction type <;> simp_all [arrayElement]

@[simp] theorem ScalarType.asArray_idempotent (type : ScalarType) :
    type.asArray.asArray = type.asArray := by
  simp [asArray, arrayElement]

/-- Declaration-shaped view, not a universal inverse of `concreteType`.
In particular, an unmodified `.char []` result is PostgreSQL `bpchar`, whereas
the declaration `CHAR` implies length one. Result reports distinguish these. -/
def ScalarType.dataType : ScalarType → Advanced.DataType
  | .smallInt => ⟨.smallInt, []⟩ | .int32 => ⟨.int, []⟩ | .int64 => ⟨.bigInt, []⟩
  | .text => ⟨.text, []⟩ | .bool => ⟨.bool, []⟩ | .real => ⟨.real, []⟩
  | .doublePrecision => ⟨.doublePrecision, []⟩
  | .numeric m => ⟨.numeric, m⟩ | .varchar m => ⟨.varchar, m⟩ | .char m => ⟨.char, m⟩
  | .date => ⟨.date, []⟩ | .time m => ⟨.time, m⟩ | .timeTZ m => ⟨.timeTZ, m⟩
  | .timestamp m => ⟨.timestamp, m⟩ | .timestampTZ m => ⟨.timestampTZ, m⟩
  | .interval m => ⟨.interval, m⟩
  | .intervalRange fields m => ⟨.intervalRange fields, m⟩
  | .uuid => ⟨.uuid, []⟩ | .json => ⟨.json, []⟩ | .jsonb => ⟨.jsonb, []⟩ | .bytea => ⟨.bytea, []⟩
  | .array element => let type := element.dataType; ⟨.array type.name, type.modifiers⟩

def ScalarType.unmodified : ScalarType → ScalarType
  | .numeric _ => .numeric [] | .varchar _ => .varchar [] | .char _ => .char []
  | .time _ => .time [] | .timeTZ _ => .timeTZ []
  | .timestamp _ => .timestamp [] | .timestampTZ _ => .timestampTZ []
  | .interval _ | .intervalRange .. => .interval []
  | .array element => element.unmodified.asArray
  | type => type

def ScalarType.numericRank : ScalarType → Option Nat
  | .smallInt => some 0 | .int32 => some 1 | .int64 => some 2
  | .numeric _ => some 3 | .real => some 4 | .doublePrecision => some 5 | _ => none

def ScalarType.isString : ScalarType → Bool
  | .text | .varchar _ | .char _ => true | _ => false

def ScalarType.orderable : ScalarType → Bool
  | .json => false
  | .array element => element.orderable
  | _ => true

/-- PostgreSQL resolves polymorphic array operators before checking element
operator availability. This profile does not certify that later runtime gap. -/
def ScalarType.arrayOperatorGap (type : ScalarType) : Bool :=
  type.isArray && !type.orderable

structure ExactType where
  base : ScalarType
  nullable : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/-- An unknown literal NULL has no concrete type until a contextual rule applies. -/
abbrev ExprType := Option ExactType

structure ParameterBinding where
  index : Nat
  type : Advanced.DataType
  nullable : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

abbrev ParameterEnv := List ParameterBinding

structure OutputColumn where
  name : Name
  type : ExactType
  deriving Repr, BEq, DecidableEq, Inhabited

structure Binding where
  qualifier : Name
  column : OutputColumn
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Qualified relation columns retain their original order and types separately
from the exposed row. USING/NATURAL may merge the latter without hiding the
former from qualified references or qualified wildcards. -/
structure Scope where
  qualified : List Binding := []
  output : List OutputColumn := []
  deriving Repr, BEq, DecidableEq, Inhabited

def Scope.empty : Scope := ⟨[], []⟩

def Scope.ofBindings (bindings : List Binding) : Scope :=
  ⟨bindings, bindings.map Binding.column⟩

def Scope.ofOutput (qualifier : Name) (output : List OutputColumn) : Scope :=
  ⟨output.map (fun column => ⟨qualifier, column⟩), output⟩

def Scope.append (left right : Scope) : Scope :=
  ⟨left.qualified ++ right.qualified, left.output ++ right.output⟩

instance : Append Scope := ⟨Scope.append⟩

def Scope.columns (scope : Scope) : Option Name → List OutputColumn
  | none => scope.output
  | some qualifier =>
      (scope.qualified.filter (fun binding => binding.qualifier == qualifier)).map Binding.column

/-- Concrete conversion preserves declaration modifiers. Well-formedness is a
separate prerequisite, not a family-level erasure through DataType.sqlType. -/
def concreteTypeName : Advanced.TypeName → List Nat → Option ScalarType
  | .array element, modifiers => (concreteTypeName element modifiers).map ScalarType.asArray
  | .smallInt, [] => some .smallInt
  | .int, [] => some .int32 | .bigInt, [] => some .int64
  | .text, [] => some .text | .bool, [] => some .bool
  | .real, [] => some .real | .doublePrecision, [] => some .doublePrecision
  | .numeric, m => some (.numeric m) | .varchar, m => some (.varchar m)
  | .char, [] => some (.char [1]) | .char, m => some (.char m)
  | .date, [] => some .date | .time, m => some (.time m)
  | .timeTZ, m => some (.timeTZ m) | .timestamp, m => some (.timestamp m)
  | .timestampTZ, m => some (.timestampTZ m) | .interval, m => some (.interval m)
  | .intervalRange fields, m => some (.intervalRange fields m)
  | .uuid, [] => some .uuid | .json, [] => some .json
  | .jsonb, [] => some .jsonb | .bytea, [] => some .bytea
  | _, _ => none

def concreteType (type : Advanced.DataType) : Option ScalarType :=
  concreteTypeName type.name type.modifiers

/-- Repeated declared dimensions do not create a different concrete type. -/
theorem concreteType_array_rank (element : Advanced.TypeName) (modifiers : List Nat) :
    concreteType ⟨.array (.array element), modifiers⟩ =
      concreteType ⟨.array element, modifiers⟩ := by
  simp only [concreteType, concreteTypeName]
  cases concreteTypeName element modifiers <;> simp

def ExprType.nullable : ExprType → Bool
  | none => true | some type => type.nullable

def ExprType.orderable : ExprType → Bool
  | none => true | some type => type.base.orderable

/-- Untyped projected NULL defaults to nullable TEXT. -/
def projectedType : ExprType → ExactType
  | none => ⟨.text, true⟩ | some type => type

/-- Numeric overload results from PostgreSQL 16 pg_operator.dat. Mixed REAL
with an integer or NUMERIC chooses FLOAT8 through overload preference, whereas
REAL/REAL has an exact FLOAT4 overload. Every arithmetic result loses typmods. -/
def numericResult (a b : ScalarType) : Option ScalarType := do
  let ra ← a.numericRank
  let rb ← b.numericRank
  if a.unmodified = b.unmodified then return a.unmodified
  if ra ≥ 4 || rb ≥ 4 then return .doublePrecision
  if ra = 3 || rb = 3 then return .numeric []
  if ra = 2 || rb = 2 then return .int64
  if ra = 1 || rb = 1 then return .int32
  return .smallInt

/-- Comparison compatibility is distinct from explicit casts. In particular,
TEXT and DATE are not interchangeable, and JSON has no equality/ordering. -/
def comparisonBase (a b : ScalarType) : Option ScalarType :=
  if !a.orderable || !b.orderable then none
  else if a.unmodified = b.unmodified then some a.unmodified
  else if a.isString && b.isString then some .text
  else match numericResult a b with
    | some type => some type
    | none => match a.unmodified, b.unmodified with
      | .date, .timestamp _ | .timestamp _, .date => some (.timestamp [])
      | .date, .timestampTZ _ | .timestampTZ _, .date
      | .timestamp _, .timestampTZ _ | .timestampTZ _, .timestamp _ => some (.timestampTZ [])
      | .time _, .timeTZ _ | .timeTZ _, .time _ => some (.timeTZ [])
      | .time _, .interval _ | .interval _, .time _ => some (.interval [])
      | _, _ => none

def commonBase : ExprType → ExprType → Option ScalarType
  | none, none => some .text
  | none, some t | some t, none => if t.base.orderable then some t.base.unmodified else none
  | some a, some b => comparisonBase a.base b.base

def acceptsBase (base : ScalarType) : ExprType → Bool
  | none => true | some type => type.base == base

/-- Selected exact temporal arithmetic overloads. No arbitrary transitive cast
path is used to invent additional signatures. -/
def temporalResult (op : BinOp) (a b : ScalarType) : Option ScalarType :=
  match op, a.unmodified, b.unmodified with
  | .add, .date, .int32 | .add, .int32, .date | .sub, .date, .int32
  | .add, .date, .smallInt | .add, .smallInt, .date | .sub, .date, .smallInt => some .date
  | .sub, .date, .date => some .int32
  | .add, .date, .interval _ | .sub, .date, .interval _ | .add, .interval _, .date => some (.timestamp [])
  | .add, .date, .time _ | .add, .time _, .date => some (.timestamp [])
  | .add, .date, .timeTZ _ | .add, .timeTZ _, .date => some (.timestampTZ [])
  | .add, .timestamp _, .interval _ | .sub, .timestamp _, .interval _
  | .add, .interval _, .timestamp _ => some (.timestamp [])
  | .add, .timestampTZ _, .interval _ | .sub, .timestampTZ _, .interval _
  | .add, .interval _, .timestampTZ _ => some (.timestampTZ [])
  | .sub, .timestamp _, .timestamp _ | .sub, .timestampTZ _, .timestampTZ _
  | .sub, .time _, .time _ => some (.interval [])
  | .add, .interval _, .interval _ | .sub, .interval _, .interval _ => some (.interval [])
  | .add, .time _, .interval _ | .sub, .time _, .interval _ | .add, .interval _, .time _ => some (.time [])
  | .add, .timeTZ _, .interval _ | .sub, .timeTZ _, .interval _ | .add, .interval _, .timeTZ _ => some (.timeTZ [])
  | .mul, .interval _, .doublePrecision | .div, .interval _, .doublePrecision
  | .mul, .doublePrecision, .interval _ => some (.interval [])
  | _, _, _ => none

def arithmeticBase (op : BinOp) : ExprType → ExprType → Option ScalarType
  | none, none => none
  | none, some t | some t, none => numericResult t.base t.base
  | some a, some b => match numericResult a.base b.base with
    | some result => some result
    | none => temporalResult op a.base b.base

/-- Normative signatures, including conservative SQL nullability. -/
def binarySignature (op : BinOp) (a b : ExprType) : Option ExprType :=
  let nullable := a.nullable || b.nullable
  match op with
  | .and | .or =>
      if acceptsBase .bool a && acceptsBase .bool b then some (some ⟨.bool, nullable⟩) else none
  | .add | .sub | .mul | .div =>
      (arithmeticBase op a b).map (fun base => some ⟨base, nullable⟩)
  | .eq | .ne | .lt | .le | .gt | .ge =>
      (commonBase a b).map (fun _ => some ⟨.bool, nullable⟩)

def unarySignature (op : UnOp) (arg : ExprType) : Option ExprType :=
  match op with
  | .not => if acceptsBase .bool arg then some (some ⟨.bool, arg.nullable⟩) else none
  | .pos | .neg => match arg with
    | some type => if type.base.numericRank.isSome then
        some (some ⟨type.base.unmodified, type.nullable⟩)
      else if op == .neg && type.base.unmodified == .interval [] then
        some (some ⟨.interval [], type.nullable⟩)
      else none
    | none => if op == .pos then some (some ⟨.doublePrecision, true⟩) else none

/-- PostgreSQL folds these signed boundary constants before operator resolution.
Generic unary derivations exclude them so their result cannot be widened twice. -/
def OrdinaryUnary : UnOp → Advanced.Expr → Prop
  | .neg, .literal (.int n) => n ≠ 2147483648 ∧ n ≠ 9223372036854775808
  | _, _ => True

instance (op : UnOp) (arg : Advanced.Expr) : Decidable (OrdinaryUnary op arg) := by
  unfold OrdinaryUnary
  split <;> infer_instance

/-- Explicit casts from pg_cast.dat, plus PostgreSQL's documented CoerceViaIO
rule for string-category sources or targets. This is not a common-type rule. -/
def explicitCastAllowed (source target : ScalarType) : Bool :=
  match source, target with
  | .array sourceElement, .array targetElement => explicitCastAllowed sourceElement targetElement
  | _, _ =>
    source.unmodified == target.unmodified ||
    (source.numericRank.isSome && target.numericRank.isSome) ||
    source.isString || target.isString ||
    match source.unmodified, target.unmodified with
    | .int32, .bool | .bool, .int32 => true
    | .date, .timestamp _ | .date, .timestampTZ _
    | .time _, .interval _ | .time _, .timeTZ _
    | .timestamp _, .date | .timestamp _, .time _ | .timestamp _, .timestampTZ _
    | .timestampTZ _, .date | .timestampTZ _, .time _ | .timestampTZ _, .timestamp _ | .timestampTZ _, .timeTZ _
    | .interval _, .time _ | .timeTZ _, .time _
    | .json, .jsonb | .jsonb, .json
    | .jsonb, .bool | .jsonb, .smallInt | .jsonb, .int32 | .jsonb, .int64
    | .jsonb, .numeric _ | .jsonb, .real | .jsonb, .doublePrecision => true
    | _, _ => false

def castAllowed (arg : ExprType) (target : ScalarType) : Bool :=
  match arg with | none => true | some type => explicitCastAllowed type.base target

/-- Scalar JSONB conversion keeps a conservative nullable result flag.
PostgreSQL 16 rejects JSON null in numeric/Boolean conversion at execution;
the flag does not promise successful conversion. Array casts propagate only
the outer array's nullability, independently of SQL NULL elements. -/
def castSignature (arg : ExprType) (target : ScalarType) : ExprType :=
  let jsonNull := match arg with
    | some type => type.base == .jsonb && (target == .bool || target.numericRank.isSome)
    | none => false
  some ⟨target, arg.nullable || jsonNull⟩

def patternSignature (a b : ExprType) : Option ExprType :=
  let accepts : ExprType → Bool := fun type => match type with | none => true | some t => t.base.isString
  if (accepts a && accepts b) || (acceptsBase .bytea a && acceptsBase .bytea b) then
    some (some ⟨.bool, a.nullable || b.nullable⟩) else none

/-- A conservative common comparison type, available separately from the
pairwise predicate signatures below. -/
def commonListBase (types : List ExprType) : Option ScalarType :=
  let concrete := types.filterMap (fun type => type.map ExactType.base)
  match concrete with
  | [] => some .text
  | first :: rest => rest.foldlM comparisonBase first

def comparisonListSignature (types : List ExprType) : Option ExprType :=
  match types with
  | [] => none
  | arg :: values =>
      if values.all (fun value => (commonBase arg value).isSome) then
        some (some ⟨.bool, types.any ExprType.nullable⟩)
      else none

/-- Decimal token grammar, independent of the lexer/checker. Numeric conversion
and arithmetic overflow remain execution obligations, as with explicit casts. -/
def decimalLexeme (text : String) : Bool := Id.run do
  let chars := text.toList
  let initial := chars.takeWhile Char.isDigit
  let mut rest := chars.dropWhile Char.isDigit
  let mut marker := false
  if rest.head? == some '.' then
    marker := true
    rest := rest.drop 1
    let fraction := rest.takeWhile Char.isDigit
    if initial.isEmpty && fraction.isEmpty then return false
    rest := rest.dropWhile Char.isDigit
  else if initial.isEmpty then return false
  if rest.head? == some 'e' || rest.head? == some 'E' then
    marker := true
    rest := rest.drop 1
    if rest.head? == some '+' || rest.head? == some '-' then rest := rest.drop 1
    if rest.isEmpty then return false
    rest := rest.dropWhile Char.isDigit
  return marker && rest.isEmpty

structure Diagnostic where
  code : String
  message : String
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Failure where
  | invalid (diagnostic : Diagnostic)
  | unsupported (diagnostic : Diagnostic)
  | inconclusive (diagnostic : Diagnostic)
  deriving Repr, BEq, DecidableEq, Inhabited

end SQLean.SelectContract
