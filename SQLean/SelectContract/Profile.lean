import SQLean.CatalogSyntax

/-! The closed, normative scalar profile for the first independent SELECT
contract. These tables describe the language; they do not inspect or validate
expressions. INT32, TEXT and BOOL are concrete types, not numeric families. -/
namespace SQLean.SelectContract

inductive Profile where
  | basicV01
  deriving Repr, BEq, DecidableEq, Inhabited

def Profile.name : Profile → String
  | .basicV01 => "sqlean-basic-select-v0.1"

inductive ScalarType where
  | int32 | text | bool
  deriving Repr, BEq, DecidableEq, Inhabited

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

abbrev Scope := List Binding

/-- Exact concrete type translation. BIGINT, NUMERIC and VARCHAR are not INT32,
FLOAT or TEXT aliases in this profile. -/
def concreteType : Advanced.DataType → Option ScalarType
  | ⟨.int, []⟩ => some .int32
  | ⟨.text, []⟩ => some .text
  | ⟨.bool, []⟩ => some .bool
  | _ => none

def ExprType.nullable : ExprType → Bool
  | none => true
  | some type => type.nullable

/-- Untyped projected NULL defaults to nullable TEXT. -/
def projectedType : ExprType → ExactType
  | none => ⟨.text, true⟩
  | some type => type

/-- There are no implicit conversions between the three concrete base types.
An unknown NULL may acquire the other operand's type; two unknown comparisons
use TEXT. -/
def commonBase : ExprType → ExprType → Option ScalarType
  | none, none => some .text
  | none, some t | some t, none => some t.base
  | some a, some b => if a.base = b.base then some a.base else none

def acceptsBase (base : ScalarType) : ExprType → Bool
  | none => true
  | some type => type.base == base

/-- Normative operator signatures, including conservative SQL nullability. -/
def binarySignature (op : BinOp) (a b : ExprType) : Option ExprType :=
  let nullable := a.nullable || b.nullable
  match op with
  | .and | .or =>
      if acceptsBase .bool a && acceptsBase .bool b then some (some ⟨.bool, nullable⟩) else none
  | .add | .sub | .mul | .div =>
      if commonBase a b = some .int32 then some (some ⟨.int32, nullable⟩) else none
  | .eq | .ne | .lt | .le | .gt | .ge =>
      match commonBase a b with
      | some _ => some (some ⟨.bool, nullable⟩)
      | none => none

def unarySignature (op : UnOp) (arg : ExprType) : Option ExprType :=
  match op with
  | .not => if acceptsBase .bool arg then some (some ⟨.bool, arg.nullable⟩) else none
  | .pos | .neg => match arg with
    | some ⟨.int32, nullable⟩ => some (some ⟨.int32, nullable⟩)
    | _ => none

/-- Every explicit conversion among INT32/TEXT/BOOL is part of this profile.
Value-dependent conversion failures remain execution obligations. -/
def castSignature (arg : ExprType) (target : ScalarType) : ExprType :=
  some ⟨target, arg.nullable⟩

def patternSignature (a b : ExprType) : Option ExprType :=
  if acceptsBase .text a && acceptsBase .text b then
    some (some ⟨.bool, a.nullable || b.nullable⟩)
  else none

/-- Common type for a finite IN/BETWEEN signature. Unknowns acquire the unique
concrete operand type; an all-NULL list defaults to TEXT. -/
def commonListBase (types : List ExprType) : Option ScalarType :=
  let concrete := types.filterMap (fun type => type.map ExactType.base)
  match concrete with
  | [] => some .text
  | first :: rest => if rest.all (· == first) then some first else none

def comparisonListSignature (types : List ExprType) : Option ExprType :=
  match commonListBase types with
  | none => none
  | some _ => some (some ⟨.bool, types.any ExprType.nullable⟩)

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
