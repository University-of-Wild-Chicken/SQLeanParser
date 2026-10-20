import SQLean.SelectContract.Profile

/-! Fixed PostgreSQL 16 scalar signatures and contextual common-type rules.
This module contains no recursive expression inference or executable checker.
The finite catalog is normative for this closed built-in profile; user-defined
functions and search-path overrides are outside its function environment.

References: PostgreSQL 16 pg_proc.dat, pg_cast.dat, pg_operator.dat and the
documented function and UNION/CASE type-resolution procedures.
-/
namespace SQLean.SelectContract
open Advanced

/-- String constants and NULL have unknown input type in a contextual call.
Their nullability differs. Declared TEXT columns/parameters remain concrete. -/
inductive ScalarInput where
  | unknown (nullable : Bool)
  | known (type : ExactType)
  deriving Repr, BEq, DecidableEq

def scalarInput (expr : Advanced.Expr) (type : ExprType) : ScalarInput :=
  match expr with
  | .literal (.text _) => .unknown false
  | _ => match type with | none => .unknown true | some type => .known type

def scalarInputs (exprs : List Advanced.Expr) (types : List ExprType) : List ScalarInput :=
  (exprs.zip types).map fun (expr, type) => scalarInput expr type

def ScalarInput.nullable : ScalarInput → Bool
  | .unknown nullable => nullable
  | .known type => type.nullable

def ScalarInput.base : ScalarInput → Option ScalarType
  | .unknown _ => none
  | .known type => some type.base

def typeCategory (type : ScalarType) : Nat :=
  if type.numericRank.isSome then 0
  else if type.isString then 1
  else match type with
  | .bool => 2
  | .date | .time _ | .timeTZ _ | .timestamp _ | .timestampTZ _ => 3
  | .interval _ => 4
  | .array _ => 6
  | _ => 5

def preferredType (type : ScalarType) : Bool :=
  match type.unmodified with
  | .doublePrecision | .text | .bool | .timestampTZ _ | .interval _ => true
  | _ => false

/-- Catalog implicit casts, distinct from assignment and explicit casts. -/
def implicitCast (source target : ScalarType) : Bool :=
  match source, target with
  | .array a, .array b => implicitCast a b
  | _, _ =>
    let a := source.unmodified
    let b := target.unmodified
    a == b ||
    (match a.numericRank, b.numericRank with
     | some i, some j => i ≤ j
     | _, _ => false) ||
    (a.isString && b.isString) ||
    (match a, b with
     | .date, .timestamp _ | .date, .timestampTZ _ | .timestamp _, .timestampTZ _
     | .time _, .timeTZ _ | .time _, .interval _ => true
     | _, _ => false)

def acceptsInput (input : ScalarInput) (target : ScalarType) : Bool :=
  match input with | .unknown _ => true | .known type => implicitCast type.base target

structure FunctionOverload where
  inputs : List ScalarType
  output : ScalarType
  deriving Repr, BEq, DecidableEq

private def keepBest (score : FunctionOverload → Nat) (candidates : List FunctionOverload) :
    List FunctionOverload :=
  let best := (candidates.map score).foldl max 0
  candidates.filter fun candidate => score candidate == best

private def exactScore (args : List ScalarInput) (candidate : FunctionOverload) : Nat :=
  ((args.zip candidate.inputs).filter fun (arg, expected) =>
    arg.base.any fun base => base.unmodified == expected.unmodified).length

private def preferredScore (args : List ScalarInput) (candidate : FunctionOverload) : Nat :=
  ((args.zip candidate.inputs).filter fun (arg, expected) =>
    arg.base.any fun base => base.unmodified == expected.unmodified ||
      (typeCategory base == typeCategory expected && preferredType expected)).length

private def unknownPosition (candidates : List FunctionOverload) (index : Nat) :
    List FunctionOverload :=
  let types := candidates.filterMap fun candidate => candidate.inputs[index]?
  let categories := types.map typeCategory
  let category := if categories.contains 1 then some 1 else
    categories.head?.filter fun first => categories.all (· == first)
  match category with
  | none => []
  | some category =>
    let matching := candidates.filter fun candidate =>
      (candidate.inputs[index]?).any fun type => typeCategory type == category
    if matching.any (fun candidate => (candidate.inputs[index]?).any preferredType) then
      matching.filter fun candidate => (candidate.inputs[index]?).any preferredType
    else matching

/-- Finite catalog overload resolution. No expression is recursively inspected.
Only admitted overloads can be returned; ambiguous matches return none. -/
def resolveOverload (catalog : List FunctionOverload) (args : List ScalarInput) :
    Option FunctionOverload :=
  let compatible := catalog.filter fun candidate =>
    candidate.inputs.length == args.length &&
      (args.zip candidate.inputs).all (fun (arg, expected) => acceptsInput arg expected)
  let exact := keepBest (exactScore args) compatible
  let preferred := keepBest (preferredScore args) exact
  let filtered := (args.zipIdx).foldl (fun candidates (arg, index) =>
    match arg with | .known _ => candidates | .unknown _ => unknownPosition candidates index) preferred
  match filtered with
  | [candidate] => some candidate
  | _ =>
    let known := args.filterMap ScalarInput.base
    match known.head? with
    | none => none
    | some first =>
      if !known.all (fun type => type.unmodified == first.unmodified) then none
      else match filtered.filter (fun candidate =>
        (args.zip candidate.inputs).all fun (arg, expected) =>
          match arg with | .known _ => true | .unknown _ => implicitCast first expected) with
      | [candidate] => some candidate
      | _ => none

private def unaryOverloads (inputs : List ScalarType) (output : Option ScalarType := none) :
    List FunctionOverload :=
  inputs.map fun input => ⟨[input], output.getD input⟩

def numericTypes : List ScalarType :=
  [.smallInt, .int32, .int64, .numeric [], .real, .doublePrecision]

/-- Auditable supported-name inventory, including the four variadic-any rules. -/
def functionNames : List Name :=
  ["abs", "sign", "ceil", "ceiling", "floor", "sqrt", "exp", "ln", "cbrt", "degrees", "radians",
   "round", "trunc", "log", "power", "div", "mod", "lower", "upper", "length", "char_length",
   "character_length", "octet_length", "btrim", "ltrim", "rtrim", "replace", "substr",
   "to_date", "to_timestamp", "now", "transaction_timestamp", "statement_timestamp",
   "clock_timestamp", "pi", "random", "json_typeof", "jsonb_typeof", "json_array_length",
   "jsonb_array_length", "concat", "concat_ws", "num_nulls", "num_nonnulls"]

/-- Explicit supported built-in inventory. Overloads for SQL arrays, ranges,
composite values and other absent scalar types are not implicitly admitted. -/
def functionCatalog (name : Name) : List FunctionOverload :=
  match name with
  | "abs" | "sign" =>
    if name == "abs" then unaryOverloads numericTypes
    else unaryOverloads [.numeric [], .doublePrecision]
  | "ceil" | "ceiling" | "floor" | "sqrt" | "exp" | "ln" =>
      unaryOverloads [.numeric [], .doublePrecision]
  | "cbrt" | "degrees" | "radians" => unaryOverloads [.doublePrecision]
  | "round" | "trunc" =>
      unaryOverloads [.numeric [], .doublePrecision] ++ [⟨[.numeric [], .int32], .numeric []⟩]
  | "log" => unaryOverloads [.numeric [], .doublePrecision] ++ [⟨[.numeric [], .numeric []], .numeric []⟩]
  | "power" => [⟨[.numeric [], .numeric []], .numeric []⟩,
      ⟨[.doublePrecision, .doublePrecision], .doublePrecision⟩]
  | "div" => [⟨[.numeric [], .numeric []], .numeric []⟩]
  | "mod" => [.smallInt, .int32, .int64, .numeric []].map fun type => ⟨[type, type], type⟩
  | "lower" | "upper" => [⟨[.text], .text⟩]
  | "length" => unaryOverloads [.text, .char [], .bytea] (some .int32)
  | "char_length" | "character_length" => unaryOverloads [.text, .char []] (some .int32)
  | "octet_length" => unaryOverloads [.text, .char [], .bytea] (some .int32)
  | "btrim" | "ltrim" | "rtrim" =>
      [⟨[.text], .text⟩, ⟨[.text, .text], .text⟩, ⟨[.bytea, .bytea], .bytea⟩]
  | "replace" => [⟨[.text, .text, .text], .text⟩]
  | "substr" => [⟨[.text, .int32], .text⟩, ⟨[.text, .int32, .int32], .text⟩,
      ⟨[.bytea, .int32], .bytea⟩, ⟨[.bytea, .int32, .int32], .bytea⟩]
  | "to_date" => [⟨[.text, .text], .date⟩]
  | "to_timestamp" => [⟨[.text, .text], .timestampTZ []⟩, ⟨[.doublePrecision], .timestampTZ []⟩]
  | "now" | "transaction_timestamp" | "statement_timestamp" | "clock_timestamp" =>
      [⟨[], .timestampTZ []⟩]
  | "pi" | "random" => [⟨[], .doublePrecision⟩]
  | "json_typeof" => [⟨[.json], .text⟩]
  | "jsonb_typeof" => [⟨[.jsonb], .text⟩]
  | "json_array_length" => [⟨[.json], .int32⟩]
  | "jsonb_array_length" => [⟨[.jsonb], .int32⟩]
  | _ => []

def builtinName : List Name → Option Name
  | [name] => some name
  | ["pg_catalog", name] => some name
  | _ => none

def knownFunction (name : List Name) : Bool :=
  (builtinName name).any functionNames.contains

def callSignature (name : List Name) (args : List ScalarInput) : Option ExactType := do
  let name ← builtinName name
  if name == "concat" then
    if args.isEmpty then none else some ⟨.text, false⟩
  else if name == "concat_ws" then
    match args with
    | separator :: _ :: _ =>
      if acceptsInput separator .text then some ⟨.text, separator.nullable⟩ else none
    | _ => none
  else if name == "num_nulls" || name == "num_nonnulls" then
    if args.isEmpty then none else some ⟨.int32, false⟩
  else
    let overload ← resolveOverload (functionCatalog name) args
    some ⟨overload.output, args.any ScalarInput.nullable⟩

/-- PostgreSQL common-type selection is directional and distinct from numeric
operator overload selection. For example INT32/REAL resolves to REAL here. -/
def conditionalBase (args : List ScalarInput) : Option ScalarType := do
  let known := args.filterMap ScalarInput.base
  let candidate ← match known with
    | [] => some .text
    | first :: rest =>
      if !rest.all (fun type => typeCategory type == typeCategory first) then none
      else some (rest.foldl (fun candidate next =>
        if !preferredType candidate && implicitCast candidate next && !implicitCast next candidate
        then next else candidate) first)
  if !args.all (fun arg => acceptsInput arg candidate) then none
  else if args.all (fun arg => arg.base == some candidate) then some candidate
  else some candidate.unmodified

/-- An inferred array constructor uses PostgreSQL common-type selection and
retains common element modifiers. NULL elements do not make the array NULL. -/
def arraySignature (args : List ScalarInput) : Option ExactType := do
  if args.isEmpty then none
  else some ⟨(← conditionalBase args).asArray, false⟩

/-- A direct cast supplies its full concrete array target to constructor
children. Once any child is array-valued, all children are explicitly coerced
to the array type; otherwise they are coerced to its scalar element type.
Shape compatibility and element-input conversion are runtime obligations. -/
def arrayCastSignature (target : ScalarType) (args : List ScalarInput) : Bool :=
  let multi := args.any (fun input => input.base.any ScalarType.isArray)
  let elementTarget := if multi then target else target.arrayElement
  target.isArray && args.all (fun input => match input with
    | .unknown _ => true
    | .known type => explicitCastAllowed type.base elementTarget)

def coalesceSignature (args : List ScalarInput) : Option ExactType := do
  if args.isEmpty then none
  else some ⟨← conditionalBase args, args.all ScalarInput.nullable⟩

def extremumSignature (args : List ScalarInput) : Option ExactType := do
  let result ← coalesceSignature args
  if result.base.orderable then some result else none

def equalityCatalog : List FunctionOverload :=
  let integers : List ScalarType := [.smallInt, .int32, .int64]
  let floating : List ScalarType := [.real, .doublePrecision]
  let dates : List ScalarType := [.date, .timestamp [], .timestampTZ []]
  (integers.flatMap fun a => integers.map fun b => ⟨[a, b], .bool⟩) ++
  (floating.flatMap fun a => floating.map fun b => ⟨[a, b], .bool⟩) ++
  (dates.flatMap fun a => dates.map fun b => ⟨[a, b], .bool⟩) ++
  ([.numeric [], .text, .char [], .bool, .time [], .timeTZ [], .interval [],
    .uuid, .jsonb, .bytea].map fun type => ⟨[type, type], .bool⟩)

/-- Binary operators first try an exact signature, assuming one unknown
operand has its known partner's type, before ordinary overload resolution. -/
def equalityOverload (left right : ScalarInput) : Option FunctionOverload :=
  let arrayType := match left.base, right.base with
    | some (.array a), some (.array b) =>
        if a.unmodified == b.unmodified && a.orderable && b.orderable then some a.unmodified.asArray else none
    | some (.array a), none | none, some (.array a) =>
        if a.orderable then some a.unmodified.asArray else none
    | _, _ => none
  if left.base.any ScalarType.isArray || right.base.any ScalarType.isArray then
    arrayType.map fun type => ⟨[type, type], .bool⟩
  else
    let assumed := match left.base, right.base with
      | none, some type | some type, none => some type.unmodified
      | _, _ => none
    match assumed with
    | some type =>
      match equalityCatalog.find? (fun signature => signature.inputs == [type, type]) with
      | some signature => some signature
      | none => resolveOverload equalityCatalog [left, right]
    | none => resolveOverload equalityCatalog [left, right]

/-- PostgreSQL 16 provides all six strict Boolean comparison operators for
these 32 scalar input pairs. The selected arguments are retained explicitly;
common-type selection is not an operator-resolution rule. -/
def comparisonOverload : Advanced.ComparisonOp → ScalarInput → ScalarInput → Option FunctionOverload
  | .eq | .ne | .lt | .le | .gt | .ge => equalityOverload

/-- Resolve a scalar operator against an array's scalar element. Unknown NULL
or string RHS inputs are contextually converted to the selected right-input
array type; a concrete non-array RHS is never treated as unknown. The full
operator signature records both selected input types and its Boolean result. -/
def quantifiedComparisonSignature (op : Advanced.ComparisonOp)
    (left right : ScalarInput) : Option FunctionOverload := do
  let element ← match right with
    | .unknown nullable => some (.unknown nullable)
    | .known ⟨.array element, _⟩ => some (.known ⟨element, true⟩)
    | .known _ => none
  let selected ← comparisonOverload op left element
  match selected.inputs with
  | [_, rightInput] =>
    if selected.output != .bool || rightInput.isArray then none
    else
      let coerces := match right with
        | .unknown _ => true
        | .known type => implicitCast type.base rightInput.asArray
      if coerces then some selected else none
  | _ => none

/-- PostgreSQL array bounds use assignment coercion to INT32, not ordinary
implicit operator coercion. Numeric narrowing is admitted; range and input
conversion success remain value obligations. Concrete strings are excluded. -/
def subscriptBoundSignature : ScalarInput → Bool
  | .unknown _ => true
  | .known type => type.base.numericRank.isSome

/-- Missing slice endpoints denote the array's existing bounds and introduce
neither an expression nor a conversion obligation. -/
def optionalSubscriptBoundSignature (expr : Option Advanced.Expr) (type : ExprType) : Bool :=
  match expr with
  | none => true
  | some expr => subscriptBoundSignature (scalarInput expr type)

def nullIfSignature (left right : ScalarInput) : Option ExactType := do
  let signature ← equalityOverload left right
  let first ← signature.inputs.head?
  let result := match left.base with
    | some declared =>
      if declared.unmodified == first.unmodified then declared else first.unmodified
    | none => first.unmodified
  some ⟨result, true⟩

def caseCondition (operand : Option ScalarInput) (condition : ScalarInput) : Bool :=
  match operand with
  | none => acceptsInput condition .bool
  | some input =>
    let input := match input with
      | .unknown nullable => .known ⟨.text, nullable⟩
      | .known type => .known type
    (equalityOverload input condition).isSome

/-- ELSE is the first input to PostgreSQL's CASE common-type resolution.
An omitted ELSE is an unknown NULL, so the result is conservatively nullable. -/
def caseSignature (operand : Option ScalarInput) (conditions results : List ScalarInput)
    (otherwise : ScalarInput) : Option ExactType := do
  if conditions.isEmpty || conditions.length != results.length ||
      !conditions.all (caseCondition operand) then none
  else
    let inputs := otherwise :: results
    some ⟨← conditionalBase inputs, inputs.any ScalarInput.nullable⟩

end SQLean.SelectContract
