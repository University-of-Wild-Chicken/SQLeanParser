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
  | .interval _ | .intervalRange .. => 4
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

/-- The five admitted PostgreSQL scalar `||` catalog declarations.
Polymorphic text conversion is distinct from an implicit cast to TEXT.
Array concatenation/append/prepend have separate, non-strict semantics. -/
inductive ConcatOperator where
  | textText | textOther | otherText | jsonb | bytea
  deriving Repr, BEq, DecidableEq

def concatOperators : List ConcatOperator :=
  [.textText, .textOther, .otherText, .jsonb, .bytea]

def ConcatOperator.catalogInputs : ConcatOperator → List String
  | .textText => ["text", "text"]
  | .textOther => ["text", "anynonarray"]
  | .otherText => ["anynonarray", "text"]
  | .jsonb => ["jsonb", "jsonb"]
  | .bytea => ["bytea", "bytea"]

def ConcatOperator.output : ConcatOperator → ScalarType
  | .textText | .textOther | .otherText => .text
  | .jsonb => .jsonb
  | .bytea => .bytea

def ConcatOperator.functionName : ConcatOperator → String
  | .textText => "textcat"
  | .textOther => "textanycat"
  | .otherText => "anytextcat"
  | .jsonb => "jsonb_concat"
  | .bytea => "byteacat"

/-- Selected catalog family and concrete argument instantiation. A polymorphic
argument retains its scalar identity; modifiers do not select an overload. -/
structure ConcatSignature where
  operator : ConcatOperator
  inputs : List ScalarType
  output : ScalarType
  deriving Repr, BEq, DecidableEq

/-- Closed scalar resolution for `||`, including PostgreSQL's exact-type
assumption for a single unknown operand. An unknown next to JSONB or BYTEA
receives that type; explicit TEXT selects a text conversion overload instead.
All admitted families propagate SQL NULL and return a non-NULL result on
successful non-NULL inputs. Literal parsing and value conversion can fail. -/
def concatSignature (left right : ScalarInput) : Option ConcatSignature :=
  let textText := some ⟨.textText, [.text, .text], .text⟩
  let jsonb := some ⟨.jsonb, [.jsonb, .jsonb], .jsonb⟩
  let bytea := some ⟨.bytea, [.bytea, .bytea], .bytea⟩
  match left.base.map ScalarType.unmodified, right.base.map ScalarType.unmodified with
  | none, none => textText
  | none, some b =>
      if b.isArray then none
      else if b == .jsonb then jsonb
      else if b == .bytea then bytea
      else if b.isString then textText
      else some ⟨.textOther, [.text, b], .text⟩
  | some a, none =>
      if a.isArray then none
      else if a == .jsonb then jsonb
      else if a == .bytea then bytea
      else if a.isString then textText
      else some ⟨.otherText, [a, .text], .text⟩
  | some a, some b =>
      if a.isArray || b.isArray then none
      else if a.isString && b.isString then textText
      else if a.isString then some ⟨.textOther, [.text, b], .text⟩
      else if b.isString then some ⟨.otherText, [a, .text], .text⟩
      else if a == .jsonb && b == .jsonb then jsonb
      else if a == .bytea && b == .bytea then bytea
      else none

/-- PostgreSQL string-matching operators represented directly by this
increment. NOT ILIKE uses the existing unary-NOT normalization instead. -/
inductive StringMatchOperator where
  | ilike
  | regex (insensitive negated : Bool)
  deriving Repr, BEq, DecidableEq

def stringMatchOperators : List StringMatchOperator :=
  [.ilike, .regex false false, .regex true false, .regex false true, .regex true true]

def StringMatchOperator.toSql : StringMatchOperator → String
  | .ilike => "~~*"
  | .regex false false => "~"
  | .regex true false => "~*"
  | .regex false true => "!~"
  | .regex true true => "!~*"

def StringMatchOperator.functionName (operator : StringMatchOperator) (charLeft : Bool) : String :=
  (if charLeft then "bpchar" else "text") ++
    match operator with
    | .ilike => "iclike"
    | .regex false false => "regexeq"
    | .regex true false => "icregexeq"
    | .regex false true => "regexne"
    | .regex true true => "icregexne"

/-- All admitted ILIKE/regex operators have these two declared signatures.
CHAR on the left retains its padding through the bpchar-specific operator.
CHAR on the right is converted to TEXT, which strips its padding. -/
def stringMatchOverloads : List FunctionOverload :=
  [⟨[.text, .text], .bool⟩, ⟨[.char [], .text], .bool⟩]

/-- Exact closed string operand selection. Unknown constants receive TEXT
context; a known CHAR left operand selects the bpchar overload. Unlike
concatenation, these operators do not accept arbitrary nonarray scalars.
BYTEA is admitted only by the separate LIKE rule. -/
def stringMatchSignature (left right : ScalarInput) : Option FunctionOverload :=
  let accepts : ScalarInput → Bool
    | .unknown _ => true
    | .known type => type.base.isString
  if accepts left && accepts right then
    let first := match left.base with
      | some (.char _) => ScalarType.char []
      | _ => .text
    some ⟨[first, .text], .bool⟩
  else none

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

/-- The six admitted PostgreSQL substring declarations. The two BIT
signatures require a separate exact bit-string type foundation. -/
def substringCatalog : List FunctionOverload :=
  [⟨[.text, .int32], .text⟩, ⟨[.text, .int32, .int32], .text⟩,
   ⟨[.bytea, .int32], .bytea⟩, ⟨[.bytea, .int32, .int32], .bytea⟩,
   ⟨[.text, .text], .text⟩, ⟨[.text, .text, .text], .text⟩]

/-- Regex extraction can return SQL NULL when no match is found, even with
non-NULL operands. Positional extraction only propagates operand NULL flags.
The selected declaration, rather than special-syntax spelling, decides this. -/
def substringNullable (selected : FunctionOverload) (inputs : List ScalarInput) : Bool :=
  selected.inputs == [.text, .text] || selected.inputs == [.text, .text, .text] ||
    inputs.any ScalarInput.nullable

/-- PostgreSQL 16's six SQL EXTRACT declarations. The syntactic field is
passed as TEXT; temporal input modifiers do not select a different overload.
Every declaration returns unmodified NUMERIC, unlike date_part's FLOAT8. -/
def extractCatalog : List FunctionOverload :=
  [.date, .time [], .timeTZ [], .timestamp [], .timestampTZ [], .interval []].map
    fun temporal => ⟨[.text, temporal], .numeric []⟩

/-- Unknown temporal operands remain ambiguous across the datetime/interval
categories. Concrete TEXT is not implicitly parsed as a temporal value. -/
def extractSignature (input : ScalarInput) : Option FunctionOverload :=
  resolveOverload extractCatalog [.known ⟨.text, false⟩, input]

/-- DATE and both timestamp families admit infinity: successful extraction
of some fields then yields SQL NULL even with a non-NULL operand. Other
admitted families only propagate their operand's SQL NULL. Field recognition,
field/type compatibility and input conversion remain runtime obligations. -/
def extractNullable (input : ScalarInput) : Bool :=
  match input.base with
  | some .date | some (.timestamp _) | some (.timestampTZ _) => true
  | _ => input.nullable

def jsonAccessOperators : List Advanced.JsonAccessOp :=
  [.field, .fieldText, .path, .pathText]

def jsonAccessSpelling : Advanced.JsonAccessOp → String
  | .field => "->"
  | .fieldText => "->>"
  | .path => "#>"
  | .pathText => "#>>"

/-- The complete twelve PostgreSQL JSON/JSONB extraction declarations.
An arrow takes either an INTEGER index or TEXT object key; a path takes
TEXT[]. Neither scalar JSON family is silently converted to the other. -/
def jsonAccessCatalog (op : Advanced.JsonAccessOp) : List FunctionOverload :=
  [.json, .jsonb].flatMap fun base =>
    let output := match op with
      | .field | .path => base
      | .fieldText | .pathText => ScalarType.text
    let keys := match op with
      | .field | .fieldText => [ScalarType.text, .int32]
      | .path | .pathText => [ScalarType.array .text]
    keys.map fun key => ⟨[base, key], output⟩

/-- Native function identity for each admitted extraction declaration.
Path functions have a variadic catalog parameter, but the operator passes
one TEXT[] argument; their fixed declared argument count remains two. -/
def jsonAccessFunctionName (op : Advanced.JsonAccessOp)
    (base key : ScalarType) : Option String := do
  let functionStem ← match base with
    | .json => some "json"
    | .jsonb => some "jsonb"
    | _ => none
  let suffix ← match op, key with
    | .field, .text => some "_object_field"
    | .fieldText, .text => some "_object_field_text"
    | .field, .int32 => some "_array_element"
    | .fieldText, .int32 => some "_array_element_text"
    | .path, .array .text => some "_extract_path"
    | .pathText, .array .text => some "_extract_path_text"
    | _, _ => none
  pure (functionStem ++ suffix)

/-- Finite operator selection retains the exact input/result types. SMALLINT
indices widen to INTEGER, string keys coerce to TEXT, and string-array paths
coerce elementwise to TEXT[]. Unknown RHS arrows prefer TEXT; unknown LHS
remains ambiguous between JSON and JSONB. Input-content errors are separate. -/
def jsonAccessSignature (op : Advanced.JsonAccessOp) (arg key : ScalarInput) :
    Option FunctionOverload :=
  resolveOverload (jsonAccessCatalog op) [arg, key]

/-- The three admitted JSONB existence operators retain their exact spellings. -/
def jsonExistenceOperators : List Advanced.JsonExistenceOp := [.key, .any, .all]

def jsonExistenceSpelling : Advanced.JsonExistenceOp → String
  | .key => "?" | .any => "?|" | .all => "?&"

def jsonExistenceFunctionName : Advanced.JsonExistenceOp → String
  | .key => "jsonb_exists" | .any => "jsonb_exists_any" | .all => "jsonb_exists_all"

/-- Strict, immutable, scalar Boolean declarations. NULL array members are
skipped by the array variants; only the outer argument flags affect nullability. -/
def jsonExistenceCatalog (op : Advanced.JsonExistenceOp) : List FunctionOverload :=
  [⟨[.jsonb, match op with | .key => .text | .any | .all => .array .text], .bool⟩]

/-- PostgreSQL also has binary POINT ?| POINT. Two unknown operands therefore
remain ambiguous for ?|, even though the JSONB-only inventory has one candidate.
The other two binary spellings have unique built-in declarations, and can give
both unknown constants their JSONB/TEXT or JSONB/TEXT[] context. Known JSON and
TEXT subjects do not become JSONB implicitly; string keys/arrays do coerce. -/
def jsonExistenceSignature (op : Advanced.JsonExistenceOp) (arg keys : ScalarInput) :
    Option FunctionOverload :=
  if op == .any && arg.base.isNone && keys.base.isNone then none
  else resolveOverload (jsonExistenceCatalog op) [arg, keys]

/-- The two directions share an exact JSONB/JSONB declaration; the AST retains
their spelling instead of swapping operands. -/
def jsonContainmentDirections : List Bool := [false, true]

def jsonContainmentSpelling (containedBy : Bool) : String :=
  if containedBy then "<@" else "@>"

def jsonContainmentFunctionName (containedBy : Bool) : String :=
  if containedBy then "jsonb_contained" else "jsonb_contains"

/-- JSONB containment is strict in both arguments. An unknown constant can
receive JSONB context from the other operand; two unknowns are ambiguous in
PostgreSQL's full built-in operator environment, which also contains array,
range, geometric and text-search families. A JSONB-only candidate list must
therefore not resolve that pair by pretending those other families are absent.
Known TEXT and JSON do not implicitly become JSONB. Array containment requires
its own polymorphic and element-comparison rules and is outside this rule. -/
def jsonContainmentSignature (left right : ScalarInput) : Option FunctionOverload :=
  match left.base, right.base with
  | some .jsonb, some .jsonb
  | some .jsonb, none
  | none, some .jsonb => some ⟨[.jsonb, .jsonb], .bool⟩
  | _, _ => none

/-- The three strict PostgreSQL anyarray predicates share element-equality
requirements but retain separate native functions and operator spellings. -/
inductive ArrayPredicateOperator where
  | contains | containedBy | overlap
  deriving Repr, BEq, DecidableEq

def arrayPredicateOperators : List ArrayPredicateOperator := [.contains, .containedBy, .overlap]

def ArrayPredicateOperator.toSql : ArrayPredicateOperator → String
  | .contains => "@>" | .containedBy => "<@" | .overlap => "&&"

def ArrayPredicateOperator.functionName : ArrayPredicateOperator → String
  | .contains => "arraycontains" | .containedBy => "arraycontained" | .overlap => "arrayoverlap"

def ArrayPredicateOperator.catalogInputs (_ : ArrayPredicateOperator) : List String :=
  ["anyarray", "anyarray"]

def ArrayPredicateOperator.catalogOutput (_ : ArrayPredicateOperator) : String := "boolean"

/-- Closed element equality inventory. VARCHAR uses the TEXT equality
implementation; CHAR uses bpchar equality. JSON has no admitted equality
implementation, even though the generic anyarray operator can analyze. -/
def arrayPredicateElementTypes : List ScalarType :=
  [.smallInt, .int32, .int64, .numeric [], .real, .doublePrecision,
   .text, .varchar [], .char [], .bool, .date, .time [], .timeTZ [],
   .timestamp [], .timestampTZ [], .interval [], .uuid, .jsonb, .bytea]

/-- anyarray requires identical element identities after typmod erasure.
Unlike anycompatiblearray concatenation, no cross-element widening occurs.
A single unknown input is contextually the known operand's array type. -/
def arrayPredicateElement (left right : ScalarInput) : Option ScalarType :=
  match left.base.map ScalarType.unmodified, right.base.map ScalarType.unmodified with
  | some (.array a), some (.array b) => if a == b then some a else none
  | some (.array a), none | none, some (.array a) => some a
  | _, _ => none

def arrayPredicateMissingEquality (left right : ScalarInput) : Bool :=
  (arrayPredicateElement left right).any fun element => !arrayPredicateElementTypes.contains element

/-- Admitted concrete anyarray instantiation. The equality inventory is a
separate requirement from native generic-operator availability, so a matching
JSON[] pair is a coverage gap rather than claimed native analysis rejection. -/
def arrayPredicateSignature (left right : ScalarInput) : Option FunctionOverload := do
  let element ← arrayPredicateElement left right
  if arrayPredicateElementTypes.contains element then
    some ⟨[element.asArray, element.asArray], .bool⟩
  else none

private def unaryOverloads (inputs : List ScalarType) (output : Option ScalarType := none) :
    List FunctionOverload :=
  inputs.map fun input => ⟨[input], output.getD input⟩

def numericTypes : List ScalarType :=
  [.smallInt, .int32, .int64, .numeric [], .real, .doublePrecision]

/-- Auditable supported-name inventory, including the four variadic-any rules. -/
def functionNames : List Name :=
  ["abs", "sign", "ceil", "ceiling", "floor", "sqrt", "exp", "ln", "cbrt", "degrees", "radians",
   "round", "trunc", "log", "power", "div", "mod", "lower", "upper", "length", "char_length",
   "character_length", "octet_length", "btrim", "ltrim", "rtrim", "replace", "substr", "substring",
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
  | "substring" => substringCatalog
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
    some ⟨overload.output, if name == "substring" then substringNullable overload args
      else args.any ScalarInput.nullable⟩

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

/-- PostgreSQL's non-strict array concatenation families are separate from
the scalar concatenation declarations and their strict NULL behavior. -/
inductive ArrayConcatOperator where
  | cat | append | prepend
  deriving Repr, BEq, DecidableEq

def arrayConcatOperators : List ArrayConcatOperator := [.cat, .append, .prepend]

def ArrayConcatOperator.catalogInputs : ArrayConcatOperator → List String
  | .cat => ["anycompatiblearray", "anycompatiblearray"]
  | .append => ["anycompatiblearray", "anycompatible"]
  | .prepend => ["anycompatible", "anycompatiblearray"]

def ArrayConcatOperator.catalogOutput (_ : ArrayConcatOperator) : String := "anycompatiblearray"

def ArrayConcatOperator.functionName : ArrayConcatOperator → String
  | .cat => "array_cat" | .append => "array_append" | .prepend => "array_prepend"

/-- Concatenating two NULL arrays returns NULL; either non-NULL array suffices.
Append/prepend replace a NULL array with an empty array and insert even a NULL
element, so successful results are always non-NULL arrays. -/
def ArrayConcatOperator.nullable (operator : ArrayConcatOperator) (left right : Bool) : Bool :=
  match operator with | .cat => left && right | .append | .prepend => false

structure ArrayConcatSignature where
  operator : ArrayConcatOperator
  inputs : List ScalarType
  output : ScalarType
  deriving Repr, BEq, DecidableEq

/-- Exact instantiations of the three anycompatible-array declarations.
A single unknown operand next to an array receives the array type, selecting
array_cat. Known scalar/array operands instead select append or prepend.
Common-type selection is directional over scalar element types; result and
declared argument typmods are erased even when both input modifiers agree.
No equality/comparison operation is required, including for JSON elements.
Array dimensions, extents and bounds remain value-dependent obligations. -/
def arrayConcatSignature (left right : ScalarInput) : Option ArrayConcatSignature := do
  match left.base.map ScalarType.unmodified, right.base.map ScalarType.unmodified with
  | some (.array a), none
  | none, some (.array a) =>
      some ⟨.cat, [a.asArray, a.asArray], a.asArray⟩
  | some (.array a), some (.array b) =>
      let common ← conditionalBase [.known ⟨a, false⟩, .known ⟨b, false⟩]
      let array := common.unmodified.asArray
      some ⟨.cat, [array, array], array⟩
  | some (.array a), some b =>
      let common ← conditionalBase [.known ⟨a, false⟩, .known ⟨b, false⟩]
      let element := common.unmodified
      some ⟨.append, [element.asArray, element], element.asArray⟩
  | some a, some (.array b) =>
      let common ← conditionalBase [.known ⟨a, false⟩, .known ⟨b, false⟩]
      let element := common.unmodified
      some ⟨.prepend, [element, element.asArray], element.asArray⟩
  | _, _ => none

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

/-- Closed PostgreSQL B-tree comparison inventory. Every scalar pair has all
five strategies; its <> operator negates strategy-3 equality. Same-element
arrays use the polymorphic array family when their element operators exist.
This is normative catalog data, not a claim about arbitrary SQL operators. -/
def rowBtreeCompatible (selected : FunctionOverload) : Bool :=
  equalityCatalog.contains selected ||
    (selected.output == .bool && match selected.inputs with
      | [.array left, .array right] =>
          left == right && !left.isArray && left.orderable
      | _ => false)

/-- PostgreSQL resolves each constructor field pair independently. One-field
rows use that scalar operator directly; longer rows additionally require the
admitted B-tree strategy family (or equality's negator for <>). Empty rows
and unequal arities have no comparison derivation. -/
def rowComparisonSignature (op : Advanced.ComparisonOp)
    (left right : List ScalarInput) : Option (List FunctionOverload) := do
  if left.isEmpty || left.length != right.length then none
  else (left.zip right).mapM fun (a, b) => do
    let selected ← comparisonOverload op a b
    if selected.output != .bool then none
    else if left.length == 1 || rowBtreeCompatible selected then some selected else none

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
