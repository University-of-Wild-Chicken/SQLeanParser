import SQLean.RenderContract.Profile

/-! Independent representation specification. This module imports neither the
parser nor the renderer nor any catalog/type validator. Its total traversal
describes all fields, required constructor combinations, and lexical domains.
Parameter occurrences follow SQL clause order, including CTE bodies first.
Acceptance does not assert name resolution, typing, or execution safety. -/
namespace SQLean.RenderContract
open Advanced

private def invalid (code message : String) : Except Failure α :=
  .error (.invalid ⟨code, message⟩)

def checkName (name : Name) : Except Failure Unit := do
  if name.isEmpty then invalid "representation.empty-name" "required identifier is empty"
  else if name.contains '\x00' then invalid "representation.name-nul" "identifier contains NUL"
  else if name.utf8ByteSize > 63 then
    invalid "representation.name-length" "identifier exceeds the fixed 63 UTF-8 byte limit"
  else pure ()

private def checkNames (names : List Name) : Except Failure Unit :=
  names.forM checkName

private def checkOptionalName (name : Option Name) : Except Failure Unit :=
  match name with | none => pure () | some name => checkName name

private def digit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

private def exponent (chars : List Char) : Bool :=
  match chars with
  | e :: tail =>
    if e == 'e' || e == 'E' then
      let digits := match tail with
        | sign :: rest => if sign == '+' || sign == '-' then rest else tail
        | [] => []
      !digits.isEmpty && digits.all digit
    else false
  | [] => false

/-- Unsigned decimal/exponent token grammar; pure integers belong to the
structural integer constructor. No signs, whitespace, comments or suffixes. -/
def numericLexeme (raw : String) : Bool :=
  let chars := raw.toList
  let whole := chars.takeWhile digit
  let rest := chars.dropWhile digit
  match rest with
  | '.' :: fraction =>
      let digits := fraction.takeWhile digit
      let suffix := fraction.dropWhile digit
      (!whole.isEmpty || !digits.isEmpty) && (suffix.isEmpty || exponent suffix)
  | _ => !whole.isEmpty && exponent rest

def checkTypeName (name : TypeName) (modifiers : List Nat) : Except Failure Unit :=
  match name, modifiers with
  | .array element, modifiers => checkTypeName element modifiers
  | _, [] => pure ()
  | .varchar, [n] | .char, [n] =>
      if 0 < n && n ≤ 10485760 then pure ()
      else invalid "representation.type-modifiers" "character length must be between 1 and 10485760"
  | .numeric, [p] =>
      if 0 < p && p ≤ 1000 then pure ()
      else invalid "representation.type-modifiers" "NUMERIC precision must be between 1 and 1000"
  | .numeric, [p, s] =>
      if 0 < p && p ≤ 1000 && s ≤ 1000 then pure ()
      else invalid "representation.type-modifiers" "NUMERIC precision/scale exceeds this profile's range"
  | .time, [p] | .timeTZ, [p] | .timestamp, [p] | .timestampTZ, [p] | .interval, [p] =>
      if p ≤ 6 then pure ()
      else invalid "representation.type-modifiers" "fractional-second precision must be between 0 and 6"
  | _, _ => invalid "representation.type-modifiers" "invalid modifiers for this type"

def checkDataType (type : DataType) : Except Failure Unit :=
  checkTypeName type.name type.modifiers

/-- Array suffixes are represented recursively, and count toward the boundary
that guards entry into serialization and reparsing. Scalar casts retain their
existing depth. This is not a runtime array-rank constraint. -/
def arrayTypeDepth : TypeName → Nat
  | .array element => 1 + arrayTypeDepth element
  | _ => 0

structure Footprint where
  parameters : List Parameter := []
  depth : Nat := 1
  deriving Repr, BEq, DecidableEq

private def combine (children : List (Except Failure Footprint)) : Except Failure Footprint := do
  let children ← children.mapM id
  pure {
    parameters := children.flatMap Footprint.parameters
    depth := 1 + children.foldl (fun depth child => max depth child.depth) 0
  }

private def leaf : Except Failure Footprint := pure {}

/-- PostgreSQL-shaped grammar interprets this spelling as an IN subquery.
Inventing a cast or arithmetic wrapper would change the represented tree. -/
private def ambiguousScalarList : List Advanced.Expr → Bool
  | [.scalarQuery _] => true
  | _ => false

mutual
  def inspectExpr (expr : Advanced.Expr) : Except Failure Footprint := do
    match expr with
    | .literal (.text value) =>
        if value.contains '\x00' then invalid "representation.text-nul" "text literal contains NUL"
        else leaf
    | .literal _ | .null | .countAll => leaf
    | .decimal raw =>
        if numericLexeme raw then leaf
        else invalid "representation.numeric-token" "decimal field is not a decimal/exponent token"
    | .parameter parameter => pure { parameters := [parameter] }
    | .column qualifier name => checkOptionalName qualifier; checkName name; leaf
    | .binary _ left right | .pattern left right _ =>
        combine [inspectExpr left, inspectExpr right]
    | .unary _ arg | .aggregate _ arg _ | .isNull arg _ => combine [inspectExpr arg]
    | .cast arg type =>
        checkDataType type
        combine [inspectExpr arg, .ok {depth := arrayTypeDepth type.name}]
    | .call name args =>
        if name.isEmpty || name.length > 3 then
          invalid "representation.function-name" "function names require one to three nonempty components"
        else
          checkNames name
          combine (args.attach.map fun (arg : {v : Advanced.Expr // v ∈ args}) =>
            have : sizeOf arg.val < sizeOf args := List.sizeOf_lt_of_mem arg.property
            inspectExpr arg.val)
    | .coalesce args | .greatest args | .least args =>
        if args.isEmpty then invalid "representation.conditional-args" "conditional expression requires arguments"
        else combine (args.attach.map fun (arg : {v : Advanced.Expr // v ∈ args}) =>
          have : sizeOf arg.val < sizeOf args := List.sizeOf_lt_of_mem arg.property
          inspectExpr arg.val)
    | .nullIf left right => combine [inspectExpr left, inspectExpr right]
    | .caseExpr operand branches otherwise =>
        if branches.isEmpty then invalid "representation.case-branches" "CASE requires at least one WHEN branch"
        else combine (
          (match _h : operand with | none => [] | some arg => [inspectExpr arg]) ++
          branches.attach.flatMap (fun (branch : {b : Advanced.Expr × Advanced.Expr // b ∈ branches}) =>
            have : sizeOf branch.val < sizeOf branches := List.sizeOf_lt_of_mem branch.property
            have : sizeOf branch.val.1 < sizeOf branch.val := by cases branch.val; simp; omega
            have : sizeOf branch.val.2 < sizeOf branch.val := by cases branch.val; simp; omega
            [inspectExpr branch.val.1, inspectExpr branch.val.2]) ++
          (match _h : otherwise with | none => [] | some arg => [inspectExpr arg]))
    | .filteredAggregate aggregate predicate =>
        match _h : aggregate with
        | .countAll | .aggregate .. => combine [inspectExpr aggregate, inspectExpr predicate]
        | _ => invalid "representation.filter" "FILTER must attach directly to an aggregate"
    | .inList arg values =>
        if values.isEmpty then invalid "representation.in-list" "IN list must be nonempty"
        else if ambiguousScalarList values then
          .error (.unsupported ⟨"coverage.scalar-in-list",
            "a singleton scalar-subquery IN list is syntactically ambiguous with an IN subquery"⟩)
        else combine (inspectExpr arg :: values.attach.map fun (value : {v : Advanced.Expr // v ∈ values}) =>
          have : sizeOf value.val < sizeOf values := List.sizeOf_lt_of_mem value.property
          inspectExpr value.val)
    | .between arg lower upper _ =>
        combine [inspectExpr arg, inspectExpr lower, inspectExpr upper]
    | .inQuery arg query => combine [inspectExpr arg, inspectQuery query]
    | .exists query | .scalarQuery query => combine [inspectQuery query]
  termination_by sizeOf expr
  decreasing_by all_goals (simp_all <;> omega)

  def inspectItem (item : Advanced.SelectItem) : Except Failure Footprint := do
    match item with
    | .all qualifier => checkOptionalName qualifier; leaf
    | .expression expr alias => checkOptionalName alias; combine [inspectExpr expr]
  termination_by sizeOf item
  decreasing_by all_goals (simp_all <;> omega)

  def inspectSource (source : From) : Except Failure Footprint := do
    match source with
    | .table name alias columns =>
        checkName name
        checkOptionalName alias
        checkNames columns
        if alias.isNone && !columns.isEmpty then
          invalid "representation.column-aliases" "table column aliases require a relation alias"
        else leaf
    | .derived query alias columns _ =>
        checkName alias; checkNames columns; combine [inspectQuery query]
    | .join kind left right condition =>
        match kind, condition with
        | .cross, .none => pure ()
        | .cross, _ => invalid "representation.cross-join" "CROSS JOIN cannot carry a condition"
        | _, .none => invalid "representation.join-condition" "non-CROSS JOIN needs ON, USING, or NATURAL"
        | _, .using names =>
            if names.isEmpty then invalid "representation.using" "USING columns must be nonempty"
            else checkNames names
        | _, _ => pure ()
        combine [inspectSource left, inspectSource right,
          match condition with | .on expr => inspectExpr expr | _ => leaf]
  termination_by sizeOf source
  decreasing_by all_goals (simp_all <;> omega)

  def inspectSelect (select : Select) : Except Failure Footprint := do
    if select.items.isEmpty then
      invalid "representation.select-list" "SELECT list must be nonempty"
    else if select.distinct && !select.distinctOn.isEmpty then
      invalid "representation.distinct" "DISTINCT and DISTINCT ON are mutually exclusive"
    else
      combine (
        (select.distinctOn.attach.map fun (expr : {e : Advanced.Expr // e ∈ select.distinctOn}) =>
          have : sizeOf expr.val < sizeOf select.distinctOn := List.sizeOf_lt_of_mem expr.property
          inspectExpr expr.val) ++
        (select.items.attach.map fun (item : {i : Advanced.SelectItem // i ∈ select.items}) =>
          have : sizeOf item.val < sizeOf select.items := List.sizeOf_lt_of_mem item.property
          inspectItem item.val) ++
        [match _h : select.source with | none => leaf | some source => inspectSource source,
         match _h : select.whereClause with | none => leaf | some expr => inspectExpr expr] ++
        (select.groupBy.attach.map fun (expr : {e : Advanced.Expr // e ∈ select.groupBy}) =>
          have : sizeOf expr.val < sizeOf select.groupBy := List.sizeOf_lt_of_mem expr.property
          inspectExpr expr.val) ++
        [match _h : select.having with | none => leaf | some expr => inspectExpr expr])
  termination_by sizeOf select
  decreasing_by all_goals cases select; simp_all; omega

  def inspectQuery (query : Advanced.Query) : Except Failure Footprint := do
    query.locking.forM fun clause => checkNames clause.targets
    if query.offsetFirst && (query.limit.isNone || query.offset.isNone) then
      invalid "representation.pagination-order" "OFFSET-first layout requires both OFFSET and LIMIT"
    else if query.recursive && query.ctes.isEmpty then
      invalid "representation.recursive" "recursive marker requires at least one CTE"
    else
      combine (
        (query.ctes.attach.map fun (cte : {c : Advanced.CTE // c ∈ query.ctes}) =>
          have : sizeOf cte.val < sizeOf query.ctes := List.sizeOf_lt_of_mem cte.property
          have : sizeOf cte.val.query < sizeOf cte.val := by cases cte.val; simp; omega
          do checkName cte.val.name
             checkNames cte.val.columns
             inspectQuery cte.val.query) ++
        [match _h : query.body with
         | .select select => inspectSelect select
         | .set _ _ left right => combine [inspectQuery left, inspectQuery right]] ++
        (query.orderBy.attach.map fun (order : {o : Advanced.OrderBy // o ∈ query.orderBy}) =>
          have : sizeOf order.val < sizeOf query.orderBy := List.sizeOf_lt_of_mem order.property
          have : sizeOf order.val.expr < sizeOf order.val := by cases order.val; simp; omega
          inspectExpr order.val.expr) ++
        (if query.offsetFirst then
          [match _h : query.offset with | none => leaf | some expr => inspectExpr expr,
           match _h : query.limit with | none => leaf | some expr => inspectExpr expr]
         else
          [match _h : query.limit with | none => leaf | some expr => inspectExpr expr,
           match _h : query.offset with | none => leaf | some expr => inspectExpr expr]))
  termination_by sizeOf query
  decreasing_by all_goals cases query; simp_all; omega
end

/-- Either all positive numbered slots, or exactly the anonymous occurrence
sequence 1..N. This is independent of what the parser or renderer happens to do. -/
def ParameterDiscipline (parameters : List Parameter) : Prop :=
  parameters.all (fun p => match p with | .numbered n => 0 < n | _ => false) = true ∨
  parameters = (List.range parameters.length).map (fun n => .anonymous (n + 1))

instance (parameters : List Parameter) : Decidable (ParameterDiscipline parameters) :=
  inferInstanceAs (Decidable (_ ∨ _))

def UniformStyle (parameters : List Parameter) : Prop :=
  ∀ p ∈ parameters, ∀ q ∈ parameters, parameterStyle p = parameterStyle q

instance (parameters : List Parameter) : Decidable (UniformStyle parameters) :=
  inferInstanceAs (Decidable (∀ p ∈ parameters, ∀ q ∈ parameters, _))

/-- The admissible domain is defined before serialization or reparsing. The
uniformity conjunct makes the binding-transport contract directly available. -/
def Admissible (query : Advanced.Query) : Prop :=
  ∃ footprint, inspectQuery query = .ok footprint ∧
    ParameterDiscipline footprint.parameters ∧ UniformStyle footprint.parameters

end SQLean.RenderContract
