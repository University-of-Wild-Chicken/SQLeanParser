import SQLean.AdvancedSyntax
import SQLean.AdvancedCatalog
import SQLean.SelectContract.ScalarSignatures

/-! Bounded, schema-aware checks for the advanced query syntax. Certificates in
this module certify the stated executable static checks. They do not establish
execution semantics, cardinality, numeric range, data constraints, or termination
of recursive SQL. The older declarative SQLean validity relations are unchanged. -/
namespace SQLean.Advanced

abbrev ParameterEnv := List (Nat × SqlType)
/-- `none` is the unknown type of a bare SQL NULL, awaiting context. -/
abbrev ExprType := Option SqlType

structure Binding where
  qualifier : Option Name
  name : Name
  type : SqlType
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Unqualified outputs are distinct from qualified bindings: USING/NATURAL
coalesce outputs while retaining both tables' original qualified columns. -/
structure Scope where
  qualified : List RelColumn := []
  output : List Binding := []
  /-- Grouped outer queries restrict the columns visible to correlated queries. -/
  allowed : Option (List (Option Name × Name)) := none
  deriving Repr, BEq, DecidableEq, Inhabited

def Scope.ofTable (table : TableDef) (alias : Option Name := none) : Scope :=
  let qualifier := alias.getD table.name
  { qualified := table.columns.map fun c => ⟨qualifier, c.name, c.type⟩
    output := table.columns.map fun c => ⟨some qualifier, c.name, c.type⟩ }

private def invalid {α : Type} (message : String) : Except ValidationError α :=
  .error ⟨message⟩

private def ensure (condition : Bool) (message : String) : Except ValidationError Unit :=
  if condition then pure () else invalid message

private def distinctNames (names : List Name) : Bool :=
  names.all (· != "") && names.eraseDups.length == names.length

def checkParameters (params : ParameterEnv) : Except ValidationError Unit := do
  ensure (params.all (fun p => p.1 > 0)) "parameter indices must start at one"
  ensure ((params.map Prod.fst).eraseDups.length == params.length) "duplicate parameter index"
  ensure (params.all (fun p => p.2 == p.2.base || p.2 == p.2.base.asNullable))
    "parameter types must be primitive or singly nullable"

/-- Exact syntactic numeric check; no machine float conversion or rounding. -/
def isDecimalLexeme (value : String) : Bool := Id.run do
  let chars := value.toList
  let before := chars.takeWhile Char.isDigit
  let mut rest := chars.drop before.length
  let mut digitCount := before.length
  let mut hasDot := false
  let mut hasExponent := false
  if rest.head? == some '.' then
    hasDot := true
    rest := rest.drop 1
    let after := rest.takeWhile Char.isDigit
    digitCount := digitCount + after.length
    rest := rest.drop after.length
  if rest.head? == some 'e' || rest.head? == some 'E' then
    hasExponent := true
    rest := rest.drop 1
    if rest.head? == some '+' || rest.head? == some '-' then rest := rest.drop 1
    let exponent := rest.takeWhile Char.isDigit
    if exponent.isEmpty then return false
    rest := rest.drop exponent.length
  return digitCount > 0 && (hasDot || hasExponent) && rest.isEmpty

def finishType : ExprType → SqlType
  | none => .nullable .text
  | some type => type

abbrev checkParameterEnv := checkParameters
abbrev finalizeType := finishType

def assignmentCompatible (source : ExprType) (target : SqlType) : Bool :=
  match source with
  | none => target.isNullable
  | some source =>
    (!source.isNullable || target.isNullable) &&
      (source.base == target.base || (source.numeric && target.numeric))

private def commonType (left right : ExprType) : Except ValidationError ExprType :=
  match left, right with
  | none, none => pure none
  | some type, none | none, some type => pure (some type.asNullable)
  | some left, some right => do
    let base ← if left.base == right.base then pure left.base
      else if left.numeric && right.numeric then pure SqlType.real
      else invalid "incompatible scalar types"
    pure (some (if left.isNullable || right.isNullable then base.asNullable else base))

private def contextual (type : ExprType) (expected : SqlType) : SqlType :=
  type.getD expected.asNullable

private def boolean (type : ExprType) : Bool :=
  type.isNone || (finishType type).base == .bool

/-- The compatibility tier retains its old numeric families, while preserving
the new opaque built-ins. Consult the independent scalar signatures for their
temporal operations and casts; this bridge is not an independent certificate. -/
private def familyExact (type : SqlType) : SelectContract.ExactType :=
  ⟨(SelectContract.concreteType (DataType.ofSqlType type)).getD .text, type.isNullable⟩

private def familyResult (type : SelectContract.ExprType) : ExprType :=
  type.map fun type =>
    let base := type.base.dataType.sqlType
    if type.nullable then base.asNullable else base

/-- Resolves one lexical scope at a time. A local qualifier shadows outer scopes
also when its requested column does not exist. Ambiguity never falls through. -/
def resolveColumn : List Scope → Option Name → Name → Except ValidationError (Binding × Nat)
  | [], qualifier, name => invalid s!"unknown column '{qualifier.getD ""}.{name}'"
  | scope :: outer, qualifier, name => do
    let candidates : List Binding := match qualifier with
      | none => scope.output.filter (·.name == name)
      | some qualifier => (scope.qualified.filter (fun c => c.qualifier == qualifier && c.name == name)).map
          (fun c => Binding.mk (some c.qualifier) c.name c.type)
    match candidates with
    | [column] =>
      ensure (scope.allowed.all (fun keys => keys.contains (column.qualifier, column.name)))
        s!"ungrouped correlated column '{name}'"
      pure (column, 0)
    | [] =>
      if qualifier.any (fun q => scope.qualified.any (·.qualifier == q)) then
        invalid s!"unknown column '{qualifier.getD ""}.{name}'"
      else do
        let (column, depth) ← resolveColumn outer qualifier name
        pure (column, depth + 1)
    | _ => invalid s!"ambiguous column '{qualifier.getD ""}.{name}'"

private def nullableScope (scope : Scope) : Scope :=
  { scope with qualified := scope.qualified.map fun c => { c with type := c.type.asNullable }
               output := scope.output.map fun c => { c with type := c.type.asNullable } }

private def appendScopes (left right : Scope) : Except ValidationError Scope := do
  let leftNames := (left.qualified.map RelColumn.qualifier).eraseDups
  let rightNames := (right.qualified.map RelColumn.qualifier).eraseDups
  ensure (!(leftNames.any rightNames.contains)) "duplicate relation alias"
  pure { qualified := left.qualified ++ right.qualified, output := left.output ++ right.output }

private def renameColumns (columns : List ColumnDef) (names : List Name) : Except ValidationError (List ColumnDef) := do
  ensure (names.length ≤ columns.length) "too many column aliases"
  ensure (names.all (· != "")) "empty column alias"
  pure (columns.zipIdx.map fun (c, i) => { c with name := names[i]?.getD c.name })

private def namedRelation (name : Name) (columns : List ColumnDef) (aliases : List Name) :
    Except ValidationError Scope := do
  ensure (name != "") "empty relation alias"
  let columns ← renameColumns columns aliases
  pure (Scope.ofTable ⟨name, columns⟩)

private def mergeJoin (kind : JoinKind) (left right : Scope) (names : List Name) : Except ValidationError Scope := do
  ensure (distinctNames names) "USING columns must be distinct nonempty names"
  let both ← appendScopes
    (if kind == .right || kind == .full then nullableScope left else left)
    (if kind == .left || kind == .full then nullableScope right else right)
  let keys ← names.mapM fun name => do
    let (lc, _) ← resolveColumn [left] none name
    let (rc, _) ← resolveColumn [right] none name
    let type ← commonType (some lc.type) (some rc.type)
    let base := (finishType type).base
    ensure base.equalityComparable "USING/NATURAL requires equality-comparable columns"
    let nullable := match kind with
      | .left => lc.type.isNullable
      | .right => rc.type.isNullable
      | _ => lc.type.isNullable || rc.type.isNullable
    let qualifier := match kind with
      | .inner | .left => lc.qualifier
      | .right => rc.qualifier
      | _ => none
    pure (Binding.mk qualifier name (if nullable then base.asNullable else base))
  pure { both with output := keys ++ both.output.filter (fun c => !names.contains c.name) }

private def expressionName : Expr → Name
  | .column _ name => name
  | .countAll | .aggregate .count _ _ => "count"
  | .aggregate .sum _ _ => "sum"
  | .aggregate .avg _ _ => "avg"
  | .aggregate .min _ _ => "min"
  | .aggregate .max _ _ => "max"
  | .subscript base _ => expressionName base
  | .array _ => "array"
  | .substring .. => "substring"
  | .call name _ => name.getLastD "?column?"
  | .caseExpr .. => "case" | .coalesce .. => "coalesce" | .nullIf .. => "nullif"
  | .greatest .. => "greatest" | .least .. => "least"
  | .cast arg _ | .filteredAggregate arg _ => expressionName arg
  | _ => "?column?"

private structure TypedOutput where
  name : Name
  type : ExprType
  expr : Expr
  deriving Inhabited

private def TypedOutput.column (column : TypedOutput) : ColumnDef :=
  ⟨column.name, finishType column.type⟩

private def aggregateCall : Expr → Bool
  | .countAll | .aggregate .. => true
  | _ => false

private def hasAggregate : Nat → Expr → Bool
  | 0, _ => true
  | fuel + 1, expr => match expr with
    | .countAll | .aggregate .. | .filteredAggregate .. => true
    | .overlap left right | .containment left right _ | .jsonAccess _ left right | .regex left right _ _ | .concat left right | .quantifiedComparison _ _ left right | .binary _ left right | .pattern left right _ | .nullIf left right => hasAggregate fuel left || hasAggregate fuel right
    | .extract _ arg | .unary _ arg | .isNull arg _ | .cast arg _ => hasAggregate fuel arg
    | .subscript base indices => hasAggregate fuel base || (indices.flatMap Subscript.expressions).any (hasAggregate fuel)
    | .array args | .row args | .substring _ args | .call _ args | .coalesce args | .greatest args | .least args => args.any (hasAggregate fuel)
    | .caseExpr operand branches otherwise => operand.any (hasAggregate fuel) ||
        branches.any (fun branch => hasAggregate fuel branch.1 || hasAggregate fuel branch.2) ||
        otherwise.any (hasAggregate fuel)
    | .inList arg values => hasAggregate fuel arg || values.any (hasAggregate fuel)
    | .between arg lower upper _ => hasAggregate fuel arg || hasAggregate fuel lower || hasAggregate fuel upper
    | .inQuery arg _ => hasAggregate fuel arg
    | _ => false

/-- Keep an aggregate's own input scope while blocking references to enclosing
query levels, including references hidden inside an argument's subquery. -/
private def aggregateScopes : List Scope → List Scope
  | [] => []
  | scope :: outer => scope :: outer.map (fun level => { level with allowed := some [] })

private def canonical : Nat → List Scope → Expr → Expr
  | 0, _, expr => expr
  | fuel + 1, scopes, expr => match expr with
    | .column qualifier name => match resolveColumn scopes qualifier name with
      | .ok (column, _) => .column column.qualifier column.name
      | .error _ => expr
    | .binary op left right => .binary op (canonical fuel scopes left) (canonical fuel scopes right)
    | .containment left right containedBy =>
        .containment (canonical fuel scopes left) (canonical fuel scopes right) containedBy
    | .overlap left right =>
        .overlap (canonical fuel scopes left) (canonical fuel scopes right)
    | .jsonAccess op arg key =>
        .jsonAccess op (canonical fuel scopes arg) (canonical fuel scopes key)
    | .regex arg pattern insensitive negated =>
        .regex (canonical fuel scopes arg) (canonical fuel scopes pattern) insensitive negated
    | .concat left right => .concat (canonical fuel scopes left) (canonical fuel scopes right)
    | .quantifiedComparison op quantifier left right =>
      .quantifiedComparison op quantifier (canonical fuel scopes left) (canonical fuel scopes right)
    | .unary op arg => .unary op (canonical fuel scopes arg)
    | .isNull arg neg => .isNull (canonical fuel scopes arg) neg
    | .extract field arg => .extract field (canonical fuel scopes arg)
    | .cast arg target => .cast (canonical fuel scopes arg) target
    | .pattern arg pattern insensitive => .pattern (canonical fuel scopes arg) (canonical fuel scopes pattern) insensitive
    | .aggregate fn arg distinct => .aggregate fn (canonical fuel scopes arg) distinct
    | .filteredAggregate arg pred => .filteredAggregate (canonical fuel scopes arg) (canonical fuel scopes pred)
    | .subscript base indices => .subscript (canonical fuel scopes base) (indices.map fun bound => match bound with
      | .index expr => .index (canonical fuel scopes expr)
      | .slice lower upper => .slice (lower.map (canonical fuel scopes)) (upper.map (canonical fuel scopes)))
    | .array args => .array (args.map (canonical fuel scopes))
    | .row args => .row (args.map (canonical fuel scopes))
    | .substring form args => .substring form (args.map (canonical fuel scopes))
    | .call name args => .call name (args.map (canonical fuel scopes))
    | .coalesce args => .coalesce (args.map (canonical fuel scopes))
    | .greatest args => .greatest (args.map (canonical fuel scopes))
    | .least args => .least (args.map (canonical fuel scopes))
    | .nullIf left right => .nullIf (canonical fuel scopes left) (canonical fuel scopes right)
    | .caseExpr operand branches otherwise => .caseExpr (operand.map (canonical fuel scopes))
        (branches.map fun branch => (canonical fuel scopes branch.1, canonical fuel scopes branch.2))
        (otherwise.map (canonical fuel scopes))
    | .inList arg values => .inList (canonical fuel scopes arg) (values.map (canonical fuel scopes))
    | .between arg lower upper negated => .between (canonical fuel scopes arg)
        (canonical fuel scopes lower) (canonical fuel scopes upper) negated
    | .inQuery arg query => .inQuery (canonical fuel scopes arg) query
    | _ => expr

private def groupedScopes (fuel : Nat) (scopes : List Scope) (groups : List Expr) : List Scope :=
  match scopes with
  | [] => []
  | scope :: outer =>
    let keys := groups.filterMap fun expr => match canonical fuel scopes expr with
      | .column qualifier name => some (qualifier, name)
      | _ => none
    { scope with allowed := some keys } :: outer

private def outputOrdinal : Expr → Option Int
  | .literal (.int value) => some (Int.ofNat value)
  | .unary .neg arg => (outputOrdinal arg).map Neg.neg
  | _ => none

private def fractionalConstant : Expr → Bool
  | .decimal _ => true
  | .unary .neg arg => fractionalConstant arg
  | _ => false

private def selectExpression (items : List TypedOutput) (scopes : List Scope) (expr : Expr)
    (preferInput : Bool) : Except ValidationError Expr := do
  if let some ordinal := outputOrdinal expr then
    ensure (ordinal > 0) "output ordinal must be positive"
    match items[ordinal.toNat - 1]? with
    | some item => return item.expr
    | none => invalid "output ordinal out of range"
  else
    ensure (!fractionalConstant expr) "non-integer constant in ordering/grouping"
    match expr with
    | .literal (.text _) | .literal (.bool _) | .null => invalid "non-integer constant in ordering/grouping"
    | .column none name =>
      if preferInput && scopes.any (fun scope => scope.output.any (·.name == name)) then pure expr
      else
        let candidates := items.filter (·.name == name)
        match candidates with
        | [] => pure expr
        | head :: tail =>
          if tail.all (fun x => canonical 256 scopes x.expr == canonical 256 scopes head.expr)
          then pure head.expr else invalid s!"ambiguous output alias '{name}'"
    | _ => pure expr

private def distinctOrder (keys order : List Expr) : Bool := Id.run do
  let mut seen := []
  for expr in order do
    if keys.contains expr then seen := expr :: seen
    else if !(keys.all seen.contains) then return false
  return true

mutual
  private def queryTables : Nat → Query → List Name
    | 0, _ => []
    | fuel + 1, query =>
      query.ctes.flatMap (fun c => queryTables fuel c.query) ++
      query.orderBy.flatMap (fun o => exprTables fuel o.expr) ++
      query.limit.toList.flatMap (exprTables fuel) ++
      query.offset.toList.flatMap (exprTables fuel) ++
      match query.body with
      | .set _ _ left right => queryTables fuel left ++ queryTables fuel right
      | .select select =>
        (select.source.toList.flatMap (fromTables fuel)) ++
        (select.items.flatMap fun item => match item with | .all _ => [] | .expression e _ => exprTables fuel e) ++
        select.whereClause.toList.flatMap (exprTables fuel) ++
        select.having.toList.flatMap (exprTables fuel) ++ select.groupBy.flatMap (exprTables fuel)
  private def exprTables : Nat → Expr → List Name
    | 0, _ => []
    | fuel + 1, expr => match expr with
      | .overlap l r | .containment l r _ | .jsonAccess _ l r | .regex l r _ _ | .concat l r | .quantifiedComparison _ _ l r | .binary _ l r | .pattern l r _ | .filteredAggregate l r | .nullIf l r => exprTables fuel l ++ exprTables fuel r
      | .extract _ e | .unary _ e | .isNull e _ | .cast e _ | .aggregate _ e _ => exprTables fuel e
      | .subscript base indices => exprTables fuel base ++ (indices.flatMap Subscript.expressions).flatMap (exprTables fuel)
      | .array args | .row args | .substring _ args | .call _ args | .coalesce args | .greatest args | .least args => args.flatMap (exprTables fuel)
      | .caseExpr operand branches otherwise => operand.toList.flatMap (exprTables fuel) ++
          branches.flatMap (fun branch => exprTables fuel branch.1 ++ exprTables fuel branch.2) ++
          otherwise.toList.flatMap (exprTables fuel)
      | .inList arg values => exprTables fuel arg ++ values.flatMap (exprTables fuel)
      | .between arg lower upper _ => exprTables fuel arg ++ exprTables fuel lower ++ exprTables fuel upper
      | .inQuery arg query => exprTables fuel arg ++ queryTables fuel query
      | .exists query | .scalarQuery query => queryTables fuel query
      | _ => []
  private def fromTables : Nat → From → List Name
    | 0, _ => []
    | fuel + 1, source => match source with
      | .table name _ _ => [name]
      | .derived query _ _ _ => queryTables fuel query
      | .join _ left right condition => fromTables fuel left ++ fromTables fuel right ++
        match condition with | .on expr => exprTables fuel expr | _ => []
end

private def simpleRecursiveSource : Nat → From → Bool
  | 0, _ => false
  | fuel + 1, source => match source with
    | .table .. => true
    | .join kind left right _ => (kind == .inner || kind == .cross) &&
        simpleRecursiveSource fuel left && simpleRecursiveSource fuel right
    | .derived .. => false

private def simpleRecursiveExpr : Nat → Expr → Bool
  | 0, _ => false
  | fuel + 1, expr => match expr with
    | .exists _ | .scalarQuery _ | .inQuery .. | .countAll | .aggregate .. | .filteredAggregate .. => false
    | .overlap left right | .containment left right _ | .jsonAccess _ left right | .regex left right _ _ | .concat left right | .quantifiedComparison _ _ left right | .binary _ left right | .pattern left right _ | .nullIf left right => simpleRecursiveExpr fuel left && simpleRecursiveExpr fuel right
    | .extract _ e | .unary _ e | .cast e _ | .isNull e _ => simpleRecursiveExpr fuel e
    | .subscript base indices => simpleRecursiveExpr fuel base && (indices.flatMap Subscript.expressions).all (simpleRecursiveExpr fuel)
    | .array args | .row args | .substring _ args | .call _ args | .coalesce args | .greatest args | .least args => args.all (simpleRecursiveExpr fuel)
    | .caseExpr operand branches otherwise => operand.all (simpleRecursiveExpr fuel) &&
        branches.all (fun branch => simpleRecursiveExpr fuel branch.1 && simpleRecursiveExpr fuel branch.2) &&
        otherwise.all (simpleRecursiveExpr fuel)
    | .inList arg values => simpleRecursiveExpr fuel arg && values.all (simpleRecursiveExpr fuel)
    | .between arg lower upper _ => simpleRecursiveExpr fuel arg &&
        simpleRecursiveExpr fuel lower && simpleRecursiveExpr fuel upper
    | _ => true

private def recursiveStepShape (fuel : Nat) (query : Query) : Bool :=
  query.ctes.isEmpty && query.orderBy.isEmpty && query.limit.isNone && query.offset.isNone && query.locking.isEmpty &&
  match query.body with
  | .set .. => false
  | .select select => select.groupBy.isEmpty && select.having.isNone && !select.distinct &&
    select.distinctOn.isEmpty && select.source.all (simpleRecursiveSource fuel) &&
    select.items.all (fun i => match i with | .all _ => true | .expression e _ => simpleRecursiveExpr fuel e) &&
    select.whereClause.all (simpleRecursiveExpr fuel)

/-- Visible source name, nullable outer-join side, and derived-source flag. -/
private def lockingRelations : Nat → Bool → From → Except ValidationError (List (Name × Bool × Bool))
  | 0, _, _ => invalid "advanced validation depth exhausted"
  | _ + 1, nullable, .table name alias _ => pure [(alias.getD name, nullable, false)]
  | _ + 1, nullable, .derived _ alias _ _ => pure [(alias, nullable, true)]
  | fuel + 1, nullable, .join kind left right _ => do
    let left ← lockingRelations fuel (nullable || kind == .right || kind == .full) left
    let right ← lockingRelations fuel (nullable || kind == .left || kind == .full) right
    pure (left ++ right)

private def checkRowLocks (fuel : Nat) (select : Select) (grouped : Bool)
    (locking : List LockingClause) : Except ValidationError Unit := do
  if locking.isEmpty then return ()
  ensure (!select.distinct && select.distinctOn.isEmpty) "row locking is forbidden with DISTINCT"
  ensure (!grouped) "row locking is forbidden with grouping, HAVING, or aggregates"
  let relations ← match select.source with
    | none => pure [] | some source => lockingRelations fuel false source
  for clause in locking do
    let selected ← if clause.targets.isEmpty then pure relations else
      clause.targets.mapM fun target => do
        ensure (target != "") "empty row-lock target"
        match relations.filter (fun relation => relation.1 == target) with
        | [relation] => pure relation
        | _ => invalid s!"unknown or ambiguous row-lock target '{target}'"
    for relation in selected do
      ensure (!relation.2.1) "row locking cannot target a nullable outer-join side"
      ensure (!relation.2.2) "derived-source row-lock propagation is outside the executable profile"

/- Keep CTE provenance separate from the legacy column-only schema. Explicit
OF targets cannot name CTE bindings, including from nested query scopes.
Targetless locks do not propagate into a CTE's defining query. -/
mutual
  private def cteSourceNames : Nat → List Name → From → Except ValidationError (List Name)
    | 0, _, _ => invalid "advanced validation depth exhausted"
    | _ + 1, names, .table name alias _ =>
      pure (if names.contains name then [alias.getD name] else [])
    | _ + 1, _, .derived .. => pure []
    | fuel + 1, names, .join _ left right _ => do
      pure ((← cteSourceNames fuel names left) ++ (← cteSourceNames fuel names right))

  private def checkCTELockExpr : Nat → List Name → Expr → Except ValidationError Unit
    | 0, _, _ => invalid "advanced validation depth exhausted"
    | fuel + 1, names, expr => do
      match expr with
      | .inQuery arg query => checkCTELockExpr fuel names arg; checkCTELockQuery fuel names query
      | .exists query | .scalarQuery query => checkCTELockQuery fuel names query
      | _ =>
        let children : List Expr := match expr with
          | .overlap a b | .containment a b _ | .jsonAccess _ a b | .regex a b _ _ | .concat a b | .quantifiedComparison _ _ a b | .binary _ a b | .pattern a b _ | .nullIf a b | .filteredAggregate a b => [a, b]
          | .extract _ a | .unary _ a | .cast a _ | .isNull a _ | .aggregate _ a _ => [a]
          | .subscript base indices => base :: indices.flatMap Subscript.expressions
          | .array args | .row args | .substring _ args | .call _ args | .coalesce args | .greatest args | .least args => args
          | .caseExpr operand branches otherwise =>
            operand.toList ++ branches.flatMap (fun (branch : Expr × Expr) => [branch.1, branch.2]) ++ otherwise.toList
          | .inList arg values => arg :: values
          | .between arg lower upper _ => [arg, lower, upper]
          | _ => []
        children.forM (checkCTELockExpr fuel names)

  private def checkCTELockSource : Nat → List Name → From → Except ValidationError Unit
    | 0, _, _ => invalid "advanced validation depth exhausted"
    | _ + 1, _, .table .. => pure ()
    | fuel + 1, names, .derived query _ _ _ => checkCTELockQuery fuel names query
    | fuel + 1, names, .join _ left right condition => do
      checkCTELockSource fuel names left
      checkCTELockSource fuel names right
      match condition with | .on expr => checkCTELockExpr fuel names expr | _ => pure ()

  private def checkCTELockQuery : Nat → List Name → Query → Except ValidationError Unit
    | 0, _, _ => invalid "advanced validation depth exhausted"
    | fuel + 1, outerNames, query => do
      let names := query.ctes.map CTE.name ++ outerNames
      if query.recursive then
        query.ctes.forM fun cte => checkCTELockQuery fuel names cte.query
      else
        let mut visible := outerNames
        for cte in query.ctes do
          checkCTELockQuery fuel visible cte.query
          visible := cte.name :: visible
      match query.body with
      | .set _ _ left right => checkCTELockQuery fuel names left; checkCTELockQuery fuel names right
      | .select select =>
        let targets ← match select.source with
          | none => pure [] | some source => cteSourceNames fuel names source
        for clause in query.locking do
          ensure (clause.targets.all fun target => !targets.contains target)
            "row locking OF cannot target a WITH query"
        select.source.toList.forM (checkCTELockSource fuel names)
        let expressions := select.items.filterMap (fun item => match item with
            | .all _ => none | .expression expr _ => some expr) ++
          select.whereClause.toList ++ select.groupBy ++ select.having.toList ++ select.distinctOn
        expressions.forM (checkCTELockExpr fuel names)
      (query.orderBy.map OrderBy.expr ++ query.limit.toList ++ query.offset.toList).forM
        (checkCTELockExpr fuel names)
end

mutual
  /-- Infer an expression under inner-to-outer lexical scopes. Fuel exhaustion is
an explicit validation error. Parameter declarations are supplied by the caller. -/
  def inferExpr : Nat → Schema → ParameterEnv → List Scope → Bool → Expr → Except ValidationError ExprType
    | 0, _, _, _, _, _ => invalid "advanced validation depth exhausted"
    | fuel + 1, schema, params, scopes, aggregates, expr => do
      match expr with
      | .literal value => pure (some value.type)
      | .null => pure none
      | .decimal lexeme =>
        ensure (isDecimalLexeme lexeme) "invalid decimal/exponent literal"
        pure (some .real)
      | .parameter parameter =>
        let index := match parameter with | .numbered n | .anonymous n => n
        ensure (index > 0) "parameter indices must start at one"
        match params.find? (·.1 == index) with
        | some (_, type) => pure (some type)
        | none => invalid s!"missing type declaration for parameter {index}"
      | .column qualifier name => pure (some (← resolveColumn scopes qualifier name).1.type)
      | .binary op left right =>
        let left ← inferExpr fuel schema params scopes aggregates left
        let right ← inferExpr fuel schema params scopes aggregates right
        ensure (!((left.toList ++ right.toList).any SqlType.isArray))
          "array operators require exact element identities; use the independent contract tier"
        ensure (!(left.isNone && right.isNone &&
          (op == .add || op == .sub || op == .mul || op == .div)))
          "ambiguous arithmetic on two untyped NULL operands; add a cast"
        let expected := match op with
          | .and | .or => SqlType.bool
          | .add | .sub | .mul | .div => SqlType.int
          | _ => (finishType (left.or right)).base
        let left := contextual left (right.getD expected).base
        let right := contextual right left.base
        match relBinaryResult op left right with
        | some type => pure (some type)
        | none =>
          match SelectContract.binarySignature op (some (familyExact left)) (some (familyExact right)) with
          | some type => pure (familyResult type)
          | none => invalid "incompatible binary operand types"
      | .unary op arg =>
        let arg ← inferExpr fuel schema params scopes aggregates arg
        ensure (!(arg.isNone && op == .neg)) "ambiguous negation of untyped NULL; add a cast"
        let arg := contextual arg (if op == .not then .bool else if op == .pos then .real else .int)
        match relUnaryResult op arg with
        | some type => pure (some type)
        | none =>
          match SelectContract.unarySignature op (some (familyExact arg)) with
          | some type => pure (familyResult type)
          | none => invalid "incompatible unary operand type"
      | .isNull arg _ =>
        let _ ← inferExpr fuel schema params scopes aggregates arg
        pure (some .bool)
      | .pattern arg pattern insensitive =>
        let arg ← inferExpr fuel schema params scopes aggregates arg
        let pattern ← inferExpr fuel schema params scopes aggregates pattern
        if (finishType arg).base == .opaque .bytea && (finishType pattern).base == .opaque .bytea then
          ensure (!insensitive) "BYTEA has LIKE but no ILIKE signature"
          return some (if (finishType arg).isNullable || (finishType pattern).isNullable
            then .nullable .bool else .bool)
        match relPatternResult (contextual arg .text) (contextual pattern .text) with
        | some type => pure (some type)
        | none => invalid "LIKE/ILIKE requires text operands"
      | .cast arg target =>
        ensure (validDataType target) "invalid type modifiers"
        let arg ← inferExpr fuel schema params scopes aggregates arg
        let type := target.sqlType
        match arg with
        | none => pure (some type.asNullable)
        | some arg =>
          ensure (SelectContract.explicitCastAllowed (familyExact arg).base (familyExact type).base)
            "unsupported cast signature"
          let nullable := arg.isNullable ||
            (arg.base == .opaque .jsonb && (type.numeric || type == .bool))
          pure (some (if nullable then type.asNullable else type))
      | .subscript .. =>
        invalid "array subscripts require exact element types and bound coercions; use the independent contract tier"
      | .containment .. =>
        invalid "containment requires exact operator-family resolution; use the independent contract tier"
      | .extract .. =>
        invalid "EXTRACT requires exact temporal overload resolution; use the independent contract tier"
      | .substring .. =>
        invalid "SUBSTRING requires exact argument normalization and overload resolution; use the independent contract tier"
      | .overlap .. =>
        invalid "overlap requires exact operator-family resolution; use the independent contract tier"
      | .jsonAccess .. =>
        invalid "JSON extraction requires exact scalar overload resolution; use the independent contract tier"
      | .regex .. =>
        invalid "regular-expression matching requires exact scalar overload resolution; use the independent contract tier"
      | .concat .. =>
        invalid "concatenation requires exact scalar overload resolution; use the independent contract tier"
      | .quantifiedComparison .. =>
        invalid "quantified array comparisons require exact scalar operator signatures; use the independent contract tier"
      | .row _ =>
        invalid "row constructors and comparisons require independent exact field typing; use the contract tier"
      | .array _ =>
        invalid "array constructors require exact contextual element typing; use the independent contract tier"
      | .call name args =>
        let types ← args.mapM (inferExpr fuel schema params scopes aggregates)
        match SelectContract.callSignature name (SelectContract.scalarInputs args (types.map (Option.map familyExact))) with
        | some result => pure (familyResult (some result))
        | none => invalid "unsupported scalar function/conditional signature"
      | .coalesce args =>
        let types ← args.mapM (inferExpr fuel schema params scopes aggregates)
        match SelectContract.coalesceSignature (SelectContract.scalarInputs args (types.map (Option.map familyExact))) with
        | some result => pure (familyResult (some result))
        | none => invalid "unsupported scalar function/conditional signature"
      | .greatest args =>
        let types ← args.mapM (inferExpr fuel schema params scopes aggregates)
        ensure (!(types.filterMap id).any SqlType.isArray)
          "array ordering requires exact element identities; use the independent contract tier"
        match SelectContract.extremumSignature (SelectContract.scalarInputs args (types.map (Option.map familyExact))) with
        | some result => pure (familyResult (some result))
        | none => invalid "unsupported scalar function/conditional signature"
      | .least args =>
        let types ← args.mapM (inferExpr fuel schema params scopes aggregates)
        ensure (!(types.filterMap id).any SqlType.isArray)
          "array ordering requires exact element identities; use the independent contract tier"
        match SelectContract.extremumSignature (SelectContract.scalarInputs args (types.map (Option.map familyExact))) with
        | some result => pure (familyResult (some result))
        | none => invalid "unsupported scalar function/conditional signature"
      | .nullIf left right =>
        let ta ← inferExpr fuel schema params scopes aggregates left
        let tb ← inferExpr fuel schema params scopes aggregates right
        ensure (!((ta.toList ++ tb.toList).any SqlType.isArray))
          "array equality requires exact element identities; use the independent contract tier"
        match SelectContract.nullIfSignature (SelectContract.scalarInput left (ta.map familyExact))
            (SelectContract.scalarInput right (tb.map familyExact)) with
        | some result => pure (familyResult (some result))
        | none => invalid "unsupported NULLIF equality signature"
      | .caseExpr operand branches otherwise =>
        let operandType ← match operand with
          | none => pure none | some expr => inferExpr fuel schema params scopes aggregates expr
        ensure (!operandType.toList.any SqlType.isArray)
          "array CASE comparison requires exact element identities; use the independent contract tier"
        let branchTypes ← branches.mapM fun branch => do
          let condition ← inferExpr fuel schema params scopes aggregates branch.1
          let result ← inferExpr fuel schema params scopes aggregates branch.2
          pure (condition, result)
        let elseType ← match otherwise with
          | none => pure none | some expr => inferExpr fuel schema params scopes aggregates expr
        match SelectContract.caseSignature
            (operand.map fun expr => SelectContract.scalarInput expr (operandType.map familyExact))
            (SelectContract.scalarInputs (branches.map Prod.fst) (branchTypes.map fun types => types.1.map familyExact))
            (SelectContract.scalarInputs (branches.map Prod.snd) (branchTypes.map fun types => types.2.map familyExact))
            ((otherwise.map fun expr => SelectContract.scalarInput expr (elseType.map familyExact)).getD (.unknown true)) with
        | some result => pure (familyResult (some result))
        | none => invalid "incompatible CASE conditions or results"
      | .countAll =>
        ensure aggregates "aggregate forbidden in this clause"
        pure (some .int)
      | .aggregate fn arg _ =>
        ensure aggregates "aggregate forbidden in this clause"
        let arg ← inferExpr fuel schema params (aggregateScopes scopes) false arg
        ensure (!(arg.isNone && (fn == .sum || fn == .avg)))
          "ambiguous aggregate on untyped NULL; add a cast"
        let type := contextual arg (if fn == .min || fn == .max then .text else .int)
        match aggregateResult fn type with
        | some result => pure (some result)
        | none => invalid "invalid aggregate argument"
      | .filteredAggregate aggregate predicate =>
        ensure (aggregates && aggregateCall aggregate) "FILTER requires one aggregate call"
        let type ← inferExpr fuel schema params scopes true aggregate
        let predicate ← inferExpr fuel schema params (aggregateScopes scopes) false predicate
        ensure (boolean predicate) "FILTER requires a Boolean predicate"
        pure type
      | .inList arg values =>
        ensure (!values.isEmpty) "IN requires a nonempty list"
        let arg ← inferExpr fuel schema params scopes aggregates arg
        let values ← values.mapM (inferExpr fuel schema params scopes aggregates)
        ensure ((arg.toList ++ values.filterMap id).all SqlType.equalityComparable)
          "IN requires equality-comparable operands"
        -- PostgreSQL can use individual comparisons when the bare NULL's
        -- list has no common type (for example NULL IN (1, TRUE)).
        if arg.isNone then pure (some (.nullable .bool))
        else
          let common ← values.foldlM commonType arg
          pure (some (if common.isNone || (finishType common).isNullable then .nullable .bool else .bool))
      | .between arg lower upper _ =>
        let lowerType ← inferExpr fuel schema params scopes aggregates (.binary .ge arg lower)
        let upperType ← inferExpr fuel schema params scopes aggregates (.binary .le arg upper)
        pure (some (if (finishType lowerType).isNullable || (finishType upperType).isNullable
          then .nullable .bool else .bool))
      | .inQuery arg query =>
        let arg ← inferExpr fuel schema params scopes aggregates arg
        checkCTELockQuery fuel [] query
        let columns ← checkQueryTypes fuel schema params scopes query
        match columns with
        | [column] =>
          let common ← commonType arg (some column.column.type)
          ensure (finishType common).equalityComparable "IN requires an equality-comparable type"
          pure (some (if (finishType common).isNullable then .nullable .bool else .bool))
        | _ => invalid "IN subquery must return exactly one column"
      | .exists query =>
        checkCTELockQuery fuel [] query
        let _ ← checkQueryTypes fuel schema params scopes query
        pure (some .bool)
      | .scalarQuery query =>
        checkCTELockQuery fuel [] query
        let columns ← checkQueryTypes fuel schema params scopes query
        match columns with
        | [column] => pure (some column.column.type.asNullable)
        | _ => invalid "scalar subquery must return exactly one column"

  private def checkFrom : Nat → Schema → ParameterEnv → List Scope → Scope → From → Except ValidationError Scope
    | 0, _, _, _, _, _ => invalid "advanced validation depth exhausted"
    | fuel + 1, schema, params, outer, lateralScope, source => do
      match source with
      | .table name alias aliases =>
        match schema.find? (·.name == name) with
        | none => invalid s!"unknown table '{name}'"
        | some table => namedRelation (alias.getD name) table.columns aliases
      | .derived query alias aliases lateral =>
        let columns ← checkQueryTypes fuel schema params
          (if lateral then lateralScope :: outer else outer) query
        namedRelation alias (columns.map TypedOutput.column) aliases
      | .join kind left right condition =>
        let left ← checkFrom fuel schema params outer lateralScope left
        let visible ← appendScopes lateralScope left
        let right ← checkFrom fuel schema params outer
          (if kind == .right || kind == .full then lateralScope else visible) right
        let unextended ← appendScopes left right
        match condition with
        | .on predicate =>
          ensure (kind != .cross) "CROSS JOIN cannot have ON"
          let type ← inferExpr fuel schema params (unextended :: outer) false predicate
          ensure (boolean type) "JOIN ON requires Boolean predicate"
          appendScopes (if kind == .right || kind == .full then nullableScope left else left)
            (if kind == .left || kind == .full then nullableScope right else right)
        | .none =>
          ensure (kind == .cross) "non-CROSS JOIN requires a join condition"
          pure unextended
        | .using names =>
          ensure (kind != .cross && !names.isEmpty) "USING requires columns and a non-CROSS join"
          mergeJoin kind left right names
        | .natural =>
          ensure (kind != .cross) "NATURAL CROSS JOIN is unsupported"
          let names := (left.output.map Binding.name).filter (fun name => right.output.any (·.name == name))
          mergeJoin kind left right names

  private def checkGrouped : Nat → Schema → ParameterEnv → List Scope → List Expr → Expr → Except ValidationError Unit
    | 0, _, _, _, _, _ => invalid "advanced validation depth exhausted"
    | fuel + 1, schema, params, scopes, groups, expr => do
      if groups.any (fun key => canonical fuel scopes key == canonical fuel scopes expr) then pure ()
      else match expr with
      | .literal _ | .null | .decimal _ | .parameter _ | .countAll | .aggregate .. | .filteredAggregate .. => pure ()
      | .column qualifier name =>
        let (_, depth) ← resolveColumn scopes qualifier name
        ensure (depth > 0) s!"ungrouped column '{name}'"
      | .overlap left right | .containment left right _ | .jsonAccess _ left right | .regex left right _ _ | .concat left right | .quantifiedComparison _ _ left right | .binary _ left right | .pattern left right _ | .nullIf left right =>
        checkGrouped fuel schema params scopes groups left
        checkGrouped fuel schema params scopes groups right
      | .extract _ arg | .unary _ arg | .isNull arg _ | .cast arg _ => checkGrouped fuel schema params scopes groups arg
      | .subscript base indices =>
        checkGrouped fuel schema params scopes groups base
        (indices.flatMap Subscript.expressions).forM (checkGrouped fuel schema params scopes groups)
      | .array args | .row args | .substring _ args | .call _ args | .coalesce args | .greatest args | .least args =>
        args.forM (checkGrouped fuel schema params scopes groups)
      | .caseExpr operand branches otherwise =>
        operand.toList.forM (checkGrouped fuel schema params scopes groups)
        branches.forM fun branch => do
          checkGrouped fuel schema params scopes groups branch.1
          checkGrouped fuel schema params scopes groups branch.2
        otherwise.toList.forM (checkGrouped fuel schema params scopes groups)
      | .inList arg values =>
        checkGrouped fuel schema params scopes groups arg
        values.forM (checkGrouped fuel schema params scopes groups)
      | .between arg lower upper _ =>
        checkGrouped fuel schema params scopes groups arg
        checkGrouped fuel schema params scopes groups lower
        checkGrouped fuel schema params scopes groups upper
      | .inQuery arg query =>
        checkGrouped fuel schema params scopes groups arg
        let _ ← checkQueryTypes fuel schema params (groupedScopes fuel scopes groups) query
        pure ()
      | .exists query | .scalarQuery query =>
        let _ ← checkQueryTypes fuel schema params (groupedScopes fuel scopes groups) query
        pure ()

  private def checkSelect : Nat → Schema → ParameterEnv → List Scope → Select → List OrderBy →
      List LockingClause → Except ValidationError (List TypedOutput)
    | 0, _, _, _, _, _, _ => invalid "advanced validation depth exhausted"
    | fuel + 1, schema, params, outer, select, orderBy, locking => do
      ensure (!select.items.isEmpty) "SELECT list must be nonempty"
      let scope : Scope ← match select.source with
        | none => pure ({} : Scope)
        | some source => checkFrom fuel schema params outer {} source
      let scopes := scope :: outer
      if let some predicate := select.whereClause then
        let type ← inferExpr fuel schema params scopes false predicate
        ensure (boolean type) "WHERE requires Boolean predicate"
      let items ← select.items.flatMapM fun item => do
        match item with
        | .expression expr alias =>
          ensure (alias.all (· != "")) "empty output alias"
          let type ← inferExpr fuel schema params scopes true expr
          pure [{ name := alias.getD (expressionName expr), type, expr }]
        | .all qualifier =>
          let columns : List Binding := match qualifier with
            | none => scope.output
            | some q => (scope.qualified.filter (·.qualifier == q)).map fun c =>
                Binding.mk (some c.qualifier) c.name c.type
          ensure (!columns.isEmpty) "wildcard has no matching relation columns"
          pure (columns.map fun c => { name := c.name, type := some c.type, expr := .column c.qualifier c.name })
      let groups ← select.groupBy.mapM (fun expr => selectExpression items scopes expr true)
      for group in groups do
        let type ← inferExpr fuel schema params scopes false group
        ensure (finishType type).equalityComparable "GROUP BY requires an equality-comparable type"
      let order ← orderBy.mapM (fun item => selectExpression items scopes item.expr false)
      for expr in order do
        let type ← inferExpr fuel schema params scopes true expr
        ensure (finishType type).equalityComparable "ORDER BY requires an orderable type"
      let keys ← select.distinctOn.mapM (fun expr => selectExpression items scopes expr false)
      for expr in keys do
        let type ← inferExpr fuel schema params scopes true expr
        ensure (finishType type).equalityComparable "DISTINCT ON requires an equality-comparable type"
      if let some predicate := select.having then
        let type ← inferExpr fuel schema params scopes true predicate
        ensure (boolean type) "HAVING requires Boolean predicate"
      let grouped := !groups.isEmpty || select.having.isSome ||
        items.any (fun item => hasAggregate fuel item.expr) || order.any (hasAggregate fuel) || keys.any (hasAggregate fuel)
      checkRowLocks fuel select grouped locking
      if grouped then
        items.forM (fun item => checkGrouped fuel schema params scopes groups item.expr)
        order.forM (checkGrouped fuel schema params scopes groups)
        keys.forM (checkGrouped fuel schema params scopes groups)
        select.having.toList.forM (checkGrouped fuel schema params scopes groups)
      ensure (!(select.distinct && !keys.isEmpty)) "DISTINCT and DISTINCT ON cannot be combined"
      if select.distinct then
        ensure (items.all (fun item => (finishType item.type).equalityComparable))
          "DISTINCT requires equality-comparable output types"
        ensure (order.all (fun expr => items.any (fun item => canonical fuel scopes item.expr == canonical fuel scopes expr)))
          "SELECT DISTINCT ORDER BY expressions must occur in the output"
      if !keys.isEmpty then
        ensure (distinctOrder (keys.map (canonical fuel scopes)) (order.map (canonical fuel scopes)))
          "DISTINCT ON keys must match the initial ORDER BY expressions"
      pure items

  private def checkQueryTypes : Nat → Schema → ParameterEnv → List Scope → Query → Except ValidationError (List TypedOutput)
    | 0, _, _, _, _ => invalid "advanced validation depth exhausted"
    | fuel + 1, schema, params, outer, query => do
      ensure (!query.recursive || !query.ctes.isEmpty) "RECURSIVE requires WITH bindings"
      ensure (distinctNames (query.ctes.map CTE.name)) "CTE names must be distinct and nonempty"
      -- WITH RECURSIVE reserves every local CTE name throughout the WITH
      -- clause. Forward references are outside this sequential subset, so they
      -- must fail rather than accidentally resolving a physical homonym.
      let mut schema := if query.recursive then
        schema.filter (fun table => !(query.ctes.any (·.name == table.name)))
        else schema
      for cte in query.ctes do
        let selfReferences := (queryTables fuel cte.query).filter (· == cte.name)
        let columns ← if query.recursive && !selfReferences.isEmpty then do
          ensure (cte.query.ctes.isEmpty && cte.query.orderBy.isEmpty && cte.query.limit.isNone &&
              cte.query.offset.isNone && cte.query.locking.isEmpty)
            "recursive CTE cannot have local WITH or top-level ordering/limits"
          match cte.query.body with
          | .set .union _ anchor step =>
            ensure (!(queryTables fuel anchor).contains cte.name) "recursive reference in anchor"
            ensure ((queryTables fuel step).count cte.name == 1 && recursiveStepShape fuel step)
              "recursive step requires one direct reference, scalar projection, and inner/cross joins"
            let anchorColumns ← checkQueryTypes fuel schema params outer anchor
            let anchorColumns ← renameColumns (anchorColumns.map TypedOutput.column) cte.columns
            ensure (distinctNames (anchorColumns.map ColumnDef.name)) "recursive CTE needs distinct output column names"
            let recursiveSchema := ⟨cte.name, anchorColumns⟩ :: schema.filter (·.name != cte.name)
            let stepColumns ← checkQueryTypes fuel recursiveSchema params outer step
            ensure (anchorColumns.length == stepColumns.length) "recursive CTE arity mismatch"
            ensure ((anchorColumns.zip stepColumns).all (fun (a, b) => a.type == finishType b.type))
              "recursive CTE requires matching types, including nullability"
            pure anchorColumns
          | _ => invalid "recursive CTE requires anchor UNION [ALL] step"
        else do
          let columns ← checkQueryTypes fuel schema params outer cte.query
          renameColumns (columns.map TypedOutput.column) cte.columns
        ensure (distinctNames (columns.map ColumnDef.name)) "CTE output names must be distinct and nonempty"
        schema := ⟨cte.name, columns⟩ :: schema.filter (·.name != cte.name)
      -- Pagination has no access to this SELECT's input columns or output
      -- aliases. Correlated outer references keep their owning query scope.
      -- Negative values and NULL behavior are execution/dialect obligations.
      for bound in query.limit.toList ++ query.offset.toList do
        let type ← inferExpr fuel schema params outer false bound
        ensure (type.isNone || (finishType type).numeric)
          "pagination requires a numeric or NULL expression outside local row scope"
      match query.body with
      | .select select => checkSelect fuel schema params outer select query.orderBy query.locking
      | .set op all left right =>
        ensure query.locking.isEmpty "row locking is forbidden on set-operation results"
        let left ← checkQueryTypes fuel schema params outer left
        let right ← checkQueryTypes fuel schema params outer right
        ensure (left.length == right.length) "set-operation arity mismatch"
        let columns ← (left.zip right).mapM fun (left, right) => do
          let type ← commonType left.type right.type
          ensure ((op == .union && all) || (finishType type).equalityComparable)
            "this set operation requires equality-comparable output types"
          pure { left with type := some (finishType type) }
        for item in query.orderBy do
          if (outputOrdinal item.expr).isSome then
            let expr ← selectExpression columns [] item.expr false
            let matching := columns.filter (fun column => column.expr == expr)
            ensure (matching.all (fun column => (finishType column.type).equalityComparable))
              "set-operation ORDER BY requires an orderable type"
            pure ()
          else match item.expr with
          | .column none name =>
            ensure ((columns.filter (·.name == name)).length == 1) "unknown or ambiguous set-operation output name"
            ensure ((columns.filter (·.name == name)).all
              (fun column => (finishType column.type).equalityComparable))
              "set-operation ORDER BY requires an orderable type"
          | _ => invalid "set-operation ORDER BY requires an output name or ordinal"
        pure columns
end

mutual
  def expressionParameters : Nat → Expr → List Parameter
    | 0, _ => []
    | fuel + 1, expr => match expr with
      | .parameter parameter => [parameter]
      | .overlap left right | .containment left right _ | .jsonAccess _ left right | .regex left right _ _ | .concat left right | .quantifiedComparison _ _ left right | .binary _ left right | .pattern left right _ | .filteredAggregate left right | .nullIf left right =>
        expressionParameters fuel left ++ expressionParameters fuel right
      | .extract _ arg | .unary _ arg | .cast arg _ | .isNull arg _ | .aggregate _ arg _ => expressionParameters fuel arg
      | .subscript base indices => expressionParameters fuel base ++ (indices.flatMap Subscript.expressions).flatMap (expressionParameters fuel)
      | .array args | .row args | .substring _ args | .call _ args | .coalesce args | .greatest args | .least args => args.flatMap (expressionParameters fuel)
      | .caseExpr operand branches otherwise => operand.toList.flatMap (expressionParameters fuel) ++
          branches.flatMap (fun branch => expressionParameters fuel branch.1 ++ expressionParameters fuel branch.2) ++
          otherwise.toList.flatMap (expressionParameters fuel)
      | .inList arg values => expressionParameters fuel arg ++ values.flatMap (expressionParameters fuel)
      | .between arg lower upper _ => expressionParameters fuel arg ++
        expressionParameters fuel lower ++ expressionParameters fuel upper
      | .inQuery arg query => expressionParameters fuel arg ++ queryParameters fuel query
      | .exists query | .scalarQuery query => queryParameters fuel query
      | _ => []
  def queryParameters : Nat → Query → List Parameter
    | 0, _ => []
    | fuel + 1, query =>
      query.ctes.flatMap (fun c => queryParameters fuel c.query) ++
      (match query.body with
      | .set _ _ left right => queryParameters fuel left ++ queryParameters fuel right
      | .select select =>
        select.distinctOn.flatMap (expressionParameters fuel) ++
        select.items.flatMap (fun item => match item with
          | .all _ => [] | .expression expr _ => expressionParameters fuel expr) ++
        select.source.toList.flatMap (sourceParameters fuel) ++
        select.whereClause.toList.flatMap (expressionParameters fuel) ++
        select.groupBy.flatMap (expressionParameters fuel) ++
        select.having.toList.flatMap (expressionParameters fuel)) ++
      query.orderBy.flatMap (fun item => expressionParameters fuel item.expr) ++
      (if query.offsetFirst then
        query.offset.toList.flatMap (expressionParameters fuel) ++ query.limit.toList.flatMap (expressionParameters fuel)
       else query.limit.toList.flatMap (expressionParameters fuel) ++ query.offset.toList.flatMap (expressionParameters fuel))
  def sourceParameters : Nat → From → List Parameter
    | 0, _ => []
    | fuel + 1, source => match source with
      | .table .. => []
      | .derived query _ _ _ => queryParameters fuel query
      | .join _ left right condition => sourceParameters fuel left ++ sourceParameters fuel right ++
        match condition with | .on expr => expressionParameters fuel expr | _ => []
end

/-- Reject mixed placeholder styles even for hand-constructed query ASTs. -/
def checkParameterUses (uses : List Parameter) : Except ValidationError Unit := do
  let numbered := uses.any (fun p => match p with | .numbered _ => true | _ => false)
  let anonymous := uses.any (fun p => match p with | .anonymous _ => true | _ => false)
  ensure (!(numbered && anonymous)) "numbered and anonymous parameters cannot be mixed"
  ensure (uses.all (fun p => match p with | .numbered n | .anonymous n => n > 0))
    "parameter indices must start at one"
  let ordinals := uses.filterMap (fun p => match p with | .anonymous n => some n | _ => none)
  ensure (ordinals == (List.range ordinals.length).map (· + 1))
    "anonymous parameter ordinals must follow source order from one without repetition"

/-- Named output columns under an explicit outer scope. NULL-only projections are
resolved to nullable text at the query boundary, as PostgreSQL does. -/
def checkQueryFuel (fuel : Nat) (schema : Schema) (params : ParameterEnv)
    (outer : List Scope) (query : Query) : Except ValidationError (List ColumnDef) := do
  checkCTELockQuery fuel [] query
  (checkQueryTypes fuel schema params outer query).map (List.map TypedOutput.column)

/-- Public static query checker. Parameter types must be declared explicitly. -/
def checkQuery (schema : Schema) (params : ParameterEnv) (query : Query) : Except ValidationError (List ColumnDef) := do
  let _ ← checkSchema schema
  checkParameters params
  checkParameterUses (queryParameters 1024 query)
  checkQueryFuel 1024 schema params [] query

/-- Contextual target checking for INSERT SELECT; a bare NULL remains unknown
until assignment to its target column. Set operations still resolve their own
common output types before this boundary. -/
def checkQueryAgainst (schema : Schema) (params : ParameterEnv) (query : Query)
    (targets : List SqlType) : Except ValidationError Unit := do
  let _ ← checkSchema schema
  checkParameters params
  checkParameterUses (queryParameters 1024 query)
  checkCTELockQuery 1024 [] query
  let columns ← checkQueryTypes 1024 schema params [] query
  ensure (columns.length == targets.length) "INSERT SELECT arity mismatch"
  ensure ((columns.zip targets).all (fun (column, target) => assignmentCompatible column.type target))
    "INSERT SELECT type or nullability mismatch"

/-- The advanced certificate states exactly successful bounded static checking;
it is deliberately not identified with the legacy declarative validity relation. -/
def QueryValid (schema : Schema) (params : ParameterEnv) (query : Query) (columns : List ColumnDef) : Prop :=
  checkQuery schema params query = .ok columns

def certifyQuery (schema : Schema) (params : ParameterEnv) (query : Query) :
    Except ValidationError {columns : List ColumnDef // QueryValid schema params query columns} :=
  match h : checkQuery schema params query with
  | .error error => .error error
  | .ok columns => .ok ⟨columns, h⟩

theorem checkQuery_sound (h : checkQuery schema params query = .ok columns) :
    QueryValid schema params query columns := h

theorem checkQuery_complete (h : QueryValid schema params query columns) :
    checkQuery schema params query = .ok columns := h

end SQLean.Advanced
