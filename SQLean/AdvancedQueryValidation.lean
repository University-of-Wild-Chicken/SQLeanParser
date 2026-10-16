import SQLean.AdvancedSyntax
import SQLean.AdvancedCatalog

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
    | .binary _ left right | .pattern left right _ => hasAggregate fuel left || hasAggregate fuel right
    | .unary _ arg | .isNull arg _ | .cast arg _ => hasAggregate fuel arg
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
    | .unary op arg => .unary op (canonical fuel scopes arg)
    | .isNull arg neg => .isNull (canonical fuel scopes arg) neg
    | .cast arg target => .cast (canonical fuel scopes arg) target
    | .pattern arg pattern insensitive => .pattern (canonical fuel scopes arg) (canonical fuel scopes pattern) insensitive
    | .aggregate fn arg distinct => .aggregate fn (canonical fuel scopes arg) distinct
    | .filteredAggregate arg pred => .filteredAggregate (canonical fuel scopes arg) (canonical fuel scopes pred)
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
      | .binary _ l r | .pattern l r _ | .filteredAggregate l r => exprTables fuel l ++ exprTables fuel r
      | .unary _ e | .isNull e _ | .cast e _ | .aggregate _ e _ => exprTables fuel e
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
    | .binary _ left right | .pattern left right _ => simpleRecursiveExpr fuel left && simpleRecursiveExpr fuel right
    | .unary _ e | .cast e _ | .isNull e _ => simpleRecursiveExpr fuel e
    | .inList arg values => simpleRecursiveExpr fuel arg && values.all (simpleRecursiveExpr fuel)
    | .between arg lower upper _ => simpleRecursiveExpr fuel arg &&
        simpleRecursiveExpr fuel lower && simpleRecursiveExpr fuel upper
    | _ => true

private def recursiveStepShape (fuel : Nat) (query : Query) : Bool :=
  query.ctes.isEmpty && query.orderBy.isEmpty && query.limit.isNone && query.offset.isNone &&
  match query.body with
  | .set .. => false
  | .select select => select.groupBy.isEmpty && select.having.isNone && !select.distinct &&
    select.distinctOn.isEmpty && select.source.all (simpleRecursiveSource fuel) &&
    select.items.all (fun i => match i with | .all _ => true | .expression e _ => simpleRecursiveExpr fuel e) &&
    select.whereClause.all (simpleRecursiveExpr fuel)

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
        | none => invalid "incompatible binary operand types"
      | .unary op arg =>
        let arg ← inferExpr fuel schema params scopes aggregates arg
        ensure (!(arg.isNone && op == .neg)) "ambiguous negation of untyped NULL; add a cast"
        let arg := contextual arg (if op == .not then .bool else if op == .pos then .real else .int)
        match relUnaryResult op arg with
        | some type => pure (some type)
        | none => invalid "incompatible unary operand type"
      | .isNull arg _ =>
        let _ ← inferExpr fuel schema params scopes aggregates arg
        pure (some .bool)
      | .pattern arg pattern _ =>
        let arg ← inferExpr fuel schema params scopes aggregates arg
        let pattern ← inferExpr fuel schema params scopes aggregates pattern
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
          ensure (arg.base == type || arg.base == .text || type == .text ||
            (arg.numeric && type.numeric) || (arg.base == .int && type == .bool) ||
            (arg.base == .bool && type == .int)) "unsupported cast signature"
          pure (some (if arg.isNullable then type.asNullable else type))
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
        let columns ← checkQueryTypes fuel schema params scopes query
        match columns with
        | [column] =>
          let common ← commonType arg (some column.column.type)
          pure (some (if (finishType common).isNullable then .nullable .bool else .bool))
        | _ => invalid "IN subquery must return exactly one column"
      | .exists query =>
        let _ ← checkQueryTypes fuel schema params scopes query
        pure (some .bool)
      | .scalarQuery query =>
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
      | .binary _ left right | .pattern left right _ =>
        checkGrouped fuel schema params scopes groups left
        checkGrouped fuel schema params scopes groups right
      | .unary _ arg | .isNull arg _ | .cast arg _ => checkGrouped fuel schema params scopes groups arg
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

  private def checkSelect : Nat → Schema → ParameterEnv → List Scope → Select → List OrderBy → Except ValidationError (List TypedOutput)
    | 0, _, _, _, _, _ => invalid "advanced validation depth exhausted"
    | fuel + 1, schema, params, outer, select, orderBy => do
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
        let _ ← inferExpr fuel schema params scopes false group
      let order ← orderBy.mapM (fun item => selectExpression items scopes item.expr false)
      for expr in order do
        let _ ← inferExpr fuel schema params scopes true expr
      let keys ← select.distinctOn.mapM (fun expr => selectExpression items scopes expr false)
      for expr in keys do
        let _ ← inferExpr fuel schema params scopes true expr
      if let some predicate := select.having then
        let type ← inferExpr fuel schema params scopes true predicate
        ensure (boolean type) "HAVING requires Boolean predicate"
      let grouped := !groups.isEmpty || select.having.isSome ||
        items.any (fun item => hasAggregate fuel item.expr) || order.any (hasAggregate fuel) || keys.any (hasAggregate fuel)
      if grouped then
        items.forM (fun item => checkGrouped fuel schema params scopes groups item.expr)
        order.forM (checkGrouped fuel schema params scopes groups)
        keys.forM (checkGrouped fuel schema params scopes groups)
        select.having.toList.forM (checkGrouped fuel schema params scopes groups)
      ensure (!(select.distinct && !keys.isEmpty)) "DISTINCT and DISTINCT ON cannot be combined"
      if select.distinct then
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
          ensure (cte.query.ctes.isEmpty && cte.query.orderBy.isEmpty && cte.query.limit.isNone && cte.query.offset.isNone)
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
      match query.body with
      | .select select => checkSelect fuel schema params outer select query.orderBy
      | .set _ _ left right =>
        let left ← checkQueryTypes fuel schema params outer left
        let right ← checkQueryTypes fuel schema params outer right
        ensure (left.length == right.length) "set-operation arity mismatch"
        let columns ← (left.zip right).mapM fun (left, right) => do
          let type ← commonType left.type right.type
          pure { left with type := some (finishType type) }
        for item in query.orderBy do
          if (outputOrdinal item.expr).isSome then
            let _ ← selectExpression columns [] item.expr false
            pure ()
          else match item.expr with
          | .column none name =>
            ensure ((columns.filter (·.name == name)).length == 1) "unknown or ambiguous set-operation output name"
          | _ => invalid "set-operation ORDER BY requires an output name or ordinal"
        pure columns
end

mutual
  def expressionParameters : Nat → Expr → List Parameter
    | 0, _ => []
    | fuel + 1, expr => match expr with
      | .parameter parameter => [parameter]
      | .binary _ left right | .pattern left right _ | .filteredAggregate left right =>
        expressionParameters fuel left ++ expressionParameters fuel right
      | .unary _ arg | .cast arg _ | .isNull arg _ | .aggregate _ arg _ => expressionParameters fuel arg
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
      query.orderBy.flatMap (fun item => expressionParameters fuel item.expr)
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
    (outer : List Scope) (query : Query) : Except ValidationError (List ColumnDef) :=
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
