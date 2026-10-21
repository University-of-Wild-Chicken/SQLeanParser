import SQLean.SelectContract.ScalarSignatures

/-! Independent structural premises for the bounded recursive SELECT profile.
References are syntactic occurrences, including unused WITH definitions; they
are not execution counts. Expression subqueries are scanned in the native forbidden-reference
context, including discarded projections and unused WITH definitions. Collation support below is deliberately sufficient, not a
claim that a concrete scalar type determines an expression's collation. -/
namespace SQLean.SelectContract
open Advanced

def recursiveOutput (columns : List OutputColumn) : List OutputColumn :=
  columns.map fun column => {column with type := {column.type with nullable := true}}

/-- Local RECURSIVE names hide inherited bindings before any definition is
analyzed. Forward dependencies are a separate explicit coverage boundary. -/
def recursiveOuterEnv (env : CTEEnv) (ctes : List Advanced.CTE) : CTEEnv :=
  env.filter fun binding => !(ctes.map Advanced.CTE.name).contains binding.name

structure RecursiveReferences where
  count : Nat := 0
  permitted : Bool := true
  deriving Repr, BEq, DecidableEq, Inhabited

def RecursiveReferences.append (left right : RecursiveReferences) : RecursiveReferences :=
  ⟨left.count + right.count, left.permitted && right.permitted⟩

mutual
  def recursiveReferences (target : Name) (hidden allowed : Bool) (query : Advanced.Query) : RecursiveReferences :=
    let localHidden := hidden || (query.ctes.map Advanced.CTE.name).contains target
    let definitions := recursiveCTEReferences target (if query.recursive then localHidden else hidden) allowed query.ctes
    let body := match _bodyEq : query.body with
      | .select select => recursiveSelectReferences target localHidden allowed select
      | .set op all left right =>
        let leftAllowed := allowed && !(op == .except && all) && !(op == .intersect && all)
        let rightAllowed := allowed && !(op == .except) && !(op == .intersect && all)
        (recursiveReferences target localHidden leftAllowed left).append
          (recursiveReferences target localHidden rightAllowed right)
    definitions.append body |>.append (recursiveOrderReferences target localHidden query.orderBy) |>.append
      (recursiveOptionalExprReferences target localHidden query.limit) |>.append
      (recursiveOptionalExprReferences target localHidden query.offset)
  termination_by sizeOf query
  decreasing_by all_goals (cases query <;> (try cases select) <;> simp_all <;> omega)

  def recursiveSelectReferences (target : Name) (hidden allowed : Bool) (select : Advanced.Select) : RecursiveReferences :=
    let source := match _sourceEq : select.source with
      | none => (⟨0, true⟩ : RecursiveReferences)
      | some source => recursiveSourceReferences target hidden allowed source
    source.append (recursiveItemReferences target hidden select.items) |>.append
      (recursiveOptionalExprReferences target hidden select.whereClause) |>.append
      (recursiveExprsReferences target hidden select.groupBy) |>.append
      (recursiveOptionalExprReferences target hidden select.having) |>.append
      (recursiveExprsReferences target hidden select.distinctOn)
  termination_by sizeOf select
  decreasing_by all_goals (cases select <;> simp_all <;> omega)

  def recursiveSourceReferences (target : Name) (hidden allowed : Bool) (source : Advanced.From) : RecursiveReferences :=
    match source with
    | .table name _ _ schema =>
      if !hidden && schema.isNone && name == target then ⟨1, allowed⟩ else ⟨0, true⟩
    | .derived query _ _ _ => recursiveReferences target hidden allowed query
    | .join kind left right condition =>
      (recursiveSourceReferences target hidden (allowed && !(kind == .right || kind == .full)) left).append
        (recursiveSourceReferences target hidden (allowed && !(kind == .left || kind == .full)) right) |>.append
        (match condition with | .on expr => recursiveExprReferences target hidden expr | _ => ⟨0, true⟩)
  termination_by sizeOf source
  decreasing_by all_goals (simp_all <;> omega)

  def recursiveCTEReferences (target : Name) (hidden allowed : Bool) (ctes : List Advanced.CTE) : RecursiveReferences :=
    match ctes with
    | [] => ⟨0, true⟩
    | head :: tail =>
      (recursiveReferences target hidden allowed head.query).append
        (recursiveCTEReferences target (hidden || head.name == target) allowed tail)
  termination_by sizeOf ctes
  decreasing_by all_goals (cases head <;> simp_all <;> omega)

  /-- Raw SubLink subselects forbid recursive self references. Their IN test
  expressions retain ordinary traversal, and nested WITH scopes still shadow. -/
  def recursiveExprReferences (target : Name) (hidden : Bool) (expr : Advanced.Expr) : RecursiveReferences :=
    match expr with
    | .literal _ | .null | .decimal _ | .parameter _ | .column .. | .contextValue _ | .countAll => ⟨0, true⟩
    | .exists child | .scalarQuery child => recursiveReferences target hidden false child
    | .inQuery arg child | .quantifiedQuery _ _ arg child => (recursiveExprReferences target hidden arg).append (recursiveReferences target hidden false child)
    | .cast arg _ | .collate arg _ | .unary _ arg | .aggregate _ arg _ | .isNull arg _ | .extract _ arg =>
      recursiveExprReferences target hidden arg
    | .binary _ left right | .concat left right | .distinctFrom left right _
    | .pattern left right _ | .regex left right _ _ | .jsonAccess _ left right
    | .jsonExistence _ left right | .containment left right _ | .overlap left right
    | .quantifiedComparison _ _ left right | .nullIf left right | .filteredAggregate left right =>
      (recursiveExprReferences target hidden left).append (recursiveExprReferences target hidden right)
    | .array args | .row args | .substring _ args | .coalesce args | .greatest args | .least args | .call _ args =>
      recursiveExprsReferences target hidden args
    | .namedCall _ args => recursiveArgumentReferences target hidden args
    | .subscript base indices =>
      (recursiveExprReferences target hidden base).append (recursiveSubscriptReferences target hidden indices)
    | .caseExpr operand branches otherwise =>
      (recursiveOptionalExprReferences target hidden operand).append
        (recursiveBranchReferences target hidden branches) |>.append
        (recursiveOptionalExprReferences target hidden otherwise)
    | .inList arg values => (recursiveExprReferences target hidden arg).append (recursiveExprsReferences target hidden values)
    | .between arg lower upper _ => (recursiveExprReferences target hidden arg).append
        (recursiveExprReferences target hidden lower) |>.append (recursiveExprReferences target hidden upper)
  termination_by sizeOf expr
  decreasing_by all_goals (simp_all <;> omega)

  def recursiveExprsReferences (target : Name) (hidden : Bool) (exprs : List Advanced.Expr) : RecursiveReferences :=
    match exprs with
    | [] => ⟨0, true⟩
    | head :: tail => (recursiveExprReferences target hidden head).append (recursiveExprsReferences target hidden tail)
  termination_by sizeOf exprs
  decreasing_by all_goals (simp_all <;> omega)

  def recursiveOptionalExprReferences (target : Name) (hidden : Bool) (expr : Option Advanced.Expr) : RecursiveReferences :=
    match expr with
    | none => ⟨0, true⟩
    | some expr => recursiveExprReferences target hidden expr
  termination_by sizeOf expr
  decreasing_by all_goals (simp_all <;> omega)

  def recursiveArgumentReferences (target : Name) (hidden : Bool) (args : List CallArgument) : RecursiveReferences :=
    match args with
    | [] => ⟨0, true⟩
    | .positional value :: tail | .named _ value _ :: tail =>
      (recursiveExprReferences target hidden value).append (recursiveArgumentReferences target hidden tail)
  termination_by sizeOf args
  decreasing_by all_goals (simp_all <;> omega)

  def recursiveSubscriptReferences (target : Name) (hidden : Bool) (indices : List Subscript) : RecursiveReferences :=
    match indices with
    | [] => ⟨0, true⟩
    | .index value :: tail => (recursiveExprReferences target hidden value).append (recursiveSubscriptReferences target hidden tail)
    | .slice lower upper :: tail =>
      (recursiveOptionalExprReferences target hidden lower).append
        (recursiveOptionalExprReferences target hidden upper) |>.append (recursiveSubscriptReferences target hidden tail)
  termination_by sizeOf indices
  decreasing_by all_goals (simp_all <;> omega)

  def recursiveBranchReferences (target : Name) (hidden : Bool) (branches : List (Advanced.Expr × Advanced.Expr)) : RecursiveReferences :=
    match branches with
    | [] => ⟨0, true⟩
    | (condition, value) :: tail => (recursiveExprReferences target hidden condition).append
        (recursiveExprReferences target hidden value) |>.append (recursiveBranchReferences target hidden tail)
  termination_by sizeOf branches
  decreasing_by all_goals (simp_all <;> omega)

  def recursiveItemReferences (target : Name) (hidden : Bool) (items : List Advanced.SelectItem) : RecursiveReferences :=
    match items with
    | [] => ⟨0, true⟩
    | .all .. :: tail => recursiveItemReferences target hidden tail
    | .expression expr _ :: tail => (recursiveExprReferences target hidden expr).append (recursiveItemReferences target hidden tail)
  termination_by sizeOf items
  decreasing_by all_goals (simp_all <;> omega)

  def recursiveOrderReferences (target : Name) (hidden : Bool) (items : List Advanced.OrderBy) : RecursiveReferences :=
    match items with
    | [] => ⟨0, true⟩
    | head :: tail => (recursiveExprReferences target hidden head.expr).append (recursiveOrderReferences target hidden tail)
  termination_by sizeOf items
  decreasing_by all_goals (cases head <;> simp_all <;> omega)
end

def NoForwardCTEReferences (remaining : List Advanced.CTE) (query : Advanced.Query) : Prop :=
  ∀ later ∈ remaining, (recursiveReferences later.name false true query).count = 0

instance (remaining : List Advanced.CTE) (query : Advanced.Query) : Decidable (NoForwardCTEReferences remaining query) :=
  inferInstanceAs (Decidable (∀ later ∈ remaining, _))

/-- These builtins can introduce native C collation even when a later cast or
operator returns TEXT. Unknown routines are already outside ExprValid. -/
def defaultCollationFunction (name : List Name) : Bool :=
  match builtinName name with
  | some name => !["current_schema", "current_database", "current_schemas", "current_user", "session_user"].contains name
  | none => false

mutual
  def uniformDefaultExpr (expr : Advanced.Expr) : Bool :=
    match expr with
    | .literal _ | .null | .decimal _ | .parameter _ | .column .. => true
    | .contextValue value => value == .systemUser
    | .collate .. => false
    | .cast arg target => target.name.scalarBase != .name && uniformDefaultExpr arg
    | .binary _ left right | .concat left right | .distinctFrom left right _
    | .pattern left right _ | .regex left right _ _ | .jsonAccess _ left right
    | .jsonExistence _ left right | .containment left right _ | .overlap left right
    | .quantifiedComparison _ _ left right | .nullIf left right
    | .filteredAggregate left right => uniformDefaultExpr left && uniformDefaultExpr right
    | .unary _ arg | .aggregate _ arg _ | .isNull arg _ | .extract _ arg => uniformDefaultExpr arg
    | .array args | .row args | .substring _ args | .coalesce args | .greatest args | .least args =>
      uniformDefaultExprs args
    | .call name args => defaultCollationFunction name && uniformDefaultExprs args
    | .namedCall name args => defaultCollationFunction name && uniformDefaultArguments args
    | .subscript base indices => uniformDefaultExpr base && uniformDefaultSubscripts indices
    | .caseExpr operand branches otherwise =>
      (match operand with | none => true | some value => uniformDefaultExpr value) &&
      uniformDefaultBranches branches &&
      (match otherwise with | none => true | some value => uniformDefaultExpr value)
    | .inList arg values => uniformDefaultExpr arg && uniformDefaultExprs values
    | .between arg lower upper _ => uniformDefaultExpr arg && uniformDefaultExpr lower && uniformDefaultExpr upper
    | .countAll => true
    | .inQuery .. | .quantifiedQuery .. | .exists _ | .scalarQuery _ => false
  termination_by sizeOf expr
  decreasing_by all_goals (simp_all <;> omega)

  def uniformDefaultExprs (exprs : List Advanced.Expr) : Bool :=
    match exprs with
    | [] => true
    | head :: tail => uniformDefaultExpr head && uniformDefaultExprs tail
  termination_by sizeOf exprs
  decreasing_by all_goals (simp_all <;> omega)

  def uniformDefaultArguments (args : List CallArgument) : Bool :=
    match args with
    | [] => true
    | .positional value :: tail | .named _ value _ :: tail =>
      uniformDefaultExpr value && uniformDefaultArguments tail
  termination_by sizeOf args
  decreasing_by all_goals (simp_all <;> omega)

  def uniformDefaultSubscripts (indices : List Subscript) : Bool :=
    match indices with
    | [] => true
    | .index value :: tail => uniformDefaultExpr value && uniformDefaultSubscripts tail
    | .slice lower upper :: tail =>
      (match lower with | none => true | some value => uniformDefaultExpr value) &&
      (match upper with | none => true | some value => uniformDefaultExpr value) && uniformDefaultSubscripts tail
  termination_by sizeOf indices
  decreasing_by all_goals (simp_all <;> omega)

  def uniformDefaultBranches (branches : List (Advanced.Expr × Advanced.Expr)) : Bool :=
    match branches with
    | [] => true
    | (condition, value) :: tail => uniformDefaultExpr condition && uniformDefaultExpr value && uniformDefaultBranches tail
  termination_by sizeOf branches
  decreasing_by all_goals (simp_all <;> omega)
end

/-- Unresolved external collatable namespaces are never assumed default. Local
WITH results and the recursive binding are safe only because their entire
closed defining expressions are checked by the same structural predicate. -/
def uniformDefaultRelation (catalog : Catalog) (env : CTEEnv) (target : Name)
    (locals : List Name) (name : Name) (schema : Option Name) : Bool :=
  if schema.isNone && (name == target || locals.contains name) then true
  else if schema.isNone && (env.lookup name).isSome then
    (env.lookup name).all fun binding => binding.output.all fun column => !column.type.base.collatable
  else
    (catalog.filter fun table => table.matchesReference name schema).all fun table =>
      table.columns.all fun column => (concreteType column.type).all fun type => !type.collatable

mutual
  def uniformDefaultQuery (catalog : Catalog) (env : CTEEnv) (target : Name)
      (locals : List Name) (query : Advanced.Query) : Bool :=
    let visible := query.ctes.map Advanced.CTE.name ++ locals
    uniformDefaultCTEs catalog env target (if query.recursive then visible else locals) query.ctes &&
    (match _bodyEq : query.body with
      | .select select =>
        (select.items.all fun item => match item with | .all .. => true | .expression expr _ => uniformDefaultExpr expr) &&
        (match _sourceEq : select.source with | none => true | some source => uniformDefaultSource catalog env target visible source) &&
        select.whereClause.all uniformDefaultExpr && uniformDefaultExprs select.groupBy &&
        select.having.all uniformDefaultExpr && uniformDefaultExprs select.distinctOn
      | .set _ _ left right => uniformDefaultQuery catalog env target visible left && uniformDefaultQuery catalog env target visible right) &&
    query.orderBy.all (fun order => uniformDefaultExpr order.expr) &&
    query.limit.all uniformDefaultExpr && query.offset.all uniformDefaultExpr
  termination_by sizeOf query
  decreasing_by all_goals (cases query <;> (try cases select) <;> simp_all <;> omega)

  def uniformDefaultSource (catalog : Catalog) (env : CTEEnv) (target : Name)
      (locals : List Name) (source : Advanced.From) : Bool :=
    match source with
    | .table name _ _ schema => uniformDefaultRelation catalog env target locals name schema
    | .derived query _ _ _ => uniformDefaultQuery catalog env target locals query
    | .join _ left right condition =>
      uniformDefaultSource catalog env target locals left && uniformDefaultSource catalog env target locals right &&
      (match condition with | .on expr => uniformDefaultExpr expr | _ => true)
  termination_by sizeOf source
  decreasing_by all_goals (simp_all <;> omega)

  def uniformDefaultCTEs (catalog : Catalog) (env : CTEEnv) (target : Name)
      (locals : List Name) (ctes : List Advanced.CTE) : Bool :=
    match ctes with
    | [] => true
    | head :: tail => uniformDefaultQuery catalog env target locals head.query &&
      uniformDefaultCTEs catalog env target (head.name :: locals) tail
  termination_by sizeOf ctes
  decreasing_by all_goals (cases head <;> simp_all <;> omega)
end

def RecursiveCollationSafe (catalog : Catalog) (params : ParameterEnv) (env : CTEEnv)
    (name : Name) (query : Advanced.Query) (output : List OutputColumn) : Prop :=
  output.all (fun column => !column.type.base.collatable) = true ∨
  (params.all (fun param => param.type.name.scalarBase != .name) = true ∧
    uniformDefaultQuery catalog env name [] query = true)

instance (catalog : Catalog) (params : ParameterEnv) (env : CTEEnv)
    (name : Name) (query : Advanced.Query) (output : List OutputColumn) :
    Decidable (RecursiveCollationSafe catalog params env name query output) :=
  inferInstanceAs (Decidable (_ ∨ (_ ∧ _)))

end SQLean.SelectContract
