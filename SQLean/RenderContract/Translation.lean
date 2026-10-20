import SQLean.AdvancedSyntax

/-! The explicit PostgreSQL parameter translation for renderer contract v0.1.
Every non-parameter AST field is retained verbatim. This total transformation
has no dependency on either a parser or a renderer. The admissibility boundary
separately requires one unmixed parameter style and valid occurrence identities;
applying this function alone does not establish those requirements. -/
namespace SQLean.RenderContract
open Advanced

/-- The fixed target slot is the logical input index. Numbered references keep
identity; anonymous occurrence i becomes numbered slot i. -/
def translateParameter : Advanced.Parameter → Advanced.Parameter
  | .numbered index => .numbered index
  | .anonymous ordinal => .numbered ordinal

mutual
  def translateExpr (expr : Advanced.Expr) : Advanced.Expr :=
    match expr with
    | .literal value => .literal value
    | .null => .null
    | .contextValue value => .contextValue value
    | .decimal raw => .decimal raw
    | .parameter parameter => .parameter (translateParameter parameter)
    | .column qualifier name schema => .column qualifier name schema
    | .binary op left right => .binary op (translateExpr left) (translateExpr right)
    | .concat left right => .concat (translateExpr left) (translateExpr right)
    | .quantifiedComparison op quantifier left right =>
        .quantifiedComparison op quantifier (translateExpr left) (translateExpr right)
    | .unary op arg => .unary op (translateExpr arg)
    | .countAll => .countAll
    | .aggregate fn arg distinct => .aggregate fn (translateExpr arg) distinct
    | .isNull arg negated => .isNull (translateExpr arg) negated
    | .pattern arg pattern insensitive => .pattern (translateExpr arg) (translateExpr pattern) insensitive
    | .regex arg pattern insensitive negated =>
        .regex (translateExpr arg) (translateExpr pattern) insensitive negated
    | .jsonAccess op arg key => .jsonAccess op (translateExpr arg) (translateExpr key)
    | .jsonExistence op arg key => .jsonExistence op (translateExpr arg) (translateExpr key)
    | .containment left right containedBy =>
        .containment (translateExpr left) (translateExpr right) containedBy
    | .overlap left right => .overlap (translateExpr left) (translateExpr right)
    | .extract field arg => .extract field (translateExpr arg)
    | .cast arg target => .cast (translateExpr arg) target
    | .subscript base subscripts => .subscript (translateExpr base)
        (subscripts.attach.map fun (subscript : {s : Subscript // s ∈ subscripts}) =>
          have : sizeOf subscript.val < sizeOf subscripts := List.sizeOf_lt_of_mem subscript.property
          translateSubscript subscript.val)
    | .array elements => .array
        (elements.attach.map fun (element : {v : Advanced.Expr // v ∈ elements}) =>
          have : sizeOf element.val < sizeOf elements := List.sizeOf_lt_of_mem element.property
          translateExpr element.val)
    | .row elements => .row
        (elements.attach.map fun (element : {v : Advanced.Expr // v ∈ elements}) =>
          have : sizeOf element.val < sizeOf elements := List.sizeOf_lt_of_mem element.property
          translateExpr element.val)
    | .substring form args => .substring form
        (args.attach.map fun (arg : {v : Advanced.Expr // v ∈ args}) =>
          have : sizeOf arg.val < sizeOf args := List.sizeOf_lt_of_mem arg.property
          translateExpr arg.val)
    | .call name args => .call name
        (args.attach.map fun (arg : {v : Advanced.Expr // v ∈ args}) =>
          have : sizeOf arg.val < sizeOf args := List.sizeOf_lt_of_mem arg.property
          translateExpr arg.val)
    | .coalesce args => .coalesce
        (args.attach.map fun (arg : {v : Advanced.Expr // v ∈ args}) =>
          have : sizeOf arg.val < sizeOf args := List.sizeOf_lt_of_mem arg.property
          translateExpr arg.val)
    | .greatest args => .greatest
        (args.attach.map fun (arg : {v : Advanced.Expr // v ∈ args}) =>
          have : sizeOf arg.val < sizeOf args := List.sizeOf_lt_of_mem arg.property
          translateExpr arg.val)
    | .least args => .least
        (args.attach.map fun (arg : {v : Advanced.Expr // v ∈ args}) =>
          have : sizeOf arg.val < sizeOf args := List.sizeOf_lt_of_mem arg.property
          translateExpr arg.val)
    | .nullIf left right => .nullIf (translateExpr left) (translateExpr right)
    | .caseExpr operand branches otherwise => .caseExpr
        (match _h : operand with | none => none | some arg => some (translateExpr arg))
        (branches.attach.map fun (branch : {b : Advanced.Expr × Advanced.Expr // b ∈ branches}) =>
          have : sizeOf branch.val < sizeOf branches := List.sizeOf_lt_of_mem branch.property
          have : sizeOf branch.val.1 < sizeOf branch.val := by cases branch.val; simp; omega
          have : sizeOf branch.val.2 < sizeOf branch.val := by cases branch.val; simp; omega
          (translateExpr branch.val.1, translateExpr branch.val.2))
        (match _h : otherwise with | none => none | some arg => some (translateExpr arg))
    | .filteredAggregate aggregate predicate => .filteredAggregate (translateExpr aggregate) (translateExpr predicate)
    | .inList arg values => .inList (translateExpr arg)
        (values.attach.map fun (value : {v : Advanced.Expr // v ∈ values}) =>
          have : sizeOf value.val < sizeOf values := List.sizeOf_lt_of_mem value.property
          translateExpr value.val)
    | .between arg lower upper negated => .between (translateExpr arg) (translateExpr lower) (translateExpr upper) negated
    | .inQuery arg query => .inQuery (translateExpr arg) (translateParameters query)
    | .exists query => .exists (translateParameters query)
    | .scalarQuery query => .scalarQuery (translateParameters query)
  termination_by sizeOf expr
  decreasing_by all_goals (simp_all <;> omega)

  def translateSubscript (subscript : Advanced.Subscript) : Advanced.Subscript :=
    match subscript with
    | .index expr => .index (translateExpr expr)
    | .slice lower upper => .slice
        (match _h : lower with | none => none | some expr => some (translateExpr expr))
        (match _h : upper with | none => none | some expr => some (translateExpr expr))
  termination_by sizeOf subscript
  decreasing_by all_goals (simp_all <;> omega)

  def translateSelectItem (item : Advanced.SelectItem) : Advanced.SelectItem :=
    match item with
    | .all qualifier schema => .all qualifier schema
    | .expression expr alias => .expression (translateExpr expr) alias
  termination_by sizeOf item
  decreasing_by all_goals (simp_all <;> omega)

  def translateOrderBy (order : Advanced.OrderBy) : Advanced.OrderBy :=
    { order with expr := translateExpr order.expr }
  termination_by sizeOf order
  decreasing_by all_goals cases order; simp_all; omega

  def translateJoinCondition (condition : Advanced.JoinCondition) : Advanced.JoinCondition :=
    match condition with
    | .none => .none
    | .on expr => .on (translateExpr expr)
    | .using columns => .using columns
    | .natural => .natural
  termination_by sizeOf condition
  decreasing_by all_goals (simp_all <;> omega)

  def translateSource (source : Advanced.From) : Advanced.From :=
    match source with
    | .table name alias columns schema => .table name alias columns schema
    | .derived query alias columns lateral => .derived (translateParameters query) alias columns lateral
    | .join kind left right condition =>
        .join kind (translateSource left) (translateSource right) (translateJoinCondition condition)
  termination_by sizeOf source
  decreasing_by all_goals (simp_all <;> omega)

  def translateSelect (select : Advanced.Select) : Advanced.Select :=
    { select with
      items := select.items.attach.map fun (item : {i : Advanced.SelectItem // i ∈ select.items}) =>
        have : sizeOf item.val < sizeOf select.items := List.sizeOf_lt_of_mem item.property
        translateSelectItem item.val
      source := match _h : select.source with | none => none | some source => some (translateSource source)
      whereClause := match _h : select.whereClause with | none => none | some expr => some (translateExpr expr)
      groupBy := select.groupBy.attach.map fun (expr : {e : Advanced.Expr // e ∈ select.groupBy}) =>
        have : sizeOf expr.val < sizeOf select.groupBy := List.sizeOf_lt_of_mem expr.property
        translateExpr expr.val
      having := match _h : select.having with | none => none | some expr => some (translateExpr expr)
      distinctOn := select.distinctOn.attach.map fun (expr : {e : Advanced.Expr // e ∈ select.distinctOn}) =>
        have : sizeOf expr.val < sizeOf select.distinctOn := List.sizeOf_lt_of_mem expr.property
        translateExpr expr.val }
  termination_by sizeOf select
  decreasing_by all_goals cases select; simp_all; omega

  def translateQueryBody (body : Advanced.QueryBody) : Advanced.QueryBody :=
    match body with
    | .select select => .select (translateSelect select)
    | .set op all left right => .set op all (translateParameters left) (translateParameters right)
  termination_by sizeOf body
  decreasing_by all_goals (simp_all <;> omega)

  /-- Parameter-only AST translation. CTE order, nested query ownership, aliases,
  literal contents, modifiers, join conditions, locking clauses and all flags
  are preserved. Lock targets contain no parameter occurrences. -/
  def translateParameters (query : Advanced.Query) : Advanced.Query :=
    { query with
      body := translateQueryBody query.body
      ctes := query.ctes.attach.map fun (cte : {c : Advanced.CTE // c ∈ query.ctes}) =>
        have : sizeOf cte.val < sizeOf query.ctes := List.sizeOf_lt_of_mem cte.property
        translateCTE cte.val
      orderBy := query.orderBy.attach.map fun (order : {o : Advanced.OrderBy // o ∈ query.orderBy}) =>
        have : sizeOf order.val < sizeOf query.orderBy := List.sizeOf_lt_of_mem order.property
        translateOrderBy order.val
      limit := match _h : query.limit with | none => none | some expr => some (translateExpr expr)
      offset := match _h : query.offset with | none => none | some expr => some (translateExpr expr)
      locking := query.locking
      offsetFirst := query.offsetFirst }
  termination_by sizeOf query
  decreasing_by all_goals cases query; simp_all; omega

  def translateCTE (cte : Advanced.CTE) : Advanced.CTE :=
    { cte with query := translateParameters cte.query }
  termination_by sizeOf cte
  decreasing_by all_goals cases cte; simp_all; omega
end

@[simp] theorem translateParameter_numbered (index : Nat) :
    translateParameter (.numbered index) = .numbered index := rfl

@[simp] theorem translateParameter_anonymous (ordinal : Nat) :
    translateParameter (.anonymous ordinal) = .numbered ordinal := rfl

/-- Lock strengths, target order, duplicate targets, and wait policies are
retained exactly by parameter translation, independently of admissibility. -/
@[simp] theorem translateParameters_locking (query : Advanced.Query) :
    (translateParameters query).locking = query.locking := by
  rw [translateParameters]

@[simp] theorem translateParameters_offsetFirst (query : Advanced.Query) :
    (translateParameters query).offsetFirst = query.offsetFirst := by
  rw [translateParameters]

end SQLean.RenderContract
