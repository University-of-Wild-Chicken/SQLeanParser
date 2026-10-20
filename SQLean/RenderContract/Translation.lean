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
    | .decimal raw => .decimal raw
    | .parameter parameter => .parameter (translateParameter parameter)
    | .column qualifier name => .column qualifier name
    | .binary op left right => .binary op (translateExpr left) (translateExpr right)
    | .unary op arg => .unary op (translateExpr arg)
    | .countAll => .countAll
    | .aggregate fn arg distinct => .aggregate fn (translateExpr arg) distinct
    | .isNull arg negated => .isNull (translateExpr arg) negated
    | .pattern arg pattern insensitive => .pattern (translateExpr arg) (translateExpr pattern) insensitive
    | .cast arg target => .cast (translateExpr arg) target
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

  def translateSelectItem (item : Advanced.SelectItem) : Advanced.SelectItem :=
    match item with
    | .all qualifier => .all qualifier
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
    | .table name alias columns => .table name alias columns
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
  literal contents, modifiers, join conditions and all flags are preserved. -/
  def translateParameters (query : Advanced.Query) : Advanced.Query :=
    { query with
      body := translateQueryBody query.body
      ctes := query.ctes.attach.map fun (cte : {c : Advanced.CTE // c ∈ query.ctes}) =>
        have : sizeOf cte.val < sizeOf query.ctes := List.sizeOf_lt_of_mem cte.property
        translateCTE cte.val
      orderBy := query.orderBy.attach.map fun (order : {o : Advanced.OrderBy // o ∈ query.orderBy}) =>
        have : sizeOf order.val < sizeOf query.orderBy := List.sizeOf_lt_of_mem order.property
        translateOrderBy order.val }
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

end SQLean.RenderContract
