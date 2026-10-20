import SQLean.RenderContract.Translation

/-! General structural laws for the explicit parameter-only AST transformation.
These theorems quantify over every finite advanced AST, independently of parser,
renderer, resource budgets, static validity, or generated examples. -/
namespace SQLean.RenderContract
open Advanced

private theorem map_twice (f : α → α) (xs : List α)
    (element : ∀ x ∈ xs, f (f x) = f x) : (xs.map f).map f = xs.map f := by
  rw [List.map_map]
  exact List.map_congr_left element

@[simp] theorem translateParameter_idempotent (parameter : Parameter) :
    translateParameter (translateParameter parameter) = translateParameter parameter := by
  cases parameter <;> rfl

mutual
  theorem translateExpr_idempotent (expr : Advanced.Expr) :
      translateExpr (translateExpr expr) = translateExpr expr := by
    cases expr with
    | literal value => simp only [translateExpr]
    | null => simp only [translateExpr]
    | contextValue value => simp only [translateExpr]
    | decimal raw => simp only [translateExpr]
    | parameter parameter => simp only [translateExpr, translateParameter_idempotent]
    | column qualifier name schema => simp only [translateExpr]
    | binary op left right => simp only [translateExpr, translateExpr_idempotent left, translateExpr_idempotent right]
    | concat left right => simp only [translateExpr, translateExpr_idempotent left, translateExpr_idempotent right]
    | quantifiedComparison op quantifier left right =>
        simp only [translateExpr, translateExpr_idempotent left, translateExpr_idempotent right]
    | unary op arg => simp only [translateExpr, translateExpr_idempotent arg]
    | countAll => simp only [translateExpr]
    | aggregate fn arg distinct => simp only [translateExpr, translateExpr_idempotent arg]
    | isNull arg negated => simp only [translateExpr, translateExpr_idempotent arg]
    | pattern arg pattern insensitive => simp only [translateExpr, translateExpr_idempotent arg, translateExpr_idempotent pattern]
    | regex arg pattern insensitive negated =>
        simp only [translateExpr, translateExpr_idempotent arg, translateExpr_idempotent pattern]
    | jsonAccess op arg key =>
        simp only [translateExpr, translateExpr_idempotent arg, translateExpr_idempotent key]
    | jsonExistence op arg key =>
        simp only [translateExpr, translateExpr_idempotent arg, translateExpr_idempotent key]
    | distinctFrom left right negated =>
        simp only [translateExpr, translateExpr_idempotent left, translateExpr_idempotent right]
    | containment left right containedBy =>
        simp only [translateExpr, translateExpr_idempotent left, translateExpr_idempotent right]
    | overlap left right =>
        simp only [translateExpr, translateExpr_idempotent left, translateExpr_idempotent right]
    | extract field arg => simp only [translateExpr, translateExpr_idempotent arg]
    | cast arg target => simp only [translateExpr, translateExpr_idempotent arg]
    | collate arg name => simp only [translateExpr, translateExpr_idempotent arg]
    | subscript base subscripts =>
        simp only [translateExpr, List.attach_map_val, translateExpr_idempotent base]
        congr 1
        exact map_twice translateSubscript subscripts fun subscript member =>
          have : sizeOf subscript < sizeOf subscripts := List.sizeOf_lt_of_mem member
          translateSubscript_idempotent subscript
    | array elements =>
        simp only [translateExpr, List.attach_map_val]
        congr 1
        exact map_twice translateExpr elements fun element member =>
          have : sizeOf element < sizeOf elements := List.sizeOf_lt_of_mem member
          translateExpr_idempotent element
    | row elements =>
        simp only [translateExpr, List.attach_map_val]
        congr 1
        exact map_twice translateExpr elements fun element member =>
          have : sizeOf element < sizeOf elements := List.sizeOf_lt_of_mem member
          translateExpr_idempotent element
    | substring form args =>
        simp only [translateExpr, List.attach_map_val]
        congr 1
        exact map_twice translateExpr args fun arg member =>
          have : sizeOf arg < sizeOf args := List.sizeOf_lt_of_mem member
          translateExpr_idempotent arg
    | call name args =>
        simp only [translateExpr, List.attach_map_val]
        congr 1
        exact map_twice translateExpr args fun arg member =>
          have : sizeOf arg < sizeOf args := List.sizeOf_lt_of_mem member
          translateExpr_idempotent arg
    | namedCall name args =>
        simp only [translateExpr, List.attach_map_val]
        congr 1
        exact map_twice translateCallArgument args fun arg member =>
          have : sizeOf arg < sizeOf args := List.sizeOf_lt_of_mem member
          translateCallArgument_idempotent arg
    | coalesce args =>
        simp only [translateExpr, List.attach_map_val]
        congr 1
        exact map_twice translateExpr args fun arg member =>
          have : sizeOf arg < sizeOf args := List.sizeOf_lt_of_mem member
          translateExpr_idempotent arg
    | greatest args =>
        simp only [translateExpr, List.attach_map_val]
        congr 1
        exact map_twice translateExpr args fun arg member =>
          have : sizeOf arg < sizeOf args := List.sizeOf_lt_of_mem member
          translateExpr_idempotent arg
    | least args =>
        simp only [translateExpr, List.attach_map_val]
        congr 1
        exact map_twice translateExpr args fun arg member =>
          have : sizeOf arg < sizeOf args := List.sizeOf_lt_of_mem member
          translateExpr_idempotent arg
    | nullIf left right =>
        simp only [translateExpr, translateExpr_idempotent left, translateExpr_idempotent right]
    | caseExpr operand branches otherwise =>
        conv => lhs; arg 1; rw [translateExpr.eq_def]
        conv => lhs; rw [translateExpr.eq_def]
        conv => rhs; rw [translateExpr.eq_def]
        simp only [List.attach_map_val (f := fun pair : Advanced.Expr × Advanced.Expr =>
          (translateExpr pair.1, translateExpr pair.2)), Advanced.Expr.caseExpr.injEq]
        refine ⟨?_, ?_, ?_⟩
        · cases operand with
          | none => rfl
          | some arg => simp only [translateExpr_idempotent arg]
        · exact map_twice
            (fun pair : Advanced.Expr × Advanced.Expr => (translateExpr pair.1, translateExpr pair.2))
            branches fun pair member => by
              have : sizeOf pair < sizeOf branches := List.sizeOf_lt_of_mem member
              have : sizeOf pair.1 < sizeOf pair := by cases pair; simp; omega
              have : sizeOf pair.2 < sizeOf pair := by cases pair; simp; omega
              simp only [translateExpr_idempotent pair.1, translateExpr_idempotent pair.2]
        · cases otherwise with
          | none => rfl
          | some arg => simp only [translateExpr_idempotent arg]
    | filteredAggregate aggregate predicate => simp only [translateExpr, translateExpr_idempotent aggregate, translateExpr_idempotent predicate]
    | inList arg values =>
        simp only [translateExpr, List.attach_map_val, translateExpr_idempotent arg]
        congr 1
        exact map_twice translateExpr values fun value member =>
          have : sizeOf value < sizeOf values := List.sizeOf_lt_of_mem member
          translateExpr_idempotent value
    | between arg lower upper negated =>
        simp only [translateExpr, translateExpr_idempotent arg, translateExpr_idempotent lower, translateExpr_idempotent upper]
    | inQuery arg query => simp only [translateExpr, translateExpr_idempotent arg, translateParameters_idempotent query]
    | «exists» query => simp only [translateExpr, translateParameters_idempotent query]
    | scalarQuery query => simp only [translateExpr, translateParameters_idempotent query]
  termination_by sizeOf expr
  decreasing_by all_goals (simp_all <;> omega)

  theorem translateCallArgument_idempotent (arg : CallArgument) :
      translateCallArgument (translateCallArgument arg) = translateCallArgument arg := by
    cases arg with
    | positional value => simp only [translateCallArgument, translateExpr_idempotent value]
    | named name value spelling => simp only [translateCallArgument, translateExpr_idempotent value]
  termination_by sizeOf arg
  decreasing_by all_goals (simp_all <;> omega)

  theorem translateSubscript_idempotent (subscript : Advanced.Subscript) :
      translateSubscript (translateSubscript subscript) = translateSubscript subscript := by
    cases subscript with
    | index expr => simp only [translateSubscript, translateExpr_idempotent expr]
    | slice lower upper =>
        cases lower with
        | none =>
            cases upper with
            | none => simp only [translateSubscript]
            | some expr => simp only [translateSubscript, translateExpr_idempotent expr]
        | some expr =>
            cases upper with
            | none => simp only [translateSubscript, translateExpr_idempotent expr]
            | some other =>
                simp only [translateSubscript, translateExpr_idempotent expr, translateExpr_idempotent other]
  termination_by sizeOf subscript
  decreasing_by all_goals (simp_all <;> omega)

  theorem translateSelectItem_idempotent (item : Advanced.SelectItem) :
      translateSelectItem (translateSelectItem item) = translateSelectItem item := by
    cases item with
    | all qualifier schema => simp only [translateSelectItem]
    | expression expr alias => simp only [translateSelectItem, translateExpr_idempotent expr]
  termination_by sizeOf item
  decreasing_by all_goals (simp_all <;> omega)

  theorem translateOrderBy_idempotent (order : Advanced.OrderBy) :
      translateOrderBy (translateOrderBy order) = translateOrderBy order := by
    cases order with
    | mk expr descending nullsFirst => simp only [translateOrderBy, translateExpr_idempotent expr]
  termination_by sizeOf order
  decreasing_by all_goals (simp_all <;> omega)

  theorem translateJoinCondition_idempotent (condition : Advanced.JoinCondition) :
      translateJoinCondition (translateJoinCondition condition) = translateJoinCondition condition := by
    cases condition with
    | none => simp only [translateJoinCondition]
    | natural => simp only [translateJoinCondition]
    | «using» names => simp only [translateJoinCondition]
    | on expr => simp only [translateJoinCondition, translateExpr_idempotent expr]
  termination_by sizeOf condition
  decreasing_by all_goals (simp_all <;> omega)

  theorem translateSource_idempotent (source : Advanced.From) :
      translateSource (translateSource source) = translateSource source := by
    cases source with
    | table name alias columns schema => simp only [translateSource]
    | derived query alias columns lateral => simp only [translateSource, translateParameters_idempotent query]
    | join kind left right condition =>
        simp only [translateSource, translateSource_idempotent left, translateSource_idempotent right,
          translateJoinCondition_idempotent condition]
  termination_by sizeOf source
  decreasing_by all_goals (simp_all <;> omega)

  theorem translateSelect_idempotent (select : Advanced.Select) :
      translateSelect (translateSelect select) = translateSelect select := by
    cases select with
    | mk items source whereClause groupBy having distinct distinctOn =>
      simp only [translateSelect, List.attach_map_val, Advanced.Select.mk.injEq]
      refine ⟨?_, ?_, ?_, ?_, ?_, True.intro, ?_⟩
      · exact map_twice translateSelectItem items fun item member =>
          have : sizeOf item < sizeOf items := List.sizeOf_lt_of_mem member
          translateSelectItem_idempotent item
      · cases source with
        | none => rfl
        | some source => simp only [translateSource_idempotent source]
      · cases whereClause with
        | none => rfl
        | some expr => simp only [translateExpr_idempotent expr]
      · exact map_twice translateExpr groupBy fun expr member =>
          have : sizeOf expr < sizeOf groupBy := List.sizeOf_lt_of_mem member
          translateExpr_idempotent expr
      · cases having with
        | none => rfl
        | some expr => simp only [translateExpr_idempotent expr]
      · exact map_twice translateExpr distinctOn fun expr member =>
          have : sizeOf expr < sizeOf distinctOn := List.sizeOf_lt_of_mem member
          translateExpr_idempotent expr
  termination_by sizeOf select
  decreasing_by all_goals (simp_all <;> omega)

  theorem translateQueryBody_idempotent (body : Advanced.QueryBody) :
      translateQueryBody (translateQueryBody body) = translateQueryBody body := by
    cases body with
    | select select => simp only [translateQueryBody, translateSelect_idempotent select]
    | set op all left right => simp only [translateQueryBody, translateParameters_idempotent left, translateParameters_idempotent right]
  termination_by sizeOf body
  decreasing_by all_goals (simp_all <;> omega)

  /-- Translating to numbered PostgreSQL parameters twice changes no additional
  fields. This holds for all finite queries, not just admissible inputs. -/
  theorem translateParameters_idempotent (query : Advanced.Query) :
      translateParameters (translateParameters query) = translateParameters query := by
    cases query with
    | mk body ctes recursive orderBy limit offset locking offsetFirst =>
      simp only [translateParameters, List.attach_map_val, Advanced.Query.mk.injEq, translateQueryBody_idempotent body]
      refine ⟨True.intro, ?_, True.intro, ?_, ?_, ?_, True.intro, True.intro⟩
      · exact map_twice translateCTE ctes fun cte member =>
          have : sizeOf cte < sizeOf ctes := List.sizeOf_lt_of_mem member
          translateCTE_idempotent cte
      · exact map_twice translateOrderBy orderBy fun order member =>
          have : sizeOf order < sizeOf orderBy := List.sizeOf_lt_of_mem member
          translateOrderBy_idempotent order
      · cases limit with
        | none => rfl
        | some expr => simp only [translateExpr_idempotent expr]
      · cases offset with
        | none => rfl
        | some expr => simp only [translateExpr_idempotent expr]
  termination_by sizeOf query
  decreasing_by all_goals (simp_all <;> omega)

  theorem translateCTE_idempotent (cte : Advanced.CTE) :
      translateCTE (translateCTE cte) = translateCTE cte := by
    cases cte with
    | mk name query columns => simp only [translateCTE, translateParameters_idempotent query]
  termination_by sizeOf cte
  decreasing_by all_goals (simp_all <;> omega)
end

end SQLean.RenderContract
