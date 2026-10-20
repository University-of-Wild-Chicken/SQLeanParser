import SQLean.AdvancedPretty
import SQLean.RenderContract.Translation

/-! Structural parameter-serialization laws for all finite advanced SELECT ASTs.
These theorems do not assume a parser roundtrip, admissibility, static validity,
a resource budget, or a finite test corpus. They concern byte equality of the
fixed PostgreSQL parameter rendering, not query-execution semantics. -/
namespace SQLean.RenderContract
open Advanced

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private theorem append_congr {a b c d : String} (left : a = b) (right : c = d) :
    a ++ c = b ++ d := by rw [left, right]

mutual
  theorem exprSql_translated (pg : Bool) (expr : Advanced.Expr) :
      exprSql pg (translateExpr expr) = exprSql true expr := by
    cases expr with
    | literal value => cases value <;> simp only [translateExpr, exprSql]
    | null => simp only [translateExpr, exprSql]
    | decimal raw => simp only [translateExpr, exprSql]
    | parameter parameter => cases parameter <;> simp only [translateExpr, translateParameter, exprSql, ite_true]
    | column qualifier name => simp only [translateExpr, exprSql]
    | binary op left right => simp only [translateExpr, exprSql, exprSql_translated pg left, exprSql_translated pg right]
    | unary op arg => cases op <;> simp only [translateExpr, exprSql, exprSql_translated pg arg]
    | countAll => simp only [translateExpr, exprSql]
    | aggregate fn arg distinct => simp only [translateExpr, exprSql, exprSql_translated pg arg]
    | isNull arg negated => simp only [translateExpr, exprSql, exprSql_translated pg arg]
    | pattern arg pattern insensitive => simp only [translateExpr, exprSql, exprSql_translated pg arg, exprSql_translated pg pattern]
    | cast arg target => simp only [translateExpr, exprSql, exprSql_translated pg arg]
    | filteredAggregate aggregate predicate =>
        simp only [translateExpr, exprSql, exprSql_translated pg aggregate, exprSql_translated pg predicate]
    | inList arg values =>
        have mapped : values.map (fun value => exprSql pg (translateExpr value)) = values.map (exprSql true) :=
          List.map_congr_left fun value member =>
            have : sizeOf value < sizeOf values := List.sizeOf_lt_of_mem member
            exprSql_translated pg value
        simp only [translateExpr, exprSql, List.attach_map_val, List.map_map, Function.comp_def,
          exprSql_translated pg arg, mapped]
    | between arg lower upper negated =>
        simp only [translateExpr, exprSql, exprSql_translated pg arg, exprSql_translated pg lower, exprSql_translated pg upper]
    | inQuery arg query => simp only [translateExpr, exprSql, exprSql_translated pg arg, querySql_translated pg query]
    | «exists» query => simp only [translateExpr, exprSql, querySql_translated pg query]
    | scalarQuery query => simp only [translateExpr, exprSql, querySql_translated pg query]
  termination_by sizeOf expr
  decreasing_by all_goals (simp_all <;> omega)

  theorem itemSql_translated (pg : Bool) (item : Advanced.SelectItem) :
      itemSql pg (translateSelectItem item) = itemSql true item := by
    cases item with
    | all qualifier => simp only [translateSelectItem, itemSql]
    | expression expr alias => simp only [translateSelectItem, itemSql, exprSql_translated pg expr]
  termination_by sizeOf item
  decreasing_by all_goals (simp_all <;> omega)

  theorem sourceSql_translated (pg : Bool) (source : Advanced.From) :
      sourceSql pg (translateSource source) = sourceSql true source := by
    cases source with
    | table name alias columns => simp only [translateSource, sourceSql.eq_def]
    | derived query alias columns lateral =>
      rw [translateSource, sourceSql.eq_def]
      conv => rhs; rw [sourceSql.eq_def]
      simp only [querySql_translated pg query]
    | join kind left right condition =>
      rw [translateSource, sourceSql.eq_def]
      conv => rhs; rw [sourceSql.eq_def]
      cases condition with
      | none => simp only [translateJoinCondition, sourceSql_translated pg left, sourceSql_translated pg right]
      | natural => simp only [translateJoinCondition, sourceSql_translated pg left, sourceSql_translated pg right]
      | «using» names => simp only [translateJoinCondition, sourceSql_translated pg left, sourceSql_translated pg right]
      | on expr => simp only [translateJoinCondition, sourceSql_translated pg left,
          sourceSql_translated pg right, exprSql_translated pg expr]
  termination_by sizeOf source
  decreasing_by all_goals (simp_all <;> omega)

  theorem selectSql_translated (pg : Bool) (select : Advanced.Select) :
      selectSql pg (translateSelect select) = selectSql true select := by
    cases select with
    | mk items source whereClause groupBy having distinct distinctOn =>
      have itemsEq : items.map (fun item => itemSql pg (translateSelectItem item)) = items.map (itemSql true) :=
        List.map_congr_left fun item member =>
          have : sizeOf item < sizeOf items := List.sizeOf_lt_of_mem member
          itemSql_translated pg item
      have groupsEq : groupBy.map (fun expr => exprSql pg (translateExpr expr)) = groupBy.map (exprSql true) :=
        List.map_congr_left fun expr member =>
          have : sizeOf expr < sizeOf groupBy := List.sizeOf_lt_of_mem member
          exprSql_translated pg expr
      have distinctEq : distinctOn.map (fun expr => exprSql pg (translateExpr expr)) = distinctOn.map (exprSql true) :=
        List.map_congr_left fun expr member =>
          have : sizeOf expr < sizeOf distinctOn := List.sizeOf_lt_of_mem member
          exprSql_translated pg expr
      have sourceEq :
          (match _h : (match _h : source with | none => none | some value => some (translateSource value)) with
           | none => "" | some value => " FROM " ++ sourceSql pg value) =
          (match _h : source with | none => "" | some value => " FROM " ++ sourceSql true value) := by
        cases source with
        | none => rfl
        | some value => simp only [sourceSql_translated pg value]
      have whereEq :
          (match _h : (match _h : whereClause with | none => none | some value => some (translateExpr value)) with
           | none => "" | some value => " WHERE " ++ exprSql pg value) =
          (match _h : whereClause with | none => "" | some value => " WHERE " ++ exprSql true value) := by
        cases whereClause with
        | none => rfl
        | some value => simp only [exprSql_translated pg value]
      have havingEq :
          (match _h : (match _h : having with | none => none | some value => some (translateExpr value)) with
           | none => "" | some value => " HAVING " ++ exprSql pg value) =
          (match _h : having with | none => "" | some value => " HAVING " ++ exprSql true value) := by
        cases having with
        | none => rfl
        | some value => simp only [exprSql_translated pg value]
      rw [translateSelect, selectSql]
      conv => rhs; rw [selectSql]
      simp only [List.attach_map_val, List.map_map, Function.comp_def, List.isEmpty_map,
        itemsEq, groupsEq, distinctEq]
      apply append_congr
      · apply append_congr
        · apply append_congr
          · apply append_congr
            · rfl
            · exact sourceEq
          · exact whereEq
        · rfl
      · exact havingEq
  termination_by sizeOf select
  decreasing_by all_goals (simp_all <;> omega)

  theorem querySql_translated (pg : Bool) (query : Advanced.Query) :
      querySql pg (translateParameters query) = querySql true query := by
    cases query with
    | mk body ctes recursive orderBy limit offset =>
      rw [translateParameters]
      simp only [List.attach_map_val]
      rw [querySql]
      conv => rhs; rw [querySql]
      simp only [List.attach_map, List.map_map, Function.comp_def, List.isEmpty_map,
        translateCTE, translateOrderBy]
      congr 3
      · congr 1
        · split
          · rfl
          · congr 3
            apply List.map_congr_left
            intro cte _member
            have : sizeOf cte.val < sizeOf ctes := List.sizeOf_lt_of_mem cte.property
            have : sizeOf cte.val.query < sizeOf cte.val := by cases cte.val; simp; omega
            simp only [querySql_translated pg cte.val.query]
        · cases body with
          | select select =>
            rw [translateQueryBody]
            exact selectSql_translated pg select
          | set op all left right =>
            rw [translateQueryBody]
            simp only [querySql_translated pg left, querySql_translated pg right]
      · split
        · rfl
        · congr 2
          apply List.map_congr_left
          intro order _member
          have : sizeOf order.val < sizeOf orderBy := List.sizeOf_lt_of_mem order.property
          have : sizeOf order.val.expr < sizeOf order.val := by cases order.val; simp; omega
          simp only [exprSql_translated pg order.val.expr]
  termination_by sizeOf query
  decreasing_by all_goals (simp_all <;> omega)
end

/-- PostgreSQL serialization is unchanged by the explicit parameter-only AST
translation, for every finite query. -/
theorem renderPostgres_translateParameters (query : Advanced.Query) :
    Advanced.renderPostgres (.query (translateParameters query)) = Advanced.renderPostgres (.query query) := by
  change querySql true (translateParameters query) ++ ";" = querySql true query ++ ";"
  rw [querySql_translated true query]

/-- Rendering the translated AST in identity mode produces exactly the bytes
of PostgreSQL rendering of the original AST. -/
theorem render_translated_eq_renderPostgres (query : Advanced.Query) :
    Advanced.render (.query (translateParameters query)) = Advanced.renderPostgres (.query query) := by
  change querySql false (translateParameters query) ++ ";" = querySql true query ++ ";"
  rw [querySql_translated false query]

/-- The query-level law applies equally inside CTEs, subqueries and compounds,
where the serializer does not add a statement terminator. -/
theorem query_toSql_translation (query : Advanced.Query) (mode : Bool) :
    (translateParameters query).toSql mode = query.toSql true :=
  querySql_translated mode query

theorem expr_toSql_translation (expr : Advanced.Expr) (mode : Bool) :
    (translateExpr expr).toSql mode = expr.toSql true :=
  exprSql_translated mode expr

end SQLean.RenderContract
