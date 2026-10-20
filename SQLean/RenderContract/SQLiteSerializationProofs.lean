import SQLean.SQLitePretty
import SQLean.RenderContract.Translation

/-! General byte-preservation laws for SQLite's native numbered-slot renderer.
They hold for every finite AST; they do not establish that unsupported query
shapes belong to the checked SQLite profile or have SQLite execution semantics. -/
namespace SQLean.RenderContract.SQLite
open Advanced

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private theorem append_congr {a b c d : String} (left : a = b) (right : c = d) :
    a ++ c = b ++ d := by rw [left, right]

mutual
  theorem exprSql_translated (expr : Advanced.Expr) :
      Advanced.SQLite.exprSql (translateExpr expr) = Advanced.SQLite.exprSql expr := by
    cases expr with
    | literal value => cases value <;> simp only [translateExpr, Advanced.SQLite.exprSql]
    | null => simp only [translateExpr, Advanced.SQLite.exprSql]
    | decimal raw => simp only [translateExpr, Advanced.SQLite.exprSql]
    | parameter parameter => cases parameter <;> simp only [translateExpr, translateParameter, Advanced.SQLite.exprSql]
    | column qualifier name => simp only [translateExpr, Advanced.SQLite.exprSql]
    | binary op left right => simp only [translateExpr, Advanced.SQLite.exprSql, exprSql_translated left, exprSql_translated right]
    | unary op arg => cases op <;> simp only [translateExpr, Advanced.SQLite.exprSql, exprSql_translated arg]
    | countAll => simp only [translateExpr, Advanced.SQLite.exprSql]
    | aggregate fn arg distinct => simp only [translateExpr, Advanced.SQLite.exprSql, exprSql_translated arg]
    | isNull arg negated => simp only [translateExpr, Advanced.SQLite.exprSql, exprSql_translated arg]
    | pattern arg pattern insensitive => simp only [translateExpr, Advanced.SQLite.exprSql, exprSql_translated arg, exprSql_translated pattern]
    | cast arg target => simp only [translateExpr, Advanced.SQLite.exprSql, exprSql_translated arg]
    | filteredAggregate aggregate predicate =>
        simp only [translateExpr, Advanced.SQLite.exprSql, exprSql_translated aggregate, exprSql_translated predicate]
    | inList arg values =>
        have mapped : values.map (fun value => Advanced.SQLite.exprSql (translateExpr value)) = values.map (Advanced.SQLite.exprSql) :=
          List.map_congr_left fun value member =>
            have : sizeOf value < sizeOf values := List.sizeOf_lt_of_mem member
            exprSql_translated value
        simp only [translateExpr, Advanced.SQLite.exprSql, List.attach_map_val, List.map_map, Function.comp_def,
          exprSql_translated arg, mapped]
    | between arg lower upper negated =>
        simp only [translateExpr, Advanced.SQLite.exprSql, exprSql_translated arg, exprSql_translated lower, exprSql_translated upper]
    | inQuery arg query => simp only [translateExpr, Advanced.SQLite.exprSql, exprSql_translated arg, querySql_translated query]
    | «exists» query => simp only [translateExpr, Advanced.SQLite.exprSql, querySql_translated query]
    | scalarQuery query => simp only [translateExpr, Advanced.SQLite.exprSql, querySql_translated query]
  termination_by sizeOf expr
  decreasing_by all_goals (simp_all <;> omega)

  theorem itemSql_translated (item : Advanced.SelectItem) :
      Advanced.SQLite.itemSql (translateSelectItem item) = Advanced.SQLite.itemSql item := by
    cases item with
    | all qualifier => simp only [translateSelectItem, Advanced.SQLite.itemSql]
    | expression expr alias => simp only [translateSelectItem, Advanced.SQLite.itemSql, exprSql_translated expr]
  termination_by sizeOf item
  decreasing_by all_goals (simp_all <;> omega)

  theorem sourceSql_translated (source : Advanced.From) :
      Advanced.SQLite.sourceSql (translateSource source) = Advanced.SQLite.sourceSql source := by
    cases source with
    | table name alias columns => simp only [translateSource, Advanced.SQLite.sourceSql.eq_def]
    | derived query alias columns lateral =>
      rw [translateSource, Advanced.SQLite.sourceSql.eq_def]
      conv => rhs; rw [Advanced.SQLite.sourceSql.eq_def]
      simp only [querySql_translated query]
    | join kind left right condition =>
      rw [translateSource, Advanced.SQLite.sourceSql.eq_def]
      conv => rhs; rw [Advanced.SQLite.sourceSql.eq_def]
      cases condition with
      | none => simp only [translateJoinCondition, sourceSql_translated left, sourceSql_translated right]
      | natural => simp only [translateJoinCondition, sourceSql_translated left, sourceSql_translated right]
      | «using» names => simp only [translateJoinCondition, sourceSql_translated left, sourceSql_translated right]
      | on expr => simp only [translateJoinCondition, sourceSql_translated left,
          sourceSql_translated right, exprSql_translated expr]
  termination_by sizeOf source
  decreasing_by all_goals (simp_all <;> omega)

  theorem selectSql_translated (select : Advanced.Select) :
      Advanced.SQLite.selectSql (translateSelect select) = Advanced.SQLite.selectSql select := by
    cases select with
    | mk items source whereClause groupBy having distinct distinctOn =>
      have itemsEq : items.map (fun item => Advanced.SQLite.itemSql (translateSelectItem item)) = items.map (Advanced.SQLite.itemSql) :=
        List.map_congr_left fun item member =>
          have : sizeOf item < sizeOf items := List.sizeOf_lt_of_mem member
          itemSql_translated item
      have groupsEq : groupBy.map (fun expr => Advanced.SQLite.exprSql (translateExpr expr)) = groupBy.map (Advanced.SQLite.exprSql) :=
        List.map_congr_left fun expr member =>
          have : sizeOf expr < sizeOf groupBy := List.sizeOf_lt_of_mem member
          exprSql_translated expr
      have distinctEq : distinctOn.map (fun expr => Advanced.SQLite.exprSql (translateExpr expr)) = distinctOn.map (Advanced.SQLite.exprSql) :=
        List.map_congr_left fun expr member =>
          have : sizeOf expr < sizeOf distinctOn := List.sizeOf_lt_of_mem member
          exprSql_translated expr
      have sourceEq :
          (match _h : (match _h : source with | none => none | some value => some (translateSource value)) with
           | none => "" | some value => " FROM " ++ Advanced.SQLite.sourceSql value) =
          (match _h : source with | none => "" | some value => " FROM " ++ Advanced.SQLite.sourceSql value) := by
        cases source with
        | none => rfl
        | some value => simp only [sourceSql_translated value]
      have whereEq :
          (match _h : (match _h : whereClause with | none => none | some value => some (translateExpr value)) with
           | none => "" | some value => " WHERE " ++ Advanced.SQLite.exprSql value) =
          (match _h : whereClause with | none => "" | some value => " WHERE " ++ Advanced.SQLite.exprSql value) := by
        cases whereClause with
        | none => rfl
        | some value => simp only [exprSql_translated value]
      have havingEq :
          (match _h : (match _h : having with | none => none | some value => some (translateExpr value)) with
           | none => "" | some value => " HAVING " ++ Advanced.SQLite.exprSql value) =
          (match _h : having with | none => "" | some value => " HAVING " ++ Advanced.SQLite.exprSql value) := by
        cases having with
        | none => rfl
        | some value => simp only [exprSql_translated value]
      rw [translateSelect, Advanced.SQLite.selectSql]
      conv => rhs; rw [Advanced.SQLite.selectSql]
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

  theorem querySql_translated (query : Advanced.Query) :
      Advanced.SQLite.querySql (translateParameters query) = Advanced.SQLite.querySql query := by
    cases query with
    | mk body ctes recursive orderBy limit offset =>
      rw [translateParameters]
      simp only [List.attach_map_val]
      rw [Advanced.SQLite.querySql]
      conv => rhs; rw [Advanced.SQLite.querySql]
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
            simp only [querySql_translated cte.val.query]
        · cases body with
          | select select =>
            rw [translateQueryBody]
            exact selectSql_translated select
          | set op all left right =>
            rw [translateQueryBody]
            simp only [querySql_translated left, querySql_translated right]
      · split
        · rfl
        · congr 2
          apply List.map_congr_left
          intro order _member
          have : sizeOf order.val < sizeOf orderBy := List.sizeOf_lt_of_mem order.property
          have : sizeOf order.val.expr < sizeOf order.val := by cases order.val; simp; omega
          simp only [exprSql_translated order.val.expr]
  termination_by sizeOf query
  decreasing_by all_goals (simp_all <;> omega)
end

end SQLean.RenderContract.SQLite

namespace SQLean.RenderContract

/-- SQLite serialization uses the same target slot before and after the explicit
parameter-only translation, on every finite query. -/
theorem renderSQLite_translateParameters (query : Advanced.Query) :
    Advanced.renderSQLite (translateParameters query) = Advanced.renderSQLite query := by
  change Advanced.SQLite.querySql (translateParameters query) ++ ";" = Advanced.SQLite.querySql query ++ ";"
  rw [SQLite.querySql_translated query]

theorem query_toSQLite_translation (query : Advanced.Query) :
    (translateParameters query).toSQLite = query.toSQLite :=
  SQLite.querySql_translated query

end SQLean.RenderContract
