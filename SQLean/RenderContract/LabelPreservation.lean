import SQLean.RenderContract.ExpressionPreservation
import SQLean.SelectContract.Spec

/-! Parameter-only translation preserves labels derived from the certified
output of an expression subquery, including inherited strong names. -/
namespace SQLean.RenderContract
open Advanced SelectContract

@[simp] theorem output_label_translated (expr : Advanced.Expr) :
    outputLabel (translateExpr expr) = outputLabel expr := by
  cases expr with
  | cast arg target =>
      simp only [translateExpr, outputLabel, output_label_translated arg]
  | collate arg name =>
      simp only [translateExpr, outputLabel, output_label_translated arg]
  | subscript arg indices =>
      simp only [translateExpr, outputLabel, output_label_translated arg]
  | caseExpr operand branches otherwise =>
      cases otherwise with
      | none =>
          simp only [translateExpr_case, outputLabel, Option.map_none]
      | some arg =>
          simp only [translateExpr_case, outputLabel, Option.map_some,
            output_label_translated arg]
  | _ => simp only [translateExpr, outputLabel]
termination_by sizeOf expr
decreasing_by all_goals (simp_all <;> omega)


@[simp] theorem label_needs_subquery_translated (expr : Advanced.Expr) :
    labelNeedsSubquery (translateExpr expr) = labelNeedsSubquery expr := by
  cases expr with
  | cast arg target => simp only [translateExpr, labelNeedsSubquery, label_needs_subquery_translated arg]
  | subscript arg indices => simp only [translateExpr, labelNeedsSubquery, label_needs_subquery_translated arg]
  | collate arg name => simp only [translateExpr, labelNeedsSubquery, label_needs_subquery_translated arg]
  | caseExpr operand branches otherwise =>
    cases otherwise with
    | none => simp only [translateExpr_case, Option.map_none, labelNeedsSubquery]
    | some arg => simp only [translateExpr_case, Option.map_some, labelNeedsSubquery, label_needs_subquery_translated arg]
  | _ => simp only [translateExpr, labelNeedsSubquery]
termination_by sizeOf expr
decreasing_by all_goals (simp_all <;> omega)

theorem expr_label_valid_translated_core
    (preserved : SubqueriesTranslated sq bound)
    (valid : ExprLabelValidCore sq env expr label)
    (small : sizeOf expr ≤ bound := by simp_all <;> omega) :
    ExprLabelValidCore sq env (translateExpr expr) label := by
  cases valid with
  | ordinary closed =>
    simpa only [output_label_translated] using
      ExprLabelValidCore.ordinary (expr := translateExpr _) (by simpa only [label_needs_subquery_translated] using closed)
  | scalarQuery query =>
    simpa only [translateExpr] using
      ExprLabelValidCore.scalarQuery (preserved _ _ _ _ (by simp_all; omega) query)
  | cast child =>
    simpa only [translateExpr] using ExprLabelValidCore.cast (expr_label_valid_translated_core preserved child)
  | subscript child =>
    simpa only [translateExpr] using ExprLabelValidCore.subscript (expr_label_valid_translated_core preserved child)
  | collate child =>
    simpa only [translateExpr] using ExprLabelValidCore.collate (expr_label_valid_translated_core preserved child)
  | caseExpr child =>
    simpa only [translateExpr_case, Option.map_some] using
      ExprLabelValidCore.caseExpr (expr_label_valid_translated_core preserved child)
termination_by sizeOf expr
decreasing_by all_goals (simp_all <;> omega)

end SQLean.RenderContract
