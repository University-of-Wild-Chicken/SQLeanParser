import SQLean.RenderContract.ExpressionCollationPreservation
import SQLean.SelectContract.Values

/-! VALUES preservation is proved over the independent row derivations. The
column resolver sees identical metadata after translation, including every
contextual collation coercion and exact source typmod. -/
namespace SQLean.RenderContract
open Advanced SelectContract

@[simp] theorem values_cell_translated (expr : Advanced.Expr) (type : ExprType)
    (derivation : CollationDerivation) :
    valuesCell (translateExpr expr) type derivation = valuesCell expr type derivation := by
  simp only [valuesCell, collation_scalar_input_translated, coerced_collation_translated]

theorem values_row_valid_translated_core
    (preserved : SubqueriesTranslated sq bound)
    (valid : ValuesRowValidCore sq profile params env row cells uses)
    (small : sizeOf row ≤ bound := by simp_all <;> omega) :
    ValuesRowValidCore sq profile params env (row.map translateExpr) cells
      (uses.map translateParameter) := by
  cases valid with
  | nil => exact .nil
  | cons typed collation tail =>
    simpa only [List.map_cons, List.map_append, values_cell_translated] using
      ValuesRowValidCore.cons (expr_valid_translated_core preserved typed)
        (expr_collation_valid_translated_core preserved collation)
        (values_row_valid_translated_core preserved tail)
termination_by sizeOf row
decreasing_by all_goals (simp_all <;> omega)

theorem values_rows_valid_translated_core
    (preserved : SubqueriesTranslated sq bound)
    (valid : ValuesRowsValidCore sq profile params env rows cells uses)
    (small : sizeOf rows ≤ bound := by simp_all <;> omega) :
    ValuesRowsValidCore sq profile params env (rows.map (List.map translateExpr)) cells
      (uses.map translateParameter) := by
  cases valid with
  | nil => exact .nil
  | cons head tail =>
    simpa only [List.map_cons, List.map_append] using
      ValuesRowsValidCore.cons (values_row_valid_translated_core preserved head)
        (values_rows_valid_translated_core preserved tail)
termination_by sizeOf rows
decreasing_by all_goals (simp_all <;> omega)

@[simp] theorem values_shape_translated (rows : List (List Advanced.Expr)) :
    valuesShape (rows.map (List.map translateExpr)) = valuesShape rows := by
  cases rows <;> simp [valuesShape, List.all_map, Function.comp_def]

end SQLean.RenderContract
