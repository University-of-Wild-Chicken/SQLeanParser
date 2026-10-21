import SQLean.SelectContract.Spec
import SQLean.RenderContract.ValidityPreservation

/-! Constructor-only witnesses for the new judgments. These proofs never call
an executable checker or infer a declaration from a successful parse. -/
namespace SQLean.Tests
open SelectContract

private def singleProjection (expr : Advanced.Expr) : Advanced.Query :=
  {body := .select {items := [.expression expr none]}}

private theorem singleProjection_valid
    (typed : ExprValidCore (QueryValid .basicV33 [] []) [] [] .empty expr type [])
    (collation : ExprCollationValidCore (QueryValid .basicV33 [] []) .basicV33 [] [] .empty expr type derivation)
    (label : ExprLabelValidCore (QueryValid .basicV33 [] []) [] expr derivedLabel) :
    QueryValid .basicV33 [] [] [] (singleProjection expr)
      [⟨derivedLabel.2, projectedType type, projectedCollation expr type derivation⟩] [] := by
  apply QueryValid.basic (cteUses := []) (visible := []) (by decide) .nil
    (scope := .empty) (sourceUses := []) (selectUses := []) (whereUses := [])
    (orderUses := []) (limitUses := []) (offsetUses := [])
  · exact .empty
  · exact .expression typed collation label (by simp) .nil
  · exact .expression typed collation label (by simp) .nil
  · simp
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact .absent
  · exact .nil
  · exact .nil
  · exact .absent
  · exact .absent
  · exact .nil
  · rfl
  · rfl
  · rfl

private def oneQuery := singleProjection (.literal (.int 1))
private def oneColumn : OutputColumn := ⟨"?column?", ⟨.int32, false⟩, none⟩

private theorem oneQuery_valid : QueryValid .basicV33 [] [] [] oneQuery [oneColumn] [] :=
  singleProjection_valid (.int (by decide)) (.atom (.int (by decide)) .int) (.ordinary rfl)

private def scalarOne := singleProjection (.scalarQuery oneQuery)
private theorem scalarOne_valid : QueryValid .basicV33 [] [] [] scalarOne
    [⟨"?column?", ⟨.int32, true⟩, none⟩] [] :=
  singleProjection_valid (.scalarQuery oneQuery_valid)
    (.scalarQuery oneQuery_valid (Or.inl rfl)) (.scalarQuery oneQuery_valid)

private def existsOne := singleProjection (.exists oneQuery)
private theorem existsOne_valid : QueryValid .basicV33 [] [] [] existsOne
    [⟨"exists", ⟨.bool, false⟩, none⟩] [] :=
  singleProjection_valid (.exists oneQuery_valid) (.exists oneQuery_valid) (.ordinary rfl)

private def inOneExpr : Advanced.Expr := .inQuery (.literal (.int 1)) oneQuery
private theorem inOne_typed : ExprValidCore (QueryValid .basicV33 [] []) [] [] .empty
    inOneExpr (some ⟨.bool, false⟩) [] :=
  .inQuery (selected := ⟨[.int32, .int32], .bool⟩) (.int (by decide)) oneQuery_valid (by decide)

private theorem inOne_collation : ExprCollationValidCore (QueryValid .basicV33 [] []) .basicV33 [] [] .empty
    inOneExpr (some ⟨.bool, false⟩) .none :=
  .inQuery (signature := ⟨[.int32, .int32], .bool⟩) (leftType := .int32) (rightType := .int32)
    inOne_typed (.atom (.int (by decide)) .int) oneQuery_valid (by decide) rfl rfl

private theorem inOne_valid : QueryValid .basicV33 [] [] [] (singleProjection inOneExpr)
    [⟨"?column?", ⟨.bool, false⟩, none⟩] [] :=
  singleProjection_valid inOne_typed inOne_collation (.ordinary rfl)

private theorem whole_valid (query : QueryValid .basicV33 [] [] [] ast output []) :
    SelectValid .basicV33 [] [] ast output := by
  apply SelectValid.certified (uses := [])
  · decide
  · decide
  · decide
  · exact query
  · decide

example : SelectValid .basicV33 [] [] scalarOne [⟨"?column?", ⟨.int32, true⟩, none⟩] :=
  whole_valid scalarOne_valid
example : SelectValid .basicV33 [] [] existsOne [⟨"exists", ⟨.bool, false⟩, none⟩] :=
  whole_valid existsOne_valid
example : SelectValid .basicV33 [] [] (singleProjection inOneExpr) [⟨"?column?", ⟨.bool, false⟩, none⟩] :=
  whole_valid inOne_valid
example : SelectValid .basicV33 [] [] (RenderContract.translateParameters scalarOne)
    [⟨"?column?", ⟨.int32, true⟩, none⟩] :=
  RenderContract.translateParameters_valid (whole_valid scalarOne_valid)

end SQLean.Tests
