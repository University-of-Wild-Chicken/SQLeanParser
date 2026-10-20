import SQLean.AdvancedSyntax

/-! Exact structural decidable equality for the mutually recursive advanced AST.
Lean's automatic DecidableEq deriving does not cover these mutual nested types.
Each positive result below proves propositional equality of every constructor
field; neither pretty printing, hashes, nor the unproved BEq instances are used.
Recursive calls follow strict first-argument subterms. -/
namespace SQLean.Advanced

set_option maxHeartbeats 800000

mutual
  private def exactExprDecEq (a b : Expr) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | solve | apply isFalse; intro h; cases h
                    | skip
    case literal.literal a0 b0 =>
      exact decidable_of_iff (a0 = b0) (by simp only [Expr.literal.injEq])
    case null.null =>
      exact isTrue rfl
    case contextValue.contextValue a0 b0 =>
      exact decidable_of_iff (a0 = b0) (by simp only [Expr.contextValue.injEq])
    case decimal.decimal a0 b0 =>
      exact decidable_of_iff (a0 = b0) (by simp only [Expr.decimal.injEq])
    case parameter.parameter a0 b0 =>
      exact decidable_of_iff (a0 = b0) (by simp only [Expr.parameter.injEq])
    case column.column a0 a1 a2 b0 b1 b2 =>
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [Expr.column.injEq])
    case binary.binary a0 a1 a2 b0 b1 b2 =>
      letI : Decidable (a1 = b1) := exactExprDecEq a1 b1
      letI : Decidable (a2 = b2) := exactExprDecEq a2 b2
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [Expr.binary.injEq])
    case unary.unary a0 a1 b0 b1 =>
      letI : Decidable (a1 = b1) := exactExprDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Expr.unary.injEq])
    case countAll.countAll =>
      exact isTrue rfl
    case aggregate.aggregate a0 a1 a2 b0 b1 b2 =>
      letI : Decidable (a1 = b1) := exactExprDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [Expr.aggregate.injEq])
    case isNull.isNull a0 a1 b0 b1 =>
      letI : Decidable (a0 = b0) := exactExprDecEq a0 b0
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Expr.isNull.injEq])
    case pattern.pattern a0 a1 a2 b0 b1 b2 =>
      letI : Decidable (a0 = b0) := exactExprDecEq a0 b0
      letI : Decidable (a1 = b1) := exactExprDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [Expr.pattern.injEq])
    case extract.extract a0 a1 b0 b1 =>
      letI : Decidable (a1 = b1) := exactExprDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Expr.extract.injEq])
    case cast.cast a0 a1 b0 b1 =>
      letI : Decidable (a0 = b0) := exactExprDecEq a0 b0
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Expr.cast.injEq])
    case call.call a0 a1 b0 b1 =>
      letI : Decidable (a1 = b1) := exactListExprDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Expr.call.injEq])
    case namedCall.namedCall a0 a1 b0 b1 =>
      letI : Decidable (a1 = b1) := exactListCallArgumentDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Expr.namedCall.injEq])
    case substring.substring a0 a1 b0 b1 =>
      letI : Decidable (a1 = b1) := exactListExprDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Expr.substring.injEq])
    case caseExpr.caseExpr a0 a1 a2 b0 b1 b2 =>
      letI : Decidable (a0 = b0) := exactOptionExprDecEq a0 b0
      letI : Decidable (a1 = b1) := exactBranchesDecEq a1 b1
      letI : Decidable (a2 = b2) := exactOptionExprDecEq a2 b2
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [Expr.caseExpr.injEq])
    case nullIf.nullIf a0 a1 b0 b1 =>
      letI : Decidable (a0 = b0) := exactExprDecEq a0 b0
      letI : Decidable (a1 = b1) := exactExprDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Expr.nullIf.injEq])
    case coalesce.coalesce a0 b0 =>
      letI : Decidable (a0 = b0) := exactListExprDecEq a0 b0
      exact decidable_of_iff (a0 = b0) (by simp only [Expr.coalesce.injEq])
    case array.array a0 b0 =>
      letI : Decidable (a0 = b0) := exactListExprDecEq a0 b0
      exact decidable_of_iff (a0 = b0) (by simp only [Expr.array.injEq])
    case row.row a0 b0 =>
      letI : Decidable (a0 = b0) := exactListExprDecEq a0 b0
      exact decidable_of_iff (a0 = b0) (by simp only [Expr.row.injEq])
    case concat.concat a0 a1 b0 b1 =>
      letI : Decidable (a0 = b0) := exactExprDecEq a0 b0
      letI : Decidable (a1 = b1) := exactExprDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Expr.concat.injEq])
    case containment.containment a0 a1 a2 b0 b1 b2 =>
      letI : Decidable (a0 = b0) := exactExprDecEq a0 b0
      letI : Decidable (a1 = b1) := exactExprDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2)
        (by simp only [Expr.containment.injEq])
    case overlap.overlap a0 a1 b0 b1 =>
      letI : Decidable (a0 = b0) := exactExprDecEq a0 b0
      letI : Decidable (a1 = b1) := exactExprDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Expr.overlap.injEq])
    case jsonAccess.jsonAccess a0 a1 a2 b0 b1 b2 =>
      letI : Decidable (a1 = b1) := exactExprDecEq a1 b1
      letI : Decidable (a2 = b2) := exactExprDecEq a2 b2
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2)
        (by simp only [Expr.jsonAccess.injEq])
    case jsonExistence.jsonExistence a0 a1 a2 b0 b1 b2 =>
      letI : Decidable (a1 = b1) := exactExprDecEq a1 b1
      letI : Decidable (a2 = b2) := exactExprDecEq a2 b2
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2)
        (by simp only [Expr.jsonExistence.injEq])
    case regex.regex a0 a1 a2 a3 b0 b1 b2 b3 =>
      letI : Decidable (a0 = b0) := exactExprDecEq a0 b0
      letI : Decidable (a1 = b1) := exactExprDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3)
        (by simp only [Expr.regex.injEq])
    case quantifiedComparison.quantifiedComparison a0 a1 a2 a3 b0 b1 b2 b3 =>
      letI : Decidable (a2 = b2) := exactExprDecEq a2 b2
      letI : Decidable (a3 = b3) := exactExprDecEq a3 b3
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3)
        (by simp only [Expr.quantifiedComparison.injEq])
    case subscript.subscript a0 a1 b0 b1 =>
      letI : Decidable (a0 = b0) := exactExprDecEq a0 b0
      letI : Decidable (a1 = b1) := exactListSubscriptDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Expr.subscript.injEq])
    case greatest.greatest a0 b0 =>
      letI : Decidable (a0 = b0) := exactListExprDecEq a0 b0
      exact decidable_of_iff (a0 = b0) (by simp only [Expr.greatest.injEq])
    case least.least a0 b0 =>
      letI : Decidable (a0 = b0) := exactListExprDecEq a0 b0
      exact decidable_of_iff (a0 = b0) (by simp only [Expr.least.injEq])
    case filteredAggregate.filteredAggregate a0 a1 b0 b1 =>
      letI : Decidable (a0 = b0) := exactExprDecEq a0 b0
      letI : Decidable (a1 = b1) := exactExprDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Expr.filteredAggregate.injEq])
    case inList.inList a0 a1 b0 b1 =>
      letI : Decidable (a0 = b0) := exactExprDecEq a0 b0
      letI : Decidable (a1 = b1) := exactListExprDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Expr.inList.injEq])
    case between.between a0 a1 a2 a3 b0 b1 b2 b3 =>
      letI : Decidable (a0 = b0) := exactExprDecEq a0 b0
      letI : Decidable (a1 = b1) := exactExprDecEq a1 b1
      letI : Decidable (a2 = b2) := exactExprDecEq a2 b2
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) (by simp only [Expr.between.injEq])
    case inQuery.inQuery a0 a1 b0 b1 =>
      letI : Decidable (a0 = b0) := exactExprDecEq a0 b0
      letI : Decidable (a1 = b1) := exactQueryDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Expr.inQuery.injEq])
    case exists.exists a0 b0 =>
      letI : Decidable (a0 = b0) := exactQueryDecEq a0 b0
      exact decidable_of_iff (a0 = b0) (by simp only [Expr.exists.injEq])
    case scalarQuery.scalarQuery a0 b0 =>
      letI : Decidable (a0 = b0) := exactQueryDecEq a0 b0
      exact decidable_of_iff (a0 = b0) (by simp only [Expr.scalarQuery.injEq])
  termination_by sizeOf a
  decreasing_by all_goals (simp_all <;> omega)

  private def exactCallArgumentDecEq (a b : CallArgument) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | solve | apply isFalse; intro h; cases h
                    | skip
    case positional.positional a0 b0 =>
      letI : Decidable (a0 = b0) := exactExprDecEq a0 b0
      exact decidable_of_iff (a0 = b0) (by simp only [CallArgument.positional.injEq])
    case named.named a0 a1 a2 b0 b1 b2 =>
      letI : Decidable (a1 = b1) := exactExprDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [CallArgument.named.injEq])
  termination_by sizeOf a
  decreasing_by all_goals (simp_all <;> omega)

  private def exactListCallArgumentDecEq (a b : List CallArgument) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | solve | apply isFalse; intro h; cases h
                    | skip
    case nil.nil => exact isTrue rfl
    case cons.cons a0 a1 b0 b1 =>
      letI : Decidable (a0 = b0) := exactCallArgumentDecEq a0 b0
      letI : Decidable (a1 = b1) := exactListCallArgumentDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [List.cons.injEq])
  termination_by sizeOf a
  decreasing_by all_goals (simp_all <;> omega)

  private def exactSubscriptDecEq (a b : Subscript) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | solve | apply isFalse; intro h; cases h
                    | skip
    case index.index a0 b0 =>
      letI : Decidable (a0 = b0) := exactExprDecEq a0 b0
      exact decidable_of_iff (a0 = b0) (by simp only [Subscript.index.injEq])
    case slice.slice a0 a1 b0 b1 =>
      letI : Decidable (a0 = b0) := exactOptionExprDecEq a0 b0
      letI : Decidable (a1 = b1) := exactOptionExprDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [Subscript.slice.injEq])
  termination_by sizeOf a
  decreasing_by all_goals (simp_all <;> omega)

  private def exactListSubscriptDecEq (a b : List Subscript) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | solve | apply isFalse; intro h; cases h
                    | skip
    case nil.nil => exact isTrue rfl
    case cons.cons a0 a1 b0 b1 =>
      letI : Decidable (a0 = b0) := exactSubscriptDecEq a0 b0
      letI : Decidable (a1 = b1) := exactListSubscriptDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [List.cons.injEq])
  termination_by sizeOf a
  decreasing_by all_goals (simp_all <;> omega)

  private def exactSelectItemDecEq (a b : SelectItem) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | solve | apply isFalse; intro h; cases h
                    | skip
    case all.all a0 a1 b0 b1 =>
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [SelectItem.all.injEq])
    case expression.expression a0 a1 b0 b1 =>
      letI : Decidable (a0 = b0) := exactExprDecEq a0 b0
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [SelectItem.expression.injEq])
  termination_by sizeOf a
  decreasing_by all_goals (simp_all <;> omega)

  private def exactOrderByDecEq (a b : OrderBy) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | solve | apply isFalse; intro h; cases h
                    | skip
    case mk.mk a0 a1 a2 b0 b1 b2 =>
      letI : Decidable (a0 = b0) := exactExprDecEq a0 b0
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [OrderBy.mk.injEq])
  termination_by sizeOf a
  decreasing_by all_goals (simp_all <;> omega)

  private def exactJoinConditionDecEq (a b : JoinCondition) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | solve | apply isFalse; intro h; cases h
                    | skip
    case none.none =>
      exact isTrue rfl
    case on.on a0 b0 =>
      letI : Decidable (a0 = b0) := exactExprDecEq a0 b0
      exact decidable_of_iff (a0 = b0) (by simp only [JoinCondition.on.injEq])
    case using.using a0 b0 =>
      exact decidable_of_iff (a0 = b0) (by simp only [JoinCondition.using.injEq])
    case natural.natural =>
      exact isTrue rfl
  termination_by sizeOf a
  decreasing_by all_goals (simp_all <;> omega)

  private def exactFromDecEq (a b : From) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | solve | apply isFalse; intro h; cases h
                    | skip
    case table.table a0 a1 a2 a3 b0 b1 b2 b3 =>
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) (by simp only [From.table.injEq])
    case derived.derived a0 a1 a2 a3 b0 b1 b2 b3 =>
      letI : Decidable (a0 = b0) := exactQueryDecEq a0 b0
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) (by simp only [From.derived.injEq])
    case join.join a0 a1 a2 a3 b0 b1 b2 b3 =>
      letI : Decidable (a1 = b1) := exactFromDecEq a1 b1
      letI : Decidable (a2 = b2) := exactFromDecEq a2 b2
      letI : Decidable (a3 = b3) := exactJoinConditionDecEq a3 b3
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) (by simp only [From.join.injEq])
  termination_by sizeOf a
  decreasing_by all_goals (simp_all <;> omega)

  private def exactSelectDecEq (a b : Select) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | solve | apply isFalse; intro h; cases h
                    | skip
    case mk.mk a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6 =>
      letI : Decidable (a0 = b0) := exactListSelectItemDecEq a0 b0
      letI : Decidable (a1 = b1) := exactOptionFromDecEq a1 b1
      letI : Decidable (a2 = b2) := exactOptionExprDecEq a2 b2
      letI : Decidable (a3 = b3) := exactListExprDecEq a3 b3
      letI : Decidable (a4 = b4) := exactOptionExprDecEq a4 b4
      letI : Decidable (a6 = b6) := exactListExprDecEq a6 b6
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5 ∧ a6 = b6) (by simp only [Select.mk.injEq])
  termination_by sizeOf a
  decreasing_by all_goals (simp_all <;> omega)

  private def exactQueryBodyDecEq (a b : QueryBody) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | solve | apply isFalse; intro h; cases h
                    | skip
    case select.select a0 b0 =>
      letI : Decidable (a0 = b0) := exactSelectDecEq a0 b0
      exact decidable_of_iff (a0 = b0) (by simp only [QueryBody.select.injEq])
    case set.set a0 a1 a2 a3 b0 b1 b2 b3 =>
      letI : Decidable (a2 = b2) := exactQueryDecEq a2 b2
      letI : Decidable (a3 = b3) := exactQueryDecEq a3 b3
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) (by simp only [QueryBody.set.injEq])
  termination_by sizeOf a
  decreasing_by all_goals (simp_all <;> omega)

  private def exactQueryDecEq (a b : Query) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | solve | apply isFalse; intro h; cases h
                    | skip
    case mk.mk a0 a1 a2 a3 a4 a5 a6 a7 b0 b1 b2 b3 b4 b5 b6 b7 =>
      letI : Decidable (a0 = b0) := exactQueryBodyDecEq a0 b0
      letI : Decidable (a1 = b1) := exactListCTEDecEq a1 b1
      letI : Decidable (a3 = b3) := exactListOrderByDecEq a3 b3
      letI : Decidable (a4 = b4) := exactOptionExprDecEq a4 b4
      letI : Decidable (a5 = b5) := exactOptionExprDecEq a5 b5
      exact decidable_of_iff
        (a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5 ∧ a6 = b6 ∧ a7 = b7)
        (by simp only [Query.mk.injEq])
  termination_by sizeOf a
  decreasing_by all_goals (simp_all <;> omega)

  private def exactCTEDecEq (a b : CTE) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | solve | apply isFalse; intro h; cases h
                    | skip
    case mk.mk a0 a1 a2 b0 b1 b2 =>
      letI : Decidable (a1 = b1) := exactQueryDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp only [CTE.mk.injEq])
  termination_by sizeOf a
  decreasing_by all_goals (simp_all <;> omega)

  private def exactListExprDecEq (a b : List Expr) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | solve | apply isFalse; intro h; cases h
                    | skip
    case nil.nil =>
      exact isTrue rfl
    case cons.cons a0 a1 b0 b1 =>
      letI : Decidable (a0 = b0) := exactExprDecEq a0 b0
      letI : Decidable (a1 = b1) := exactListExprDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [List.cons.injEq])
  termination_by sizeOf a
  decreasing_by all_goals (simp_all <;> omega)

  private def exactBranchesDecEq (a b : List (Expr × Expr)) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | solve | apply isFalse; intro h; cases h
                    | skip
    case nil.nil => exact isTrue rfl
    case cons.cons a0 a1 b0 b1 =>
      have : sizeOf a0.1 < sizeOf a0 := by cases a0; simp; omega
      have : sizeOf a0.2 < sizeOf a0 := by cases a0; simp; omega
      letI : Decidable (a0.1 = b0.1) := exactExprDecEq a0.1 b0.1
      letI : Decidable (a0.2 = b0.2) := exactExprDecEq a0.2 b0.2
      letI : Decidable (a0 = b0) := decidable_of_iff (a0.1 = b0.1 ∧ a0.2 = b0.2)
        (by exact Prod.ext_iff.symm)
      letI : Decidable (a1 = b1) := exactBranchesDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [List.cons.injEq])
  termination_by sizeOf a
  decreasing_by all_goals (simp_all <;> omega)

  private def exactListSelectItemDecEq (a b : List SelectItem) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | solve | apply isFalse; intro h; cases h
                    | skip
    case nil.nil =>
      exact isTrue rfl
    case cons.cons a0 a1 b0 b1 =>
      letI : Decidable (a0 = b0) := exactSelectItemDecEq a0 b0
      letI : Decidable (a1 = b1) := exactListSelectItemDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [List.cons.injEq])
  termination_by sizeOf a
  decreasing_by all_goals (simp_all <;> omega)

  private def exactListOrderByDecEq (a b : List OrderBy) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | solve | apply isFalse; intro h; cases h
                    | skip
    case nil.nil =>
      exact isTrue rfl
    case cons.cons a0 a1 b0 b1 =>
      letI : Decidable (a0 = b0) := exactOrderByDecEq a0 b0
      letI : Decidable (a1 = b1) := exactListOrderByDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [List.cons.injEq])
  termination_by sizeOf a
  decreasing_by all_goals (simp_all <;> omega)

  private def exactListCTEDecEq (a b : List CTE) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | solve | apply isFalse; intro h; cases h
                    | skip
    case nil.nil =>
      exact isTrue rfl
    case cons.cons a0 a1 b0 b1 =>
      letI : Decidable (a0 = b0) := exactCTEDecEq a0 b0
      letI : Decidable (a1 = b1) := exactListCTEDecEq a1 b1
      exact decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp only [List.cons.injEq])
  termination_by sizeOf a
  decreasing_by all_goals (simp_all <;> omega)

  private def exactOptionExprDecEq (a b : Option Expr) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | solve | apply isFalse; intro h; cases h
                    | skip
    case none.none =>
      exact isTrue rfl
    case some.some a0 b0 =>
      letI : Decidable (a0 = b0) := exactExprDecEq a0 b0
      exact decidable_of_iff (a0 = b0) (by simp only [Option.some.injEq])
  termination_by sizeOf a
  decreasing_by all_goals (simp_all <;> omega)

  private def exactOptionFromDecEq (a b : Option From) : Decidable (a = b) := by
    cases a <;> cases b
    all_goals first | solve | apply isFalse; intro h; cases h
                    | skip
    case none.none =>
      exact isTrue rfl
    case some.some a0 b0 =>
      letI : Decidable (a0 = b0) := exactFromDecEq a0 b0
      exact decidable_of_iff (a0 = b0) (by simp only [Option.some.injEq])
  termination_by sizeOf a
  decreasing_by all_goals (simp_all <;> omega)

end

instance : DecidableEq Expr := exactExprDecEq
instance : DecidableEq CallArgument := exactCallArgumentDecEq
instance : DecidableEq Subscript := exactSubscriptDecEq
instance : DecidableEq SelectItem := exactSelectItemDecEq
instance : DecidableEq OrderBy := exactOrderByDecEq
instance : DecidableEq JoinCondition := exactJoinConditionDecEq
instance : DecidableEq From := exactFromDecEq
instance : DecidableEq Select := exactSelectDecEq
instance : DecidableEq QueryBody := exactQueryBodyDecEq
instance : DecidableEq Query := exactQueryDecEq
instance : DecidableEq CTE := exactCTEDecEq

end SQLean.Advanced
