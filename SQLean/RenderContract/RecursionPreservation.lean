import SQLean.RenderContract.Translation
import SQLean.SelectContract.Recursion

/-! Structural recursive-query premises are invariant under parameter-only
translation. These proofs do not use a parser, renderer, executable checker,
or evaluation of database statements. -/
namespace SQLean.RenderContract
open Advanced SelectContract
set_option maxHeartbeats 1000000

@[simp] theorem recursive_cte_names_translated (ctes : List Advanced.CTE) :
    (ctes.map translateCTE).map Advanced.CTE.name = ctes.map Advanced.CTE.name := by
  simp only [List.map_map, Function.comp_def, translateCTE]

@[simp] theorem recursive_outer_env_translated (env : CTEEnv) (ctes : List Advanced.CTE) :
    recursiveOuterEnv env (ctes.map translateCTE) = recursiveOuterEnv env ctes := by
  simp only [recursiveOuterEnv, recursive_cte_names_translated]

private theorem recursive_append_congr {a b c d : RecursiveReferences}
    (left : a = b) (right : c = d) : a.append c = b.append d := by
  cases left
  cases right
  rfl

mutual
  @[simp] theorem recursive_references_translated (target : Name) (hidden allowed : Bool)
      (query : Advanced.Query) :
      recursiveReferences target hidden allowed (translateParameters query) =
        recursiveReferences target hidden allowed query := by
    cases query with
    | mk body ctes recursive orders limit offset locking offsetFirst =>
      have defs := recursive_cte_references_translated target
        (if recursive then hidden || (ctes.map Advanced.CTE.name).contains target else hidden) allowed ctes
      have ordering := recursive_order_references_translated target
        (hidden || (ctes.map Advanced.CTE.name).contains target) orders
      have limiting := recursive_optional_expr_references_translated target
        (hidden || (ctes.map Advanced.CTE.name).contains target) limit
      have offsetting := recursive_optional_expr_references_translated target
        (hidden || (ctes.map Advanced.CTE.name).contains target) offset
      rw [translateParameters]
      simp only [List.attach_map_val]
      cases body with
      | values rows =>
        have selected :
            rows.map (fun row => recursiveExprsReferences target
              (hidden || (ctes.map Advanced.CTE.name).contains target) (row.map translateExpr)) =
            rows.map (recursiveExprsReferences target
              (hidden || (ctes.map Advanced.CTE.name).contains target)) :=
          List.map_congr_left fun row member =>
            have : sizeOf row < sizeOf rows := List.sizeOf_lt_of_mem member
            recursive_exprs_references_translated target _ row
        rw [translate_values_body]
        conv => lhs; rw [recursiveReferences.eq_def]
        conv => rhs; rw [recursiveReferences.eq_def]
        cases limit <;> cases offset <;>
          simpa only [List.attach_map_val, List.map_map, Function.comp_def, translateCTE,
            Option.map_none, Option.map_some] using
            recursive_append_congr
              (recursive_append_congr
                (recursive_append_congr
                  (recursive_append_congr defs
                    (congrArg (fun inputs => inputs.foldl RecursiveReferences.append ⟨0, true⟩) selected))
                  ordering) limiting) offsetting
      | select select =>
        have selected := recursive_select_references_translated target
          (hidden || (ctes.map Advanced.CTE.name).contains target) allowed select
        simp only [translateQueryBody]
        conv => lhs; rw [recursiveReferences.eq_def]
        conv => rhs; rw [recursiveReferences.eq_def]
        cases limit <;> cases offset <;>
          simpa only [recursive_cte_names_translated, Option.map_none, Option.map_some] using
            recursive_append_congr
              (recursive_append_congr
                (recursive_append_congr
                  (recursive_append_congr defs selected) ordering) limiting) offsetting
      | set op all left right =>
        have lhs := recursive_references_translated target
          (hidden || (ctes.map Advanced.CTE.name).contains target)
          (allowed && !(op == .except && all) && !(op == .intersect && all)) left
        have rhs := recursive_references_translated target
          (hidden || (ctes.map Advanced.CTE.name).contains target)
          (allowed && !(op == .except) && !(op == .intersect && all)) right
        simp only [translateQueryBody]
        conv => lhs; rw [recursiveReferences.eq_def]
        conv => rhs; rw [recursiveReferences.eq_def]
        cases limit <;> cases offset <;>
          simpa only [recursive_cte_names_translated, Option.map_none, Option.map_some] using
            recursive_append_congr
              (recursive_append_congr
                (recursive_append_congr
                  (recursive_append_congr defs
                    (recursive_append_congr lhs rhs)) ordering) limiting) offsetting
  termination_by sizeOf query
  decreasing_by all_goals (simp <;> omega)

  @[simp] theorem recursive_select_references_translated (target : Name) (hidden allowed : Bool)
      (select : Advanced.Select) :
      recursiveSelectReferences target hidden allowed (translateSelect select) =
        recursiveSelectReferences target hidden allowed select := by
    cases select with
    | mk items source whereClause groupBy having distinct distinctOn =>
      have projected := recursive_item_references_translated target hidden items
      have filtered := recursive_optional_expr_references_translated target hidden whereClause
      have grouped := recursive_exprs_references_translated target hidden groupBy
      have aggregateFiltered := recursive_optional_expr_references_translated target hidden having
      have distincted := recursive_exprs_references_translated target hidden distinctOn
      cases source with
      | none =>
        cases whereClause <;> cases having <;>
          simpa only [translateSelect, recursiveSelectReferences, List.attach_map_val,
            Option.map_none, Option.map_some] using
            recursive_append_congr
              (recursive_append_congr
                (recursive_append_congr
                  (recursive_append_congr
                    (recursive_append_congr (rfl : (⟨0, true⟩ : RecursiveReferences) = _) projected) filtered) grouped)
                  aggregateFiltered) distincted
      | some source =>
        have sourced := recursive_source_references_translated target hidden allowed source
        cases whereClause <;> cases having <;>
          simpa only [translateSelect, recursiveSelectReferences, List.attach_map_val,
            Option.map_none, Option.map_some] using
            recursive_append_congr
              (recursive_append_congr
                (recursive_append_congr
                  (recursive_append_congr
                    (recursive_append_congr sourced projected) filtered) grouped)
                  aggregateFiltered) distincted
  termination_by sizeOf select
  decreasing_by all_goals (simp <;> omega)

  @[simp] theorem recursive_source_references_translated (target : Name) (hidden allowed : Bool)
      (source : Advanced.From) :
      recursiveSourceReferences target hidden allowed (translateSource source) =
        recursiveSourceReferences target hidden allowed source := by
    cases source with
    | table name alias columns schema => simp only [translateSource]
    | derivedAnonymous query lateral =>
      simp only [translateSource, recursiveSourceReferences,
        recursive_references_translated target hidden allowed query]
    | derived query alias columns lateral =>
      simp only [translateSource, recursiveSourceReferences,
        recursive_references_translated target hidden allowed query]
    | join kind left right condition =>
      have lhs := recursive_source_references_translated target hidden
        (allowed && !(kind == .right || kind == .full)) left
      have rhs := recursive_source_references_translated target hidden
        (allowed && !(kind == .left || kind == .full)) right
      cases condition with
      | on expr =>
        simp only [translateSource, translateJoinCondition, recursiveSourceReferences,
          lhs, rhs, recursive_expr_references_translated target hidden expr]
      | «using» columns => simp only [translateSource, translateJoinCondition, recursiveSourceReferences, lhs, rhs]
      | natural => simp only [translateSource, translateJoinCondition, recursiveSourceReferences, lhs, rhs]
      | none => simp only [translateSource, translateJoinCondition, recursiveSourceReferences, lhs, rhs]
  termination_by sizeOf source
  decreasing_by all_goals (simp <;> omega)

  @[simp] theorem recursive_cte_references_translated (target : Name) (hidden allowed : Bool)
      (ctes : List Advanced.CTE) :
      recursiveCTEReferences target hidden allowed (ctes.map translateCTE) =
        recursiveCTEReferences target hidden allowed ctes := by
    cases ctes with
    | nil => rfl
    | cons head tail =>
      cases head with
      | mk name query columns =>
        simp only [List.map_cons, translateCTE, recursiveCTEReferences,
          recursive_references_translated target hidden allowed query,
          recursive_cte_references_translated target (hidden || name == target) allowed tail]
  termination_by sizeOf ctes
  decreasing_by all_goals (simp <;> omega)

  @[simp] theorem recursive_optional_expr_references_translated (target : Name) (hidden : Bool)
      (expr : Option Advanced.Expr) :
      recursiveOptionalExprReferences target hidden (expr.map translateExpr) =
        recursiveOptionalExprReferences target hidden expr := by
    cases expr with
    | none => rfl
    | some value =>
      simp only [Option.map_some, recursiveOptionalExprReferences,
        recursive_expr_references_translated target hidden value]
  termination_by sizeOf expr
  decreasing_by all_goals (simp <;> omega)

  @[simp] theorem recursive_item_references_translated (target : Name) (hidden : Bool)
      (items : List Advanced.SelectItem) :
      recursiveItemReferences target hidden (items.map translateSelectItem) =
        recursiveItemReferences target hidden items := by
    cases items with
    | nil => rfl
    | cons head tail =>
      cases head with
      | all qualifier schema =>
        simp only [List.map_cons, translateSelectItem, recursiveItemReferences,
          recursive_item_references_translated target hidden tail]
      | expression expr alias =>
        simp only [List.map_cons, translateSelectItem, recursiveItemReferences,
          recursive_expr_references_translated target hidden expr,
          recursive_item_references_translated target hidden tail]
  termination_by sizeOf items
  decreasing_by all_goals (simp <;> omega)

  @[simp] theorem recursive_order_references_translated (target : Name) (hidden : Bool)
      (items : List Advanced.OrderBy) :
      recursiveOrderReferences target hidden (items.map translateOrderBy) =
        recursiveOrderReferences target hidden items := by
    cases items with
    | nil => rfl
    | cons head tail =>
      cases head with
      | mk expr direction nulls =>
        simp only [List.map_cons, translateOrderBy, recursiveOrderReferences,
          recursive_expr_references_translated target hidden expr,
          recursive_order_references_translated target hidden tail]
  termination_by sizeOf items
  decreasing_by all_goals (simp <;> omega)

  @[simp] theorem recursive_expr_references_translated (target : Name) (hidden : Bool) (expr : Advanced.Expr) :
      recursiveExprReferences target hidden (translateExpr expr) = recursiveExprReferences target hidden expr := by
    cases expr with
    | literal value => simp only [translateExpr, recursiveExprReferences]
    | null => simp only [translateExpr, recursiveExprReferences]
    | contextValue value => simp only [translateExpr, recursiveExprReferences]
    | decimal raw => simp only [translateExpr, recursiveExprReferences]
    | parameter parameter => simp only [translateExpr, recursiveExprReferences]
    | column qualifier name schema => simp only [translateExpr, recursiveExprReferences]
    | countAll => simp only [translateExpr, recursiveExprReferences]
    | collate arg name => simp only [translateExpr, recursiveExprReferences, recursive_expr_references_translated target hidden arg]
    | quantifiedQuery op quantifier arg query => simp only [translateExpr, recursiveExprReferences, recursive_expr_references_translated target hidden arg, recursive_references_translated target hidden false query]
    | inQuery arg query => simp only [translateExpr, recursiveExprReferences, recursive_expr_references_translated target hidden arg, recursive_references_translated target hidden false query]
    | «exists» query => simp only [translateExpr, recursiveExprReferences, recursive_references_translated target hidden false query]
    | scalarQuery query => simp only [translateExpr, recursiveExprReferences, recursive_references_translated target hidden false query]
    | binary op left right =>
      simp only [translateExpr, recursiveExprReferences, recursive_expr_references_translated target hidden left, recursive_expr_references_translated target hidden right]
    | concat left right =>
      simp only [translateExpr, recursiveExprReferences, recursive_expr_references_translated target hidden left, recursive_expr_references_translated target hidden right]
    | distinctFrom left right negated =>
      simp only [translateExpr, recursiveExprReferences, recursive_expr_references_translated target hidden left, recursive_expr_references_translated target hidden right]
    | pattern arg pattern insensitive =>
      simp only [translateExpr, recursiveExprReferences, recursive_expr_references_translated target hidden arg, recursive_expr_references_translated target hidden pattern]
    | regex arg pattern insensitive negated =>
      simp only [translateExpr, recursiveExprReferences, recursive_expr_references_translated target hidden arg, recursive_expr_references_translated target hidden pattern]
    | jsonAccess op arg key =>
      simp only [translateExpr, recursiveExprReferences, recursive_expr_references_translated target hidden arg, recursive_expr_references_translated target hidden key]
    | jsonExistence op arg keys =>
      simp only [translateExpr, recursiveExprReferences, recursive_expr_references_translated target hidden arg, recursive_expr_references_translated target hidden keys]
    | containment left right containedBy =>
      simp only [translateExpr, recursiveExprReferences, recursive_expr_references_translated target hidden left, recursive_expr_references_translated target hidden right]
    | overlap left right =>
      simp only [translateExpr, recursiveExprReferences, recursive_expr_references_translated target hidden left, recursive_expr_references_translated target hidden right]
    | quantifiedComparison op quantifier left right =>
      simp only [translateExpr, recursiveExprReferences, recursive_expr_references_translated target hidden left, recursive_expr_references_translated target hidden right]
    | nullIf left right =>
      simp only [translateExpr, recursiveExprReferences, recursive_expr_references_translated target hidden left, recursive_expr_references_translated target hidden right]
    | filteredAggregate aggregate predicate =>
      simp only [translateExpr, recursiveExprReferences, recursive_expr_references_translated target hidden aggregate, recursive_expr_references_translated target hidden predicate]
    | unary op arg =>
      simp only [translateExpr, recursiveExprReferences, recursive_expr_references_translated target hidden arg]
    | aggregate fn arg distinct =>
      simp only [translateExpr, recursiveExprReferences, recursive_expr_references_translated target hidden arg]
    | isNull arg negated =>
      simp only [translateExpr, recursiveExprReferences, recursive_expr_references_translated target hidden arg]
    | extract field arg =>
      simp only [translateExpr, recursiveExprReferences, recursive_expr_references_translated target hidden arg]
    | cast arg targetType =>
      simp only [translateExpr, recursiveExprReferences, recursive_expr_references_translated target hidden arg]
    | between arg lower upper negated =>
      simp only [translateExpr, recursiveExprReferences, recursive_expr_references_translated target hidden arg, recursive_expr_references_translated target hidden lower, recursive_expr_references_translated target hidden upper]
    | array elements =>
      simp only [translateExpr, List.attach_map_val, recursiveExprReferences, recursive_exprs_references_translated target hidden elements]
    | row elements =>
      simp only [translateExpr, List.attach_map_val, recursiveExprReferences, recursive_exprs_references_translated target hidden elements]
    | substring form args =>
      simp only [translateExpr, List.attach_map_val, recursiveExprReferences, recursive_exprs_references_translated target hidden args]
    | call name args =>
      simp only [translateExpr, List.attach_map_val, recursiveExprReferences, recursive_exprs_references_translated target hidden args]
    | coalesce args =>
      simp only [translateExpr, List.attach_map_val, recursiveExprReferences, recursive_exprs_references_translated target hidden args]
    | greatest args =>
      simp only [translateExpr, List.attach_map_val, recursiveExprReferences, recursive_exprs_references_translated target hidden args]
    | least args =>
      simp only [translateExpr, List.attach_map_val, recursiveExprReferences, recursive_exprs_references_translated target hidden args]
    | namedCall name args =>
      simp only [translateExpr, List.attach_map_val, recursiveExprReferences, recursive_argument_references_translated target hidden args]
    | subscript base indices =>
      simp only [translateExpr, List.attach_map_val, recursiveExprReferences,
        recursive_expr_references_translated target hidden base, recursive_subscript_references_translated target hidden indices]
    | inList arg values =>
      simp only [translateExpr, List.attach_map_val, recursiveExprReferences,
        recursive_expr_references_translated target hidden arg, recursive_exprs_references_translated target hidden values]
    | caseExpr operand branches otherwise =>
      cases operand with
      | none =>
        cases otherwise with
        | none => simp only [translateExpr, recursiveExprReferences, recursiveOptionalExprReferences,
            List.attach_map_val (f := fun pair : Advanced.Expr × Advanced.Expr =>
              (translateExpr pair.1, translateExpr pair.2)), recursive_branch_references_translated target hidden branches]
        | some value => simp only [translateExpr, recursiveExprReferences, recursiveOptionalExprReferences,
            List.attach_map_val (f := fun pair : Advanced.Expr × Advanced.Expr =>
              (translateExpr pair.1, translateExpr pair.2)), recursive_branch_references_translated target hidden branches,
            recursive_expr_references_translated target hidden value]
      | some arg =>
        cases otherwise with
        | none => simp only [translateExpr, recursiveExprReferences, recursiveOptionalExprReferences,
            List.attach_map_val (f := fun pair : Advanced.Expr × Advanced.Expr =>
              (translateExpr pair.1, translateExpr pair.2)), recursive_branch_references_translated target hidden branches,
            recursive_expr_references_translated target hidden arg]
        | some value => simp only [translateExpr, recursiveExprReferences, recursiveOptionalExprReferences,
            List.attach_map_val (f := fun pair : Advanced.Expr × Advanced.Expr =>
              (translateExpr pair.1, translateExpr pair.2)), recursive_branch_references_translated target hidden branches,
            recursive_expr_references_translated target hidden arg, recursive_expr_references_translated target hidden value]
  termination_by sizeOf expr
  decreasing_by all_goals (simp <;> omega)

  @[simp] theorem recursive_exprs_references_translated (target : Name) (hidden : Bool) (exprs : List Advanced.Expr) :
      recursiveExprsReferences target hidden (exprs.map translateExpr) = recursiveExprsReferences target hidden exprs := by
    cases exprs with
    | nil => rfl
    | cons head tail =>
      simp only [List.map_cons, recursiveExprsReferences,
        recursive_expr_references_translated target hidden head, recursive_exprs_references_translated target hidden tail]
  termination_by sizeOf exprs
  decreasing_by all_goals (simp <;> omega)

  @[simp] theorem recursive_argument_references_translated (target : Name) (hidden : Bool) (args : List CallArgument) :
      recursiveArgumentReferences target hidden (args.map translateCallArgument) = recursiveArgumentReferences target hidden args := by
    cases args with
    | nil => rfl
    | cons head tail =>
      cases head with
      | positional value =>
        simp only [List.map_cons, translateCallArgument, recursiveArgumentReferences,
          recursive_expr_references_translated target hidden value, recursive_argument_references_translated target hidden tail]
      | named name value spelling =>
        simp only [List.map_cons, translateCallArgument, recursiveArgumentReferences,
          recursive_expr_references_translated target hidden value, recursive_argument_references_translated target hidden tail]
  termination_by sizeOf args
  decreasing_by all_goals (simp <;> omega)

  @[simp] theorem recursive_subscript_references_translated (target : Name) (hidden : Bool) (indices : List Subscript) :
      recursiveSubscriptReferences target hidden (indices.map translateSubscript) = recursiveSubscriptReferences target hidden indices := by
    cases indices with
    | nil => rfl
    | cons head tail =>
      cases head with
      | index value =>
        simp only [List.map_cons, translateSubscript, recursiveSubscriptReferences,
          recursive_expr_references_translated target hidden value, recursive_subscript_references_translated target hidden tail]
      | slice lower upper =>
        cases lower with
        | none =>
          cases upper with
          | none => simp only [List.map_cons, translateSubscript, recursiveSubscriptReferences, recursiveOptionalExprReferences,
              recursive_subscript_references_translated target hidden tail]
          | some value => simp only [List.map_cons, translateSubscript, recursiveSubscriptReferences, recursiveOptionalExprReferences,
              recursive_expr_references_translated target hidden value, recursive_subscript_references_translated target hidden tail]
        | some value =>
          cases upper with
          | none => simp only [List.map_cons, translateSubscript, recursiveSubscriptReferences, recursiveOptionalExprReferences,
              recursive_expr_references_translated target hidden value, recursive_subscript_references_translated target hidden tail]
          | some other => simp only [List.map_cons, translateSubscript, recursiveSubscriptReferences, recursiveOptionalExprReferences,
              recursive_expr_references_translated target hidden value, recursive_expr_references_translated target hidden other,
              recursive_subscript_references_translated target hidden tail]
  termination_by sizeOf indices
  decreasing_by all_goals (simp <;> omega)

  @[simp] theorem recursive_branch_references_translated (target : Name) (hidden : Bool) (branches : List (Advanced.Expr × Advanced.Expr)) :
      recursiveBranchReferences target hidden (branches.map fun pair => (translateExpr pair.1, translateExpr pair.2)) =
        recursiveBranchReferences target hidden branches := by
    cases branches with
    | nil => rfl
    | cons head tail =>
      cases head with
      | mk condition value =>
        simp only [List.map_cons, recursiveBranchReferences,
          recursive_expr_references_translated target hidden condition, recursive_expr_references_translated target hidden value,
          recursive_branch_references_translated target hidden tail]
  termination_by sizeOf branches
  decreasing_by all_goals (simp <;> omega)
end

@[simp] theorem no_forward_cte_references_translated (remaining : List Advanced.CTE)
    (query : Advanced.Query) :
    NoForwardCTEReferences (remaining.map translateCTE) (translateParameters query) ↔
      NoForwardCTEReferences remaining query := by
  simp only [NoForwardCTEReferences, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, translateCTE, recursive_references_translated]

mutual
  @[simp] theorem uniform_default_expr_translated (expr : Advanced.Expr) :
      uniformDefaultExpr (translateExpr expr) = uniformDefaultExpr expr := by
    cases expr with
    | literal value => simp only [translateExpr, uniformDefaultExpr]
    | null => simp only [translateExpr, uniformDefaultExpr]
    | contextValue value => simp only [translateExpr, uniformDefaultExpr]
    | decimal raw => simp only [translateExpr, uniformDefaultExpr]
    | parameter parameter => simp only [translateExpr, uniformDefaultExpr]
    | column qualifier name schema => simp only [translateExpr, uniformDefaultExpr]
    | countAll => simp only [translateExpr, uniformDefaultExpr]
    | collate arg name => simp only [translateExpr, uniformDefaultExpr]
    | quantifiedQuery op quantifier arg query => simp only [translateExpr, uniformDefaultExpr]
    | inQuery arg query => simp only [translateExpr, uniformDefaultExpr]
    | «exists» query => simp only [translateExpr, uniformDefaultExpr]
    | scalarQuery query => simp only [translateExpr, uniformDefaultExpr]
    | binary op left right =>
      simp only [translateExpr, uniformDefaultExpr, uniform_default_expr_translated left, uniform_default_expr_translated right]
    | concat left right =>
      simp only [translateExpr, uniformDefaultExpr, uniform_default_expr_translated left, uniform_default_expr_translated right]
    | distinctFrom left right negated =>
      simp only [translateExpr, uniformDefaultExpr, uniform_default_expr_translated left, uniform_default_expr_translated right]
    | pattern arg pattern insensitive =>
      simp only [translateExpr, uniformDefaultExpr, uniform_default_expr_translated arg, uniform_default_expr_translated pattern]
    | regex arg pattern insensitive negated =>
      simp only [translateExpr, uniformDefaultExpr, uniform_default_expr_translated arg, uniform_default_expr_translated pattern]
    | jsonAccess op arg key =>
      simp only [translateExpr, uniformDefaultExpr, uniform_default_expr_translated arg, uniform_default_expr_translated key]
    | jsonExistence op arg keys =>
      simp only [translateExpr, uniformDefaultExpr, uniform_default_expr_translated arg, uniform_default_expr_translated keys]
    | containment left right containedBy =>
      simp only [translateExpr, uniformDefaultExpr, uniform_default_expr_translated left, uniform_default_expr_translated right]
    | overlap left right =>
      simp only [translateExpr, uniformDefaultExpr, uniform_default_expr_translated left, uniform_default_expr_translated right]
    | quantifiedComparison op quantifier left right =>
      simp only [translateExpr, uniformDefaultExpr, uniform_default_expr_translated left, uniform_default_expr_translated right]
    | nullIf left right =>
      simp only [translateExpr, uniformDefaultExpr, uniform_default_expr_translated left, uniform_default_expr_translated right]
    | filteredAggregate aggregate predicate =>
      simp only [translateExpr, uniformDefaultExpr, uniform_default_expr_translated aggregate, uniform_default_expr_translated predicate]
    | unary op arg =>
      simp only [translateExpr, uniformDefaultExpr, uniform_default_expr_translated arg]
    | aggregate fn arg distinct =>
      simp only [translateExpr, uniformDefaultExpr, uniform_default_expr_translated arg]
    | isNull arg negated =>
      simp only [translateExpr, uniformDefaultExpr, uniform_default_expr_translated arg]
    | extract field arg =>
      simp only [translateExpr, uniformDefaultExpr, uniform_default_expr_translated arg]
    | cast arg target =>
      simp only [translateExpr, uniformDefaultExpr, uniform_default_expr_translated arg]
    | between arg lower upper negated =>
      simp only [translateExpr, uniformDefaultExpr, uniform_default_expr_translated arg, uniform_default_expr_translated lower, uniform_default_expr_translated upper]
    | array elements =>
      simp only [translateExpr, List.attach_map_val, uniformDefaultExpr, uniform_default_exprs_translated elements]
    | row elements =>
      simp only [translateExpr, List.attach_map_val, uniformDefaultExpr, uniform_default_exprs_translated elements]
    | substring form args =>
      simp only [translateExpr, List.attach_map_val, uniformDefaultExpr, uniform_default_exprs_translated args]
    | call name args =>
      simp only [translateExpr, List.attach_map_val, uniformDefaultExpr, uniform_default_exprs_translated args]
    | coalesce args =>
      simp only [translateExpr, List.attach_map_val, uniformDefaultExpr, uniform_default_exprs_translated args]
    | greatest args =>
      simp only [translateExpr, List.attach_map_val, uniformDefaultExpr, uniform_default_exprs_translated args]
    | least args =>
      simp only [translateExpr, List.attach_map_val, uniformDefaultExpr, uniform_default_exprs_translated args]
    | namedCall name args =>
      simp only [translateExpr, List.attach_map_val, uniformDefaultExpr, uniform_default_arguments_translated args]
    | subscript base indices =>
      simp only [translateExpr, List.attach_map_val, uniformDefaultExpr,
        uniform_default_expr_translated base, uniform_default_subscripts_translated indices]
    | inList arg values =>
      simp only [translateExpr, List.attach_map_val, uniformDefaultExpr,
        uniform_default_expr_translated arg, uniform_default_exprs_translated values]
    | caseExpr operand branches otherwise =>
      cases operand with
      | none =>
        cases otherwise with
        | none => simp only [translateExpr, uniformDefaultExpr,
            List.attach_map_val (f := fun pair : Advanced.Expr × Advanced.Expr =>
              (translateExpr pair.1, translateExpr pair.2)), uniform_default_branches_translated branches]
        | some value => simp only [translateExpr, uniformDefaultExpr,
            List.attach_map_val (f := fun pair : Advanced.Expr × Advanced.Expr =>
              (translateExpr pair.1, translateExpr pair.2)), uniform_default_branches_translated branches,
            uniform_default_expr_translated value]
      | some arg =>
        cases otherwise with
        | none => simp only [translateExpr, uniformDefaultExpr,
            List.attach_map_val (f := fun pair : Advanced.Expr × Advanced.Expr =>
              (translateExpr pair.1, translateExpr pair.2)), uniform_default_branches_translated branches,
            uniform_default_expr_translated arg]
        | some value => simp only [translateExpr, uniformDefaultExpr,
            List.attach_map_val (f := fun pair : Advanced.Expr × Advanced.Expr =>
              (translateExpr pair.1, translateExpr pair.2)), uniform_default_branches_translated branches,
            uniform_default_expr_translated arg, uniform_default_expr_translated value]
  termination_by sizeOf expr
  decreasing_by all_goals (simp_all <;> omega)

  @[simp] theorem uniform_default_exprs_translated (exprs : List Advanced.Expr) :
      uniformDefaultExprs (exprs.map translateExpr) = uniformDefaultExprs exprs := by
    cases exprs with
    | nil => rfl
    | cons head tail =>
      simp only [List.map_cons, uniformDefaultExprs,
        uniform_default_expr_translated head, uniform_default_exprs_translated tail]
  termination_by sizeOf exprs
  decreasing_by all_goals (simp_all <;> omega)

  @[simp] theorem uniform_default_arguments_translated (args : List CallArgument) :
      uniformDefaultArguments (args.map translateCallArgument) = uniformDefaultArguments args := by
    cases args with
    | nil => rfl
    | cons head tail =>
      cases head with
      | positional value =>
        simp only [List.map_cons, translateCallArgument, uniformDefaultArguments,
          uniform_default_expr_translated value, uniform_default_arguments_translated tail]
      | named name value spelling =>
        simp only [List.map_cons, translateCallArgument, uniformDefaultArguments,
          uniform_default_expr_translated value, uniform_default_arguments_translated tail]
  termination_by sizeOf args
  decreasing_by all_goals (simp_all <;> omega)

  @[simp] theorem uniform_default_subscripts_translated (indices : List Subscript) :
      uniformDefaultSubscripts (indices.map translateSubscript) = uniformDefaultSubscripts indices := by
    cases indices with
    | nil => rfl
    | cons head tail =>
      cases head with
      | index value =>
        simp only [List.map_cons, translateSubscript, uniformDefaultSubscripts,
          uniform_default_expr_translated value, uniform_default_subscripts_translated tail]
      | slice lower upper =>
        cases lower with
        | none =>
          cases upper with
          | none => simp only [List.map_cons, translateSubscript, uniformDefaultSubscripts,
              uniform_default_subscripts_translated tail]
          | some value => simp only [List.map_cons, translateSubscript, uniformDefaultSubscripts,
              uniform_default_expr_translated value, uniform_default_subscripts_translated tail]
        | some value =>
          cases upper with
          | none => simp only [List.map_cons, translateSubscript, uniformDefaultSubscripts,
              uniform_default_expr_translated value, uniform_default_subscripts_translated tail]
          | some other => simp only [List.map_cons, translateSubscript, uniformDefaultSubscripts,
              uniform_default_expr_translated value, uniform_default_expr_translated other,
              uniform_default_subscripts_translated tail]
  termination_by sizeOf indices
  decreasing_by all_goals (simp_all <;> omega)

  @[simp] theorem uniform_default_branches_translated (branches : List (Advanced.Expr × Advanced.Expr)) :
      uniformDefaultBranches (branches.map fun pair => (translateExpr pair.1, translateExpr pair.2)) =
        uniformDefaultBranches branches := by
    cases branches with
    | nil => rfl
    | cons head tail =>
      cases head with
      | mk condition value =>
        simp only [List.map_cons, uniformDefaultBranches,
          uniform_default_expr_translated condition, uniform_default_expr_translated value,
          uniform_default_branches_translated tail]
  termination_by sizeOf branches
  decreasing_by all_goals (simp_all <;> omega)
end

private theorem uniform_default_items_translated (items : List Advanced.SelectItem) :
    (items.map translateSelectItem).all (fun item => match item with
      | .all .. => true | .expression expr _ => uniformDefaultExpr expr) =
    items.all (fun item => match item with
      | .all .. => true | .expression expr _ => uniformDefaultExpr expr) := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
    cases head <;> simp only [List.map_cons, List.all_cons, translateSelectItem,
      uniform_default_expr_translated, ih]

private theorem uniform_default_order_translated (order : Advanced.OrderBy) :
    uniformDefaultExpr (translateOrderBy order).expr = uniformDefaultExpr order.expr := by
  simp only [translateOrderBy, uniform_default_expr_translated]

mutual
  @[simp] theorem uniform_default_query_translated (catalog : Catalog) (env : CTEEnv)
      (target : Name) (locals : List Name) (query : Advanced.Query) :
      uniformDefaultQuery catalog env target locals (translateParameters query) =
        uniformDefaultQuery catalog env target locals query := by
    cases query with
    | mk body ctes recursive orders limit offset locking offsetFirst =>
      have definitions := uniform_default_ctes_translated catalog env target
        (if recursive then ctes.map Advanced.CTE.name ++ locals else locals) ctes
      cases body with
      | values rows =>
        cases limit <;> cases offset <;> rw [translateParameters] <;>
          simp only [translate_values_body, List.attach_map_val]
        all_goals conv => lhs; rw [uniformDefaultQuery.eq_def]
        all_goals conv => rhs; rw [uniformDefaultQuery.eq_def]
        all_goals simp only [List.attach_map_val]
        all_goals simp only [recursive_cte_names_translated, definitions, List.all_map,
          Function.comp_def, uniform_default_exprs_translated, uniform_default_order_translated,
          uniform_default_expr_translated, Option.all]
      | select select =>
        cases select with
        | mk items source whereClause groupBy having distinct distinctOn =>
          have sourceEq :
              source.all (fun inputSource => uniformDefaultSource catalog env target
                (ctes.map Advanced.CTE.name ++ locals) (translateSource inputSource)) =
              source.all (fun inputSource => uniformDefaultSource catalog env target
                (ctes.map Advanced.CTE.name ++ locals) inputSource) := by
            cases source with
            | none => rfl
            | some inputSource => exact uniform_default_source_translated catalog env target _ inputSource
          cases source <;> cases whereClause <;> cases having <;> cases limit <;> cases offset <;>
            rw [translateParameters] <;>
            simp only [translateQueryBody, translateSelect, List.attach_map_val]
          all_goals conv => lhs; rw [uniformDefaultQuery.eq_def]
          all_goals conv => rhs; rw [uniformDefaultQuery.eq_def]
          all_goals simp only [Option.all] at sourceEq
          all_goals simp only [recursive_cte_names_translated, definitions, sourceEq,
            List.all_map, Function.comp_def,
            uniform_default_order_translated, uniform_default_expr_translated,
            uniform_default_exprs_translated, Option.all]
          all_goals congr 9 <;> first
            | rfl
            | (apply congrArg (fun f => items.all f); funext item; cases item <;> simp only [translateSelectItem, uniform_default_expr_translated])
      | set op all left right =>
        cases limit <;> cases offset <;> rw [translateParameters] <;>
          simp only [translateQueryBody, List.attach_map_val]
        all_goals conv => lhs; rw [uniformDefaultQuery.eq_def]
        all_goals conv => rhs; rw [uniformDefaultQuery.eq_def]
        all_goals simp only [recursive_cte_names_translated, definitions,
          uniform_default_query_translated catalog env target _ left,
          uniform_default_query_translated catalog env target _ right,
          List.all_map, Function.comp_def, uniform_default_order_translated,
          Option.all, uniform_default_expr_translated]
  termination_by sizeOf query
  decreasing_by all_goals (simp_all <;> omega)

  @[simp] theorem uniform_default_source_translated (catalog : Catalog) (env : CTEEnv)
      (target : Name) (locals : List Name) (source : Advanced.From) :
      uniformDefaultSource catalog env target locals (translateSource source) =
        uniformDefaultSource catalog env target locals source := by
    cases source with
    | table name alias columns schema => simp only [translateSource]
    | derivedAnonymous query lateral =>
      simp only [translateSource, uniformDefaultSource, uniform_default_query_translated catalog env target locals query]
    | derived query alias columns lateral =>
      simp only [translateSource, uniformDefaultSource, uniform_default_query_translated catalog env target locals query]
    | join kind left right condition =>
      cases condition <;>
        simp only [translateSource, translateJoinCondition, uniformDefaultSource,
          uniform_default_source_translated catalog env target locals left,
          uniform_default_source_translated catalog env target locals right,
          uniform_default_expr_translated]
  termination_by sizeOf source
  decreasing_by all_goals (simp_all <;> omega)

  @[simp] theorem uniform_default_ctes_translated (catalog : Catalog) (env : CTEEnv)
      (target : Name) (locals : List Name) (ctes : List Advanced.CTE) :
      uniformDefaultCTEs catalog env target locals (ctes.map translateCTE) =
        uniformDefaultCTEs catalog env target locals ctes := by
    cases ctes with
    | nil => rfl
    | cons head tail =>
      cases head with
      | mk name query columns =>
        simp only [List.map_cons, translateCTE, uniformDefaultCTEs,
          uniform_default_query_translated catalog env target locals query,
          uniform_default_ctes_translated catalog env target (name :: locals) tail]
  termination_by sizeOf ctes
  decreasing_by all_goals (simp_all <;> omega)
end

theorem recursive_collation_safe_translated
    (safe : RecursiveCollationSafe catalog params env name query output) :
    RecursiveCollationSafe catalog params env name (translateParameters query) output := by
  simpa only [RecursiveCollationSafe, uniform_default_query_translated] using safe

end SQLean.RenderContract
