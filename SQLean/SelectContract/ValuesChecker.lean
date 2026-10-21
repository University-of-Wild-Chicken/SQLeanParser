import SQLean.SelectContract.CollationChecker

/-! The bounded VALUES implementation constructs the independent row and
column derivations. The target-parametric cell annotation is supplied only by
certified typing and collation premises, never by executing source SQL. -/
namespace SQLean.SelectContract
open Advanced

structure ValuesRowCertificate (subqueries : SubqueryJudgment) (profile : Profile)
    (params : ParameterEnv) (env : CTEEnv) (row : List Advanced.Expr) where
  cells : List ValuesCell
  uses : List Parameter
  valid : ValuesRowValidCore subqueries profile params env row cells uses

structure ValuesRowsCertificate (subqueries : SubqueryJudgment) (profile : Profile)
    (params : ParameterEnv) (env : CTEEnv) (rows : List (List Advanced.Expr)) where
  cells : List (List ValuesCell)
  uses : List Parameter
  valid : ValuesRowsValidCore subqueries profile params env rows cells uses

def checkValuesRow (subqueries : SubqueryJudgment) (env : CTEEnv)
    (checkSubquery : SubqueryChecker subqueries env) (fuel : Nat) (profile : Profile)
    (params : ParameterEnv) (row : List Advanced.Expr) :
    Except Failure (ValuesRowCertificate subqueries profile params env row) :=
  match fuel with
  | 0 => .error exhausted
  | fuel + 1 => match row with
    | [] => .ok ⟨[], [], .nil⟩
    | expr :: exprs => do
      let head ← checkCompleteExprCore subqueries env checkSubquery fuel profile params .empty expr
      let tail ← checkValuesRow subqueries env checkSubquery fuel profile params exprs
      .ok ⟨valuesCell expr head.type head.derivation :: tail.cells, head.uses ++ tail.uses,
        .cons head.valid head.collationValid tail.valid⟩

def checkValuesRows (subqueries : SubqueryJudgment) (env : CTEEnv)
    (checkSubquery : SubqueryChecker subqueries env) (fuel : Nat) (profile : Profile)
    (params : ParameterEnv) (rows : List (List Advanced.Expr)) :
    Except Failure (ValuesRowsCertificate subqueries profile params env rows) :=
  match fuel with
  | 0 => .error exhausted
  | fuel + 1 => match rows with
    | [] => .ok ⟨[], [], .nil⟩
    | row :: rows => do
      let head ← checkValuesRow subqueries env checkSubquery fuel profile params row
      let tail ← checkValuesRows subqueries env checkSubquery fuel profile params rows
      .ok ⟨head.cells :: tail.cells, head.uses ++ tail.uses, .cons head.valid tail.valid⟩

def checkValuesColumns (fuel index : Nat) (columns : List (List ValuesCell)) :
    Except Failure {output : List OutputColumn // ValuesColumnsValid index columns output} :=
  match fuel with
  | 0 => .error exhausted
  | fuel + 1 => match columns with
    | [] => .ok ⟨[], .nil⟩
    | cells :: columns => do
      match common : conditionalBase (cells.map ValuesCell.input) with
      | none => .error (invalid "values_common_type" "VALUES column inputs have no common native scalar type")
      | some base =>
        if coercions : (cells.map ValuesCell.input).all (fun input => acceptsInput input base) = true then
          match collation : CollationDerivation.mergeList (cells.map (fun cell => cell.coercion base)) with
          | none => .error (invalid "collation_conflict" "VALUES column combines different explicit collations")
          | some derivation =>
            let tail ← checkValuesColumns fuel (index + 1) columns
            .ok ⟨⟨"column" ++ toString (index + 1),
              ⟨base, cells.any (fun cell => cell.input.nullable)⟩, derivation.identity⟩ :: tail.val,
              .cons common coercions collation tail.property⟩
        else .error (invalid "values_common_type" "VALUES input cannot be coerced to its column's common type")

end SQLean.SelectContract
