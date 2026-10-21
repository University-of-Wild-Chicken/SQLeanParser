import SQLean.SelectContract.CollationRules

/-! Independent VALUES rules. Rows have no local input namespace. Each cell
records its scalar input and native collation coercion for a later common type;
no query checker or left-associated set operation participates in these rules. -/
namespace SQLean.SelectContract
open Advanced
set_option inductive.autoPromoteIndices false

structure ValuesCell where
  input : ScalarInput
  coercion : ScalarType → CollationDerivation

def valuesCell (expr : Advanced.Expr) (type : ExprType)
    (derivation : CollationDerivation) : ValuesCell :=
  ⟨scalarInput expr type, fun target => coercedCollation expr type target derivation⟩

inductive ValuesRowValidCore (subqueries : SubqueryJudgment) (profile : Profile)
    (params : ParameterEnv) :
    CTEEnv → List Advanced.Expr → List ValuesCell → List Parameter → Prop where
  | nil : ValuesRowValidCore subqueries profile params env [] [] []
  | cons (typed : ExprValidCore subqueries params env .empty expr type headUses)
      (collation : ExprCollationValidCore subqueries profile params env .empty expr type derivation)
      (tail : ValuesRowValidCore subqueries profile params env exprs cells tailUses) :
      ValuesRowValidCore subqueries profile params env (expr :: exprs)
        (valuesCell expr type derivation :: cells) (headUses ++ tailUses)

inductive ValuesRowsValidCore (subqueries : SubqueryJudgment) (profile : Profile)
    (params : ParameterEnv) :
    CTEEnv → List (List Advanced.Expr) → List (List ValuesCell) → List Parameter → Prop where
  | nil : ValuesRowsValidCore subqueries profile params env [] [] []
  | cons (head : ValuesRowValidCore subqueries profile params env row cells headUses)
      (tail : ValuesRowsValidCore subqueries profile params env rows rest tailUses) :
      ValuesRowsValidCore subqueries profile params env (row :: rows) (cells :: rest)
        (headUses ++ tailUses)

/-- PostgreSQL permits neither a zero-width row nor ragged VALUES rows. -/
def valuesShape : List (List Advanced.Expr) → Bool
  | [] => false
  | first :: rest => !first.isEmpty && rest.all (fun row => row.length == first.length)

/-- Transpose only after the independent row-shape premise has been checked.
All column inputs remain in original row order for directional common typing. -/
def valuesTranspose (rows : List (List ValuesCell)) : List (List ValuesCell) :=
  (List.range (rows.headD []).length).map fun index =>
    rows.filterMap fun row => row[index]?

/-- conditionalBase resolves the entire column simultaneously. It retains a
modifier only when every input has exactly that type. Unknown literals acquire
the target with no typmod, so an unknown alongside VARCHAR(n), for example,
correctly removes n before common typmod selection. Collation is merged after
coercion; implicit indeterminacy is a valid output, explicit conflict is not. -/
inductive ValuesColumnsValid : Nat → List (List ValuesCell) → List OutputColumn → Prop where
  | nil : ValuesColumnsValid index [] []
  | cons (common : conditionalBase (cells.map ValuesCell.input) = some base)
      (coercions : (cells.map ValuesCell.input).all (fun input => acceptsInput input base) = true)
      (collation : CollationDerivation.mergeList (cells.map (fun cell => cell.coercion base)) = some derivation)
      (tail : ValuesColumnsValid (index + 1) columns output) :
      ValuesColumnsValid index (cells :: columns)
        (⟨"column" ++ toString (index + 1),
          ⟨base, cells.any (fun cell => cell.input.nullable)⟩, derivation.identity⟩ :: output)

end SQLean.SelectContract
