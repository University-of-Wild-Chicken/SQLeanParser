import SQLean.SelectContract.Collation

/-! Local native argument coercions for expression collation. These declarations
describe operator/function arguments after type resolution. They are independent
of traversal, resource bounds, and executable inference. -/
namespace SQLean.SelectContract
open Advanced

inductive CollationApplication :
    Advanced.Expr → List Advanced.Expr → List ExprType → List (Option ScalarType) → Prop where
  | boolean (op : BinOp) (ordinary : op = .and ∨ op = .or) :
      CollationApplication (.binary op a b) [a, b] [ta, tb] [some .bool, some .bool]
  | arithmetic (op : BinOp) (ordinary : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .div)
      (selected : binarySignature op ta tb = some (some result)) :
      CollationApplication (.binary op a b) [a, b] [ta, tb]
        [some ((ta.map ExactType.base).getD result.base), some ((tb.map ExactType.base).getD result.base)]
  | comparison (op : ComparisonOp)
      (selected : comparisonOverload op (scalarInput a ta) (scalarInput b tb) = some signature) :
      CollationApplication (.binary op.toBinOp a b) [a, b] [ta, tb]
        (concreteCollationTargets signature.inputs)
  | concat (selected : concatSignature (scalarInput a ta) (scalarInput b tb) = some signature) :
      CollationApplication (.concat a b) [a, b] [ta, tb]
        (concreteCollationTargets signature.inputs)
  | arrayConcat (selected : arrayConcatSignature (scalarInput a ta) (scalarInput b tb) = some signature) :
      CollationApplication (.concat a b) [a, b] [ta, tb]
        (concreteCollationTargets signature.inputs)
  | distinct (left : OrdinaryDistinctOperand a) (right : OrdinaryDistinctOperand b)
      (selected : distinctSignature (scalarInput a ta) (scalarInput b tb) = some signature) :
      CollationApplication (.distinctFrom a b negated) [a, b] [ta, tb]
        (concreteCollationTargets signature.inputs)
  | unary (selected : unarySignature op ta = some (some result)) :
      CollationApplication (.unary op a) [a] [ta]
        [some ((ta.map ExactType.base).getD result.base)]
  | pattern (selected : stringMatchSignature (scalarInput a ta) (scalarInput b tb) = some signature) :
      CollationApplication (.pattern a b false) [a, b] [ta, tb]
        (concreteCollationTargets signature.inputs)
  | byteaPattern (left : acceptsBase .bytea ta = true) (right : acceptsBase .bytea tb = true) :
      CollationApplication (.pattern a b false) [a, b] [ta, tb] [some .bytea, some .bytea]
  | ilike (selected : stringMatchSignature (scalarInput a ta) (scalarInput b tb) = some signature) :
      CollationApplication (.pattern a b true) [a, b] [ta, tb]
        (concreteCollationTargets signature.inputs)
  | regex (selected : stringMatchSignature (scalarInput a ta) (scalarInput b tb) = some signature) :
      CollationApplication (.regex a b insensitive negated) [a, b] [ta, tb]
        (concreteCollationTargets signature.inputs)
  | jsonAccess (selected : jsonAccessSignature op (scalarInput a ta) (scalarInput b tb) = some signature) :
      CollationApplication (.jsonAccess op a b) [a, b] [ta, tb]
        (concreteCollationTargets signature.inputs)
  | jsonExistence (selected : jsonExistenceSignature op (scalarInput a ta) (scalarInput b tb) = some signature) :
      CollationApplication (.jsonExistence op a b) [a, b] [ta, tb]
        (concreteCollationTargets signature.inputs)
  | containment (selected : jsonContainmentSignature (scalarInput a ta) (scalarInput b tb) = some signature) :
      CollationApplication (.containment a b containedBy) [a, b] [ta, tb]
        (concreteCollationTargets signature.inputs)
  | arrayContainment (selected : arrayPredicateSignature (scalarInput a ta) (scalarInput b tb) = some signature) :
      CollationApplication (.containment a b containedBy) [a, b] [ta, tb]
        (concreteCollationTargets signature.inputs)
  | overlap (selected : arrayPredicateSignature (scalarInput a ta) (scalarInput b tb) = some signature) :
      CollationApplication (.overlap a b) [a, b] [ta, tb]
        (concreteCollationTargets signature.inputs)
  | array (common : conditionalBase (scalarInputs es ts) = some base) :
      CollationApplication (.array es) es ts (List.replicate es.length (some base))
  | call (callee : builtinName name = some functionName)
      (selected : resolveOverload (functionCatalog functionName) (scalarInputs es ts) = some signature) :
      CollationApplication (.call name es) es ts (concreteCollationTargets signature.inputs)
  /-- Polymorphic ANY arguments are not converted to TEXT merely because the
  result is TEXT. Their input collation can remain absent. -/
  | variadicCall (callee : builtinName name = some functionName)
      (kind : functionName = "concat" ∨ functionName = "num_nulls" ∨ functionName = "num_nonnulls") :
      CollationApplication (.call name es) es ts (List.replicate es.length none)
  | concatWS (callee : builtinName name = some "concat_ws") :
      CollationApplication (.call name (separator :: es)) (separator :: es) (separatorType :: ts)
        (some .text :: List.replicate es.length none)
  | coalesce (common : conditionalBase (scalarInputs es ts) = some base) :
      CollationApplication (.coalesce es) es ts (List.replicate es.length (some base))
  | greatest (common : conditionalBase (scalarInputs es ts) = some base) :
      CollationApplication (.greatest es) es ts (List.replicate es.length (some base))
  | least (common : conditionalBase (scalarInputs es ts) = some base) :
      CollationApplication (.least es) es ts (List.replicate es.length (some base))
  | nullIf (selected : equalityOverload (scalarInput a ta) (scalarInput b tb) = some signature) :
      CollationApplication (.nullIf a b) [a, b] [ta, tb]
        (concreteCollationTargets signature.inputs)
  | quantified (selected : quantifiedComparisonSignature op
        (scalarInput a ta) (scalarInput b tb) = some signature)
      (inputs : signature.inputs = [leftType, rightType]) :
      CollationApplication (.quantifiedComparison op quantifier a b) [a, b] [ta, tb]
        [some leftType, some rightType.asArray]

end SQLean.SelectContract
