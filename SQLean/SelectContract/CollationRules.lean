import SQLean.SelectContract.ExpressionSpec
import SQLean.SelectContract.CollationApplications

/-! Independent expression collation derivations. Type validity is a separate
premise. Native argument coercions and explicit/implicit merge strength are
recorded even when an operator's Boolean result has no collation. -/
namespace SQLean.SelectContract
open Advanced

inductive CollationAtom : Advanced.Expr → ExprType → CollationDerivation → Prop where
  | int : CollationAtom (.literal (.int value)) type .none
  | decimal : CollationAtom (.decimal value) type .none
  | bool : CollationAtom (.literal (.bool value)) type .none
  | signedInt : CollationAtom (.unary .neg (.literal (.int value))) type .none
  | text : CollationAtom (.literal (.text value)) type .none
  | null : CollationAtom .null none .none
  | context : CollationAtom (.contextValue value) (some (contextValueType value))
      (.stored (contextValueType value).base.defaultCollation)

inductive IndependentCollationChildren : Advanced.Expr → List Advanced.Expr → Prop where
  | isNull : IndependentCollationChildren (.isNull arg negated) [arg]
  | isNullRow : IndependentCollationChildren (.isNull (.row fields) negated) fields
  | distinctNullLeft : IndependentCollationChildren (.distinctFrom .null arg negated) [arg]
  | distinctNullRight : IndependentCollationChildren (.distinctFrom arg .null negated) [arg]
  | distinctRowNullLeft : IndependentCollationChildren (.distinctFrom .null (.row fields) negated) fields
  | distinctRowNullRight : IndependentCollationChildren (.distinctFrom (.row fields) .null negated) fields

/-- Each row-comparison field has an independent selected operator and input
collation. Explicit identities in different field pairs do not conflict. -/
inductive ComparisonCollations :
    List Advanced.Expr → List ExprType → List CollationDerivation →
    List Advanced.Expr → List ExprType → List CollationDerivation →
    List FunctionOverload → Prop where
  | nil : ComparisonCollations [] [] [] [] [] [] []
  | cons (coercion : contextualCollations [a, b] [ta, tb] [da, db]
        (concreteCollationTargets selected.inputs) = some coerced)
      (merge : CollationDerivation.mergeList coerced = some input)
      (tail : ComparisonCollations as ats ads bs bts bds rest) :
      ComparisonCollations (a :: as) (ta :: ats) (da :: ads)
        (b :: bs) (tb :: bts) (db :: bds) (selected :: rest)

inductive CaseConditionCollations :
    ExactType → CollationDerivation → List Advanced.Expr →
    List ExprType → List CollationDerivation → Prop where
  | nil : CaseConditionCollations operand derivation [] [] []
  | cons (selected : equalityOverload (.known operand) (scalarInput condition type) = some signature)
      (arguments : signature.inputs = [leftType, rightType])
      (merge : CollationDerivation.merge
        (knownCoercedCollation operand.base leftType derivation)
        (coercedCollation condition type rightType conditionDerivation) = some input)
      (tail : CaseConditionCollations operand derivation conditions types derivations) :
      CaseConditionCollations operand derivation (condition :: conditions)
        (type :: types) (conditionDerivation :: derivations)

/-- Ungrouped IN members are independent equality comparisons. -/
inductive InScalarCollations (arg : Advanced.Expr) (type : ExprType) (derivation : CollationDerivation) :
    List (Advanced.Expr × ExprType × CollationDerivation) → Prop where
  | nil : InScalarCollations arg type derivation []
  | cons (selected : equalityOverload (scalarInput arg type) (scalarInput value valueType) = some signature)
      (coercions : contextualCollations [arg, value] [type, valueType] [derivation, valueDerivation]
        (concreteCollationTargets signature.inputs) = some coerced)
      (merged : CollationDerivation.mergeList coerced = some input)
      (tail : InScalarCollations arg type derivation rest) :
      InScalarCollations arg type derivation ((value, valueType, valueDerivation) :: rest)

/-- PostgreSQL combines two or more Var-free RHS members into one array
when their common type has an array type. Remaining Var-bearing members keep
independent equality contexts. -/
inductive InCollations (arg : Advanced.Expr) (type : ExprType) (derivation : CollationDerivation)
    (es : List Advanced.Expr) (types : List ExprType) (derivations : List CollationDerivation) : Prop where
  | scalar (few : (inConstantArguments es types derivations).length ≤ 1)
      (pairs : InScalarCollations arg type derivation (inCollationArguments es types derivations)) :
      InCollations arg type derivation es types derivations
  | noCommon (common : conditionalBase (scalarInput arg type ::
        (inConstantArguments es types derivations).map (fun row => scalarInput row.1 row.2.1)) = none)
      (pairs : InScalarCollations arg type derivation (inCollationArguments es types derivations)) :
      InCollations arg type derivation es types derivations
  | arrays (common : conditionalBase (scalarInput arg type ::
        (inConstantArguments es types derivations).map (fun row => scalarInput row.1 row.2.1)) = some base)
      (noArrayType : base.isArray = true)
      (pairs : InScalarCollations arg type derivation (inCollationArguments es types derivations)) :
      InCollations arg type derivation es types derivations
  | grouped (many : 1 < (inConstantArguments es types derivations).length)
      (common : conditionalBase (scalarInput arg type ::
        (inConstantArguments es types derivations).map (fun row => scalarInput row.1 row.2.1)) = some base)
      (hasArrayType : base.isArray = false)
      (coercions : coercedCollations
        ((inConstantArguments es types derivations).map Prod.fst)
        ((inConstantArguments es types derivations).map (fun row => row.2.1))
        ((inConstantArguments es types derivations).map (fun row => row.2.2))
        (List.replicate (inConstantArguments es types derivations).length base) = some coerced)
      (arrayMerge : CollationDerivation.mergeList coerced = some arrayInput)
      (selected : equalityOverload (.known ⟨base, false⟩) (.known ⟨base, false⟩) = some signature)
      (inputs : signature.inputs = [leftType, rightType])
      (merged : CollationDerivation.merge
        (knownCoercedCollation base leftType (coercedCollation arg type base derivation))
        (knownCoercedCollation base.asArray rightType.asArray (base.asArray.collationResult arrayInput)) = some input)
      (pairs : InScalarCollations arg type derivation (inVariableArguments es types derivations)) :
      InCollations arg type derivation es types derivations

mutual
  inductive ExprCollationValid (profile : Profile) (params : ParameterEnv) (scope : Scope) :
      Advanced.Expr → ExprType → CollationDerivation → Prop where
    | atom (typed : ExprValid params scope expr type uses)
        (atom : CollationAtom expr type derivation) :
        ExprCollationValid profile params scope expr type derivation
    | parameter (present : binding ∈ params) (identity : binding.index = parameterIndex parameter)
        (supported : concreteType binding.type = some base) :
        ExprCollationValid profile params scope (.parameter parameter)
          (some ⟨base.unmodified, binding.nullable⟩) (.stored base.unmodified.defaultCollation)
    | column (resolved : Resolves scope qualifier name column schema) :
        ExprCollationValid profile params scope (.column qualifier name schema)
          (some column.type) (.stored column.collation)
    | application (typed : ExprValid params scope expr type uses)
        (children : ExprCollationListValid profile params scope es types derivations)
        (application : CollationApplication expr es types targets)
        (coercions : contextualCollations es types derivations targets = some coerced)
        (merge : CollationDerivation.mergeList coerced = some input) :
        ExprCollationValid profile params scope expr type (resultCollation type input)
    | independent (typed : ExprValid params scope expr type uses)
        (children : ExprCollationListValid profile params scope es types derivations)
        (shape : IndependentCollationChildren expr es) :
        ExprCollationValid profile params scope expr type .none
    | cast (typed : ExprValid params scope (.cast arg target) type uses)
        (child : ExprCollationValid profile params scope arg input derivation)
        (supported : concreteType target = some base) :
        ExprCollationValid profile params scope (.cast arg target) type
          (coercedCollation arg input base derivation)
    | collate (typed : ExprValid params scope (.collate arg name) type uses)
        (child : ExprCollationValid profile params scope arg type derivation)
        (resolved : profile.collations.lookup name = some entry)
        (allowed : (scalarInput arg type).base.isNone ||
          (scalarInput arg type).base.any ScalarType.collatable = true) :
        ExprCollationValid profile params scope (.collate arg name) type (.explicit entry.id)
    | castArray (typed : ExprValid params scope (.cast (.array es) target) type uses)
        (supported : concreteType target = some base)
        (elements : ArrayCollationValid profile params scope base es derivation) :
        ExprCollationValid profile params scope (.cast (.array es) target) type derivation
    | subscript (typed : ExprValid params scope (.subscript arg indices) type uses)
        (base : ExprCollationValid profile params scope arg input derivation)
        (bounds : ExprCollationListValid profile params scope
          (indices.flatMap Subscript.expressions) boundTypes boundDerivations) :
        ExprCollationValid profile params scope (.subscript arg indices) type
          (resultCollation type derivation)
    | rowComparison (typed : ExprValid params scope (.binary op.toBinOp (.row as) (.row bs)) type uses)
        (left : ExprCollationListValid profile params scope as ats ads)
        (right : ExprCollationListValid profile params scope bs bts bds)
        (selected : rowComparisonSignature op (scalarInputs as ats) (scalarInputs bs bts) = some signatures)
        (pairs : ComparisonCollations as ats ads bs bts bds signatures) :
        ExprCollationValid profile params scope (.binary op.toBinOp (.row as) (.row bs)) type .none
    | rowDistinct (typed : ExprValid params scope (.distinctFrom (.row as) (.row bs) negated) type uses)
        (left : ExprCollationListValid profile params scope as ats ads)
        (right : ExprCollationListValid profile params scope bs bts bds)
        (selected : rowDistinctSignature (scalarInputs as ats) (scalarInputs bs bts) = some signatures)
        (pairs : ComparisonCollations as ats ads bs bts bds signatures) :
        ExprCollationValid profile params scope (.distinctFrom (.row as) (.row bs) negated) type .none
    | inList (typed : ExprValid params scope (.inList arg es) type uses)
        (child : ExprCollationValid profile params scope arg input derivation)
        (children : ExprCollationListValid profile params scope es types derivations)
        (contexts : InCollations arg input derivation es types derivations) :
        ExprCollationValid profile params scope (.inList arg es) type .none
    | between (typed : ExprValid params scope (.between arg lower upper negated) type uses)
        (args : ExprCollationListValid profile params scope [arg, lower, upper] [ta, tl, tu] [da, dl, du])
        (low : comparisonOverload .ge (scalarInput arg ta) (scalarInput lower tl) = some lowOperator)
        (high : comparisonOverload .le (scalarInput arg ta) (scalarInput upper tu) = some highOperator)
        (pairs : ComparisonCollations [arg, arg] [ta, ta] [da, da]
          [lower, upper] [tl, tu] [dl, du] [lowOperator, highOperator]) :
        ExprCollationValid profile params scope (.between arg lower upper negated) type .none
    | extract (typed : ExprValid params scope (.extract field arg) type uses)
        (child : ExprCollationValid profile params scope arg input derivation)
        (selected : extractSignature (scalarInput arg input) = some signature) :
        ExprCollationValid profile params scope (.extract field arg) type .none
    | defaultCall (typed : ExprValid params scope (.call name es) type uses)
        (children : ExprCollationListValid profile params scope es types derivations)
        (callee : builtinName name = some "make_interval")
        (arguments : ArgumentsBound makeIntervalParameters (es.map fun _ => none)
          (scalarInputs es types) inputs) :
        ExprCollationValid profile params scope (.call name es) type .none
    | namedCall (typed : ExprValid params scope (.namedCall name args) type uses)
        (children : ExprCollationListValid profile params scope
          (args.map CallArgument.expression) types derivations)
        (callee : builtinName name = some "make_interval")
        (arguments : ArgumentsBound makeIntervalParameters (args.map CallArgument.name?)
          (scalarInputs (args.map CallArgument.expression) types) inputs) :
        ExprCollationValid profile params scope (.namedCall name args) type .none
    | substring (typed : ExprValid params scope (.substring form es) type uses)
        (children : ExprCollationListValid profile params scope es types derivations)
        (arguments : SubstringArguments form (scalarInputs es types) inputs)
        (selected : resolveOverload substringCatalog inputs = some signature)
        (targets : substringCollationTargets form signature.inputs = some lexicalTargets)
        (coercions : coercedCollations es types derivations lexicalTargets = some coerced)
        (merge : CollationDerivation.mergeList (substringCollationOrder form coerced) = some input) :
        ExprCollationValid profile params scope (.substring form es) type (resultCollation type input)
    | searchedCase (typed : ExprValid params scope (.caseExpr none branches otherwise) (some type) uses)
        (conditions : ExprCollationListValid profile params scope
          (branches.map Prod.fst) conditionTypes conditionDerivations)
        (results : ExprCollationListValid profile params scope
          (branches.map Prod.snd ++ otherwise.toList) resultTypes resultDerivations)
        (coercions : coercedCollations (branches.map Prod.snd ++ otherwise.toList)
          resultTypes resultDerivations
          (List.replicate (branches.length + otherwise.toList.length) type.base) = some coerced)
        (merge : CollationDerivation.mergeList coerced = some input) :
        ExprCollationValid profile params scope (.caseExpr none branches otherwise)
          (some type) (type.base.collationResult input)
    | simpleCase (typed : ExprValid params scope (.caseExpr (some operand) branches otherwise) (some type) uses)
        (operandValid : ExprCollationValid profile params scope operand operandType operandDerivation)
        (conditions : ExprCollationListValid profile params scope
          (branches.map Prod.fst) conditionTypes conditionDerivations)
        (comparisons : CaseConditionCollations (caseOperandType operandType operand)
          (.stored (coercedCollation operand operandType
            (caseOperandType operandType operand).base operandDerivation).identity)
          (branches.map Prod.fst) conditionTypes conditionDerivations)
        (results : ExprCollationListValid profile params scope
          (branches.map Prod.snd ++ otherwise.toList) resultTypes resultDerivations)
        (coercions : coercedCollations (branches.map Prod.snd ++ otherwise.toList)
          resultTypes resultDerivations
          (List.replicate (branches.length + otherwise.toList.length) type.base) = some coerced)
        (merge : CollationDerivation.mergeList coerced = some input) :
        ExprCollationValid profile params scope (.caseExpr (some operand) branches otherwise)
          (some type) (type.base.collationResult input)

  inductive ExprCollationListValid (profile : Profile) (params : ParameterEnv) (scope : Scope) :
      List Advanced.Expr → List ExprType → List CollationDerivation → Prop where
    | nil : ExprCollationListValid profile params scope [] [] []
    | cons (head : ExprCollationValid profile params scope expr type derivation)
        (tail : ExprCollationListValid profile params scope exprs types derivations) :
        ExprCollationListValid profile params scope (expr :: exprs) (type :: types) (derivation :: derivations)

  /-- A direct array cast supplies one type to every raw nested constructor.
  Empty arrays therefore need no invented inference derivation. -/
  inductive ArrayCollationValid (profile : Profile) (params : ParameterEnv) (scope : Scope) :
      ScalarType → List Advanced.Expr → CollationDerivation → Prop where
    | targeted (elements : ArrayElementsCollationValid profile params scope target es ts ds)
        (coercions : coercedCollations es ts ds
          (List.replicate es.length
            (if (scalarInputs es ts).any (fun input => input.base.any ScalarType.isArray)
             then target else target.arrayElement)) = some coerced)
        (merge : CollationDerivation.mergeList coerced = some input) :
        ArrayCollationValid profile params scope target es (target.collationResult input)

  inductive ArrayElementsCollationValid (profile : Profile) (params : ParameterEnv) (scope : Scope) :
      ScalarType → List Advanced.Expr → List ExprType → List CollationDerivation → Prop where
    | nil : ArrayElementsCollationValid profile params scope target [] [] []
    | ordinary (category : OrdinaryArrayElement expr)
        (head : ExprCollationValid profile params scope expr type derivation)
        (tail : ArrayElementsCollationValid profile params scope target exprs types derivations) :
        ArrayElementsCollationValid profile params scope target (expr :: exprs)
          (type :: types) (derivation :: derivations)
    | nested (head : ArrayCollationValid profile params scope target exprs derivation)
        (tail : ArrayElementsCollationValid profile params scope target rest types derivations) :
        ArrayElementsCollationValid profile params scope target (.array exprs :: rest)
          (some ⟨target, false⟩ :: types) (derivation :: derivations)
end

end SQLean.SelectContract
