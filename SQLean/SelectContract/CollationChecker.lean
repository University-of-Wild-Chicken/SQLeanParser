import SQLean.SelectContract.ExpressionChecker

/-! Proof-producing collation annotation. Successful branches construct the
independent CollationRules judgments; no native execution is used as evidence. -/
namespace SQLean.SelectContract
open Advanced

structure CompleteExprCertificateCore (subqueries : SubqueryJudgment) (env : CTEEnv) (profile : Profile) (params : ParameterEnv)
    (scope : Scope) (expr : Advanced.Expr) extends ExprCertificateCore subqueries env params scope expr where
  derivation : CollationDerivation
  collationValid : ExprCollationValidCore subqueries profile params env scope expr type derivation

structure CollationListCertificateCore (subqueries : SubqueryJudgment) (env : CTEEnv) (profile : Profile) (params : ParameterEnv)
    (scope : Scope) (exprs : List Advanced.Expr) where
  types : List ExprType
  derivations : List CollationDerivation
  valid : ExprCollationListValidCore subqueries profile params env scope exprs types derivations

structure ArrayCollationCertificateCore (subqueries : SubqueryJudgment) (env : CTEEnv) (profile : Profile) (params : ParameterEnv)
    (scope : Scope) (target : ScalarType) (exprs : List Advanced.Expr) where
  derivation : CollationDerivation
  valid : ArrayCollationValidCore subqueries profile params env scope target exprs derivation

structure ArrayElementsCollationCertificateCore (subqueries : SubqueryJudgment) (env : CTEEnv) (profile : Profile) (params : ParameterEnv)
    (scope : Scope) (target : ScalarType) (exprs : List Advanced.Expr) where
  types : List ExprType
  derivations : List CollationDerivation
  valid : ArrayElementsCollationValidCore subqueries profile params env scope target exprs types derivations

private def conflict : Failure :=
  invalid "collation_conflict" "Different explicit collation identities cannot be combined in one native input context"

private def collationShape : Failure :=
  unsupported "collation_expression" "This expression's native collation normalization has no independent rule"

private def applicationCertificate (typed : ExprCertificateCore subqueries env params scope expr)
    (children : CollationListCertificateCore subqueries env profile params scope es)
    (application : CollationApplication expr es children.types targets) :
    Except Failure (CompleteExprCertificateCore subqueries env profile params scope expr) := do
  match coercions : contextualCollations es children.types children.derivations targets with
  | none => .error collationShape
  | some coerced =>
    match merge : CollationDerivation.mergeList coerced with
    | none => .error conflict
    | some input => .ok ⟨typed, resultCollation typed.type input,
        .application typed.valid children.valid application coercions merge⟩

private def pairCertificate (left : CompleteExprCertificateCore subqueries env profile params scope a)
    (right : CompleteExprCertificateCore subqueries env profile params scope b) :
    CollationListCertificateCore subqueries env profile params scope [a, b] :=
  ⟨[left.type, right.type], [left.derivation, right.derivation],
    .cons left.collationValid (.cons right.collationValid .nil)⟩

private def checkComparisonCollations
    (as : List Advanced.Expr) (ats : List ExprType) (ads : List CollationDerivation)
    (bs : List Advanced.Expr) (bts : List ExprType) (bds : List CollationDerivation)
    (signatures : List FunctionOverload) :
    Except Failure (PLift (ComparisonCollations as ats ads bs bts bds signatures)) :=
  match as, ats, ads, bs, bts, bds, signatures with
  | [], [], [], [], [], [], [] => .ok ⟨.nil⟩
  | a :: as, ta :: ats, da :: ads, b :: bs, tb :: bts, db :: bds, selected :: rest => do
    match coercion : contextualCollations [a, b] [ta, tb] [da, db]
        (concreteCollationTargets selected.inputs) with
    | none => .error collationShape
    | some coerced =>
      match merge : CollationDerivation.mergeList coerced with
      | none => do
        .error conflict
      | some _ => do
        let tail ← checkComparisonCollations as ats ads bs bts bds rest
        .ok ⟨.cons coercion merge tail.down⟩
  | _, _, _, _, _, _, _ => .error collationShape

private def checkCaseCollations (operand : ExactType) (derivation : CollationDerivation)
    (conditions : List Advanced.Expr) (types : List ExprType) (derivations : List CollationDerivation) :
    Except Failure (PLift (CaseConditionCollations operand derivation conditions types derivations)) :=
  match conditions, types, derivations with
  | [], [], [] => .ok ⟨.nil⟩
  | condition :: conditions, type :: types, conditionDerivation :: derivations => do
    match selected : equalityOverload (.known operand) (scalarInput condition type) with
    | none => .error collationShape
    | some signature =>
      match arguments : signature.inputs with
      | [leftType, rightType] => do
        match merge : CollationDerivation.merge
            (knownCoercedCollation operand.base leftType derivation)
            (coercedCollation condition type rightType conditionDerivation) with
        | none => .error conflict
        | some _ =>
          let tail ← checkCaseCollations operand derivation conditions types derivations
          .ok ⟨.cons selected arguments merge tail.down⟩
      | _ => .error collationShape
  | _, _, _ => .error collationShape

private def checkInScalarCollations (arg : Advanced.Expr) (type : ExprType)
    (derivation : CollationDerivation) (rows : List (Advanced.Expr × ExprType × CollationDerivation)) :
    Except Failure (PLift (InScalarCollations arg type derivation rows)) :=
  match rows with
  | [] => .ok ⟨.nil⟩
  | (value, valueType, valueDerivation) :: rest => do
    match selected : equalityOverload (scalarInput arg type) (scalarInput value valueType) with
    | none => .error collationShape
    | some signature =>
      match coercions : contextualCollations [arg, value] [type, valueType] [derivation, valueDerivation]
          (concreteCollationTargets signature.inputs) with
      | none => .error collationShape
      | some coerced =>
        match merged : CollationDerivation.mergeList coerced with
        | none => .error conflict
        | some _ =>
          let tail ← checkInScalarCollations arg type derivation rest
          .ok ⟨.cons selected coercions merged tail.down⟩

private def checkInCollations (arg : Advanced.Expr) (type : ExprType)
    (derivation : CollationDerivation) (es : List Advanced.Expr) (types : List ExprType)
    (derivations : List CollationDerivation) :
    Except Failure (PLift (InCollations arg type derivation es types derivations)) := do
  if few : (inConstantArguments es types derivations).length ≤ 1 then
    let pairs ← checkInScalarCollations arg type derivation (inCollationArguments es types derivations)
    .ok ⟨.scalar few pairs.down⟩
  else
    match common : conditionalBase (scalarInput arg type ::
        (inConstantArguments es types derivations).map (fun row => scalarInput row.1 row.2.1)) with
    | none => do
      let pairs ← checkInScalarCollations arg type derivation (inCollationArguments es types derivations)
      .ok ⟨.noCommon common pairs.down⟩
    | some base =>
      if noArrayType : base.isArray = true then
        let pairs ← checkInScalarCollations arg type derivation (inCollationArguments es types derivations)
        .ok ⟨.arrays common noArrayType pairs.down⟩
      else
        have hasArrayType : base.isArray = false := Bool.eq_false_iff.mpr noArrayType
        match coercions : coercedCollations
            ((inConstantArguments es types derivations).map Prod.fst)
            ((inConstantArguments es types derivations).map (fun row => row.2.1))
            ((inConstantArguments es types derivations).map (fun row => row.2.2))
            (List.replicate (inConstantArguments es types derivations).length base) with
        | none => .error collationShape
        | some coerced =>
          match arrayMerge : CollationDerivation.mergeList coerced with
          | none => .error conflict
          | some arrayInput =>
            match selected : equalityOverload (.known ⟨base, false⟩) (.known ⟨base, false⟩) with
            | none => .error collationShape
            | some signature =>
              match inputs : signature.inputs with
              | [leftType, rightType] =>
                match merged : CollationDerivation.merge
                    (knownCoercedCollation base leftType (coercedCollation arg type base derivation))
                    (knownCoercedCollation base.asArray rightType.asArray (base.asArray.collationResult arrayInput)) with
                | none => .error conflict
                | some _ =>
                  let pairs ← checkInScalarCollations arg type derivation (inVariableArguments es types derivations)
                  .ok ⟨.grouped (by omega) common hasArrayType coercions arrayMerge selected inputs merged pairs.down⟩
              | _ => .error collationShape

mutual
  def checkCompleteExprCore (subqueries : SubqueryJudgment) (env : CTEEnv)
      (checkSubquery : SubqueryChecker subqueries env) (fuel : Nat) (profile : Profile) (params : ParameterEnv)
      (scope : Scope) (expr : Advanced.Expr) :
      Except Failure (CompleteExprCertificateCore subqueries env profile params scope expr) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => match expr with
      | .literal (.int value) => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.literal (.int value))
        .ok ⟨typed, .none, .atom typed.valid .int⟩
      | .literal (.text value) => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.literal (.text value))
        .ok ⟨typed, .none, .atom typed.valid .text⟩
      | .literal (.bool value) => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.literal (.bool value))
        .ok ⟨typed, .none, .atom typed.valid .bool⟩
      | .decimal value => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.decimal value)
        .ok ⟨typed, .none, .atom typed.valid .decimal⟩
      | .unary .neg (.literal (.int value)) => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.unary .neg (.literal (.int value)))
        .ok ⟨typed, .none, .atom typed.valid .signedInt⟩
      | .null => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.null)
        if typeEq : typed.type = none then
          .ok ⟨typed, .none, by
            have root : ExprValidCore subqueries params env scope .null none typed.uses := by simpa only [typeEq] using typed.valid
            simpa only [typeEq] using (ExprCollationValidCore.atom (profile := profile) root CollationAtom.null)⟩
        else .error collationShape
      | .contextValue value => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.contextValue value)
        if typeEq : typed.type = some (contextValueType value) then
          .ok ⟨typed, .stored (contextValueType value).base.defaultCollation,
            by
              have root : ExprValidCore subqueries params env scope (.contextValue value) (some (contextValueType value)) typed.uses := by
                simpa only [typeEq] using typed.valid
              simpa only [typeEq] using (ExprCollationValidCore.atom (profile := profile) root CollationAtom.context)⟩
        else .error collationShape
      | .parameter parameter => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.parameter parameter)
        match present : params.find? (fun binding => binding.index == parameterIndex parameter) with
        | none => .error collationShape
        | some binding =>
          have member := List.mem_of_find?_eq_some present
          have identity : binding.index = parameterIndex parameter := by
            simpa using List.find?_some present
          match supported : concreteType binding.type with
          | none => .error collationShape
          | some base =>
            if typeEq : typed.type = some ⟨base.unmodified, binding.nullable⟩ then
              .ok ⟨typed, .stored base.unmodified.defaultCollation,
                by rw [typeEq]; exact .parameter member identity supported⟩
            else .error collationShape
      | .column qualifier name schema => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.column qualifier name schema)
        match resolved : (scope.columns qualifier schema).filter (fun column => column.name == name) with
        | [column] =>
          if typeEq : typed.type = some column.type then
            .ok ⟨typed, .stored column.collation, by rw [typeEq]; exact .column resolved⟩
          else .error collationShape
        | _ => .error collationShape
      | .collate arg name => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.collate arg name)
        if name.length > 3 then
          throw (invalid "collation_name" "A collation name has at most three components")
        if name.length == 3 then
          throw (unsupported "collation_database" "Database-qualified collations require a current-database identity")
        let child ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope arg
        if typeEq : child.type = typed.type then
          match resolved : profile.collations.lookup name with
          | none => .error (unsupported "collation_environment" "The supplied collation snapshot does not resolve this exact name")
          | some entry =>
            if allowed : (scalarInput arg typed.type).base.isNone ||
                (scalarInput arg typed.type).base.any ScalarType.collatable = true then
              .ok ⟨typed, .explicit entry.id,
                .collate typed.valid (typeEq ▸ child.collationValid) resolved allowed⟩
            else .error (invalid "collation_type" "COLLATE requires a collatable type or an unresolved literal")
        else .error collationShape
      | .cast (.array es) target => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.cast (.array es) target)
        match supported : concreteType target with
        | none => .error collationShape
        | some base =>
          if base.isArray then
            let child ← checkArrayCollationCore subqueries env checkSubquery fuel profile params scope base es
            .ok ⟨typed, child.derivation, .castArray typed.valid supported child.valid⟩
          else
            let child ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope (.array es)
            .ok ⟨typed, coercedCollation (.array es) child.type base child.derivation,
              .cast typed.valid child.collationValid supported⟩
      | .cast arg target => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.cast arg target)
        match supported : concreteType target with
        | none => .error collationShape
        | some base =>
          let child ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope arg
          .ok ⟨typed, coercedCollation arg child.type base child.derivation,
            .cast typed.valid child.collationValid supported⟩
      | .binary op (.row as) (.row bs) => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.binary op (.row as) (.row bs))
        let left ← checkCollationListCore subqueries env checkSubquery fuel profile params scope as
        let right ← checkCollationListCore subqueries env checkSubquery fuel profile params scope bs
        let comparison := match op with
          | .eq => some ComparisonOp.eq | .ne => some .ne
          | .lt => some .lt | .le => some .le | .gt => some .gt | .ge => some .ge
          | _ => none
        match comparison with
        | none => .error collationShape
        | some comparison =>
          if opEq : op = comparison.toBinOp then
            match selected : rowComparisonSignature comparison
                (scalarInputs as left.types) (scalarInputs bs right.types) with
            | none => .error collationShape
            | some signatures =>
              let pairs ← checkComparisonCollations as left.types left.derivations
                bs right.types right.derivations signatures
              .ok ⟨typed, .none, by
                have root : ExprValidCore subqueries params env scope (.binary comparison.toBinOp (.row as) (.row bs))
                    typed.type typed.uses := by simpa only [opEq] using typed.valid
                simpa only [opEq] using
                  (ExprCollationValidCore.rowComparison root left.valid right.valid selected pairs.down)⟩
          else .error collationShape
      | .binary op a b => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.binary op a b)
        let left ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope a
        let right ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope b
        let children := pairCertificate left right
        match opEq : op with
        | .and => applicationCertificate typed children (by simpa only [opEq, children, pairCertificate] using (CollationApplication.boolean .and (Or.inl rfl)))
        | .or => applicationCertificate typed children (by simpa only [opEq, children, pairCertificate] using (CollationApplication.boolean .or (Or.inr rfl)))
        | .add | .sub | .mul | .div =>
          if ordinary : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .div then
            match selected : binarySignature op left.type right.type with
            | some (some _) => applicationCertificate typed children (.arithmetic op ordinary selected)
            | _ => .error collationShape
          else .error collationShape
        | .eq => match selected : comparisonOverload .eq (scalarInput a left.type) (scalarInput b right.type) with
          | some _ => applicationCertificate typed children (by simpa only [opEq, ComparisonOp.toBinOp, children, pairCertificate] using (CollationApplication.comparison .eq selected))
          | none => .error collationShape
        | .ne => match selected : comparisonOverload .ne (scalarInput a left.type) (scalarInput b right.type) with
          | some _ => applicationCertificate typed children (by simpa only [opEq, ComparisonOp.toBinOp, children, pairCertificate] using (CollationApplication.comparison .ne selected))
          | none => .error collationShape
        | .lt => match selected : comparisonOverload .lt (scalarInput a left.type) (scalarInput b right.type) with
          | some _ => applicationCertificate typed children (by simpa only [opEq, ComparisonOp.toBinOp, children, pairCertificate] using (CollationApplication.comparison .lt selected))
          | none => .error collationShape
        | .le => match selected : comparisonOverload .le (scalarInput a left.type) (scalarInput b right.type) with
          | some _ => applicationCertificate typed children (by simpa only [opEq, ComparisonOp.toBinOp, children, pairCertificate] using (CollationApplication.comparison .le selected))
          | none => .error collationShape
        | .gt => match selected : comparisonOverload .gt (scalarInput a left.type) (scalarInput b right.type) with
          | some _ => applicationCertificate typed children (by simpa only [opEq, ComparisonOp.toBinOp, children, pairCertificate] using (CollationApplication.comparison .gt selected))
          | none => .error collationShape
        | .ge => match selected : comparisonOverload .ge (scalarInput a left.type) (scalarInput b right.type) with
          | some _ => applicationCertificate typed children (by simpa only [opEq, ComparisonOp.toBinOp, children, pairCertificate] using (CollationApplication.comparison .ge selected))
          | none => .error collationShape
      | .concat a b => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.concat a b)
        let left ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope a
        let right ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope b
        match selected : concatSignature (scalarInput a left.type) (scalarInput b right.type) with
        | some _ => applicationCertificate typed (pairCertificate left right) (.concat selected)
        | none => match selected : arrayConcatSignature (scalarInput a left.type) (scalarInput b right.type) with
          | some _ => applicationCertificate typed (pairCertificate left right) (.arrayConcat selected)
          | none => .error collationShape
      | .containment a b containedBy => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.containment a b containedBy)
        let left ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope a
        let right ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope b
        match selected : jsonContainmentSignature (scalarInput a left.type) (scalarInput b right.type) with
        | some _ => applicationCertificate typed (pairCertificate left right) (.containment selected)
        | none => match selected : arrayPredicateSignature (scalarInput a left.type) (scalarInput b right.type) with
          | some _ => applicationCertificate typed (pairCertificate left right) (.arrayContainment selected)
          | none => .error collationShape
      | .pattern a b false => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.pattern a b false)
        let left ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope a
        let right ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope b
        match selected : stringMatchSignature (scalarInput a left.type) (scalarInput b right.type) with
        | some _ => applicationCertificate typed (pairCertificate left right) (.pattern selected)
        | none =>
          if leftBytea : acceptsBase .bytea left.type = true then
            if rightBytea : acceptsBase .bytea right.type = true then
              applicationCertificate typed (pairCertificate left right) (.byteaPattern leftBytea rightBytea)
            else .error collationShape
          else .error collationShape
      | .quantifiedComparison op quantifier a b => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.quantifiedComparison op quantifier a b)
        let left ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope a
        let right ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope b
        match selected : quantifiedComparisonSignature op (scalarInput a left.type) (scalarInput b right.type) with
        | none => .error collationShape
        | some signature =>
          match inputs : signature.inputs with
          | [_, _] => applicationCertificate typed (pairCertificate left right) (.quantified selected inputs)
          | _ => .error collationShape
      | .isNull (.row fields) negated => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.isNull (.row fields) negated)
        let children ← checkCollationListCore subqueries env checkSubquery fuel profile params scope fields
        .ok ⟨typed, .none, .independent typed.valid children.valid .isNullRow⟩
      | .isNull arg negated => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.isNull arg negated)
        let child ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope arg
        .ok ⟨typed, .none, .independent typed.valid (.cons child.collationValid .nil) .isNull⟩
      | .distinctFrom .null (.row fields) negated => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.distinctFrom .null (.row fields) negated)
        let children ← checkCollationListCore subqueries env checkSubquery fuel profile params scope fields
        .ok ⟨typed, .none, .independent typed.valid children.valid .distinctRowNullLeft⟩
      | .distinctFrom (.row fields) .null negated => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.distinctFrom (.row fields) .null negated)
        let children ← checkCollationListCore subqueries env checkSubquery fuel profile params scope fields
        .ok ⟨typed, .none, .independent typed.valid children.valid .distinctRowNullRight⟩
      | .distinctFrom .null arg negated => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.distinctFrom .null arg negated)
        let child ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope arg
        .ok ⟨typed, .none, .independent typed.valid (.cons child.collationValid .nil) .distinctNullLeft⟩
      | .distinctFrom arg .null negated => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.distinctFrom arg .null negated)
        let child ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope arg
        .ok ⟨typed, .none, .independent typed.valid (.cons child.collationValid .nil) .distinctNullRight⟩
      | .distinctFrom (.row as) (.row bs) negated => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.distinctFrom (.row as) (.row bs) negated)
        let left ← checkCollationListCore subqueries env checkSubquery fuel profile params scope as
        let right ← checkCollationListCore subqueries env checkSubquery fuel profile params scope bs
        match selected : rowDistinctSignature (scalarInputs as left.types) (scalarInputs bs right.types) with
        | none => .error collationShape
        | some signatures =>
          let pairs ← checkComparisonCollations as left.types left.derivations
            bs right.types right.derivations signatures
          .ok ⟨typed, .none, .rowDistinct typed.valid left.valid right.valid selected pairs.down⟩
      | .distinctFrom a b negated => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.distinctFrom a b negated)
        let left ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope a
        let right ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope b
        if ordinaryLeft : OrdinaryDistinctOperand a then
          if ordinaryRight : OrdinaryDistinctOperand b then
            match selected : distinctSignature (scalarInput a left.type) (scalarInput b right.type) with
            | none => .error collationShape
            | some _ =>
              applicationCertificate typed (pairCertificate left right)
                (.distinct ordinaryLeft ordinaryRight selected)
          else .error collationShape
        else .error collationShape
      | .subscript arg indices => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.subscript arg indices)
        let base ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope arg
        let bounds ← checkCollationListCore subqueries env checkSubquery fuel profile params scope (indices.flatMap Subscript.expressions)
        .ok ⟨typed, resultCollation typed.type base.derivation,
          .subscript typed.valid base.collationValid bounds.valid⟩
      | .extract field arg => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.extract field arg)
        let child ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope arg
        match selected : extractSignature (scalarInput arg child.type) with
        | none => .error collationShape
        | some _ => .ok ⟨typed, .none, .extract typed.valid child.collationValid selected⟩
      | .call name es => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.call name es)
        let children ← checkCollationListCore subqueries env checkSubquery fuel profile params scope es
        match callee : builtinName name with
        | none => .error collationShape
        | some functionName =>
          if interval : functionName = "make_interval" then
            let arguments ← checkArguments makeIntervalParameters
              (es.map fun _ => none) (scalarInputs es children.types)
            .ok ⟨typed, .none, .defaultCall typed.valid children.valid (interval ▸ callee) arguments.property⟩
          else if variadic : functionName = "concat" ∨ functionName = "num_nulls" ∨ functionName = "num_nonnulls" then
            applicationCertificate typed children (.variadicCall callee variadic)
          else if separated : functionName = "concat_ws" then
            match esEq : es, children with
            | separator :: rest, ⟨separatorType :: types, derivations, valid⟩ =>
              applicationCertificate typed ⟨separatorType :: types, derivations, valid⟩
                (by simpa only [esEq] using (CollationApplication.concatWS (separated ▸ callee)))
            | _, _ => .error collationShape
          else
            match selected : resolveOverload (functionCatalog functionName) (scalarInputs es children.types) with
            | none => .error collationShape
            | some _ => applicationCertificate typed children (.call callee selected)
      | .namedCall name args => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.namedCall name args)
        let children ← checkCollationListCore subqueries env checkSubquery fuel profile params scope (args.map CallArgument.expression)
        if callee : builtinName name = some "make_interval" then
          let arguments ← checkArguments makeIntervalParameters (args.map CallArgument.name?)
            (scalarInputs (args.map CallArgument.expression) children.types)
          .ok ⟨typed, .none, .namedCall typed.valid children.valid callee arguments.property⟩
        else .error collationShape
      | .substring form es => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.substring form es)
        let children ← checkCollationListCore subqueries env checkSubquery fuel profile params scope es
        let arguments ← checkSubstringArguments form (scalarInputs es children.types)
        match selected : resolveOverload substringCatalog arguments.val with
        | none => .error collationShape
        | some signature =>
          match targets : substringCollationTargets form signature.inputs with
          | none => .error collationShape
          | some lexicalTargets =>
            match coercions : coercedCollations es children.types children.derivations lexicalTargets with
            | none => .error collationShape
            | some coerced =>
              match merge : CollationDerivation.mergeList (substringCollationOrder form coerced) with
              | none => .error conflict
              | some input => .ok ⟨typed, resultCollation typed.type input,
                  .substring typed.valid children.valid arguments.property selected targets coercions merge⟩
      | .inList arg es => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.inList arg es)
        let child ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope arg
        let children ← checkCollationListCore subqueries env checkSubquery fuel profile params scope es
        let contexts ← checkInCollations arg child.type child.derivation es children.types children.derivations
        .ok ⟨typed, .none, .inList typed.valid child.collationValid children.valid contexts.down⟩
      | .between arg lower upper negated => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.between arg lower upper negated)
        let a ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope arg
        let lo ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope lower
        let hi ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope upper
        match low : comparisonOverload .ge (scalarInput arg a.type) (scalarInput lower lo.type) with
        | none => .error collationShape
        | some lowOperator =>
          match high : comparisonOverload .le (scalarInput arg a.type) (scalarInput upper hi.type) with
          | none => .error collationShape
          | some highOperator =>
            let pairs ← checkComparisonCollations [arg, arg] [a.type, a.type] [a.derivation, a.derivation]
              [lower, upper] [lo.type, hi.type] [lo.derivation, hi.derivation] [lowOperator, highOperator]
            .ok ⟨typed, .none, .between typed.valid
              (.cons a.collationValid (.cons lo.collationValid (.cons hi.collationValid .nil))) low high pairs.down⟩
      | .caseExpr operand branches otherwise => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.caseExpr operand branches otherwise)
        match typeEq : typed.type with
        | none => .error collationShape
        | some result =>
          let conditions ← checkCollationListCore subqueries env checkSubquery fuel profile params scope (branches.map Prod.fst)
          let results ← checkCollationListCore subqueries env checkSubquery fuel profile params scope (branches.map Prod.snd ++ otherwise.toList)
          match coercions : coercedCollations (branches.map Prod.snd ++ otherwise.toList)
              results.types results.derivations
              (List.replicate (branches.length + otherwise.toList.length) result.base) with
          | none => .error collationShape
          | some coerced =>
            match merge : CollationDerivation.mergeList coerced with
            | none => .error conflict
            | some input =>
              match operandEq : operand with
              | none =>
                .ok ⟨typed, result.base.collationResult input, by
                  have root : ExprValidCore subqueries params env scope (.caseExpr none branches otherwise)
                      (some result) typed.uses := by simpa only [typeEq, operandEq] using typed.valid
                  simpa only [typeEq, operandEq] using
                    (ExprCollationValidCore.searchedCase root conditions.valid results.valid coercions merge)⟩
              | some operand =>
                let child ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope operand
                let comparisons ← checkCaseCollations (caseOperandType child.type operand)
                  (.stored (coercedCollation operand child.type
                    (caseOperandType child.type operand).base child.derivation).identity)
                  (branches.map Prod.fst) conditions.types conditions.derivations
                .ok ⟨typed, result.base.collationResult input, by
                  have root : ExprValidCore subqueries params env scope (.caseExpr (some operand) branches otherwise)
                      (some result) typed.uses := by simpa only [typeEq, operandEq] using typed.valid
                  simpa only [typeEq, operandEq] using
                    (ExprCollationValidCore.simpleCase root child.collationValid conditions.valid comparisons.down
                      results.valid coercions merge)⟩
      | .pattern a b true => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.pattern a b true)
        let left ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope a
        let right ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope b
        match selected : stringMatchSignature (scalarInput a left.type) (scalarInput b right.type) with
        | some _ => applicationCertificate typed (pairCertificate left right) (.ilike selected)
        | none => .error collationShape
      | .regex a b insensitive negated => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.regex a b insensitive negated)
        let left ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope a
        let right ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope b
        match selected : stringMatchSignature (scalarInput a left.type) (scalarInput b right.type) with
        | some _ => applicationCertificate typed (pairCertificate left right) (.regex selected)
        | none => .error collationShape
      | .jsonAccess op a b => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.jsonAccess op a b)
        let left ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope a
        let right ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope b
        match selected : jsonAccessSignature op (scalarInput a left.type) (scalarInput b right.type) with
        | some _ => applicationCertificate typed (pairCertificate left right) (.jsonAccess selected)
        | none => .error collationShape
      | .jsonExistence op a b => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.jsonExistence op a b)
        let left ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope a
        let right ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope b
        match selected : jsonExistenceSignature op (scalarInput a left.type) (scalarInput b right.type) with
        | some _ => applicationCertificate typed (pairCertificate left right) (.jsonExistence selected)
        | none => .error collationShape
      | .overlap a b => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.overlap a b)
        let left ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope a
        let right ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope b
        match selected : arrayPredicateSignature (scalarInput a left.type) (scalarInput b right.type) with
        | some _ => applicationCertificate typed (pairCertificate left right) (.overlap selected)
        | none => .error collationShape
      | .nullIf a b => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.nullIf a b)
        let left ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope a
        let right ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope b
        match selected : equalityOverload (scalarInput a left.type) (scalarInput b right.type) with
        | some _ => applicationCertificate typed (pairCertificate left right) (.nullIf selected)
        | none => .error collationShape
      | .unary op arg => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.unary op arg)
        let child ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope arg
        match selected : unarySignature op child.type with
        | some (some _) =>
          applicationCertificate typed
            ⟨[child.type], [child.derivation], .cons child.collationValid .nil⟩ (.unary selected)
        | _ => .error collationShape
      | .array es => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.array es)
        let children ← checkCollationListCore subqueries env checkSubquery fuel profile params scope es
        match common : conditionalBase (scalarInputs es children.types) with
        | some _ => applicationCertificate typed children (.array common)
        | none => .error collationShape
      | .coalesce es => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.coalesce es)
        let children ← checkCollationListCore subqueries env checkSubquery fuel profile params scope es
        match common : conditionalBase (scalarInputs es children.types) with
        | some _ => applicationCertificate typed children (.coalesce common)
        | none => .error collationShape
      | .greatest es => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.greatest es)
        let children ← checkCollationListCore subqueries env checkSubquery fuel profile params scope es
        match common : conditionalBase (scalarInputs es children.types) with
        | some _ => applicationCertificate typed children (.greatest common)
        | none => .error collationShape
      | .least es => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.least es)
        let children ← checkCollationListCore subqueries env checkSubquery fuel profile params scope es
        match common : conditionalBase (scalarInputs es children.types) with
        | some _ => applicationCertificate typed children (.least common)
        | none => .error collationShape
      | .exists child => do
        let checked ← checkSubquery child
        .ok ⟨⟨some ⟨.bool, false⟩, checked.uses, .exists checked.valid⟩,
          .none, .exists checked.valid⟩
      | .scalarQuery child => do
        let checked ← checkSubquery child
        match width : checked.output with
        | [column] =>
          if reentry : column.type.base.collatable = false ∨ column.collation.isSome = true then
            .ok ⟨⟨some ⟨column.type.base, true⟩, checked.uses,
              .scalarQuery (width ▸ checked.valid)⟩,
              .stored column.collation, .scalarQuery (width ▸ checked.valid) reentry⟩
          else .error (unsupported "scalar_subquery_collation"
            "A scalar subquery's indeterminate collatable output requires implicit-invalid collation provenance")
        | _ => .error (invalid "scalar_subquery_arity" "A scalar subquery must expose exactly one column")
      | .inQuery arg child => do
        let typed ← checkExprCore subqueries env checkSubquery (fuel + 1) params scope (.inQuery arg child)
        let left ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope arg
        let checked ← checkSubquery child
        match width : checked.output with
        | [column] =>
          match selected : equalityOverload (scalarInput arg left.type) (.known column.type) with
          | none => .error collationShape
          | some signature =>
            match arguments : signature.inputs with
            | [leftType, rightType] =>
              match merge : CollationDerivation.merge
                  (coercedCollation arg left.type leftType left.derivation)
                  (knownCoercedCollation column.type.base rightType (.stored column.collation)) with
              | none => .error conflict
              | some _ => .ok ⟨typed, .none,
                  .inQuery typed.valid left.collationValid (width ▸ checked.valid) selected arguments merge⟩
            | _ => .error collationShape
        | _ => .error (invalid "in_subquery_arity" "A scalar IN subquery must expose exactly one column")
      | _ =>
        match checkExprCore subqueries env checkSubquery (fuel + 1) params scope expr with
        | .error failure => .error failure
        | .ok _ => .error collationShape


  def checkCollationListCore (subqueries : SubqueryJudgment) (env : CTEEnv)
      (checkSubquery : SubqueryChecker subqueries env) (fuel : Nat) (profile : Profile) (params : ParameterEnv)
      (scope : Scope) (exprs : List Advanced.Expr) :
      Except Failure (CollationListCertificateCore subqueries env profile params scope exprs) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => match exprs with
      | [] => .ok ⟨[], [], .nil⟩
      | expr :: exprs => do
        let head ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope expr
        let tail ← checkCollationListCore subqueries env checkSubquery fuel profile params scope exprs
        .ok ⟨head.type :: tail.types, head.derivation :: tail.derivations,
          .cons head.collationValid tail.valid⟩

  def checkArrayCollationCore (subqueries : SubqueryJudgment) (env : CTEEnv)
      (checkSubquery : SubqueryChecker subqueries env) (fuel : Nat) (profile : Profile) (params : ParameterEnv)
      (scope : Scope) (target : ScalarType) (exprs : List Advanced.Expr) :
      Except Failure (ArrayCollationCertificateCore subqueries env profile params scope target exprs) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => do
      let children ← checkArrayElementsCollationCore subqueries env checkSubquery fuel profile params scope target exprs
      let targetElement := if (scalarInputs exprs children.types).any (fun input => input.base.any ScalarType.isArray)
        then target else target.arrayElement
      match coercions : coercedCollations exprs children.types children.derivations
          (List.replicate exprs.length targetElement) with
      | none => .error collationShape
      | some coerced =>
        match merge : CollationDerivation.mergeList coerced with
        | none => .error conflict
        | some input => .ok ⟨target.collationResult input, .targeted children.valid coercions merge⟩

  def checkArrayElementsCollationCore (subqueries : SubqueryJudgment) (env : CTEEnv)
      (checkSubquery : SubqueryChecker subqueries env) (fuel : Nat) (profile : Profile) (params : ParameterEnv)
      (scope : Scope) (target : ScalarType) (exprs : List Advanced.Expr) :
      Except Failure (ArrayElementsCollationCertificateCore subqueries env profile params scope target exprs) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => match exprs with
      | [] => .ok ⟨[], [], .nil⟩
      | .array es :: rest => do
        let head ← checkArrayCollationCore subqueries env checkSubquery fuel profile params scope target es
        let tail ← checkArrayElementsCollationCore subqueries env checkSubquery fuel profile params scope target rest
        .ok ⟨some ⟨target, false⟩ :: tail.types, head.derivation :: tail.derivations,
          .nested head.valid tail.valid⟩
      | expr :: rest => do
        if ordinary : OrdinaryArrayElement expr then
          let head ← checkCompleteExprCore subqueries env checkSubquery fuel profile params scope expr
          let tail ← checkArrayElementsCollationCore subqueries env checkSubquery fuel profile params scope target rest
          .ok ⟨head.type :: tail.types, head.derivation :: tail.derivations,
            .ordinary ordinary head.collationValid tail.valid⟩
        else .error collationShape
end

abbrev CompleteExprCertificate := CompleteExprCertificateCore NoSubqueries []
abbrev CollationListCertificate := CollationListCertificateCore NoSubqueries []
abbrev ArrayCollationCertificate := ArrayCollationCertificateCore NoSubqueries []
abbrev ArrayElementsCollationCertificate := ArrayElementsCollationCertificateCore NoSubqueries []
abbrev checkCompleteExpr := checkCompleteExprCore NoSubqueries [] noSubqueryChecker
abbrev checkCollationList := checkCollationListCore NoSubqueries [] noSubqueryChecker
abbrev checkArrayCollation := checkArrayCollationCore NoSubqueries [] noSubqueryChecker
abbrev checkArrayElementsCollation := checkArrayElementsCollationCore NoSubqueries [] noSubqueryChecker

end SQLean.SelectContract
