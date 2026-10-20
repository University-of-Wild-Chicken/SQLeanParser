import SQLean.SelectContract.Spec

/-! Proof-producing bounded implementation of the independent SELECT rules.
Every successful branch constructs a Spec derivation. Exhausted operational
fuel is Inconclusive; missing coverage is Unsupported, never validity evidence.
-/
namespace SQLean.SelectContract
open Advanced

private def invalid (code message : String) : Failure := .invalid ⟨code, message⟩
private def unsupported (code message : String) : Failure := .unsupported ⟨code, message⟩
private def exhausted : Failure := .inconclusive ⟨"resource_limit", "SELECT contract checking exhausted its recursion budget"⟩

/-- PostgreSQL warns and clamps excess SECOND precision. This profile keeps
only canonical 0..6 declarations, so that boundary is missing coverage. -/
private def intervalPrecisionGap (type : DataType) : Bool :=
  match type.name.scalarBase, type.modifiers with
  | .intervalRange fields, [precision] => fields.allowsPrecision && precision > 6
  | _, _ => false

/-- Used only to distinguish an unsupported precision boundary from unrelated
invalid metadata. No certificate is ever constructed for this replacement. -/
private def precisionDiagnosticType (type : DataType) : DataType :=
  if intervalPrecisionGap type then {type with modifiers := [6]} else type

private def precisionDiagnosticParameters (params : ParameterEnv) : ParameterEnv :=
  params.map fun binding => {binding with type := precisionDiagnosticType binding.type}

private def precisionDiagnosticCatalog (catalog : Catalog) : Catalog :=
  catalog.map fun table => {table with columns := table.columns.map fun column =>
    {column with type := precisionDiagnosticType column.type}}

private def intervalPrecisionFailure : Failure :=
  unsupported "interval_precision"
    "Qualified interval precision above six requires PostgreSQL warning/clamping normalization outside this profile"

private def uncontextualizedString : Advanced.Expr → Bool
  | .literal (.text _) => true
  | _ => false

private def missingSignature (hasUnknownString : Bool) (code message : String) : Failure :=
  if hasUnknownString then
    unsupported "unknown_string_context" "Contextual type resolution of an uncast string literal is outside this profile"
  else invalid code message

private def operatorFailure (types : List ExprType) (hasUnknownString : Bool)
    (code message : String) : Failure :=
  if types.any (fun type => type.any (fun type => type.base.arrayOperatorGap)) then
    unsupported "array_element_operator"
      "This array element type has no certified comparison operator; PostgreSQL may defer that check until execution"
  else missingSignature hasUnknownString code message

private def hasUncoveredArithmetic : ExprType → Bool
  | none => false
  | some type => match type.base with
    | .date | .time _ | .timeTZ _ | .timestamp _ | .timestampTZ _
    | .interval _ | .intervalRange .. | .jsonb => true
    | _ => false

private def binaryFailure (op : BinOp) (a b : Advanced.Expr) (ta tb : ExprType) : Failure :=
  if uncontextualizedString a || uncontextualizedString b then
    missingSignature true "" ""
  else match op with
    | .add | .sub | .mul | .div =>
        if hasUncoveredArithmetic ta || hasUncoveredArithmetic tb then
          unsupported "operator_signature" "This temporal/JSONB overload is outside the explicit signature table"
        else invalid "operator_signature" "Binary operands have no applicable PostgreSQL scalar signature"
    | .eq | .ne | .lt | .le | .gt | .ge =>
        operatorFailure [ta, tb] false "operator_signature"
        "Binary operands have no applicable PostgreSQL scalar signature"
    | .and | .or => invalid "operator_signature" "Boolean operators require Boolean operands"

structure ExprCertificate (params : ParameterEnv) (scope : Scope) (expr : Advanced.Expr) where
  type : ExprType
  uses : List Parameter
  valid : ExprValid params scope expr type uses

structure ExprListCertificate (params : ParameterEnv) (scope : Scope) (exprs : List Advanced.Expr) where
  types : List ExprType
  uses : List Parameter
  valid : ExprListValid params scope exprs types uses

structure OptionalExprCertificate (params : ParameterEnv) (scope : Scope) (expr : Option Advanced.Expr) where
  type : ExprType
  uses : List Parameter
  valid : OptionalExprValid params scope expr type uses

structure BranchesCertificate (params : ParameterEnv) (scope : Scope)
    (branches : List (Advanced.Expr × Advanced.Expr)) where
  conditions : List ExprType
  results : List ExprType
  uses : List Parameter
  valid : BranchesValid params scope branches conditions results uses

structure ArrayCertificate (params : ParameterEnv) (scope : Scope)
    (target : ScalarType) (exprs : List Advanced.Expr) where
  uses : List Parameter
  valid : ArrayValid params scope target exprs uses

structure ArrayElementsCertificate (params : ParameterEnv) (scope : Scope)
    (target : ScalarType) (exprs : List Advanced.Expr) where
  types : List ExprType
  uses : List Parameter
  valid : ArrayElementsValid params scope target exprs types uses

structure SubscriptsCertificate (params : ParameterEnv) (scope : Scope)
    (indices : List Advanced.Subscript) where
  uses : List Parameter
  valid : SubscriptsValid params scope indices uses

/-- Namespace errors precede column lookup. Missing legacy schema provenance
and PostgreSQL's whole-row function notation remain explicit coverage gaps. -/
private def checkNamespace (scope : Scope) (qualifier : Option Name)
    (schema : Option Name) : Except Failure Unit :=
  if schema == some "pg_temp" then
    .error (unsupported "namespace_alias" "The pg_temp schema alias requires explicit schema-alias resolution")
  else
  match qualifier, schema with
  | none, none => .ok ()
  | none, some _ => .error (invalid "qualified_reference_shape" "A schema-qualified column or star requires a relation name")
  | some qualifier, schema =>
    match scope.matchingRelations qualifier schema with
    | [_] => .ok ()
    | [] =>
      if schema.isSome && scope.relations.any (fun relation => !relation.aliased &&
          relation.origin.any (fun origin => origin.schema.isNone && origin.name == qualifier)) then
        .error (unsupported "relation_schema_metadata" "The legacy relation binding has no schema provenance")
      else .error (invalid "relation_reference" "No visible relation has this qualified name")
    | _ => .error (invalid "ambiguous_relation_reference" "The relation qualifier identifies multiple visible namespaces")

private def checkSubstringArguments (form : Advanced.SubstringForm) (args : List ScalarInput) :
    Except Failure {callInputs // SubstringArguments form args callInputs} :=
  match form, args with
  | .from, [subject, start] => .ok ⟨[subject, start], .from⟩
  | .fromFor, [subject, start, length] => .ok ⟨[subject, start, length], .fromFor⟩
  | .forFrom, [subject, length, start] => .ok ⟨[subject, start, length], .forFrom⟩
  | .similar, [subject, pattern, escape] => .ok ⟨[subject, pattern, escape], .similar⟩
  | .forOnly, [subject, .unknown nullable] =>
      .ok ⟨[subject, .known ⟨.int32, false⟩, .known ⟨.int32, nullable⟩], .forOnly (.unknown nullable)⟩
  | .forOnly, [subject, .known input] =>
      if allowed : explicitCastAllowed input.base .int32 = true then
        match result : castSignature (some input) .int32 with
        | some target => .ok ⟨[subject, .known ⟨.int32, false⟩, .known target],
            .forOnly (.known allowed result)⟩
        | none => .error (invalid "substring_length_cast" "SUBSTRING FOR-only requires an explicit INT32 cast")
      else .error (invalid "substring_length_cast" "SUBSTRING FOR-only length has no explicit INT32 cast")
  | _, _ => .error (invalid "substring_arity" "SUBSTRING special syntax has the wrong number of arguments")

mutual
  def checkExpr (fuel : Nat) (params : ParameterEnv) (scope : Scope) (expr : Advanced.Expr) :
      Except Failure (ExprCertificate params scope expr) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => match expr with
      | .literal (.int n) =>
          if range : n ≤ 2147483647 then
            .ok ⟨some ⟨.int32, false⟩, [], .int range⟩
          else if bigRange : n ≤ 9223372036854775807 then
            .ok ⟨some ⟨.int64, false⟩, [], .bigInt (by omega) bigRange⟩
          else .ok ⟨some ⟨.numeric [], false⟩, [], .numericInt (by omega)⟩
      | .literal (.text _) => .ok ⟨some ⟨.text, false⟩, [], .text⟩
      | .literal (.bool _) => .ok ⟨some ⟨.bool, false⟩, [], .bool⟩
      | .null => .ok ⟨none, [], .null⟩
      | .decimal lexeme =>
          if lexical : decimalLexeme lexeme = true then
            .ok ⟨some ⟨.numeric [], false⟩, [], .decimal lexical⟩
          else .error (invalid "decimal_literal" "Malformed decimal/exponent lexeme in the AST")
      | .parameter parameter => do
          match found : params.filter (fun binding => binding.index == parameterIndex parameter) with
          | [binding] =>
              have member : binding ∈ params.filter (fun b => b.index == parameterIndex parameter) := by
                rw [found]; simp
              have facts := List.mem_filter.mp member
              match supported : concreteType binding.type with
              | none => .error (unsupported "parameter_type" "Parameter type is outside the concrete PostgreSQL scalar profile")
              | some base => .ok ⟨some ⟨base.unmodified, binding.nullable⟩, [parameter],
                  .parameter facts.1 (by simpa using facts.2) supported⟩
          | _ => .error (invalid "parameter_binding" "Parameter must resolve to exactly one declared binding")
      | .column qualifier name schema => do
          checkNamespace scope qualifier schema
          if qualifier.isNone &&
              ["ctid", "tableoid", "xmin", "xmax", "cmin", "cmax"].contains name &&
              scope.relations.any (fun relation => relation.origin.isSome &&
                !relation.columns.any (fun column => column.name == name)) then
            throw (unsupported "system_column"
              "Implicit PostgreSQL system columns may participate in unqualified name resolution")
          match found : (scope.columns qualifier schema).filter (fun (col : OutputColumn) => col.name == name) with
          | [column] => .ok ⟨some column.type, [], .column found⟩
          | [] =>
              if qualifier.isSome then .error (unsupported "whole_row_function"
                "A missing qualified scalar column may denote PostgreSQL function-on-row notation")
              else match scope.matchingRelations name with
                | [_] => .error (unsupported "whole_row_reference"
                    "A bare relation name denotes a composite whole-row value outside the scalar profile")
                | [] => .error (invalid "column_binding" s!"Column '{name}' has no visible binding")
                | _ => .error (invalid "ambiguous_relation_reference"
                    "A whole-row reference identifies multiple visible relation namespaces")
          | _ => .error (invalid "column_binding" s!"Column '{name}' must resolve to exactly one visible binding")
      | .binary op (.row left) (.row right) =>
          match op with
          | .eq => checkRowComparison fuel params scope .eq left right
          | .ne => checkRowComparison fuel params scope .ne left right
          | .lt => checkRowComparison fuel params scope .lt left right
          | .le => checkRowComparison fuel params scope .le left right
          | .gt => checkRowComparison fuel params scope .gt left right
          | .ge => checkRowComparison fuel params scope .ge left right
          | _ => .error (invalid "row_operator"
              "Constructor-pair rows require one of the six comparison operators")
      | .binary op a b => do
          let left ← checkExpr fuel params scope a
          let right ← checkExpr fuel params scope b
          match signature : binarySignature op left.type right.type with
          | none => .error (binaryFailure op a b left.type right.type)
          | some type => .ok ⟨type, left.uses ++ right.uses, .binary left.valid right.valid signature⟩
      | .concat a b => do
          let left ← checkExpr fuel params scope a
          let right ← checkExpr fuel params scope b
          match signature : concatSignature (scalarInput a left.type) (scalarInput b right.type) with
          | some selected => .ok ⟨some ⟨selected.output,
                (scalarInput a left.type).nullable || (scalarInput b right.type).nullable⟩,
              left.uses ++ right.uses, .concat left.valid right.valid signature⟩
          | none =>
              match arraySignature :
                  arrayConcatSignature (scalarInput a left.type) (scalarInput b right.type) with
              | some selected => .ok ⟨some ⟨selected.output,
                    selected.operator.nullable (scalarInput a left.type).nullable
                      (scalarInput b right.type).nullable⟩, left.uses ++ right.uses,
                  .arrayConcat left.valid right.valid arraySignature⟩
              | none => .error (invalid "concatenation_signature"
                  "No admitted PostgreSQL scalar or compatible-array concatenation operator accepts these input types")
      | .unary .neg (.literal (.int 2147483648)) => .ok ⟨some ⟨.int32, false⟩, [], .minInt32⟩
      | .unary .neg (.literal (.int 9223372036854775808)) => .ok ⟨some ⟨.int64, false⟩, [], .minInt64⟩
      | .unary op a => do
          if ordinary : OrdinaryUnary op a then
            let arg ← checkExpr fuel params scope a
            match signature : unarySignature op arg.type with
            | none => .error (missingSignature (uncontextualizedString a)
                "operator_signature" "Unary overload resolution is outside the explicit profile signatures")
            | some type => .ok ⟨type, arg.uses, .unary arg.valid signature ordinary⟩
          else .error (unsupported "signed_integer_boundary" "Signed integer boundary requires literal folding")
      | .isNull a negated => do
          let arg ← checkExpr fuel params scope a
          .ok ⟨some ⟨.bool, false⟩, arg.uses, .isNull (negated := negated) arg.valid⟩
      | .pattern a b false => do
          let arg ← checkExpr fuel params scope a
          let pattern ← checkExpr fuel params scope b
          match signature : patternSignature arg.type pattern.type with
          | none => .error (missingSignature (uncontextualizedString a || uncontextualizedString b)
              "pattern_signature" "LIKE requires compatible string or BYTEA operands")
          | some type => .ok ⟨type, arg.uses ++ pattern.uses, .pattern arg.valid pattern.valid signature⟩
      | .pattern a b true => do
          let arg ← checkExpr fuel params scope a
          let pattern ← checkExpr fuel params scope b
          match signature : stringMatchSignature (scalarInput a arg.type) (scalarInput b pattern.type) with
          | none => .error (invalid "ilike_signature" "ILIKE requires string or contextually typed unknown operands")
          | some _selected => .ok ⟨some ⟨.bool,
                (scalarInput a arg.type).nullable || (scalarInput b pattern.type).nullable⟩,
              arg.uses ++ pattern.uses, .ilike arg.valid pattern.valid signature⟩
      | .regex a b insensitive negated => do
          let arg ← checkExpr fuel params scope a
          let pattern ← checkExpr fuel params scope b
          match signature : stringMatchSignature (scalarInput a arg.type) (scalarInput b pattern.type) with
          | none => .error (invalid "regex_signature" "Regex matching requires string or contextually typed unknown operands")
          | some _selected => .ok ⟨some ⟨.bool,
                (scalarInput a arg.type).nullable || (scalarInput b pattern.type).nullable⟩,
              arg.uses ++ pattern.uses,
              .regex (insensitive := insensitive) (negated := negated) arg.valid pattern.valid signature⟩
      | .extract field a => do
          let arg ← checkExpr fuel params scope a
          match signature : extractSignature (scalarInput a arg.type) with
          | none => .error (invalid "extract_signature"
              "EXTRACT requires an unambiguous DATE, TIME, TIMETZ, TIMESTAMP, TIMESTAMPTZ or INTERVAL input")
          | some selected => .ok ⟨some ⟨selected.output, extractNullable (scalarInput a arg.type)⟩,
              arg.uses, .extract (field := field) arg.valid signature⟩
      | .jsonAccess op a b => do
          let arg ← checkExpr fuel params scope a
          let key ← checkExpr fuel params scope b
          match signature : jsonAccessSignature op (scalarInput a arg.type) (scalarInput b key.type) with
          | none => .error (invalid "json_extraction_signature"
              "JSON extraction requires an unambiguous JSON/JSONB input and a compatible INTEGER/TEXT key or TEXT[] path")
          | some selected => .ok ⟨some ⟨selected.output, true⟩, arg.uses ++ key.uses,
              .jsonAccess arg.valid key.valid signature⟩
      | .containment a b containedBy => do
          let left ← checkExpr fuel params scope a
          let right ← checkExpr fuel params scope b
          match signature : jsonContainmentSignature (scalarInput a left.type) (scalarInput b right.type) with
          | some _selected => .ok ⟨some ⟨.bool,
                (scalarInput a left.type).nullable || (scalarInput b right.type).nullable⟩,
              left.uses ++ right.uses,
              .containment (containedBy := containedBy) left.valid right.valid signature⟩
          | none =>
              match arraySignature :
                  arrayPredicateSignature (scalarInput a left.type) (scalarInput b right.type) with
              | some _selected => .ok ⟨some ⟨.bool,
                    (scalarInput a left.type).nullable || (scalarInput b right.type).nullable⟩,
                  left.uses ++ right.uses,
                  .arrayContainment (containedBy := containedBy) left.valid right.valid arraySignature⟩
              | none => .error (if arrayPredicateMissingEquality
                    (scalarInput a left.type) (scalarInput b right.type) then
                  unsupported "array_element_equality"
                    "The generic array predicate lacks an admitted element equality implementation"
                else invalid "json_containment_signature"
                  "Containment requires compatible JSONB operands or matching concrete array element types")
      | .overlap a b => do
          let left ← checkExpr fuel params scope a
          let right ← checkExpr fuel params scope b
          match signature : arrayPredicateSignature (scalarInput a left.type) (scalarInput b right.type) with
          | some _selected => .ok ⟨some ⟨.bool,
                (scalarInput a left.type).nullable || (scalarInput b right.type).nullable⟩,
              left.uses ++ right.uses, .overlap left.valid right.valid signature⟩
          | none => .error (if arrayPredicateMissingEquality
                (scalarInput a left.type) (scalarInput b right.type) then
              unsupported "array_element_equality"
                "The generic array predicate lacks an admitted element equality implementation"
            else invalid "array_overlap_signature"
              "Array overlap requires matching concrete array element types and a known array context")
      | .cast a target => do
          if intervalPrecisionGap target then throw intervalPrecisionFailure
          if declaration : DataTypeWellFormed target then
            match supported : concreteType target with
            | none => .error (unsupported "cast_type" "Cast target is outside the concrete PostgreSQL scalar profile")
            | some base =>
                if ordinary : OrdinaryCast a target then
                  let arg ← checkExpr fuel params scope a
                  if allowed : castAllowed arg.type base = true then
                    .ok ⟨castSignature arg.type base, arg.uses,
                      .cast arg.valid supported declaration allowed ordinary⟩
                  else .error (invalid "cast_signature" "PostgreSQL has no explicit cast between these concrete scalar types")
                else match shape : a with
                  | .array elements =>
                    let args ← checkArray fuel params scope base elements
                    .ok ⟨some ⟨base, false⟩, args.uses,
                      by simpa only [shape] using ExprValid.castArray args.valid supported declaration⟩
                  | _ => .error (invalid "cast_category" "Unclassified contextual cast")
          else .error (invalid "type_declaration" "Cast target has invalid type modifiers")
      | .array elements => do
          let args ← checkExprList fuel params scope elements
          match signature : arraySignature (scalarInputs elements args.types) with
          | none => .error (invalid "array_constructor_type"
              "An inferred array requires nonempty elements with a common implicit type; empty arrays require a direct array cast")
          | some result => .ok ⟨some result, args.uses, .array args.valid signature⟩
      | .row _ => .error (unsupported "record_value"
          "Standalone and nested record values require a separate composite-type contract")
      | .substring form args => do
          if args.length != form.arity then
            throw (invalid "substring_arity" "SUBSTRING special syntax has the wrong number of arguments")
          let argsTyped ← checkExprList fuel params scope args
          let arguments ← checkSubstringArguments form (scalarInputs args argsTyped.types)
          match signature : resolveOverload substringCatalog arguments.val with
          | none => .error (invalid "substring_signature"
              "SUBSTRING has no unique applicable TEXT/BYTEA positional or TEXT regex overload")
          | some selected => .ok ⟨some ⟨selected.output, substringNullable selected arguments.val⟩,
              argsTyped.uses, .substring argsTyped.valid arguments.property signature⟩
      | .call name args => do
          let argsTyped ← checkExprList fuel params scope args
          match signature : callSignature name (scalarInputs args argsTyped.types) with
          | none => .error (if knownFunction name then
              invalid "function_signature" "Built-in function has no unique applicable overload for these arguments"
            else unsupported "function_signature"
              "User-defined functions and other built-ins require a separate signature profile")
          | some result => .ok ⟨some result, argsTyped.uses, .call argsTyped.valid signature⟩
      | .coalesce args => do
          let argsTyped ← checkExprList fuel params scope args
          match signature : coalesceSignature (scalarInputs args argsTyped.types) with
          | none => .error (invalid "conditional_signature" "COALESCE requires nonempty, implicitly compatible arguments")
          | some result => .ok ⟨some result, argsTyped.uses, .coalesce argsTyped.valid signature⟩
      | .greatest args => do
          let argsTyped ← checkExprList fuel params scope args
          match signature : extremumSignature (scalarInputs args argsTyped.types) with
          | none => .error (operatorFailure argsTyped.types false "conditional_signature"
              "GREATEST requires a nonempty common orderable type")
          | some result => .ok ⟨some result, argsTyped.uses, .greatest argsTyped.valid signature⟩
      | .least args => do
          let argsTyped ← checkExprList fuel params scope args
          match signature : extremumSignature (scalarInputs args argsTyped.types) with
          | none => .error (operatorFailure argsTyped.types false "conditional_signature"
              "LEAST requires a nonempty common orderable type")
          | some result => .ok ⟨some result, argsTyped.uses, .least argsTyped.valid signature⟩
      | .nullIf left right => do
          let leftTyped ← checkExpr fuel params scope left
          let rightTyped ← checkExpr fuel params scope right
          match signature : nullIfSignature (scalarInput left leftTyped.type) (scalarInput right rightTyped.type) with
          | none => .error (operatorFailure [leftTyped.type, rightTyped.type] false
              "conditional_signature" "NULLIF requires a unique equality operator")
          | some result => .ok ⟨some result, leftTyped.uses ++ rightTyped.uses,
              .nullIf leftTyped.valid rightTyped.valid signature⟩
      | .caseExpr operand branches otherwise => do
          let operandTyped ← checkOptionalExpr fuel params scope operand
          let branchesTyped ← checkBranches fuel params scope branches
          let otherwiseTyped ← checkOptionalExpr fuel params scope otherwise
          match signature : caseSignature (operand.map fun expr => scalarInput expr operandTyped.type)
              (scalarInputs (branches.map Prod.fst) branchesTyped.conditions)
              (scalarInputs (branches.map Prod.snd) branchesTyped.results)
              ((otherwise.map fun expr => scalarInput expr otherwiseTyped.type).getD (.unknown true)) with
          | none => .error (if operand.isSome then
              operatorFailure (operandTyped.type :: branchesTyped.conditions) false "case_signature"
                "CASE requires valid conditions and branches with one implicit common result type"
            else invalid "case_signature"
              "CASE requires Boolean conditions and branches with one implicit common result type")
          | some result => .ok ⟨some result, operandTyped.uses ++ branchesTyped.uses ++ otherwiseTyped.uses,
              .caseExpr operandTyped.valid branchesTyped.valid otherwiseTyped.valid signature⟩
      | .quantifiedComparison op quantifier left right => do
          let leftTyped ← checkExpr fuel params scope left
          let rightTyped ← checkExpr fuel params scope right
          match signature : quantifiedComparisonSignature op
              (scalarInput left leftTyped.type) (scalarInput right rightTyped.type) with
          | none => .error (invalid "quantified_comparison_signature"
              "ANY/SOME/ALL requires a scalar Boolean comparison operator and an array or contextually typed unknown RHS")
          | some _selected => .ok ⟨some ⟨.bool, true⟩, leftTyped.uses ++ rightTyped.uses,
              .quantifiedComparison (quantifier := quantifier) leftTyped.valid rightTyped.valid signature⟩
      | .subscript base indices => do
          if nonempty : indices ≠ [] then
            if dimensions : indices.length ≤ 6 then
              let baseTyped ← checkExpr fuel params scope base
              match shape : baseTyped.type with
              | some ⟨.array element, nullable⟩ =>
                  let bounds ← checkSubscripts fuel params scope indices
                  .ok ⟨some ⟨if indices.any Advanced.Subscript.isSlice then .array element else element, true⟩,
                    baseTyped.uses ++ bounds.uses,
                    .subscript (shape ▸ baseTyped.valid) bounds.valid nonempty dimensions⟩
              | some ⟨.jsonb, _⟩ => .error (unsupported "jsonb_subscript"
                  "JSONB subscripting requires its own container and bound rules")
              | _ => .error (invalid "subscript_container"
                  "Array subscripting requires a concrete array expression")
            else .error (unsupported "subscript_dimensions"
              "PostgreSQL 16 array subscripting supports at most six adjacent dimensions")
          else .error (invalid "empty_subscripts" "A subscript group requires at least one dimension")
      | .inList a values => do
          if nonempty : values ≠ [] then
            let arg ← checkExpr fuel params scope a
            let items ← checkExprList fuel params scope values
            match signature : comparisonListSignature (arg.type :: items.types) with
            | none => .error (operatorFailure (arg.type :: items.types) (uncontextualizedString a || values.any uncontextualizedString)
                "comparison_signature" "IN operands have no covered common comparison signature")
            | some type => .ok ⟨type, arg.uses ++ items.uses, .inList arg.valid items.valid nonempty signature⟩
          else .error (invalid "empty_in_list" "IN requires at least one value")
      | .between a b c negated => do
          let arg ← checkExpr fuel params scope a
          let lower ← checkExpr fuel params scope b
          let upper ← checkExpr fuel params scope c
          match signature : comparisonListSignature [arg.type, lower.type, upper.type] with
          | none => .error (operatorFailure [arg.type, lower.type, upper.type]
              (uncontextualizedString a || uncontextualizedString b || uncontextualizedString c)
              "comparison_signature" "BETWEEN operands have no covered common comparison signature")
          | some type => .ok ⟨type, arg.uses ++ lower.uses ++ upper.uses,
              .between (negated := negated) arg.valid lower.valid upper.valid signature⟩
      | .countAll | .aggregate .. | .filteredAggregate .. =>
          .error (unsupported "aggregate" "Independent aggregate and grouped-query rules are not implemented yet")
      | .inQuery .. | .exists .. | .scalarQuery .. =>
          .error (unsupported "subquery" "Independent subquery and correlation rules are not implemented yet")

  def checkExprList (fuel : Nat) (params : ParameterEnv) (scope : Scope) (exprs : List Advanced.Expr) :
      Except Failure (ExprListCertificate params scope exprs) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => match exprs with
      | [] => .ok ⟨[], [], .nil⟩
      | expr :: exprs => do
          let head ← checkExpr fuel params scope expr
          let tail ← checkExprList fuel params scope exprs
          .ok ⟨head.type :: tail.types, head.uses ++ tail.uses, .cons head.valid tail.valid⟩

  def checkRowComparison (fuel : Nat) (params : ParameterEnv) (scope : Scope)
      (op : Advanced.ComparisonOp) (left right : List Advanced.Expr) :
      Except Failure (ExprCertificate params scope (.binary op.toBinOp (.row left) (.row right))) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => do
      if left.isEmpty || left.length != right.length then
        .error (invalid "row_comparison_arity" "Row comparison requires equal positive field counts")
      else
        let leftTyped ← checkExprList fuel params scope left
        let rightTyped ← checkExprList fuel params scope right
        match signature : rowComparisonSignature op
            (scalarInputs left leftTyped.types) (scalarInputs right rightTyped.types) with
        | some _selected => .ok ⟨some ⟨.bool, true⟩, leftTyped.uses ++ rightTyped.uses,
            .rowComparison leftTyped.valid rightTyped.valid signature⟩
        | none => .error (operatorFailure (leftTyped.types ++ rightTyped.types) false
            "row_comparison_signature" "Row fields require compatible scalar comparison operators with admitted B-tree strategies")

  /-- Direct target-directed array construction; target context follows only
  nested raw constructors. It never crosses a function/conditional/cast node. -/
  def checkArray (fuel : Nat) (params : ParameterEnv) (scope : Scope)
      (target : ScalarType) (exprs : List Advanced.Expr) :
      Except Failure (ArrayCertificate params scope target exprs) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => do
      let args ← checkArrayElements fuel params scope target exprs
      if signature : arrayCastSignature target (scalarInputs exprs args.types) = true then
        .ok ⟨args.uses, .targeted args.valid signature⟩
      else .error (invalid "array_constructor_cast"
        "Array constructor elements cannot be explicitly coerced to the direct cast target")

  def checkArrayElements (fuel : Nat) (params : ParameterEnv) (scope : Scope)
      (target : ScalarType) (exprs : List Advanced.Expr) :
      Except Failure (ArrayElementsCertificate params scope target exprs) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => match exprs with
      | [] => .ok ⟨[], [], .nil⟩
      | .array elements :: rest => do
          let head ← checkArray fuel params scope target elements
          let tail ← checkArrayElements fuel params scope target rest
          .ok ⟨some ⟨target, false⟩ :: tail.types, head.uses ++ tail.uses,
            .nested head.valid tail.valid⟩
      | expr :: exprs => do
          if category : OrdinaryArrayElement expr then
            let head ← checkExpr fuel params scope expr
            let tail ← checkArrayElements fuel params scope target exprs
            .ok ⟨head.type :: tail.types, head.uses ++ tail.uses,
              .ordinary category head.valid tail.valid⟩
          else .error (invalid "array_element_category" "Unclassified array constructor child")

  def checkOptionalExpr (fuel : Nat) (params : ParameterEnv) (scope : Scope) (expr : Option Advanced.Expr) :
      Except Failure (OptionalExprCertificate params scope expr) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => match expr with
      | none => .ok ⟨none, [], .absent⟩
      | some expr => do
          let typed ← checkExpr fuel params scope expr
          .ok ⟨typed.type, typed.uses, .present typed.valid⟩

  def checkSubscripts (fuel : Nat) (params : ParameterEnv) (scope : Scope)
      (indices : List Advanced.Subscript) :
      Except Failure (SubscriptsCertificate params scope indices) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => match indices with
      | [] => .ok ⟨[], .nil⟩
      | .index expr :: rest => do
          let bound ← checkExpr fuel params scope expr
          if signature : subscriptBoundSignature (scalarInput expr bound.type) = true then
            let tail ← checkSubscripts fuel params scope rest
            .ok ⟨bound.uses ++ tail.uses, .index bound.valid signature tail.valid⟩
          else .error (invalid "subscript_bound"
            "Array bounds require assignment coercion to INTEGER; concrete numeric types or unknown inputs are admitted")
      | .slice lo hi :: rest => do
          let lower ← checkOptionalExpr fuel params scope lo
          let upper ← checkOptionalExpr fuel params scope hi
          if lowerSignature : optionalSubscriptBoundSignature lo lower.type = true then
            if upperSignature : optionalSubscriptBoundSignature hi upper.type = true then
              let tail ← checkSubscripts fuel params scope rest
              .ok ⟨lower.uses ++ upper.uses ++ tail.uses,
                .slice lower.valid upper.valid lowerSignature upperSignature tail.valid⟩
            else .error (invalid "subscript_bound" "Array upper bound has no assignment coercion to INTEGER")
          else .error (invalid "subscript_bound" "Array lower bound has no assignment coercion to INTEGER")

  def checkBranches (fuel : Nat) (params : ParameterEnv) (scope : Scope)
      (branches : List (Advanced.Expr × Advanced.Expr)) :
      Except Failure (BranchesCertificate params scope branches) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => match branches with
      | [] => .ok ⟨[], [], [], .nil⟩
      | (condition, result) :: branches => do
          let conditionTyped ← checkExpr fuel params scope condition
          let resultTyped ← checkExpr fuel params scope result
          let tail ← checkBranches fuel params scope branches
          .ok ⟨conditionTyped.type :: tail.conditions, resultTyped.type :: tail.results,
            conditionTyped.uses ++ resultTyped.uses ++ tail.uses,
            .cons conditionTyped.valid resultTyped.valid tail.valid⟩
end

structure SourceCertificate (profile : Profile) (catalog : Catalog) (params : ParameterEnv) (source : Option Advanced.From) where
  scope : Scope
  uses : List Parameter
  valid : SourceValid profile catalog params source scope uses

private def tableColumns (table : CatalogTable) (columns : List Advanced.Column) :
    Except Failure {bindings : List OutputColumn // TableColumns table columns bindings} :=
  match columns with
  | [] => .ok ⟨[], .nil⟩
  | col :: cols => do
      match supported : concreteType col.type with
      | none => .error (unsupported "column_type" "Column type is outside the concrete PostgreSQL scalar profile")
      | some base =>
          let rest ← tableColumns table cols
          .ok ⟨⟨col.name, ⟨base, columnNullable table col⟩⟩ :: rest.val,
            .cons supported rest.property⟩

private def checkJoinKeys (kind : JoinKind) (left right : List OutputColumn)
    (keys : List Name) :
    Except Failure {merged : List OutputColumn // JoinKeysValid kind left right keys merged} :=
  match keys with
  | [] => .ok ⟨[], .nil⟩
  | key :: keys => do
      match leftResolved : left.filter (fun col => col.name == key) with
      | [leftColumn] =>
        match rightResolved : right.filter (fun col => col.name == key) with
        | [rightColumn] =>
          match equality : equalityOverload (.known leftColumn.type) (.known rightColumn.type) with
          | none => .error (operatorFailure [some leftColumn.type, some rightColumn.type] false "join_key_equality" s!"JOIN key '{key}' has no supported equality operator")
          | some _operator =>
            match common : conditionalBase [.known leftColumn.type, .known rightColumn.type] with
            | none => .error (invalid "join_key_common_type" s!"JOIN key '{key}' has no common PostgreSQL scalar type")
            | some base =>
              let tail ← checkJoinKeys kind left right keys
              .ok ⟨⟨key, ⟨base, mergedKeyNullable kind leftColumn.type rightColumn.type⟩⟩ :: tail.val,
                .cons leftResolved rightResolved equality common tail.property⟩
        | _ => .error (invalid "join_key_binding" s!"JOIN key '{key}' must occur exactly once in the right exposed row")
      | _ => .error (invalid "join_key_binding" s!"JOIN key '{key}' must occur exactly once in the left exposed row")

structure ItemsCertificate (params : ParameterEnv) (scope : Scope) (items : List Advanced.SelectItem) where
  output : List OutputColumn
  uses : List Parameter
  valid : ItemsValid params scope items output uses

private def checkItems (fuel : Nat) (params : ParameterEnv) (scope : Scope) (items : List Advanced.SelectItem) :
    Except Failure (ItemsCertificate params scope items) :=
  match fuel with
  | 0 => .error exhausted
  | fuel + 1 => match items with
    | [] => .ok ⟨[], [], .nil⟩
    | .expression expr alias :: items => do
        if goodAlias : ∀ name ∈ alias, name ≠ "" then
          let item ← checkExpr fuel params scope expr
          let tail ← checkItems fuel params scope items
          .ok ⟨⟨outputName expr alias, projectedType item.type⟩ :: tail.output, item.uses ++ tail.uses,
            .expression item.valid goodAlias tail.valid⟩
        else .error (invalid "empty_alias" "A projection alias must be nonempty")
    | .all qualifier schema :: items => do
        checkNamespace scope qualifier schema
        let selected := scope.columns qualifier schema
        if nonempty : selected ≠ [] then
          let tail ← checkItems fuel params scope items
          .ok ⟨selected ++ tail.output, tail.uses, .all rfl nonempty tail.valid⟩
        else .error (invalid "wildcard_binding" "Wildcard must identify a nonempty visible input scope")

private def checkPredicate (fuel : Nat) (params : ParameterEnv) (scope : Scope) (expr : Option Advanced.Expr) :
    Except Failure {uses : List Parameter // PredicateValid params scope expr uses} :=
  match expr with
  | none => .ok ⟨[], .absent⟩
  | some expr => do
      match expr with
      | .literal (.text _) =>
        throw (unsupported "predicate_string_coercion"
          "Contextual Boolean conversion of an unknown string literal is not implemented yet")
      | _ => pure ()
      let arg ← checkExpr fuel params scope expr
      if boolean : acceptsBase .bool arg.type = true then
        .ok ⟨arg.uses, .present arg.valid boolean⟩
      else .error (invalid "predicate_type" "WHERE requires a Boolean expression")

private def checkSort (fuel : Nat) (params : ParameterEnv) (scope : Scope) (output : List OutputColumn)
    (distinct : Bool) (expr : Advanced.Expr) :
    Except Failure {uses : List Parameter // SortValid params scope output distinct expr uses} :=
  match expr with
  | .literal (.int n) =>
      if positive : 0 < n then
        if inRange : n ≤ output.length then
          if orderable : OrdinalOrderable output n then .ok ⟨[], .ordinal positive inRange orderable⟩
          else .error (operatorFailure [((output[n - 1]?).map OutputColumn.type)] false
              "order_type" "ORDER BY output type has no PostgreSQL ordering operator")
        else .error (invalid "order_position" "ORDER BY position exceeds expanded output width")
      else .error (invalid "order_position" "ORDER BY positions are one-based")
  | .column none name none =>
      match found : output.filter (·.name == name) with
      | [column] =>
          if orderable : column.type.base.orderable = true then .ok ⟨[], .outputName found orderable⟩
          else .error (operatorFailure [some column.type] false
              "order_type" "ORDER BY output type has no PostgreSQL ordering operator")
      | [] => do
          if ordinary : distinct = false then
            let typed ← checkExpr fuel params scope (.column none name)
            if orderable : typed.type.orderable = true then
              .ok ⟨typed.uses, .inputName found ordinary typed.valid orderable⟩
            else .error (operatorFailure [typed.type] false
                "order_type" "ORDER BY input type has no PostgreSQL ordering operator")
          else .error (unsupported "distinct_order_expression" "DISTINCT ordering by an input name requires projected-expression identity rules; use an output label or position")
      | _ => .error (invalid "ambiguous_output" s!"ORDER BY label '{name}' is ambiguous")
  | expr => do
      if ordinary : distinct = false then
        if category : SortExpression expr then
          let typed ← checkExpr fuel params scope expr
          if orderable : typed.type.orderable = true then
            .ok ⟨typed.uses, .expression ordinary typed.valid category orderable⟩
          else .error (operatorFailure [typed.type] false
              "order_type" "ORDER BY expression type has no PostgreSQL ordering operator")
        else .error (invalid "order_category" "Unclassified ORDER BY syntax")
      else .error (unsupported "distinct_order_expression" "This milestone supports DISTINCT ordering by output name or position")

private def checkOrders (fuel : Nat) (params : ParameterEnv) (scope : Scope) (output : List OutputColumn)
    (distinct : Bool) (items : List Advanced.OrderBy) :
    Except Failure {uses : List Parameter // OrdersValid params scope output distinct items uses} :=
  match fuel with
  | 0 => .error exhausted
  | fuel + 1 => match items with
    | [] => .ok ⟨[], .nil⟩
    | item :: items => do
        let head ← checkSort fuel params scope output distinct item.expr
        let tail ← checkOrders fuel params scope output distinct items
        .ok ⟨head.val ++ tail.val, .cons head.property tail.property⟩

/-- Check one pagination expression in an empty local scope. This proves a
static coercion to a row count, not nonnegativity of its eventual runtime value. -/
def checkPagination (fuel : Nat) (params : ParameterEnv) (expr : Option Advanced.Expr) :
    Except Failure {uses : List Parameter // PaginationValid params expr uses} :=
  match fuel with
  | 0 => .error exhausted
  | fuel + 1 => match expr with
    | none => .ok ⟨[], .absent⟩
    | some (.literal (.text _)) =>
        .error (unsupported "pagination_string_literal" "Contextual conversion of an unknown string literal to a row count is outside this profile")
    | some expr => do
        let arg ← checkExpr fuel params .empty expr
        match typeEq : arg.type with
        | none =>
            .ok ⟨arg.uses, .present (by simpa only [typeEq] using arg.valid) .unknownNull⟩
        | some ⟨.int32, nullable⟩ =>
            .ok ⟨arg.uses, .present (by simpa only [typeEq] using arg.valid) (.int32Widen nullable)⟩
        | some ⟨.smallInt, nullable⟩ =>
            .ok ⟨arg.uses, .present (by simpa only [typeEq] using arg.valid) (.smallIntWiden nullable)⟩
        | some ⟨.int64, nullable⟩ =>
            .ok ⟨arg.uses, .present (by simpa only [typeEq] using arg.valid) (.int64Identity nullable)⟩
        | some ⟨.numeric modifiers, nullable⟩ =>
            .ok ⟨arg.uses, .present (by simpa only [typeEq] using arg.valid) (.numericAssignment modifiers nullable)⟩
        | some ⟨.real, nullable⟩ =>
            .ok ⟨arg.uses, .present (by simpa only [typeEq] using arg.valid) (.realAssignment nullable)⟩
        | some ⟨.doublePrecision, nullable⟩ =>
            .ok ⟨arg.uses, .present (by simpa only [typeEq] using arg.valid) (.doubleAssignment nullable)⟩
        | some _ =>
            .error (invalid "pagination_type" "Pagination requires a numeric expression assignable to INT8 or untyped NULL")

/-- Certify only the outer LIMIT/OFFSET expressions of an exact query.
The body may be outside the basic SELECT fragment. This API does not establish
query-wide parameter notation or any property of unexamined query clauses. -/
def checkPaginationBounds (profile : Profile) (params : ParameterEnv) (query : Advanced.Query)
    (fuel : Nat := 1024) : Except Failure (PaginationBoundsCertificate profile params query) := do
  if fuel = 0 then throw exhausted
  if environment : ParametersWellFormed params then
    let limit ← checkPagination fuel params query.limit
    let offset ← checkPagination fuel params query.offset
    .ok ⟨limit.val, offset.val, .bounds environment limit.property offset.property⟩
  else if ParametersWellFormed (precisionDiagnosticParameters params) then
    .error intervalPrecisionFailure
  else .error (invalid "invalid_environment" "Parameter metadata violates index uniqueness, positivity or type-declaration rules")

/-- Pagination-only soundness has no premise asserting validity of the body. -/
theorem checkPaginationBounds_sound
    (profile : Profile) (params : ParameterEnv) (query : Advanced.Query)
    (fuel : Nat) (certificate : PaginationBoundsCertificate profile params query)
    (_success : checkPaginationBounds profile params query fuel = .ok certificate) :
    PaginationBoundsValid profile params query certificate.limitUses certificate.offsetUses :=
  certificate.valid

structure LockingCertificate (scope : Scope) (distinct : Bool)
    (clauses : List Advanced.LockingClause) : Type where
  valid : LockingValid scope distinct clauses

/-- OF selects the first matching relation, independently of column ambiguity. -/
def checkLocking (scope : Scope) (distinct : Bool)
    (clauses : List Advanced.LockingClause) :
    Except Failure (LockingCertificate scope distinct clauses) :=
  match clauses with
  | [] => .ok ⟨.nil⟩
  | clause :: clauses => do
    if ordinary : distinct = false then
      let selected := if clause.targets.isEmpty then scope.relations else
        clause.targets.filterMap (fun target => scope.relations.find? (fun relation => relation.name == target))
      if selected.any (fun relation => relation.origin.isNone) then
        throw (unsupported "derived_locking"
          "Row-lock propagation through a selected derived source is not independently modeled")
      if targets : LockTargets scope clause.targets then
        let tail ← checkLocking scope distinct clauses
        .ok ⟨.cons ordinary targets tail.valid⟩
      else .error (invalid "locking_target" "FOR locking targets must select nonnullable base relations")
    else .error (invalid "locking_distinct" "Row locking cannot be combined with DISTINCT")

/-- Diagnostic traversal only. Nested query aggregates belong to their own
query level; unsupported correlation still cannot acquire a basic certificate.
Resource exhaustion remains Inconclusive rather than an invalidity claim. -/
private def currentAggregate : Nat → Advanced.Expr → Except Failure Bool
  | 0, _ => .error exhausted
  | fuel + 1, expr => do
    match expr with
    | .countAll | .aggregate .. | .filteredAggregate .. => pure true
    | _ =>
      let children : List Advanced.Expr := match expr with
        | .binary _ a b | .pattern a b _ | .nullIf a b
        | .quantifiedComparison _ _ a b | .concat a b | .regex a b .. | .jsonAccess _ a b
        | .containment a b _ | .overlap a b => [a, b]
        | .unary _ a | .cast a _ | .extract _ a | .isNull a _ | .inQuery a _ => [a]
        | .subscript base indices => base :: indices.flatMap Advanced.Subscript.expressions
        | .array args | .row args | .call _ args | .substring _ args
        | .coalesce args | .greatest args | .least args => args
        | .caseExpr operand branches otherwise =>
          operand.toList ++ branches.flatMap (fun (branch : Advanced.Expr × Advanced.Expr) =>
            [branch.1, branch.2]) ++ otherwise.toList
        | .inList arg values => arg :: values
        | .between arg lower upper _ => [arg, lower, upper]
        | _ => []
      children.foldlM (fun found child => do
        let childAggregate ← currentAggregate fuel child
        pure (found || childAggregate)) false

private def checkLockingShape (fuel : Nat) (query : Advanced.Query) : Except Failure Unit := do
  if query.locking.isEmpty then pure () else
  match query.body with
  | .set .. => .error (invalid "locking_set_operation" "Row locking cannot apply to a set-operation result")
  | .select select =>
    if select.distinct || !select.distinctOn.isEmpty then
      .error (invalid "locking_distinct" "Row locking cannot be combined with DISTINCT or DISTINCT ON")
    else if !select.groupBy.isEmpty || select.having.isSome then
      .error (invalid "locking_grouping" "Row locking cannot be combined with GROUP BY or HAVING")
    else
      let exprs := select.items.filterMap (fun item => match item with
          | .all .. => none | .expression expr _ => some expr) ++
        select.whereClause.toList ++ query.orderBy.map Advanced.OrderBy.expr ++
        query.limit.toList ++ query.offset.toList
      let aggregate ← exprs.foldlM (fun found expr => do
        let present ← currentAggregate fuel expr
        pure (found || present)) false
      if aggregate then .error (invalid "locking_aggregate" "Row locking cannot apply to an aggregate query")
      else pure ()

structure QueryCertificate (profile : Profile) (catalog : Catalog) (params : ParameterEnv)
    (query : Advanced.Query) where
  output : List OutputColumn
  uses : List Parameter
  valid : QueryValid profile catalog params query output uses

mutual
  private def checkSource (fuel : Nat) (profile : Profile) (catalog : Catalog) (params : ParameterEnv)
      (source : Option Advanced.From) :
      Except Failure (SourceCertificate profile catalog params source) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => match source with
    | none => .ok ⟨.empty, [], .empty⟩
    | some (.table name alias columns schema) => do
        if schema == some "pg_temp" then
          throw (unsupported "namespace_alias" "The pg_temp schema alias requires explicit schema-alias resolution")
        if goodAlias : ∀ name ∈ alias, name ≠ "" then
          match found : catalog.filter (fun table => table.matchesReference name schema) with
          | [table] =>
              have member : table ∈ catalog.filter (fun t => t.matchesReference name schema) := by rw [found]; simp
              have facts := List.mem_filter.mp member
              let bindings ← tableColumns table table.columns
              if noRenaming : columns = [] then
                .ok ⟨Scope.ofTable table.identity alias bindings.val, [],
                  noRenaming ▸ .table facts.1 (by simpa using facts.2) goodAlias bindings.property⟩
              else match aliasEq : alias with
                | none => .error (invalid "table_column_aliases" "A table column alias list requires a relation alias")
                | some aliasName =>
                    if aliasesValid : ColumnAliasesValid columns bindings.val then
                      .ok ⟨Scope.ofTable table.identity (some aliasName) (renameOutput columns bindings.val), [], by
                        rw [aliasEq]
                        exact .tableRenamed facts.1 (by simpa using facts.2)
                          (goodAlias aliasName (by simp [aliasEq])) bindings.property aliasesValid⟩
                    else .error (invalid "table_column_aliases"
                      "Table column aliases must be nonempty and cannot exceed the column count")
          | _ =>
              if schema.isSome && catalog.any (fun table => table.schema.isNone && table.name == name) then
                .error (unsupported "relation_schema_metadata" "Legacy catalog metadata does not identify this schema-qualified relation")
              else .error (invalid "relation_binding" s!"Relation '{name}' must resolve to exactly one catalog entry")
        else .error (invalid "empty_alias" "A relation alias must be nonempty")
    | some (.derived query alias columns lateral) => do
        if nonLateral : lateral = false then
          if aliasValid : alias ≠ "" then
            let child ← checkQueryCore fuel profile catalog params query
            if columnsValid : ColumnAliasesValid columns child.output then
              .ok ⟨Scope.ofOutput alias (renameOutput columns child.output), child.uses,
                .derived child.valid aliasValid columnsValid nonLateral⟩
            else .error (invalid "derived_column_aliases" "Derived column aliases must be nonempty and cannot exceed the output width")
          else .error (invalid "empty_alias" "A derived relation alias must be nonempty")
        else .error (unsupported "lateral_source" "Independent correlated LATERAL source rules are not implemented yet")
    | some (.join kind left right condition) => do
        match conditionEq : condition with
        | .using keys =>
          if kindValid : kind ≠ .cross then
            if nonempty : keys ≠ [] then
              if unique : keys.Nodup then
                let leftValid ← checkSource fuel profile catalog params (some left)
                let rightValid ← checkSource fuel profile catalog params (some right)
                if aliases : JoinAliasesDistinct leftValid.scope rightValid.scope then
                  let merged ← checkJoinKeys kind leftValid.scope.output rightValid.scope.output keys
                  .ok ⟨mergedJoinScope kind leftValid.scope rightValid.scope keys merged.val,
                    leftValid.uses ++ rightValid.uses, by
                      rw [conditionEq]
                      exact .using leftValid.valid rightValid.valid aliases kindValid nonempty unique merged.property⟩
                else .error (invalid "duplicate_relation_alias" "Visible relation aliases must be distinct")
              else .error (invalid "duplicate_join_key" "JOIN USING keys must be distinct")
            else .error (invalid "empty_join_keys" "JOIN USING requires at least one key")
          else .error (invalid "join_condition" "CROSS JOIN cannot carry USING")
        | .natural =>
          if kindValid : kind ≠ .cross then
            let leftValid ← checkSource fuel profile catalog params (some left)
            let rightValid ← checkSource fuel profile catalog params (some right)
            if aliases : JoinAliasesDistinct leftValid.scope rightValid.scope then
              let keys := naturalJoinKeys leftValid.scope.output rightValid.scope.output
              if unique : keys.Nodup then
                let merged ← checkJoinKeys kind leftValid.scope.output rightValid.scope.output keys
                .ok ⟨mergedJoinScope kind leftValid.scope rightValid.scope keys merged.val,
                  leftValid.uses ++ rightValid.uses, by
                    rw [conditionEq]
                    exact .natural leftValid.valid rightValid.valid aliases kindValid unique merged.property⟩
              else .error (invalid "duplicate_join_key" "NATURAL JOIN finds repeated exposed key names")
            else .error (invalid "duplicate_relation_alias" "Visible relation aliases must be distinct")
          else .error (invalid "join_condition" "CROSS JOIN cannot be NATURAL")
        | .none =>
          if cross : kind = .cross then
            let leftValid ← checkSource fuel profile catalog params (some left)
            let rightValid ← checkSource fuel profile catalog params (some right)
            if aliases : JoinAliasesDistinct leftValid.scope rightValid.scope then
              .ok ⟨leftValid.scope ++ rightValid.scope, leftValid.uses ++ rightValid.uses,
                by rw [conditionEq, cross]; exact .cross leftValid.valid rightValid.valid aliases⟩
            else .error (invalid "duplicate_relation_alias" "Visible relation aliases must be distinct")
          else .error (invalid "join_condition" "An ordinary join requires an ON condition")
        | .on expr =>
          if kindValid : kind ≠ .cross then
            match expr with
            | .literal (.text _) =>
              throw (unsupported "predicate_string_coercion"
                "Contextual Boolean conversion of an unknown string literal is not implemented yet")
            | _ => pure ()
            let leftValid ← checkSource fuel profile catalog params (some left)
            let rightValid ← checkSource fuel profile catalog params (some right)
            if aliases : JoinAliasesDistinct leftValid.scope rightValid.scope then
              let predicate ← checkExpr fuel params (leftValid.scope ++ rightValid.scope) expr
              if boolean : acceptsBase .bool predicate.type = true then
                .ok ⟨joinScope kind leftValid.scope rightValid.scope,
                  leftValid.uses ++ rightValid.uses ++ predicate.uses,
                  by
                    rw [conditionEq]
                    exact .on leftValid.valid rightValid.valid aliases kindValid
                      (.present predicate.valid boolean)⟩
              else .error (invalid "join_predicate_type" "JOIN ON requires a Boolean expression")
            else .error (invalid "duplicate_relation_alias" "Visible relation aliases must be distinct")
          else .error (invalid "join_condition" "CROSS JOIN cannot carry an ON condition")


  private def checkQueryCore (fuel : Nat) (profile : Profile) (catalog : Catalog)
      (params : ParameterEnv) (query : Advanced.Query) :
      Except Failure (QueryCertificate profile catalog params query) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => do
      checkLockingShape fuel query
      match queryEq : query with
      | ⟨body, ctes, recursive, orderBy, limit, offset, locking, offsetFirst⟩ =>
        if noCTEs : ctes = [] then
          if noRecursive : recursive = false then
            match bodyEq : body with
            | .set .. => .error (unsupported "set_operation" "Independent set-operation rules are not implemented yet")
            | .select select =>
              if noGrouping : select.groupBy = [] then
                if noHaving : select.having = none then
                  if noDistinctOn : select.distinctOn = [] then
                    let source ← checkSource fuel profile catalog params select.source
                    let items ← checkItems fuel params source.scope select.items
                    if nonempty : items.output ≠ [] then
                      if distinctComparable : DistinctAllowed select.distinct items.output then
                        let predicate ← checkPredicate fuel params source.scope select.whereClause
                        let orders ← checkOrders fuel params source.scope items.output select.distinct orderBy
                        let checkedLimit ← checkPagination fuel params limit
                        let checkedOffset ← checkPagination fuel params offset
                        let checkedLocking ← checkLocking source.scope select.distinct locking
                        .ok ⟨items.output,
                          (if offsetFirst then items.uses ++ source.uses ++ predicate.val ++ orders.val ++ checkedOffset.val ++ checkedLimit.val
                           else items.uses ++ source.uses ++ predicate.val ++ orders.val ++ checkedLimit.val ++ checkedOffset.val), by
                          rw [queryEq, bodyEq, noCTEs, noRecursive]
                          exact .basic source.valid items.valid nonempty distinctComparable predicate.property
                            orders.property checkedLimit.property checkedOffset.property checkedLocking.valid
                            noGrouping noHaving noDistinctOn⟩
                      else .error (operatorFailure (items.output.map (fun column => some column.type)) false
                        "distinct_type" "DISTINCT output type has no PostgreSQL equality operator")
                    else .error (invalid "empty_projection" "SELECT must produce at least one output column")
                  else .error (unsupported "distinct_on" "DISTINCT ON requires a separate dialect extension")
                else .error (unsupported "having" "Independent HAVING and grouped-query rules are not implemented yet")
              else .error (unsupported "group_by" "Independent grouping rules are not implemented yet")
          else .error (unsupported "recursive_cte" "Independent recursive CTE rules are not implemented yet")
        else .error (unsupported "cte" "Independent CTE rules are not implemented yet")
end

/-- Validate exact metadata and complete statement parameter notation once.
Nested query checks collect occurrences without restarting anonymous indices. -/
def checkQuery (profile : Profile) (catalog : Catalog) (params : ParameterEnv) (query : Advanced.Query)
    (fuel : Nat := 1024) : Except Failure (Certificate profile catalog params query) := do
  if fuel = 0 then throw exhausted
  if environment : WellFormedEnvironment catalog params then
    if catalog.any (fun table => table.schema == some "pg_temp") then
      throw (unsupported "namespace_alias" "Catalog metadata cannot treat pg_temp as a distinct physical schema")
    if supported : SupportedEnvironment catalog params then
      let checked ← checkQueryCore fuel profile catalog params query
      if parameterOrder : ParameterOrder checked.uses then
        .ok ⟨checked.output, .certified environment supported checked.valid parameterOrder⟩
      else .error (invalid "parameter_notation" "Use positive numbered parameters or consecutive anonymous parameters, without mixing styles")
    else .error (unsupported "environment_type" "A catalog or parameter type is outside the concrete PostgreSQL scalar inventory")
  else if WellFormedEnvironment (precisionDiagnosticCatalog catalog)
      (precisionDiagnosticParameters params) then
    .error intervalPrecisionFailure
  else .error (invalid "invalid_environment" "Catalog or parameter metadata violates uniqueness, naming, type-declaration or key rules")

/-- Soundness is against Spec.SelectValid, not an abbreviation for checker
success. The theorem needs no operational fuel premise beyond success. -/
theorem checkQuery_sound
    (profile : Profile) (catalog : Catalog) (params : ParameterEnv) (query : Advanced.Query)
    (fuel : Nat) (certificate : Certificate profile catalog params query)
    (_success : checkQuery profile catalog params query fuel = .ok certificate) :
    SelectValid profile catalog params query certificate.output := certificate.valid

end SQLean.SelectContract
