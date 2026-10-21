import SQLean.SelectContract.Spec
import SQLean.AdvancedEquality

/-! Proof-producing bounded implementation of the independent SELECT rules.
Every successful branch constructs a Spec derivation. Exhausted operational
fuel is Inconclusive; missing coverage is Unsupported, never validity evidence.
-/
namespace SQLean.SelectContract
open Advanced

def invalid (code message : String) : Failure := .invalid ⟨code, message⟩
def unsupported (code message : String) : Failure := .unsupported ⟨code, message⟩
def exhausted : Failure := .inconclusive ⟨"resource_limit", "SELECT contract checking exhausted its recursion budget"⟩

private instance (profile : Profile) (items : List Advanced.SelectItem) (output : List OutputColumn) (name : Name) :
    Decidable (SameOutputExpressions profile items output name) := by
  unfold SameOutputExpressions
  split <;> infer_instance

/-- PostgreSQL warns and clamps excess SECOND precision. This profile keeps
only canonical 0..6 declarations, so that boundary is missing coverage. -/
def intervalPrecisionGap (type : DataType) : Bool :=
  match type.name.scalarBase, type.modifiers with
  | .intervalRange fields, [precision] => fields.allowsPrecision && precision > 6
  | _, _ => false

/-- Used only to distinguish an unsupported precision boundary from unrelated
invalid metadata. No certificate is ever constructed for this replacement. -/
def precisionDiagnosticType (type : DataType) : DataType :=
  if intervalPrecisionGap type then {type with modifiers := [6]} else type

def precisionDiagnosticParameters (params : ParameterEnv) : ParameterEnv :=
  params.map fun binding => {binding with type := precisionDiagnosticType binding.type}

def precisionDiagnosticCatalog (catalog : Catalog) : Catalog :=
  catalog.map fun table => {table with columns := table.columns.map fun column =>
    {column with type := precisionDiagnosticType column.type}}

def intervalPrecisionFailure : Failure :=
  unsupported "interval_precision"
    "Qualified interval precision above six requires PostgreSQL warning/clamping normalization outside this profile"

def uncontextualizedString : Advanced.Expr → Bool
  | .literal (.text _) => true
  | .collate arg _ => uncontextualizedString arg
  | _ => false

def missingSignature (hasUnknownString : Bool) (code message : String) : Failure :=
  if hasUnknownString then
    unsupported "unknown_string_context" "Contextual type resolution of an uncast string literal is outside this profile"
  else invalid code message

def operatorFailure (types : List ExprType) (hasUnknownString : Bool)
    (code message : String) : Failure :=
  if types.any (fun type => type.any (fun type => type.base.arrayOperatorGap)) then
    unsupported "array_element_operator"
      "This array element type has no certified comparison operator; PostgreSQL may defer that check until execution"
  else missingSignature hasUnknownString code message

def hasUncoveredArithmetic : ExprType → Bool
  | none => false
  | some type => match type.base with
    | .date | .time _ | .timeTZ _ | .timestamp _ | .timestampTZ _
    | .interval _ | .intervalRange .. | .jsonb => true
    | _ => false

def binaryFailure (op : BinOp) (a b : Advanced.Expr) (ta tb : ExprType) : Failure :=
  if op == .add && (scalarInput a ta).base.isNone && (scalarInput b tb).base.isNone then
    invalid "binary_signature" "Addition of two unresolved operands has no unique native operator"
  else if uncontextualizedString a || uncontextualizedString b then
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

structure SubqueryCertificate (subqueries : SubqueryJudgment) (env : CTEEnv) (query : Advanced.Query) where
  output : List OutputColumn
  uses : List Parameter
  valid : subqueries env query output uses

abbrev SubqueryChecker (subqueries : SubqueryJudgment) (env : CTEEnv) :=
  (query : Advanced.Query) → Except Failure (SubqueryCertificate subqueries env query)

def noSubqueryChecker : SubqueryChecker NoSubqueries env := fun _ =>
  .error (unsupported "subquery" "This entry point has no certified query context")

structure ExprLabelCertificate (subqueries : SubqueryJudgment) (env : CTEEnv) (expr : Advanced.Expr) where
  label : Nat × Name
  valid : ExprLabelValidCore subqueries env expr label

def checkExprLabel (subqueries : SubqueryJudgment) (env : CTEEnv)
    (checkSubquery : SubqueryChecker subqueries env) (fuel : Nat) (expr : Advanced.Expr) :
    Except Failure (ExprLabelCertificate subqueries env expr) :=
  match fuel with
  | 0 => .error exhausted
  | fuel + 1 =>
    if closed : labelNeedsSubquery expr = false then
      .ok ⟨outputLabel expr, .ordinary closed⟩
    else match expr with
    | .scalarQuery child => do
      let checked ← checkSubquery child
      match width : checked.output with
      | [column] => .ok ⟨(2, column.name), .scalarQuery (width ▸ checked.valid)⟩
      | _ => .error (invalid "scalar_subquery_arity" "A scalar subquery must expose exactly one column")
    | .cast arg target => do
      let child ← checkExprLabel subqueries env checkSubquery fuel arg
      .ok ⟨if child.label.1 ≤ 1 then (1, typeNameLabel target.name) else child.label, .cast child.valid⟩
    | .subscript arg _indices => do
      let child ← checkExprLabel subqueries env checkSubquery fuel arg
      .ok ⟨child.label, .subscript child.valid⟩
    | .collate arg _name => do
      let child ← checkExprLabel subqueries env checkSubquery fuel arg
      .ok ⟨child.label, .collate child.valid⟩
    | .caseExpr _operand _branches (some arg) => do
      let child ← checkExprLabel subqueries env checkSubquery fuel arg
      .ok ⟨if child.label.1 ≤ 1 then (1, "case") else child.label, .caseExpr child.valid⟩
    | _ => .error (unsupported "subquery_label" "The subquery-dependent output label has no independent derivation")

structure ExprCertificateCore (subqueries : SubqueryJudgment) (env : CTEEnv) (params : ParameterEnv) (scope : Scope) (expr : Advanced.Expr) where
  type : ExprType
  uses : List Parameter
  valid : ExprValidCore subqueries params env scope expr type uses

structure ExprListCertificateCore (subqueries : SubqueryJudgment) (env : CTEEnv) (params : ParameterEnv) (scope : Scope) (exprs : List Advanced.Expr) where
  types : List ExprType
  uses : List Parameter
  valid : ExprListValidCore subqueries params env scope exprs types uses

structure OptionalExprCertificateCore (subqueries : SubqueryJudgment) (env : CTEEnv) (params : ParameterEnv) (scope : Scope) (expr : Option Advanced.Expr) where
  type : ExprType
  uses : List Parameter
  valid : OptionalExprValidCore subqueries params env scope expr type uses

structure BranchesCertificateCore (subqueries : SubqueryJudgment) (env : CTEEnv) (params : ParameterEnv) (scope : Scope)
    (branches : List (Advanced.Expr × Advanced.Expr)) where
  conditions : List ExprType
  results : List ExprType
  uses : List Parameter
  valid : BranchesValidCore subqueries params env scope branches conditions results uses

structure ArrayCertificateCore (subqueries : SubqueryJudgment) (env : CTEEnv) (params : ParameterEnv) (scope : Scope)
    (target : ScalarType) (exprs : List Advanced.Expr) where
  uses : List Parameter
  valid : ArrayValidCore subqueries params env scope target exprs uses

structure ArrayElementsCertificateCore (subqueries : SubqueryJudgment) (env : CTEEnv) (params : ParameterEnv) (scope : Scope)
    (target : ScalarType) (exprs : List Advanced.Expr) where
  types : List ExprType
  uses : List Parameter
  valid : ArrayElementsValidCore subqueries params env scope target exprs types uses

structure SubscriptsCertificateCore (subqueries : SubqueryJudgment) (env : CTEEnv) (params : ParameterEnv) (scope : Scope)
    (indices : List Advanced.Subscript) where
  uses : List Parameter
  valid : SubscriptsValidCore subqueries params env scope indices uses

/-- Namespace errors precede column lookup. Missing legacy schema provenance
and PostgreSQL's whole-row function notation remain explicit coverage gaps. -/
def checkNamespace (scope : Scope) (qualifier : Option Name)
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
          relation.origin.base?.any (fun origin => origin.schema.isNone && origin.name == qualifier)) then
        .error (unsupported "relation_schema_metadata" "The legacy relation binding has no schema provenance")
      else .error (invalid "relation_reference" "No visible relation has this qualified name")
    | _ => .error (invalid "ambiguous_relation_reference" "The relation qualifier identifies multiple visible namespaces")

def checkSubstringArguments (form : Advanced.SubstringForm) (args : List ScalarInput) :
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

def findArgumentIndex (parameters : List Name) (name : Name) :
    Option {index : Nat // parameters[index]? = some name} :=
  match parameters with
  | [] => none
  | parameter :: parameters =>
      if identity : parameter = name then some ⟨0, by simp [identity]⟩
      else match findArgumentIndex parameters name with
      | none => none
      | some found => some ⟨found.val + 1, by simpa using found.property⟩

def checkArgumentAssignments (parameters : List Name) (next : Nat) (namedSeen : Bool)
    (names : List (Option Name)) (inputs : List ScalarInput) :
    Except Failure {assignments // ArgumentAssignments parameters next namedSeen names inputs assignments} :=
  match names, inputs with
  | [], [] => .ok ⟨[], .nil⟩
  | none :: names, input :: inputs => do
      if order : namedSeen = false then
        if range : next < parameters.length then
          let tail ← checkArgumentAssignments parameters (next + 1) false names inputs
          .ok ⟨(next, input) :: tail.val, by subst namedSeen; exact .positional range tail.property⟩
        else .error (invalid "function_arity" "Too many positional arguments for the declared function")
      else .error (invalid "named_argument_order" "Positional arguments cannot follow named arguments")
  | some name :: names, input :: inputs => do
      match findArgumentIndex parameters name with
      | none => .error (invalid "named_argument_name" "No declared function parameter has this exact name")
      | some index =>
          let tail ← checkArgumentAssignments parameters next true names inputs
          .ok ⟨(index.val, input) :: tail.val, .named index.property tail.property⟩
  | _, _ => .error (invalid "named_argument_shape" "Argument metadata and lexical inputs have different lengths")

def checkArgumentSlots (assignments : List (Nat × ScalarInput)) (next : Nat)
    (parameters : List FunctionParameter) :
    Except Failure {inputs // ArgumentSlots assignments next parameters inputs} :=
  match parameters with
  | [] => .ok ⟨[], .nil⟩
  | parameter :: parameters => do
      let tail ← checkArgumentSlots assignments (next + 1) parameters
      match found : assignments.find? (fun entry => entry.1 == next) with
      | some (index, input) =>
          if identity : index = next then
            .ok ⟨input :: tail.val, .cons (.supplied (by simpa [identity] using found)) tail.property⟩
          else .error (invalid "argument_slot" "Argument assignment has an inconsistent slot index")
      | none => match defaultValue : parameter.defaultValue with
          | none => .error (invalid "missing_argument" "A required function argument is absent")
          | some value =>
              .ok ⟨value.input :: tail.val, .cons (.defaulted found defaultValue) tail.property⟩

/-- Successful binding exposes independent evidence, not a bare acceptance bit. -/
def checkArguments (parameters : List FunctionParameter)
    (names : List (Option Name)) (inputs : List ScalarInput) :
    Except Failure {callInputs // ArgumentsBound parameters names inputs callInputs} := do
  let assignments ← checkArgumentAssignments (parameters.map FunctionParameter.name) 0 false names inputs
  if unique : (assignments.val.map Prod.fst).Nodup then
    let slots ← checkArgumentSlots assignments.val 0 parameters
    pure ⟨slots.val, .intro assignments.property unique slots.property⟩
  else .error (invalid "duplicate_argument" "A function parameter is supplied more than once")

mutual
  def checkExprCore (subqueries : SubqueryJudgment) (env : CTEEnv)
      (checkSubquery : SubqueryChecker subqueries env) (fuel : Nat) (params : ParameterEnv) (scope : Scope) (expr : Advanced.Expr) :
      Except Failure (ExprCertificateCore subqueries env params scope expr) :=
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
      | .contextValue value => .ok ⟨some (contextValueType value), [], .contextValue⟩
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
              scope.relations.any (fun relation => relation.origin.isBase &&
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
          | .eq => checkRowComparisonCore subqueries env checkSubquery fuel params scope .eq left right
          | .ne => checkRowComparisonCore subqueries env checkSubquery fuel params scope .ne left right
          | .lt => checkRowComparisonCore subqueries env checkSubquery fuel params scope .lt left right
          | .le => checkRowComparisonCore subqueries env checkSubquery fuel params scope .le left right
          | .gt => checkRowComparisonCore subqueries env checkSubquery fuel params scope .gt left right
          | .ge => checkRowComparisonCore subqueries env checkSubquery fuel params scope .ge left right
          | _ => .error (invalid "row_operator"
              "Constructor-pair rows require one of the six comparison operators")
      | .binary op a b => do
          let left ← checkExprCore subqueries env checkSubquery fuel params scope a
          let right ← checkExprCore subqueries env checkSubquery fuel params scope b
          match signature : binarySignature op left.type right.type with
          | none => .error (binaryFailure op a b left.type right.type)
          | some type => .ok ⟨type, left.uses ++ right.uses, .binary left.valid right.valid signature⟩
      | .distinctFrom (.row args) .null negated => do
          let typed ← checkExprListCore subqueries env checkSubquery fuel params scope args
          .ok ⟨some ⟨.bool, false⟩, typed.uses, .distinctRowNullRight (negated := negated) typed.valid⟩
      | .distinctFrom .null (.row args) negated => do
          let typed ← checkExprListCore subqueries env checkSubquery fuel params scope args
          .ok ⟨some ⟨.bool, false⟩, typed.uses, .distinctRowNullLeft (negated := negated) typed.valid⟩
      | .distinctFrom .null arg negated => do
          let typed ← checkExprCore subqueries env checkSubquery fuel params scope arg
          .ok ⟨some ⟨.bool, false⟩, typed.uses, .distinctNullLeft (negated := negated) typed.valid⟩
      | .distinctFrom arg .null negated => do
          let typed ← checkExprCore subqueries env checkSubquery fuel params scope arg
          .ok ⟨some ⟨.bool, false⟩, typed.uses, .distinctNullRight (negated := negated) typed.valid⟩
      | .distinctFrom (.row left) (.row right) negated => do
          if left.length != right.length then
            .error (invalid "distinct_row_arity" "DISTINCT row constructors require equal field counts")
          else
            let leftTyped ← checkExprListCore subqueries env checkSubquery fuel params scope left
            let rightTyped ← checkExprListCore subqueries env checkSubquery fuel params scope right
            let leftInputs := scalarInputs left leftTyped.types
            let rightInputs := scalarInputs right rightTyped.types
            match signature : rowDistinctSignature leftInputs rightInputs with
            | some _selected => .ok ⟨some ⟨.bool, false⟩, leftTyped.uses ++ rightTyped.uses,
                .distinctRows (negated := negated) leftTyped.valid rightTyped.valid signature⟩
            | none => .error (if (leftInputs.zip rightInputs).any
                  (fun pair => arrayPredicateMissingEquality pair.1 pair.2) then
                unsupported "array_element_operator"
                  "Array field equality requires a certified element operator"
              else invalid "distinct_signature" "Row fields have no admitted exact Boolean equality operator")
      | .distinctFrom left right negated => do
          if ordinaryLeft : OrdinaryDistinctOperand left then
            if ordinaryRight : OrdinaryDistinctOperand right then
              let leftTyped ← checkExprCore subqueries env checkSubquery fuel params scope left
              let rightTyped ← checkExprCore subqueries env checkSubquery fuel params scope right
              match signature : distinctSignature
                  (scalarInput left leftTyped.type) (scalarInput right rightTyped.type) with
              | some _selected => .ok ⟨some ⟨.bool, false⟩, leftTyped.uses ++ rightTyped.uses,
                  .distinctScalar (negated := negated) leftTyped.valid rightTyped.valid ordinaryLeft ordinaryRight signature⟩
              | none => .error (if arrayPredicateMissingEquality
                    (scalarInput left leftTyped.type) (scalarInput right rightTyped.type) then
                  unsupported "array_element_operator"
                    "Array equality requires a certified element operator"
                else invalid "distinct_signature" "Operands have no admitted exact Boolean equality operator")
            else .error (unsupported "distinct_composite"
              "Composite values outside direct flat-row pairs require a separate record type contract")
          else .error (unsupported "distinct_composite"
            "Composite values outside direct flat-row pairs require a separate record type contract")
      | .concat a b => do
          let left ← checkExprCore subqueries env checkSubquery fuel params scope a
          let right ← checkExprCore subqueries env checkSubquery fuel params scope b
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
      | .unary op a => do
          match folded : rawIntegerValue (.unary op a) with
          | some value => .ok ⟨some ⟨foldedIntegerType value, false⟩, [], .foldedInteger folded⟩
          | none =>
            if ordinary : OrdinaryUnary op a then
              let arg ← checkExprCore subqueries env checkSubquery fuel params scope a
              match signature : unarySignature op arg.type with
              | none => .error (missingSignature (uncontextualizedString a)
                  "operator_signature" "Unary overload resolution is outside the explicit profile signatures")
              | some type => .ok ⟨type, arg.uses, .unary arg.valid signature ordinary⟩
            else .error (unsupported "signed_integer_boundary" "Raw signed integer syntax requires literal folding")
      | .isNull (.row args) negated => do
          let typed ← checkExprListCore subqueries env checkSubquery fuel params scope args
          .ok ⟨some ⟨.bool, false⟩, typed.uses, .isNullRow (negated := negated) typed.valid⟩
      | .isNull a negated => do
          let arg ← checkExprCore subqueries env checkSubquery fuel params scope a
          .ok ⟨some ⟨.bool, false⟩, arg.uses, .isNull (negated := negated) arg.valid⟩
      | .pattern a b false => do
          let arg ← checkExprCore subqueries env checkSubquery fuel params scope a
          let pattern ← checkExprCore subqueries env checkSubquery fuel params scope b
          match signature : patternSignature arg.type pattern.type with
          | none => .error (missingSignature (uncontextualizedString a || uncontextualizedString b)
              "pattern_signature" "LIKE requires compatible string or BYTEA operands")
          | some type => .ok ⟨type, arg.uses ++ pattern.uses, .pattern arg.valid pattern.valid signature⟩
      | .pattern a b true => do
          let arg ← checkExprCore subqueries env checkSubquery fuel params scope a
          let pattern ← checkExprCore subqueries env checkSubquery fuel params scope b
          match signature : stringMatchSignature (scalarInput a arg.type) (scalarInput b pattern.type) with
          | none => .error (invalid "ilike_signature" "ILIKE requires string or contextually typed unknown operands")
          | some _selected => .ok ⟨some ⟨.bool,
                (scalarInput a arg.type).nullable || (scalarInput b pattern.type).nullable⟩,
              arg.uses ++ pattern.uses, .ilike arg.valid pattern.valid signature⟩
      | .regex a b insensitive negated => do
          let arg ← checkExprCore subqueries env checkSubquery fuel params scope a
          let pattern ← checkExprCore subqueries env checkSubquery fuel params scope b
          match signature : stringMatchSignature (scalarInput a arg.type) (scalarInput b pattern.type) with
          | none => .error (invalid "regex_signature" "Regex matching requires string or contextually typed unknown operands")
          | some _selected => .ok ⟨some ⟨.bool,
                (scalarInput a arg.type).nullable || (scalarInput b pattern.type).nullable⟩,
              arg.uses ++ pattern.uses,
              .regex (insensitive := insensitive) (negated := negated) arg.valid pattern.valid signature⟩
      | .extract field a => do
          let arg ← checkExprCore subqueries env checkSubquery fuel params scope a
          match signature : extractSignature (scalarInput a arg.type) with
          | none => .error (invalid "extract_signature"
              "EXTRACT requires an unambiguous DATE, TIME, TIMETZ, TIMESTAMP, TIMESTAMPTZ or INTERVAL input")
          | some selected => .ok ⟨some ⟨selected.output, extractNullable (scalarInput a arg.type)⟩,
              arg.uses, .extract (field := field) arg.valid signature⟩
      | .jsonAccess op a b => do
          let arg ← checkExprCore subqueries env checkSubquery fuel params scope a
          let key ← checkExprCore subqueries env checkSubquery fuel params scope b
          match signature : jsonAccessSignature op (scalarInput a arg.type) (scalarInput b key.type) with
          | none => .error (invalid "json_extraction_signature"
              "JSON extraction requires an unambiguous JSON/JSONB input and a compatible INTEGER/TEXT key or TEXT[] path")
          | some selected => .ok ⟨some ⟨selected.output, true⟩, arg.uses ++ key.uses,
              .jsonAccess arg.valid key.valid signature⟩
      | .jsonExistence op a b => do
          let arg ← checkExprCore subqueries env checkSubquery fuel params scope a
          let keys ← checkExprCore subqueries env checkSubquery fuel params scope b
          match signature : jsonExistenceSignature op (scalarInput a arg.type) (scalarInput b keys.type) with
          | none => .error (invalid "json_existence_signature"
              "JSONB existence requires JSONB and a TEXT key or TEXT[] keys; two unknown operands are ambiguous for ?|")
          | some selected =>
              .ok ⟨some ⟨selected.output,
                (scalarInput a arg.type).nullable || (scalarInput b keys.type).nullable⟩,
                arg.uses ++ keys.uses, .jsonExistence arg.valid keys.valid signature⟩
      | .containment a b containedBy => do
          let left ← checkExprCore subqueries env checkSubquery fuel params scope a
          let right ← checkExprCore subqueries env checkSubquery fuel params scope b
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
          let left ← checkExprCore subqueries env checkSubquery fuel params scope a
          let right ← checkExprCore subqueries env checkSubquery fuel params scope b
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
      | .collate a name => do
          let arg ← checkExprCore subqueries env checkSubquery fuel params scope a
          .ok ⟨arg.type, arg.uses, .collate arg.valid⟩
      | .cast a target => do
          if intervalPrecisionGap target then throw intervalPrecisionFailure
          if declaration : DataTypeWellFormed target then
            match supported : concreteType target with
            | none => .error (unsupported "cast_type" "Cast target is outside the concrete PostgreSQL scalar profile")
            | some base =>
                if ordinary : OrdinaryCast a target then
                  let arg ← checkExprCore subqueries env checkSubquery fuel params scope a
                  if allowed : castAllowed arg.type base = true then
                    .ok ⟨castSignature arg.type base, arg.uses,
                      .cast arg.valid supported declaration allowed ordinary⟩
                  else .error (invalid "cast_signature" "PostgreSQL has no explicit cast between these concrete scalar types")
                else match shape : a with
                  | .array elements =>
                    let args ← checkArrayCore subqueries env checkSubquery fuel params scope base elements
                    .ok ⟨some ⟨base, false⟩, args.uses,
                      by simpa only [shape] using ExprValid.castArray args.valid supported declaration⟩
                  | _ => .error (invalid "cast_category" "Unclassified contextual cast")
          else .error (invalid "type_declaration" "Cast target has invalid type modifiers")
      | .array elements => do
          let args ← checkExprListCore subqueries env checkSubquery fuel params scope elements
          match signature : arraySignature (scalarInputs elements args.types) with
          | none => .error (invalid "array_constructor_type"
              "An inferred array requires nonempty elements with a common implicit type; empty arrays require a direct array cast")
          | some result => .ok ⟨some result, args.uses, .array args.valid signature⟩
      | .row _ => .error (unsupported "record_value"
          "Standalone and nested record values require a separate composite-type contract")
      | .substring form args => do
          if args.length != form.arity then
            throw (invalid "substring_arity" "SUBSTRING special syntax has the wrong number of arguments")
          let argsTyped ← checkExprListCore subqueries env checkSubquery fuel params scope args
          let arguments ← checkSubstringArguments form (scalarInputs args argsTyped.types)
          match signature : resolveOverload substringCatalog arguments.val with
          | none => .error (invalid "substring_signature"
              "SUBSTRING has no unique applicable TEXT/BYTEA positional or TEXT regex overload")
          | some selected => .ok ⟨some ⟨selected.output, substringNullable selected arguments.val⟩,
              argsTyped.uses, .substring argsTyped.valid arguments.property signature⟩
      | .call name args => do
          let argsTyped ← checkExprListCore subqueries env checkSubquery fuel params scope args
          if callee : builtinName name = some "make_interval" then
            let binding ← checkArguments makeIntervalParameters (args.map fun _ => none)
              (scalarInputs args argsTyped.types)
            match signature : makeIntervalSignature binding.val with
            | none => .error (invalid "function_signature"
                "make_interval arguments require implicit coercion to six INTEGER fields and DOUBLE PRECISION seconds")
            | some result => .ok ⟨some result, argsTyped.uses,
                .defaultCall argsTyped.valid callee binding.property signature⟩
          else
            match signature : callSignature name (scalarInputs args argsTyped.types) with
            | none => .error (if knownFunction name then
                invalid "function_signature" "Built-in function has no unique applicable overload for these arguments"
              else unsupported "function_signature"
                "User-defined functions and other built-ins require a separate signature profile")
            | some result => .ok ⟨some result, argsTyped.uses, .call argsTyped.valid signature⟩
      | .namedCall name args => do
          if callee : builtinName name = some "make_interval" then
            let argsTyped ← checkExprListCore subqueries env checkSubquery fuel params scope (args.map CallArgument.expression)
            let binding ← checkArguments makeIntervalParameters (args.map CallArgument.name?)
              (scalarInputs (args.map CallArgument.expression) argsTyped.types)
            match signature : makeIntervalSignature binding.val with
            | none => .error (invalid "function_signature"
                "make_interval arguments require implicit coercion to six INTEGER fields and DOUBLE PRECISION seconds")
            | some result => .ok ⟨some result, argsTyped.uses,
                .namedCall argsTyped.valid callee binding.property signature⟩
          else .error (unsupported "named_function_signature"
              "Named arguments require an explicit parameter-name and default-value declaration")
      | .coalesce args => do
          let argsTyped ← checkExprListCore subqueries env checkSubquery fuel params scope args
          match signature : coalesceSignature (scalarInputs args argsTyped.types) with
          | none => .error (invalid "conditional_signature" "COALESCE requires nonempty, implicitly compatible arguments")
          | some result => .ok ⟨some result, argsTyped.uses, .coalesce argsTyped.valid signature⟩
      | .greatest args => do
          let argsTyped ← checkExprListCore subqueries env checkSubquery fuel params scope args
          match signature : extremumSignature (scalarInputs args argsTyped.types) with
          | none => .error (operatorFailure argsTyped.types false "conditional_signature"
              "GREATEST requires a nonempty common orderable type")
          | some result => .ok ⟨some result, argsTyped.uses, .greatest argsTyped.valid signature⟩
      | .least args => do
          let argsTyped ← checkExprListCore subqueries env checkSubquery fuel params scope args
          match signature : extremumSignature (scalarInputs args argsTyped.types) with
          | none => .error (operatorFailure argsTyped.types false "conditional_signature"
              "LEAST requires a nonempty common orderable type")
          | some result => .ok ⟨some result, argsTyped.uses, .least argsTyped.valid signature⟩
      | .nullIf left right => do
          let leftTyped ← checkExprCore subqueries env checkSubquery fuel params scope left
          let rightTyped ← checkExprCore subqueries env checkSubquery fuel params scope right
          match signature : nullIfSignature (scalarInput left leftTyped.type) (scalarInput right rightTyped.type) with
          | none => .error (operatorFailure [leftTyped.type, rightTyped.type] false
              "conditional_signature" "NULLIF requires a unique equality operator")
          | some result => .ok ⟨some result, leftTyped.uses ++ rightTyped.uses,
              .nullIf leftTyped.valid rightTyped.valid signature⟩
      | .caseExpr operand branches otherwise => do
          let operandTyped ← checkOptionalExprCore subqueries env checkSubquery fuel params scope operand
          let branchesTyped ← checkBranchesCore subqueries env checkSubquery fuel params scope branches
          let otherwiseTyped ← checkOptionalExprCore subqueries env checkSubquery fuel params scope otherwise
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
          let leftTyped ← checkExprCore subqueries env checkSubquery fuel params scope left
          let rightTyped ← checkExprCore subqueries env checkSubquery fuel params scope right
          match signature : quantifiedComparisonSignature op
              (scalarInput left leftTyped.type) (scalarInput right rightTyped.type) with
          | none => .error (invalid "quantified_comparison_signature"
              "ANY/SOME/ALL requires a scalar Boolean comparison operator and an array or contextually typed unknown RHS")
          | some _selected => .ok ⟨some ⟨.bool, true⟩, leftTyped.uses ++ rightTyped.uses,
              .quantifiedComparison (quantifier := quantifier) leftTyped.valid rightTyped.valid signature⟩
      | .subscript base indices => do
          if nonempty : indices ≠ [] then
            if dimensions : indices.length ≤ 6 then
              let baseTyped ← checkExprCore subqueries env checkSubquery fuel params scope base
              match shape : baseTyped.type with
              | some ⟨.array element, nullable⟩ =>
                  let bounds ← checkSubscriptsCore subqueries env checkSubquery fuel params scope indices
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
            let arg ← checkExprCore subqueries env checkSubquery fuel params scope a
            let items ← checkExprListCore subqueries env checkSubquery fuel params scope values
            match signature : comparisonListSignature (arg.type :: items.types) with
            | none => .error (operatorFailure (arg.type :: items.types) (uncontextualizedString a || values.any uncontextualizedString)
                "comparison_signature" "IN operands have no covered common comparison signature")
            | some type => .ok ⟨type, arg.uses ++ items.uses, .inList arg.valid items.valid nonempty signature⟩
          else .error (invalid "empty_in_list" "IN requires at least one value")
      | .between a b c negated => do
          let arg ← checkExprCore subqueries env checkSubquery fuel params scope a
          let lower ← checkExprCore subqueries env checkSubquery fuel params scope b
          let upper ← checkExprCore subqueries env checkSubquery fuel params scope c
          match signature : comparisonListSignature [arg.type, lower.type, upper.type] with
          | none => .error (operatorFailure [arg.type, lower.type, upper.type]
              (uncontextualizedString a || uncontextualizedString b || uncontextualizedString c)
              "comparison_signature" "BETWEEN operands have no covered common comparison signature")
          | some type => .ok ⟨type, arg.uses ++ lower.uses ++ upper.uses,
              .between (negated := negated) arg.valid lower.valid upper.valid signature⟩
      | .countAll | .aggregate .. | .filteredAggregate .. =>
          .error (unsupported "aggregate" "Independent aggregate and grouped-query rules are not implemented yet")
      | .exists child => do
          let checked ← checkSubquery child
          .ok ⟨some ⟨.bool, false⟩, checked.uses, .exists checked.valid⟩
      | .scalarQuery child => do
          let checked ← checkSubquery child
          match width : checked.output with
          | [column] => .ok ⟨some ⟨column.type.base, true⟩, checked.uses,
              .scalarQuery (width ▸ checked.valid)⟩
          | _ => .error (invalid "scalar_subquery_arity" "A scalar subquery must expose exactly one column")
      | .inQuery (.row fields) child => do
          if nonempty : fields ≠ [] then
            let left ← checkExprListCore subqueries env checkSubquery fuel params scope fields
            let checked ← checkSubquery child
            if arity : fields.length = checked.output.length then
              match signature : rowDistinctSignature (scalarInputs fields left.types)
                  (checked.output.map (fun column => ScalarInput.known column.type)) with
              | some _ => .ok ⟨some ⟨.bool, true⟩, left.uses ++ checked.uses,
                  .inRowQuery left.valid checked.valid nonempty arity signature⟩
              | none => .error (operatorFailure
                  (left.types ++ checked.output.map (fun column => some column.type))
                  (fields.any uncontextualizedString) "in_row_subquery_signature"
                  "Row IN fields require compatible equality operators for each child output column")
            else .error (invalid "in_row_subquery_arity" "A row IN subquery must expose exactly one column per left field")
          else .error (invalid "in_row_subquery_arity" "A row IN subquery requires at least one left field")
      | .inQuery arg child => do
            let left ← checkExprCore subqueries env checkSubquery fuel params scope arg
            let checked ← checkSubquery child
            match width : checked.output with
            | [column] =>
              match signature : equalityOverload (scalarInput arg left.type) (.known column.type) with
              | none => .error (operatorFailure [left.type, some column.type] (uncontextualizedString arg)
                  "in_subquery_signature" "IN subquery operands have no covered equality signature")
              | some _ => .ok ⟨some ⟨.bool, (scalarInput arg left.type).nullable || column.type.nullable⟩,
                  left.uses ++ checked.uses, .inQuery left.valid (width ▸ checked.valid) signature⟩
            | _ => .error (invalid "in_subquery_arity" "A scalar IN subquery must expose exactly one column")

  def checkExprListCore (subqueries : SubqueryJudgment) (env : CTEEnv)
      (checkSubquery : SubqueryChecker subqueries env) (fuel : Nat) (params : ParameterEnv) (scope : Scope) (exprs : List Advanced.Expr) :
      Except Failure (ExprListCertificateCore subqueries env params scope exprs) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => match exprs with
      | [] => .ok ⟨[], [], .nil⟩
      | expr :: exprs => do
          let head ← checkExprCore subqueries env checkSubquery fuel params scope expr
          let tail ← checkExprListCore subqueries env checkSubquery fuel params scope exprs
          .ok ⟨head.type :: tail.types, head.uses ++ tail.uses, .cons head.valid tail.valid⟩

  def checkRowComparisonCore (subqueries : SubqueryJudgment) (env : CTEEnv)
      (checkSubquery : SubqueryChecker subqueries env) (fuel : Nat) (params : ParameterEnv) (scope : Scope)
      (op : Advanced.ComparisonOp) (left right : List Advanced.Expr) :
      Except Failure (ExprCertificateCore subqueries env params scope (.binary op.toBinOp (.row left) (.row right))) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => do
      if left.isEmpty || left.length != right.length then
        .error (invalid "row_comparison_arity" "Row comparison requires equal positive field counts")
      else
        let leftTyped ← checkExprListCore subqueries env checkSubquery fuel params scope left
        let rightTyped ← checkExprListCore subqueries env checkSubquery fuel params scope right
        match signature : rowComparisonSignature op
            (scalarInputs left leftTyped.types) (scalarInputs right rightTyped.types) with
        | some _selected => .ok ⟨some ⟨.bool, true⟩, leftTyped.uses ++ rightTyped.uses,
            .rowComparison leftTyped.valid rightTyped.valid signature⟩
        | none => .error (operatorFailure (leftTyped.types ++ rightTyped.types) false
            "row_comparison_signature" "Row fields require compatible scalar comparison operators with admitted B-tree strategies")

  /-- Direct target-directed array construction; target context follows only
  nested raw constructors. It never crosses a function/conditional/cast node. -/
  def checkArrayCore (subqueries : SubqueryJudgment) (env : CTEEnv)
      (checkSubquery : SubqueryChecker subqueries env) (fuel : Nat) (params : ParameterEnv) (scope : Scope)
      (target : ScalarType) (exprs : List Advanced.Expr) :
      Except Failure (ArrayCertificateCore subqueries env params scope target exprs) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => do
      let args ← checkArrayElementsCore subqueries env checkSubquery fuel params scope target exprs
      if signature : arrayCastSignature target (scalarInputs exprs args.types) = true then
        .ok ⟨args.uses, .targeted args.valid signature⟩
      else .error (invalid "array_constructor_cast"
        "Array constructor elements cannot be explicitly coerced to the direct cast target")

  def checkArrayElementsCore (subqueries : SubqueryJudgment) (env : CTEEnv)
      (checkSubquery : SubqueryChecker subqueries env) (fuel : Nat) (params : ParameterEnv) (scope : Scope)
      (target : ScalarType) (exprs : List Advanced.Expr) :
      Except Failure (ArrayElementsCertificateCore subqueries env params scope target exprs) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => match exprs with
      | [] => .ok ⟨[], [], .nil⟩
      | .array elements :: rest => do
          let head ← checkArrayCore subqueries env checkSubquery fuel params scope target elements
          let tail ← checkArrayElementsCore subqueries env checkSubquery fuel params scope target rest
          .ok ⟨some ⟨target, false⟩ :: tail.types, head.uses ++ tail.uses,
            .nested head.valid tail.valid⟩
      | expr :: exprs => do
          if category : OrdinaryArrayElement expr then
            let head ← checkExprCore subqueries env checkSubquery fuel params scope expr
            let tail ← checkArrayElementsCore subqueries env checkSubquery fuel params scope target exprs
            .ok ⟨head.type :: tail.types, head.uses ++ tail.uses,
              .ordinary category head.valid tail.valid⟩
          else .error (invalid "array_element_category" "Unclassified array constructor child")

  def checkOptionalExprCore (subqueries : SubqueryJudgment) (env : CTEEnv)
      (checkSubquery : SubqueryChecker subqueries env) (fuel : Nat) (params : ParameterEnv) (scope : Scope) (expr : Option Advanced.Expr) :
      Except Failure (OptionalExprCertificateCore subqueries env params scope expr) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => match expr with
      | none => .ok ⟨none, [], .absent⟩
      | some expr => do
          let typed ← checkExprCore subqueries env checkSubquery fuel params scope expr
          .ok ⟨typed.type, typed.uses, .present typed.valid⟩

  def checkSubscriptsCore (subqueries : SubqueryJudgment) (env : CTEEnv)
      (checkSubquery : SubqueryChecker subqueries env) (fuel : Nat) (params : ParameterEnv) (scope : Scope)
      (indices : List Advanced.Subscript) :
      Except Failure (SubscriptsCertificateCore subqueries env params scope indices) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => match indices with
      | [] => .ok ⟨[], .nil⟩
      | .index expr :: rest => do
          let bound ← checkExprCore subqueries env checkSubquery fuel params scope expr
          if signature : subscriptBoundSignature (scalarInput expr bound.type) = true then
            let tail ← checkSubscriptsCore subqueries env checkSubquery fuel params scope rest
            .ok ⟨bound.uses ++ tail.uses, .index bound.valid signature tail.valid⟩
          else .error (invalid "subscript_bound"
            "Array bounds require assignment coercion to INTEGER; concrete numeric types or unknown inputs are admitted")
      | .slice lo hi :: rest => do
          let lower ← checkOptionalExprCore subqueries env checkSubquery fuel params scope lo
          let upper ← checkOptionalExprCore subqueries env checkSubquery fuel params scope hi
          if lowerSignature : optionalSubscriptBoundSignature lo lower.type = true then
            if upperSignature : optionalSubscriptBoundSignature hi upper.type = true then
              let tail ← checkSubscriptsCore subqueries env checkSubquery fuel params scope rest
              .ok ⟨lower.uses ++ upper.uses ++ tail.uses,
                .slice lower.valid upper.valid lowerSignature upperSignature tail.valid⟩
            else .error (invalid "subscript_bound" "Array upper bound has no assignment coercion to INTEGER")
          else .error (invalid "subscript_bound" "Array lower bound has no assignment coercion to INTEGER")

  def checkBranchesCore (subqueries : SubqueryJudgment) (env : CTEEnv)
      (checkSubquery : SubqueryChecker subqueries env) (fuel : Nat) (params : ParameterEnv) (scope : Scope)
      (branches : List (Advanced.Expr × Advanced.Expr)) :
      Except Failure (BranchesCertificateCore subqueries env params scope branches) :=
    match fuel with
    | 0 => .error exhausted
    | fuel + 1 => match branches with
      | [] => .ok ⟨[], [], [], .nil⟩
      | (condition, result) :: branches => do
          let conditionTyped ← checkExprCore subqueries env checkSubquery fuel params scope condition
          let resultTyped ← checkExprCore subqueries env checkSubquery fuel params scope result
          let tail ← checkBranchesCore subqueries env checkSubquery fuel params scope branches
          .ok ⟨conditionTyped.type :: tail.conditions, resultTyped.type :: tail.results,
            conditionTyped.uses ++ resultTyped.uses ++ tail.uses,
            .cons conditionTyped.valid resultTyped.valid tail.valid⟩
end


abbrev ExprCertificate := ExprCertificateCore NoSubqueries []
abbrev ExprListCertificate := ExprListCertificateCore NoSubqueries []
abbrev OptionalExprCertificate := OptionalExprCertificateCore NoSubqueries []
abbrev BranchesCertificate := BranchesCertificateCore NoSubqueries []
abbrev ArrayCertificate := ArrayCertificateCore NoSubqueries []
abbrev ArrayElementsCertificate := ArrayElementsCertificateCore NoSubqueries []
abbrev SubscriptsCertificate := SubscriptsCertificateCore NoSubqueries []
abbrev checkExpr := checkExprCore NoSubqueries [] noSubqueryChecker
abbrev checkExprList := checkExprListCore NoSubqueries [] noSubqueryChecker
abbrev checkRowComparison := checkRowComparisonCore NoSubqueries [] noSubqueryChecker
abbrev checkArray := checkArrayCore NoSubqueries [] noSubqueryChecker
abbrev checkArrayElements := checkArrayElementsCore NoSubqueries [] noSubqueryChecker
abbrev checkOptionalExpr := checkOptionalExprCore NoSubqueries [] noSubqueryChecker
abbrev checkSubscripts := checkSubscriptsCore NoSubqueries [] noSubqueryChecker
abbrev checkBranches := checkBranchesCore NoSubqueries [] noSubqueryChecker

end SQLean.SelectContract
