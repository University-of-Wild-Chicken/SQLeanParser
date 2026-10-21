import SQLean.RenderContract.CollationPreservation

/-! Parameter translation preserves the independent basic SELECT judgment.

The derivations below do not import the parser, renderer, executable checker,
or render certificate. They preserve the exact output labels, concrete types,
nullability, and index-keyed parameter environment for every valid basic SELECT.
This is a static preservation theorem, not an interpretation of database
execution or a claim that every advanced construct has basic-tier validity.
-/
namespace SQLean.RenderContract
open Advanced SelectContract
set_option maxHeartbeats 1000000

@[simp] theorem translateExpr_case (operand : Option Advanced.Expr)
    (branches : List (Advanced.Expr × Advanced.Expr)) (otherwise : Option Advanced.Expr) :
    translateExpr (.caseExpr operand branches otherwise) =
      .caseExpr (operand.map translateExpr)
        (branches.map fun pair => (translateExpr pair.1, translateExpr pair.2))
        (otherwise.map translateExpr) := by
  rw [translateExpr.eq_def]
  simp only [List.attach_map_val (f := fun pair : Advanced.Expr × Advanced.Expr =>
    (translateExpr pair.1, translateExpr pair.2))]
  cases operand <;> cases otherwise <;> rfl

@[simp] theorem translateParameter_index (parameter : Parameter) :
    parameterIndex (translateParameter parameter) = parameterIndex parameter := by
  cases parameter <;> rfl

@[simp] theorem raw_integer_value_translated (expr : Advanced.Expr) :
    rawIntegerValue (translateExpr expr) = rawIntegerValue expr := by
  cases expr <;> simp only [translateExpr, translateExpr_case, rawIntegerValue]
  rename_i op arg
  cases op <;> simp only [rawIntegerValue]
  rw [raw_integer_value_translated arg]
termination_by sizeOf expr
decreasing_by all_goals (simp_all <;> omega)

@[simp] theorem ordinary_unary_translated (op : UnOp) (expr : Advanced.Expr) :
    OrdinaryUnary op (translateExpr expr) ↔ OrdinaryUnary op expr := by
  cases op <;> simp only [OrdinaryUnary, raw_integer_value_translated]

@[simp] theorem ordinary_cast_translated (expr : Advanced.Expr) (target : DataType) :
    OrdinaryCast (translateExpr expr) target ↔ OrdinaryCast expr target := by
  cases expr <;> simp only [OrdinaryCast, translateExpr, translateExpr_case]

@[simp] theorem ordinary_array_element_translated (expr : Advanced.Expr) :
    OrdinaryArrayElement (translateExpr expr) ↔ OrdinaryArrayElement expr := by
  cases expr <;> simp only [OrdinaryArrayElement, translateExpr, translateExpr_case]

@[simp] theorem ordinary_distinct_operand_translated (expr : Advanced.Expr) :
    OrdinaryDistinctOperand (translateExpr expr) ↔ OrdinaryDistinctOperand expr := by
  cases expr <;> simp only [OrdinaryDistinctOperand, translateExpr, translateExpr_case]

@[simp] theorem scalar_input_translated (expr : Advanced.Expr) (type : ExprType) :
    scalarInput (translateExpr expr) type = scalarInput expr type := by
  exact collation_scalar_input_translated expr type

@[simp] theorem scalar_inputs_translated (exprs : List Advanced.Expr) (types : List ExprType) :
    scalarInputs (exprs.map translateExpr) types = scalarInputs exprs types := by
  induction exprs generalizing types with
  | nil => cases types <;> rfl
  | cons expr exprs ih =>
    cases types with
    | nil => rfl
    | cons type types =>
      simpa only [scalarInputs, List.zip_cons_cons, List.map_cons, scalar_input_translated] using
        congrArg (scalarInput expr type :: ·) (ih types)

@[simp] theorem translateSubscript_slice (lower upper : Option Advanced.Expr) :
    translateSubscript (.slice lower upper) =
      .slice (lower.map translateExpr) (upper.map translateExpr) := by
  rw [translateSubscript.eq_def]
  cases lower <;> cases upper <;> rfl

@[simp] theorem subscript_isSlice_translated (subscript : Advanced.Subscript) :
    (translateSubscript subscript).isSlice = subscript.isSlice := by
  cases subscript <;> simp only [translateSubscript_slice, translateSubscript,
    Advanced.Subscript.isSlice]

@[simp] theorem subscripts_any_slice_translated (subscripts : List Advanced.Subscript) :
    (subscripts.map translateSubscript).any Advanced.Subscript.isSlice =
      subscripts.any Advanced.Subscript.isSlice := by
  simp only [List.any_map, Function.comp_def, subscript_isSlice_translated]

@[simp] theorem optional_subscript_bound_translated (expr : Option Advanced.Expr) (type : ExprType) :
    optionalSubscriptBoundSignature (expr.map translateExpr) type =
      optionalSubscriptBoundSignature expr type := by
  cases expr <;> simp only [Option.map, optionalSubscriptBoundSignature, scalar_input_translated]

private theorem call_arguments_size (args : List CallArgument) :
    sizeOf (args.map CallArgument.expression) ≤ sizeOf args := by
  induction args with
  | nil => simp
  | cons arg args ih => cases arg <;> simp_all [CallArgument.expression] <;> omega


/-- Only child queries smaller than the current AST bound are assumed to have
parameter-translation derivations. The outer query proof discharges these
premises by well-founded recursion; no checker result is used. -/
def SubqueriesTranslated (subqueries : SubqueryJudgment) (bound : Nat) : Prop :=
  ∀ env query output uses, sizeOf query < bound → subqueries env query output uses →
    subqueries env (translateParameters query) output (uses.map translateParameter)

private theorem no_subqueries_translated (bound : Nat) :
    SubqueriesTranslated NoSubqueries bound := by
  intro env query output uses small impossible
  exact False.elim impossible

mutual
  /-- Each scalar typing derivation survives the explicit parameter translation,
  with parameter occurrences translated in their original order. -/
  theorem expr_valid_translated_core
      (preserved : SubqueriesTranslated sq bound)
      (valid : ExprValidCore sq params env scope expr type uses)
      (small : sizeOf expr ≤ bound := by simp_all <;> omega) :
      ExprValidCore sq params env scope (translateExpr expr) type (uses.map translateParameter) := by
    cases valid with
    | int range => simpa only [translateExpr, List.map_nil] using ExprValid.int range
    | bigInt large range => simpa only [translateExpr, List.map_nil] using ExprValid.bigInt large range
    | numericInt large => simpa only [translateExpr, List.map_nil] using ExprValid.numericInt large
    | decimal lexical => simpa only [translateExpr, List.map_nil] using ExprValid.decimal lexical
    | minInt32 => simpa only [translateExpr, List.map_nil] using ExprValid.minInt32
    | minInt64 => simpa only [translateExpr, List.map_nil] using ExprValid.minInt64
    | foldedInteger folded =>
        exact .foldedInteger (by simpa only [raw_integer_value_translated] using folded)
    | text => simpa only [translateExpr, List.map_nil] using ExprValid.text
    | bool => simpa only [translateExpr, List.map_nil] using ExprValid.bool
    | null => simpa only [translateExpr, List.map_nil] using ExprValid.null
    | contextValue => simpa only [translateExpr, List.map_nil] using ExprValid.contextValue
    | parameter present identity supported =>
        simpa only [translateExpr, List.map_cons, List.map_nil] using
          ExprValid.parameter present
            (identity.trans (translateParameter_index _).symm) supported
    | column resolved =>
        simpa only [translateExpr, List.map_nil] using ExprValid.column resolved
    | binary left right signature =>
        simpa only [translateExpr, List.map_append] using
          ExprValid.binary (expr_valid_translated_core preserved left) (expr_valid_translated_core preserved right) signature
    | concat left right signature =>
        simpa only [translateExpr, List.map_append, scalar_input_translated] using
          ExprValid.concat (expr_valid_translated_core preserved left) (expr_valid_translated_core preserved right)
            (by simpa only [scalar_input_translated] using signature)
    | arrayConcat left right signature =>
        simpa only [translateExpr, List.map_append, scalar_input_translated] using
          ExprValid.arrayConcat (expr_valid_translated_core preserved left) (expr_valid_translated_core preserved right)
            (by simpa only [scalar_input_translated] using signature)
    | rowComparison left right signature =>
        simpa only [translateExpr, List.attach_map_val, List.map_append] using
          ExprValid.rowComparison (expr_list_valid_translated_core preserved left) (expr_list_valid_translated_core preserved right)
            (by simpa only [scalar_inputs_translated] using signature)
    | distinctScalar left right ordinaryLeft ordinaryRight signature =>
        simpa only [translateExpr, List.map_append] using
          ExprValid.distinctScalar (expr_valid_translated_core preserved left) (expr_valid_translated_core preserved right)
            ((ordinary_distinct_operand_translated _).mpr ordinaryLeft)
            ((ordinary_distinct_operand_translated _).mpr ordinaryRight)
            (by simpa only [scalar_input_translated] using signature)
    | distinctNullLeft arg =>
        simpa only [translateExpr] using ExprValid.distinctNullLeft (expr_valid_translated_core preserved arg)
    | distinctNullRight arg =>
        simpa only [translateExpr] using ExprValid.distinctNullRight (expr_valid_translated_core preserved arg)
    | distinctRows left right signature =>
        simpa only [translateExpr, List.attach_map_val, List.map_append] using
          ExprValid.distinctRows (expr_list_valid_translated_core preserved left) (expr_list_valid_translated_core preserved right)
            (by simpa only [scalar_inputs_translated] using signature)
    | distinctRowNullLeft args =>
        simpa only [translateExpr, List.attach_map_val] using
          ExprValid.distinctRowNullLeft (expr_list_valid_translated_core preserved args)
    | distinctRowNullRight args =>
        simpa only [translateExpr, List.attach_map_val] using
          ExprValid.distinctRowNullRight (expr_list_valid_translated_core preserved args)
    | quantifiedComparison left right signature =>
        simpa only [translateExpr, List.map_append] using
          ExprValid.quantifiedComparison (expr_valid_translated_core preserved left) (expr_valid_translated_core preserved right)
            (by simpa only [scalar_input_translated] using signature)
    | subscript base bounds nonempty dimensions =>
        simpa only [translateExpr, List.attach_map_val, List.map_append,
          subscripts_any_slice_translated] using
          ExprValid.subscript (expr_valid_translated_core preserved base) (subscripts_valid_translated_core preserved bounds)
            (by simpa using nonempty) (by simpa using dimensions)
    | unary arg signature ordinary =>
        simpa only [translateExpr] using ExprValid.unary (expr_valid_translated_core preserved arg) signature
          ((ordinary_unary_translated _ _).mpr ordinary)
    | isNull arg =>
        simpa only [translateExpr] using ExprValid.isNull (expr_valid_translated_core preserved arg)
    | isNullRow args =>
        simpa only [translateExpr, List.attach_map_val] using
          ExprValid.isNullRow (expr_list_valid_translated_core preserved args)
    | pattern arg pattern signature =>
        simpa only [translateExpr, List.map_append] using
          ExprValid.pattern (expr_valid_translated_core preserved arg) (expr_valid_translated_core preserved pattern) signature
    | ilike arg pattern signature =>
        simpa only [translateExpr, List.map_append, scalar_input_translated] using
          ExprValid.ilike (expr_valid_translated_core preserved arg) (expr_valid_translated_core preserved pattern)
            (by simpa only [scalar_input_translated] using signature)
    | regex arg pattern signature =>
        simpa only [translateExpr, List.map_append, scalar_input_translated] using
          ExprValid.regex (expr_valid_translated_core preserved arg) (expr_valid_translated_core preserved pattern)
            (by simpa only [scalar_input_translated] using signature)
    | jsonAccess arg key signature =>
        simpa only [translateExpr, List.map_append] using
          ExprValid.jsonAccess (expr_valid_translated_core preserved arg) (expr_valid_translated_core preserved key)
            (by simpa only [scalar_input_translated] using signature)
    | jsonExistence arg key signature =>
        simpa only [translateExpr, List.map_append, scalar_input_translated] using
          ExprValid.jsonExistence (expr_valid_translated_core preserved arg) (expr_valid_translated_core preserved key)
            (by simpa only [scalar_input_translated] using signature)
    | containment left right signature =>
        simpa only [translateExpr, List.map_append, scalar_input_translated] using
          ExprValid.containment (expr_valid_translated_core preserved left) (expr_valid_translated_core preserved right)
            (by simpa only [scalar_input_translated] using signature)
    | arrayContainment left right signature =>
        simpa only [translateExpr, List.map_append, scalar_input_translated] using
          ExprValid.arrayContainment (expr_valid_translated_core preserved left) (expr_valid_translated_core preserved right)
            (by simpa only [scalar_input_translated] using signature)
    | overlap left right signature =>
        simpa only [translateExpr, List.map_append, scalar_input_translated] using
          ExprValid.overlap (expr_valid_translated_core preserved left) (expr_valid_translated_core preserved right)
            (by simpa only [scalar_input_translated] using signature)
    | extract arg signature =>
        simpa only [translateExpr, scalar_input_translated] using
          ExprValid.extract (expr_valid_translated_core preserved arg)
            (by simpa only [scalar_input_translated] using signature)
    | cast arg supported declaration allowed ordinary =>
        simpa only [translateExpr] using ExprValid.cast (expr_valid_translated_core preserved arg)
          supported declaration allowed ((ordinary_cast_translated _ _).mpr ordinary)
    | collate arg =>
        simpa only [translateExpr] using ExprValid.collate (expr_valid_translated_core preserved arg)
    | array args signature =>
        simpa only [translateExpr, List.attach_map_val] using
          ExprValid.array (expr_list_valid_translated_core preserved args) (by simpa using signature)
    | castArray args supported declaration =>
        simpa only [translateExpr, List.attach_map_val] using
          ExprValid.castArray (array_valid_translated_core preserved args) supported declaration
    | defaultCall args callee binding signature =>
        simpa only [translateExpr, List.attach_map_val] using
          ExprValid.defaultCall (expr_list_valid_translated_core preserved args) callee
            (by simpa only [List.map_map, Function.comp_def, scalar_inputs_translated] using binding)
            signature
    | @namedCall _ _ ts uses name callInputs result arguments args callee binding signature =>
        have sizeBound := call_arguments_size arguments
        simpa only [translateExpr, List.attach_map_val] using
          ExprValid.namedCall
            (by simpa only [translated_call_expressions] using expr_list_valid_translated_core preserved args)
            callee
            (by simpa only [translated_call_names, translated_call_expressions,
              scalar_inputs_translated] using binding) signature
    | call args signature =>
        simpa only [translateExpr, List.attach_map_val] using
          ExprValid.call (expr_list_valid_translated_core preserved args) (by simpa using signature)
    | substring args arguments signature =>
        simpa only [translateExpr, List.attach_map_val] using
          ExprValid.substring (expr_list_valid_translated_core preserved args)
            (by simpa only [scalar_inputs_translated] using arguments) signature
    | coalesce args signature =>
        simpa only [translateExpr, List.attach_map_val] using
          ExprValid.coalesce (expr_list_valid_translated_core preserved args) (by simpa using signature)
    | greatest args signature =>
        simpa only [translateExpr, List.attach_map_val] using
          ExprValid.greatest (expr_list_valid_translated_core preserved args) (by simpa using signature)
    | least args signature =>
        simpa only [translateExpr, List.attach_map_val] using
          ExprValid.least (expr_list_valid_translated_core preserved args) (by simpa using signature)
    | nullIf left right signature =>
        simpa only [translateExpr, List.map_append] using
          ExprValid.nullIf (expr_valid_translated_core preserved left) (expr_valid_translated_core preserved right)
            (by simpa using signature)
    | @caseExpr _ _ operand ta ua branches conditions results ub otherwise te ue result
        operandValid branchesValid otherwiseValid signature =>
        have transformedSignature :
            caseSignature ((operand.map translateExpr).map fun expr => scalarInput expr ta)
              (scalarInputs ((branches.map fun pair => (translateExpr pair.1, translateExpr pair.2)).map Prod.fst) conditions)
              (scalarInputs ((branches.map fun pair => (translateExpr pair.1, translateExpr pair.2)).map Prod.snd) results)
              (((otherwise.map translateExpr).map fun expr => scalarInput expr te).getD (.unknown true)) =
              some result := by
          have fstMap :
              (branches.map (fun pair => (translateExpr pair.1, translateExpr pair.2))).map Prod.fst =
                (branches.map Prod.fst).map translateExpr := by simp only [List.map_map, Function.comp_def]
          have sndMap :
              (branches.map (fun pair => (translateExpr pair.1, translateExpr pair.2))).map Prod.snd =
                (branches.map Prod.snd).map translateExpr := by simp only [List.map_map, Function.comp_def]
          simpa only [fstMap, sndMap, scalar_inputs_translated, Option.map_map, Function.comp_def,
            scalar_input_translated] using signature
        have resultValid := ExprValid.caseExpr
          (optional_expr_valid_translated_core preserved operandValid) (branches_valid_translated_core preserved branchesValid)
          (optional_expr_valid_translated_core preserved otherwiseValid) transformedSignature
        simpa only [translateExpr_case, List.map_append] using resultValid
    | inList arg values nonempty signature =>
        simpa only [translateExpr, List.attach_map_val, List.map_append] using
          ExprValid.inList (expr_valid_translated_core preserved arg) (expr_list_valid_translated_core preserved values)
            (by simpa using nonempty) signature
    | «exists» child =>
        simpa only [translateExpr] using
          ExprValid.exists (preserved _ _ _ _ (by simp_all; omega) child)
    | scalarQuery child =>
        simpa only [translateExpr] using
          ExprValid.scalarQuery (preserved _ _ _ _ (by simp_all; omega) child)
    | inQuery arg child signature =>
        simpa only [translateExpr, List.map_append, scalar_input_translated] using
          ExprValid.inQuery (expr_valid_translated_core preserved arg)
            (preserved _ _ _ _ (by simp_all; omega) child)
            (by simpa only [scalar_input_translated] using signature)
    | inRowQuery args child nonempty arity signature =>
        simpa only [translateExpr, List.attach_map_val, List.map_append] using
          ExprValid.inRowQuery (expr_list_valid_translated_core preserved args)
            (preserved _ _ _ _ (by simp_all; omega) child)
            (by simpa using nonempty) (by simpa using arity)
            (by simpa only [scalar_inputs_translated] using signature)
    | between arg lower upper signature =>
        simpa only [translateExpr, List.map_append] using
          ExprValid.between (expr_valid_translated_core preserved arg) (expr_valid_translated_core preserved lower)
            (expr_valid_translated_core preserved upper) signature
  termination_by sizeOf expr
  decreasing_by all_goals subst_vars; all_goals (try simp); all_goals omega

  theorem expr_list_valid_translated_core
      (preserved : SubqueriesTranslated sq bound)
      (valid : ExprListValidCore sq params env scope exprs types uses)
      (small : sizeOf exprs ≤ bound := by simp_all <;> omega) :
      ExprListValidCore sq params env scope (exprs.map translateExpr) types
        (uses.map translateParameter) := by
    cases valid with
    | nil => exact ExprListValid.nil
    | cons head tail =>
        simpa only [List.map_cons, List.map_append] using
          ExprListValid.cons (expr_valid_translated_core preserved head) (expr_list_valid_translated_core preserved tail)
  termination_by sizeOf exprs
  decreasing_by all_goals subst_vars; all_goals (try simp); all_goals omega

  /-- Target-directed array elaboration preserves the exact target declaration
  and original occurrence sequence, including nested empty constructors. -/
  theorem array_valid_translated_core
      (preserved : SubqueriesTranslated sq bound)
      (valid : ArrayValidCore sq params env scope target exprs uses)
      (small : sizeOf exprs ≤ bound := by simp_all <;> omega) :
      ArrayValidCore sq params env scope target (exprs.map translateExpr)
        (uses.map translateParameter) := by
    cases valid with
    | targeted args signature =>
        exact ArrayValid.targeted (array_elements_valid_translated_core preserved args)
          (by simpa only [scalar_inputs_translated] using signature)
  termination_by sizeOf exprs + 1
  decreasing_by subst_vars; omega

  theorem array_elements_valid_translated_core
      (preserved : SubqueriesTranslated sq bound)
      (valid : ArrayElementsValidCore sq params env scope target exprs types uses)
      (small : sizeOf exprs ≤ bound := by simp_all <;> omega) :
      ArrayElementsValidCore sq params env scope target (exprs.map translateExpr) types
        (uses.map translateParameter) := by
    cases valid with
    | nil => exact ArrayElementsValid.nil
    | ordinary category head tail =>
        simpa only [List.map_cons, List.map_append] using
          ArrayElementsValid.ordinary ((ordinary_array_element_translated _).mpr category)
            (expr_valid_translated_core preserved head) (array_elements_valid_translated_core preserved tail)
    | nested head tail =>
        simpa only [List.map_cons, List.map_append, translateExpr, List.attach_map_val] using
          ArrayElementsValid.nested (array_valid_translated_core preserved head)
            (array_elements_valid_translated_core preserved tail)
  termination_by sizeOf exprs
  decreasing_by all_goals subst_vars; all_goals (try simp); all_goals omega

  theorem optional_expr_valid_translated_core
      (preserved : SubqueriesTranslated sq bound)
      (valid : OptionalExprValidCore sq params env scope expr type uses)
      (small : sizeOf expr ≤ bound := by simp_all <;> omega) :
      OptionalExprValidCore sq params env scope (expr.map translateExpr) type (uses.map translateParameter) := by
    cases valid with
    | absent => exact OptionalExprValid.absent
    | present typed => exact OptionalExprValid.present (expr_valid_translated_core preserved typed)
  termination_by sizeOf expr
  decreasing_by all_goals subst_vars; all_goals (try simp); all_goals omega

  /-- Group boundaries, omitted endpoints and lower-before-upper occurrence
  order survive the parameter-only transformation. -/
  theorem subscripts_valid_translated_core
      (preserved : SubqueriesTranslated sq bound)
      (valid : SubscriptsValidCore sq params env scope subscripts uses)
      (small : sizeOf subscripts ≤ bound := by simp_all <;> omega) :
      SubscriptsValidCore sq params env scope (subscripts.map translateSubscript)
        (uses.map translateParameter) := by
    cases valid with
    | nil => exact SubscriptsValid.nil
    | index bound signature tail =>
        simpa only [List.map_cons, translateSubscript, List.map_append] using
          SubscriptsValid.index (expr_valid_translated_core preserved bound)
            (by simpa only [scalar_input_translated] using signature)
            (subscripts_valid_translated_core preserved tail)
    | slice lower upper lowerSignature upperSignature tail =>
        simpa only [List.map_cons, translateSubscript_slice, List.map_append] using
          SubscriptsValid.slice (optional_expr_valid_translated_core preserved lower)
            (optional_expr_valid_translated_core preserved upper)
            (by simpa only [optional_subscript_bound_translated] using lowerSignature)
            (by simpa only [optional_subscript_bound_translated] using upperSignature)
            (subscripts_valid_translated_core preserved tail)
  termination_by sizeOf subscripts
  decreasing_by all_goals subst_vars; all_goals (try simp); all_goals omega

  theorem branches_valid_translated_core
      (preserved : SubqueriesTranslated sq bound)
      (valid : BranchesValidCore sq params env scope branches conditions results uses)
      (small : sizeOf branches ≤ bound := by simp_all <;> omega) :
      BranchesValidCore sq params env scope
        (branches.map fun branch => (translateExpr branch.1, translateExpr branch.2))
        conditions results (uses.map translateParameter) := by
    cases valid with
    | nil => exact BranchesValid.nil
    | cons conditionTyped resultTyped tail =>
      simpa only [List.map_cons, List.map_append] using
        BranchesValid.cons (expr_valid_translated_core preserved conditionTyped) (expr_valid_translated_core preserved resultTyped)
          (branches_valid_translated_core preserved tail)
  termination_by sizeOf branches
  decreasing_by all_goals subst_vars; all_goals (try simp); all_goals omega
end

/-- Compatibility entry point for the original expression-only judgment. -/
theorem expr_valid_translated (valid : ExprValid params scope expr type uses) :
    ExprValid params scope (translateExpr expr) type (uses.map translateParameter) :=
  expr_valid_translated_core (no_subqueries_translated (sizeOf expr)) valid

theorem expr_list_valid_translated (valid : ExprListValid params scope exprs types uses) :
    ExprListValid params scope (exprs.map translateExpr) types (uses.map translateParameter) :=
  expr_list_valid_translated_core (no_subqueries_translated (sizeOf exprs)) valid

theorem array_valid_translated (valid : ArrayValid params scope target exprs uses) :
    ArrayValid params scope target (exprs.map translateExpr) (uses.map translateParameter) :=
  array_valid_translated_core (no_subqueries_translated (sizeOf exprs)) valid

theorem array_elements_valid_translated
    (valid : ArrayElementsValid params scope target exprs types uses) :
    ArrayElementsValid params scope target (exprs.map translateExpr) types (uses.map translateParameter) :=
  array_elements_valid_translated_core (no_subqueries_translated (sizeOf exprs)) valid

theorem optional_expr_valid_translated (valid : OptionalExprValid params scope expr type uses) :
    OptionalExprValid params scope (expr.map translateExpr) type (uses.map translateParameter) :=
  optional_expr_valid_translated_core (no_subqueries_translated (sizeOf expr)) valid

theorem subscripts_valid_translated (valid : SubscriptsValid params scope subscripts uses) :
    SubscriptsValid params scope (subscripts.map translateSubscript) (uses.map translateParameter) :=
  subscripts_valid_translated_core (no_subqueries_translated (sizeOf subscripts)) valid

theorem branches_valid_translated
    (valid : BranchesValid params scope branches conditions results uses) :
    BranchesValid params scope (branches.map fun branch => (translateExpr branch.1, translateExpr branch.2))
      conditions results (uses.map translateParameter) :=
  branches_valid_translated_core (no_subqueries_translated (sizeOf branches)) valid

end SQLean.RenderContract
