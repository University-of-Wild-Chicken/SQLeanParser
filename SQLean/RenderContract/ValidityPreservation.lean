import SQLean.RenderContract.Translation
import SQLean.SelectContract.Spec

/-! Parameter translation preserves the independent basic SELECT judgment.

The derivations below do not import the parser, renderer, executable checker,
or render certificate. They preserve the exact output labels, concrete types,
nullability, and index-keyed parameter environment for every valid basic SELECT.
This is a static preservation theorem, not an interpretation of database
execution or a claim that every advanced construct has basic-tier validity.
-/
namespace SQLean.RenderContract
open Advanced SelectContract

@[simp] theorem translateParameter_index (parameter : Parameter) :
    parameterIndex (translateParameter parameter) = parameterIndex parameter := by
  cases parameter <;> rfl

mutual
  /-- Each scalar typing derivation survives the explicit parameter translation,
  with parameter occurrences translated in their original order. -/
  theorem expr_valid_translated
      (valid : ExprValid params scope expr type uses) :
      ExprValid params scope (translateExpr expr) type (uses.map translateParameter) := by
    cases valid with
    | int range => simpa only [translateExpr, List.map_nil] using ExprValid.int range
    | text => simpa only [translateExpr, List.map_nil] using ExprValid.text
    | bool => simpa only [translateExpr, List.map_nil] using ExprValid.bool
    | null => simpa only [translateExpr, List.map_nil] using ExprValid.null
    | parameter present identity supported =>
        simpa only [translateExpr, List.map_cons, List.map_nil] using
          ExprValid.parameter present
            (identity.trans (translateParameter_index _).symm) supported
    | column resolved =>
        simpa only [translateExpr, List.map_nil] using ExprValid.column resolved
    | binary left right signature =>
        simpa only [translateExpr, List.map_append] using
          ExprValid.binary (expr_valid_translated left) (expr_valid_translated right) signature
    | unary arg signature =>
        simpa only [translateExpr] using ExprValid.unary (expr_valid_translated arg) signature
    | isNull arg =>
        simpa only [translateExpr] using ExprValid.isNull (expr_valid_translated arg)
    | pattern arg pattern signature =>
        simpa only [translateExpr, List.map_append] using
          ExprValid.pattern (expr_valid_translated arg) (expr_valid_translated pattern) signature
    | cast arg supported =>
        simpa only [translateExpr] using ExprValid.cast (expr_valid_translated arg) supported
    | inList arg values nonempty signature =>
        simpa only [translateExpr, List.attach_map_val, List.map_append] using
          ExprValid.inList (expr_valid_translated arg) (expr_list_valid_translated values)
            (by simpa using nonempty) signature
    | between arg lower upper signature =>
        simpa only [translateExpr, List.map_append] using
          ExprValid.between (expr_valid_translated arg) (expr_valid_translated lower)
            (expr_valid_translated upper) signature
  termination_by sizeOf expr
  decreasing_by all_goals (simp_all <;> omega)

  theorem expr_list_valid_translated
      (valid : ExprListValid params scope exprs types uses) :
      ExprListValid params scope (exprs.map translateExpr) types
        (uses.map translateParameter) := by
    cases valid with
    | nil => exact ExprListValid.nil
    | cons head tail =>
        simpa only [List.map_cons, List.map_append] using
          ExprListValid.cons (expr_valid_translated head) (expr_list_valid_translated tail)
  termination_by sizeOf exprs
  decreasing_by all_goals (simp_all <;> omega)
end

@[simp] theorem translated_output_name (expr : Advanced.Expr) (alias : Option Name) :
    outputName (translateExpr expr) alias = outputName expr alias := by
  cases expr <;> simp only [translateExpr, outputName]

theorem source_valid_translated (valid : SourceValid catalog source scope) :
    SourceValid catalog (source.map translateSource) scope := by
  cases valid with
  | empty => exact SourceValid.empty
  | table present sameName aliasValid columns =>
      simpa only [Option.map_some, translateSource] using
        SourceValid.table present sameName aliasValid columns

theorem items_valid_translated (valid : ItemsValid params scope items output uses) :
    ItemsValid params scope (items.map translateSelectItem) output
      (uses.map translateParameter) := by
  induction valid with
  | nil => exact ItemsValid.nil
  | expression typed aliasValid tail ih =>
      simpa only [List.map_cons, translateSelectItem, List.map_append, translated_output_name] using
        ItemsValid.expression (expr_valid_translated typed) aliasValid ih
  | all bindings nonempty tail ih =>
      simpa only [List.map_cons, translateSelectItem] using ItemsValid.all bindings nonempty ih

theorem predicate_valid_translated (valid : PredicateValid params scope predicate uses) :
    PredicateValid params scope (predicate.map translateExpr)
      (uses.map translateParameter) := by
  cases valid with
  | absent => exact PredicateValid.absent
  | present typed boolean =>
      exact PredicateValid.present (expr_valid_translated typed) boolean

@[simp] theorem translated_sort_expression (expr : Advanced.Expr) :
    SortExpression (translateExpr expr) ↔ SortExpression expr := by
  cases expr <;> simp only [translateExpr, SortExpression]

theorem sort_valid_translated (valid : SortValid params scope output distinct expr uses) :
    SortValid params scope output distinct (translateExpr expr)
      (uses.map translateParameter) := by
  cases valid with
  | ordinal positive inRange =>
      simpa only [translateExpr, List.map_nil] using SortValid.ordinal positive inRange
  | outputName resolved =>
      simpa only [translateExpr, List.map_nil] using SortValid.outputName resolved
  | inputName noOutput ordinary typed =>
      simpa only [translateExpr] using
        SortValid.inputName noOutput ordinary
          (by simpa only [translateExpr] using expr_valid_translated typed)
  | expression ordinary typed category =>
      exact SortValid.expression ordinary (expr_valid_translated typed)
        ((translated_sort_expression _).mpr category)

theorem orders_valid_translated (valid : OrdersValid params scope output distinct orders uses) :
    OrdersValid params scope output distinct (orders.map translateOrderBy)
      (uses.map translateParameter) := by
  induction valid with
  | nil => exact OrdersValid.nil
  | cons head tail ih =>
      simpa only [List.map_cons, List.map_append, translateOrderBy] using
        OrdersValid.cons (sort_valid_translated head) ih

theorem parameter_order_translated (ordered : ParameterOrder uses) :
    ParameterOrder (uses.map translateParameter) := by
  apply Or.inl
  intro parameter member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  rcases ordered with numbered | anonymous
  · have positive := numbered original present
    cases original with
    | numbered _ => exact positive
    | anonymous _ => exact False.elim positive
  · rw [anonymous] at present
    obtain ⟨index, inRange, rfl⟩ := List.mem_map.mp present
    simp only [translateParameter, NumberedPositive]
    omega

/-- Translating anonymous occurrences to numbered parameters preserves every
independent basic SELECT validity derivation, with exactly the same environment
and ordered output schema. No parser/renderer success is a hypothesis. -/
theorem translateParameters_valid
    (valid : SelectValid profile catalog params query output) :
    SelectValid profile catalog params (translateParameters query) output := by
  cases valid with
  | basic environment supported source items nonempty predicate orders parameterOrder noGrouping noHaving noDistinctOn =>
      rename_i select
      simp only [translateParameters, translateQueryBody, List.attach_map_val,
        List.map_nil]
      apply SelectValid.basic environment supported
      · have translated := source_valid_translated source
        simp only [translateSelect]
        cases relation : select.source <;> simpa [relation] using translated
      · simpa only [translateSelect, List.attach_map_val] using items_valid_translated items
      · exact nonempty
      · have translated := predicate_valid_translated predicate
        simp only [translateSelect]
        cases condition : select.whereClause <;> simpa [condition] using translated
      · simpa only [translateSelect] using orders_valid_translated orders
      · simpa only [List.map_append] using parameter_order_translated parameterOrder
      · simp only [translateSelect, List.attach_map_val, noGrouping, List.map_nil]
      · simp only [translateSelect]
        split <;> simp_all
      · simp only [translateSelect, List.attach_map_val, noDistinctOn, List.map_nil]

end SQLean.RenderContract
