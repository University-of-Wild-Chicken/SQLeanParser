import SQLean.SelectContract.Profile

/-! Independent declarative rules for the first SELECT contract milestone.
There is deliberately no import of any SELECT checker or expression inference
procedure. The judgments below are inductive derivations over the original AST.
They use the fixed scalar signature tables in Profile, never checker success.

The first milestone covers source-free and single-table queries. More advanced
syntax retains the older assurance tiers until its own independent rules land.
-/
namespace SQLean.SelectContract
open Advanced

/-- Well-formed metadata is distinct from support by the chosen scalar profile. -/
def DataTypeWellFormed (type : DataType) : Prop :=
  match type.name, type.modifiers with
  | .varchar, [] | .numeric, [] => True
  | .varchar, [n] => 0 < n ∧ n ≤ 10485760
  | .numeric, [p] => 0 < p ∧ p ≤ 1000
  | .numeric, [p, s] => 0 < p ∧ p ≤ 1000 ∧ s ≤ 1000
  | .varchar, _ | .numeric, _ => False
  | _, modifiers => modifiers = []

instance (type : DataType) : Decidable (DataTypeWellFormed type) := by
  unfold DataTypeWellFormed
  split <;> infer_instance

def KeyWellFormed (names key : List Name) : Prop :=
  key ≠ [] ∧ key.Nodup ∧ ∀ name ∈ key, name ∈ names

instance (names key : List Name) : Decidable (KeyWellFormed names key) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def TableWellFormed (table : CatalogTable) : Prop :=
  table.name ≠ "" ∧ table.columns ≠ [] ∧
  (table.columns.map Advanced.Column.name).Nodup ∧
  (∀ column ∈ table.columns, column.name ≠ "" ∧ DataTypeWellFormed column.type) ∧
  (∀ key ∈ table.uniqueKeys, KeyWellFormed (table.columns.map Advanced.Column.name) key) ∧
  (table.primaryKey = [] ∨ KeyWellFormed (table.columns.map Advanced.Column.name) table.primaryKey) ∧
  (table.namedKeys.map Prod.fst).Nodup ∧
  (∀ key ∈ table.namedKeys, key.1 ≠ "" ∧ KeyWellFormed (table.columns.map Advanced.Column.name) key.2) ∧
  ((table.columns.filter (·.primaryKey)).length ≤ 1) ∧
  ((table.columns.filter (·.primaryKey)).map Advanced.Column.name = [] ∨ table.primaryKey = [] ∨
    (table.columns.filter (·.primaryKey)).map Advanced.Column.name = table.primaryKey)

instance (table : CatalogTable) : Decidable (TableWellFormed table) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def CatalogWellFormed (catalog : Catalog) : Prop :=
  (catalog.map CatalogTable.name).Nodup ∧ ∀ table ∈ catalog, TableWellFormed table

instance (catalog : Catalog) : Decidable (CatalogWellFormed catalog) :=
  inferInstanceAs (Decidable (_ ∧ _))

def ParametersWellFormed (params : ParameterEnv) : Prop :=
  (params.map ParameterBinding.index).Nodup ∧
  ∀ param ∈ params, 0 < param.index ∧ DataTypeWellFormed param.type

instance (params : ParameterEnv) : Decidable (ParametersWellFormed params) :=
  inferInstanceAs (Decidable (_ ∧ _))

def WellFormedEnvironment (catalog : Catalog) (params : ParameterEnv) : Prop :=
  CatalogWellFormed catalog ∧ ParametersWellFormed params

instance (catalog : Catalog) (params : ParameterEnv) : Decidable (WellFormedEnvironment catalog params) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- ALL supplied concrete types must belong to the fixed profile. Unsupported
metadata is not silently coerced through Advanced.DataType.sqlType. -/
def SupportedEnvironment (catalog : Catalog) (params : ParameterEnv) : Prop :=
  (∀ table ∈ catalog, ∀ col ∈ table.columns, concreteType col.type ≠ none) ∧
  (∀ param ∈ params, concreteType param.type ≠ none)

instance (catalog : Catalog) (params : ParameterEnv) : Decidable (SupportedEnvironment catalog params) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Parameter notation is a query-wide property. Numbered references can repeat;
anonymous references must be exactly 1,2,... in AST source order. -/
def NumberedPositive : Parameter → Prop
  | .numbered n => 0 < n
  | .anonymous _ => False

instance (parameter : Parameter) : Decidable (NumberedPositive parameter) := by
  cases parameter <;> unfold NumberedPositive <;> infer_instance

def ParameterOrder (uses : List Parameter) : Prop :=
  (∀ use ∈ uses, NumberedPositive use) ∨
  uses = (List.range uses.length).map (fun n => Parameter.anonymous (n + 1))

instance (uses : List Parameter) : Decidable (ParameterOrder uses) :=
  inferInstanceAs (Decidable (_ ∨ _))

def parameterIndex : Parameter → Nat
  | .numbered n | .anonymous n => n

/-- Nullability comes from explicit declarations and explicit primary-key
metadata. Predicate-based refinements are absent. -/
def columnNullable (table : CatalogTable) (col : Advanced.Column) : Bool :=
  !(col.primaryKey || table.primaryKey.contains col.name || col.nullable == some false)

inductive TableColumns (table : CatalogTable) (qualifier : Name) : List Advanced.Column → Scope → Prop where
  | nil : TableColumns table qualifier [] []
  | cons (supported : concreteType col.type = some base)
      (tail : TableColumns table qualifier cols bindings) :
      TableColumns table qualifier (col :: cols)
        (⟨qualifier, ⟨col.name, ⟨base, columnNullable table col⟩⟩⟩ :: bindings)

inductive SourceValid (catalog : Catalog) : Option Advanced.From → Scope → Prop where
  | empty : SourceValid catalog none []
  | table (present : table ∈ catalog) (sameName : table.name = name)
      (aliasValid : ∀ aliasName ∈ alias, aliasName ≠ "")
      (columns : TableColumns table (alias.getD name) table.columns scope) :
      SourceValid catalog (some (.table name alias [])) scope

/-- Exact unique binding, with alias replacement represented by the scope. -/
def Resolves (scope : Scope) (qualifier : Option Name) (name : Name) (binding : Binding) : Prop :=
  scope.filter (fun b => b.column.name == name &&
    match qualifier with | none => true | some q => b.qualifier == q) = [binding]

instance (scope : Scope) (qualifier : Option Name) (name : Name) (binding : Binding) :
    Decidable (Resolves scope qualifier name binding) := inferInstanceAs (Decidable (_ = _))

mutual
  inductive ExprValid (params : ParameterEnv) (scope : Scope) : Advanced.Expr → ExprType → List Parameter → Prop where
    | int (range : n ≤ 2147483647) : ExprValid params scope (.literal (.int n)) (some ⟨.int32, false⟩) []
    | text : ExprValid params scope (.literal (.text value)) (some ⟨.text, false⟩) []
    | bool : ExprValid params scope (.literal (.bool value)) (some ⟨.bool, false⟩) []
    | null : ExprValid params scope .null none []
    | parameter (present : binding ∈ params) (identity : binding.index = parameterIndex parameter)
        (supported : concreteType binding.type = some base) :
        ExprValid params scope (.parameter parameter) (some ⟨base, binding.nullable⟩) [parameter]
    | column (resolved : Resolves scope qualifier name binding) :
        ExprValid params scope (.column qualifier name) (some binding.column.type) []
    | binary (left : ExprValid params scope a ta ua) (right : ExprValid params scope b tb ub)
        (signature : binarySignature op ta tb = some result) :
        ExprValid params scope (.binary op a b) result (ua ++ ub)
    | unary (arg : ExprValid params scope a ta uses) (signature : unarySignature op ta = some result) :
        ExprValid params scope (.unary op a) result uses
    | isNull (arg : ExprValid params scope a ta uses) :
        ExprValid params scope (.isNull a negated) (some ⟨.bool, false⟩) uses
    | pattern (arg : ExprValid params scope a ta ua) (pattern : ExprValid params scope b tb ub)
        (signature : patternSignature ta tb = some result) :
        ExprValid params scope (.pattern a b false) result (ua ++ ub)
    | cast (arg : ExprValid params scope a ta uses) (supported : concreteType target = some base) :
        ExprValid params scope (.cast a target) (castSignature ta base) uses
    | inList (arg : ExprValid params scope a ta ua) (values : ExprListValid params scope es ts us)
        (nonempty : es ≠ []) (signature : comparisonListSignature (ta :: ts) = some result) :
        ExprValid params scope (.inList a es) result (ua ++ us)
    | between (arg : ExprValid params scope a ta ua) (lower : ExprValid params scope b tb ub)
        (upper : ExprValid params scope c tc uc)
        (signature : comparisonListSignature [ta, tb, tc] = some result) :
        ExprValid params scope (.between a b c negated) result (ua ++ ub ++ uc)

  inductive ExprListValid (params : ParameterEnv) (scope : Scope) : List Advanced.Expr → List ExprType → List Parameter → Prop where
    | nil : ExprListValid params scope [] [] []
    | cons (head : ExprValid params scope e t u) (tail : ExprListValid params scope es ts us) :
        ExprListValid params scope (e :: es) (t :: ts) (u ++ us)
end

/-- A label is independent of expression typing. Computed unnamed top-level
outputs use ?column?; duplicate labels are retained, never deduplicated. -/
def outputName (expr : Advanced.Expr) (alias : Option Name) : Name :=
  alias.getD (match expr with | .column _ name => name | _ => "?column?")

inductive ItemsValid (params : ParameterEnv) (scope : Scope) :
    List Advanced.SelectItem → List OutputColumn → List Parameter → Prop where
  | nil : ItemsValid params scope [] [] []
  | expression (typed : ExprValid params scope expr type uses)
      (aliasValid : ∀ name ∈ alias, name ≠ "")
      (tail : ItemsValid params scope items output remaining) :
      ItemsValid params scope (.expression expr alias :: items)
        (⟨outputName expr alias, projectedType type⟩ :: output) (uses ++ remaining)
  | all (bindings : scope.filter (fun b => match qualifier with | none => true | some q => b.qualifier == q) = selected)
      (nonempty : selected ≠ [])
      (tail : ItemsValid params scope items output uses) :
      ItemsValid params scope (.all qualifier :: items) (selected.map Binding.column ++ output) uses

inductive PredicateValid (params : ParameterEnv) (scope : Scope) : Option Advanced.Expr → List Parameter → Prop where
  | absent : PredicateValid params scope none []
  | present (typed : ExprValid params scope expr type uses) (boolean : acceptsBase .bool type = true) :
      PredicateValid params scope (some expr) uses

/-- Sort syntax categories are part of the name-resolution rule, not an
executable typing predicate. -/
def SortExpression : Advanced.Expr → Prop
  | .literal (.int _) | .column none _ => False
  | _ => True

instance (expr : Advanced.Expr) : Decidable (SortExpression expr) := by
  unfold SortExpression
  split <;> infer_instance

/-- Output-name lookup takes precedence only for a bare name. Duplicate output
names are an error. Compound expressions see input bindings, not aliases. -/
inductive SortValid (params : ParameterEnv) (scope : Scope) (output : List OutputColumn) (distinct : Bool) :
    Advanced.Expr → List Parameter → Prop where
  | ordinal (positive : 0 < n) (inRange : n ≤ output.length) :
      SortValid params scope output distinct (.literal (.int n)) []
  | outputName (resolved : output.filter (·.name == name) = [column]) :
      SortValid params scope output distinct (.column none name) []
  | inputName (noOutput : output.filter (·.name == name) = []) (ordinary : distinct = false)
      (typed : ExprValid params scope (.column none name) type uses) :
      SortValid params scope output distinct (.column none name) uses
  | expression (ordinary : distinct = false) (typed : ExprValid params scope expr type uses)
      (category : SortExpression expr) :
      SortValid params scope output distinct expr uses

inductive OrdersValid (params : ParameterEnv) (scope : Scope) (output : List OutputColumn) (distinct : Bool) :
    List Advanced.OrderBy → List Parameter → Prop where
  | nil : OrdersValid params scope output distinct [] []
  | cons (head : SortValid params scope output distinct item.expr uses)
      (tail : OrdersValid params scope output distinct items remaining) :
      OrdersValid params scope output distinct (item :: items) (uses ++ remaining)

/-- First milestone SELECT rule. Pagination is intrinsically nonnegative in the
AST. All supported scalar types admit equality and ordering. Larger clauses
have no constructors and therefore cannot acquire this certificate by fallback. -/
inductive SelectValid (profile : Profile) (catalog : Catalog) (params : ParameterEnv) :
    Advanced.Query → List OutputColumn → Prop where
  | basic {select : Advanced.Select} (environment : WellFormedEnvironment catalog params)
      (supported : SupportedEnvironment catalog params)
      (source : SourceValid catalog select.source scope)
      (items : ItemsValid params scope select.items output selectUses)
      (nonempty : output ≠ [])
      (predicate : PredicateValid params scope select.whereClause whereUses)
      (orders : OrdersValid params scope output select.distinct orderBy orderUses)
      (parameterOrder : ParameterOrder (selectUses ++ whereUses ++ orderUses))
      (noGrouping : select.groupBy = []) (noHaving : select.having = none)
      (noDistinctOn : select.distinctOn = []) :
      SelectValid profile catalog params
        ⟨.select select, [], false, orderBy, limit, offset⟩ output

structure Certificate (profile : Profile) (catalog : Catalog) (params : ParameterEnv) (query : Advanced.Query) where
  output : List OutputColumn
  valid : SelectValid profile catalog params query output

def Certificate.outputCatalog (_certificate : Certificate profile catalog params query) : Catalog := catalog

@[simp] theorem Certificate.catalog_unchanged (certificate : Certificate profile catalog params query) :
    certificate.outputCatalog = catalog := rfl

end SQLean.SelectContract
