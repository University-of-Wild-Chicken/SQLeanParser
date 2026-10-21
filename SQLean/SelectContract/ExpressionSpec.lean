import SQLean.SelectContract.Recursion
import SQLean.SelectContract.Collation

/-! Independent declarative rules for the first SELECT contract milestone.
There is deliberately no import of any SELECT checker or expression inference
procedure. The judgments below are inductive derivations over the original AST.
They use the fixed scalar signature tables in Profile, never checker success.

The current milestone covers source-free and base-table join queries. More advanced
syntax retains the older assurance tiers until its own independent rules land.
-/
namespace SQLean.SelectContract
open Advanced

/-- Well-formed metadata is distinct from support by the chosen scalar profile. -/
def DataTypeWellFormed (type : DataType) : Prop :=
  match type.name.scalarBase, type.modifiers with
  | .varchar, [] | .char, [] | .numeric, [] => True
  | .varchar, [n] | .char, [n] => 0 < n ∧ n ≤ 10485760
  | .numeric, [p] => 0 < p ∧ p ≤ 1000
  | .numeric, [p, s] => 0 < p ∧ p ≤ 1000 ∧ s ≤ 1000
  | .time, [] | .timeTZ, [] | .timestamp, [] | .timestampTZ, [] | .interval, [] => True
  | .time, [p] | .timeTZ, [p] | .timestamp, [p] | .timestampTZ, [p] | .interval, [p] => p ≤ 6
  | .intervalRange _, [] => True
  | .intervalRange fields, [p] => fields.allowsPrecision = true ∧ p ≤ 6
  | .intervalRange _, _ => False
  | .varchar, _ | .char, _ | .numeric, _
  | .time, _ | .timeTZ, _ | .timestamp, _ | .timestampTZ, _ | .interval, _ => False
  | _, modifiers => modifiers = []

instance (type : DataType) : Decidable (DataTypeWellFormed type) := by
  unfold DataTypeWellFormed
  split <;> infer_instance

def KeyWellFormed (names key : List Name) : Prop :=
  key ≠ [] ∧ key.Nodup ∧ ∀ name ∈ key, name ∈ names

instance (names key : List Name) : Decidable (KeyWellFormed names key) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def TableWellFormed (table : CatalogTable) : Prop :=
  table.name ≠ "" ∧ (∀ schema ∈ table.schema, schema ≠ "") ∧ table.columns ≠ [] ∧
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
  by unfold TableWellFormed; infer_instance

/-- Catalog keys and exposed unqualified names are independently unique.
A legacy unknown-schema entry cannot double-register a qualified object. -/
def CatalogWellFormed (catalog : Catalog) : Prop :=
  (catalog.map CatalogTable.identity).Nodup ∧
  ((catalog.filter (·.exposeUnqualified)).map CatalogTable.name).Nodup ∧
  (∀ table ∈ catalog, ∀ other ∈ catalog,
    table.name = other.name → table.schema.isSome = other.schema.isSome) ∧
  ∀ table ∈ catalog, TableWellFormed table

instance (catalog : Catalog) : Decidable (CatalogWellFormed catalog) := by
  unfold CatalogWellFormed
  infer_instance

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
  (∀ table ∈ catalog, table.schema ≠ some "pg_temp") ∧
  (∀ table ∈ catalog, ∀ col ∈ table.columns, concreteType col.type ≠ none) ∧
  (∀ param ∈ params, concreteType param.type ≠ none)

instance (catalog : Catalog) (params : ParameterEnv) : Decidable (SupportedEnvironment catalog params) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

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

inductive TableColumns (table : CatalogTable) : List Advanced.Column → List OutputColumn → Prop where
  | nil : TableColumns table [] []
  | cons (supported : concreteType col.type = some base)
      (tail : TableColumns table cols bindings) :
      TableColumns table (col :: cols)
        (⟨col.name, ⟨base, columnNullable table col⟩, tableColumnCollation table col base⟩ :: bindings)

/-- A unique relation namespace is selected before looking up its column. -/
def Resolves (scope : Scope) (qualifier : Option Name) (name : Name) (column : OutputColumn)
    (schema : Option Name := none) : Prop :=
  (scope.columns qualifier schema).filter (fun col => col.name == name) = [column]

instance (scope : Scope) (qualifier : Option Name) (name : Name) (column : OutputColumn)
    (schema : Option Name) : Decidable (Resolves scope qualifier name column schema) :=
  inferInstanceAs (Decidable (_ = _))

/-- Direct array-to-array casts must use target-directed element coercion.
Allowing the ordinary inferred-array route would invent transitive casts. -/
def OrdinaryCast : Advanced.Expr → DataType → Prop
  | .array _, target => target.name.isArray = false
  | _, _ => True

instance (expr : Advanced.Expr) (target : DataType) : Decidable (OrdinaryCast expr target) := by
  unfold OrdinaryCast
  split <;> infer_instance

/-- Cast context reaches raw nested constructors, not arbitrary expressions. -/
def OrdinaryArrayElement : Advanced.Expr → Prop
  | .array _ => False
  | _ => True

instance (expr : Advanced.Expr) : Decidable (OrdinaryArrayElement expr) := by
  unfold OrdinaryArrayElement
  split <;> infer_instance

/-- FOR-only SUBSTRING inserts an explicit INT32 cast. This conversion is
not an implicit positional-argument coercion and carries its own evidence. -/
inductive SubstringLengthValid : ScalarInput → ExactType → Prop where
  | unknown (nullable : Bool) :
      SubstringLengthValid (.unknown nullable) ⟨.int32, nullable⟩
  | known (allowed : explicitCastAllowed input.base .int32 = true)
      (result : castSignature (some input) .int32 = some target) :
      SubstringLengthValid (.known input) target

/-- Native call argument order is separate from lexical expression order.
Only FOR-only inserts arguments/conversion; FOR/FROM permutes typed inputs,
while the independent expression derivation retains original parameter uses. -/
inductive SubstringArguments : Advanced.SubstringForm → List ScalarInput → List ScalarInput → Prop where
  | from : SubstringArguments .from [subject, start] [subject, start]
  | fromFor : SubstringArguments .fromFor [subject, start, length] [subject, start, length]
  | forFrom : SubstringArguments .forFrom [subject, length, start] [subject, start, length]
  | similar : SubstringArguments .similar [subject, pattern, escape] [subject, pattern, escape]
  | forOnly (conversion : SubstringLengthValid length target) :
      SubstringArguments .forOnly [subject, length]
        [subject, .known ⟨.int32, false⟩, .known target]

/-- Lexical arguments select declared slots. The positional counter advances
only across the initial positional prefix; once a named argument occurs no
later positional constructor applies. Names are matched exactly. -/
inductive ArgumentAssignments (parameters : List Name) :
    Nat → Bool → List (Option Name) → List ScalarInput → List (Nat × ScalarInput) → Prop where
  | nil : ArgumentAssignments parameters next namedSeen [] [] []
  | positional (range : next < parameters.length)
      (tail : ArgumentAssignments parameters (next + 1) false names inputs assignments) :
      ArgumentAssignments parameters next false (none :: names) (input :: inputs)
        ((next, input) :: assignments)
  | named (identity : parameters[index]? = some name)
      (tail : ArgumentAssignments parameters next true names inputs assignments) :
      ArgumentAssignments parameters next namedSeen (some name :: names) (input :: inputs)
        ((index, input) :: assignments)

/-- A declared slot is either explicitly supplied or obtains its catalog
constant default. Only absent slots may use defaults. -/
inductive ArgumentSlot (assignments : List (Nat × ScalarInput)) (index : Nat)
    (parameter : FunctionParameter) : ScalarInput → Prop where
  | supplied (found : assignments.find? (fun entry => entry.1 == index) = some (index, input)) :
      ArgumentSlot assignments index parameter input
  | defaulted (absent : assignments.find? (fun entry => entry.1 == index) = none)
      (defaultValue : parameter.defaultValue = some value) :
      ArgumentSlot assignments index parameter value.input

inductive ArgumentSlots (assignments : List (Nat × ScalarInput)) :
    Nat → List FunctionParameter → List ScalarInput → Prop where
  | nil : ArgumentSlots assignments next [] []
  | cons (head : ArgumentSlot assignments next parameter input)
      (tail : ArgumentSlots assignments (next + 1) parameters inputs) :
      ArgumentSlots assignments next (parameter :: parameters) (input :: inputs)

/-- Unique slot assignment rules out duplicate names and a named argument
colliding with a positional prefix. Slot order never changes lexical uses. -/
inductive ArgumentsBound (parameters : List FunctionParameter)
    (names : List (Option Name)) (inputs : List ScalarInput) : List ScalarInput → Prop where
  | intro (assignment : ArgumentAssignments (parameters.map FunctionParameter.name)
        0 false names inputs assignments)
      (unique : (assignments.map Prod.fst).Nodup)
      (slots : ArgumentSlots assignments 0 parameters callInputs) :
      ArgumentsBound parameters names inputs callInputs

/-- The query relation is a strictly positive parameter. Its CTE environment
is an index, so nested expression queries inherit exactly the visible bindings. -/
abbrev SubqueryJudgment := CTEEnv → Advanced.Query → List OutputColumn → List Parameter → Prop

/-- Legacy expression-only entry points have no child-query capability. -/
def NoSubqueries : SubqueryJudgment := fun _ _ _ _ => False

set_option inductive.autoPromoteIndices false in
mutual
  inductive ExprValidCore (subqueries : SubqueryJudgment) (params : ParameterEnv) :
      CTEEnv → Scope → Advanced.Expr → ExprType → List Parameter → Prop where
    | int (range : n ≤ 2147483647) : ExprValidCore subqueries params env scope (.literal (.int n)) (some ⟨.int32, false⟩) []
    | bigInt (large : 2147483647 < n) (range : n ≤ 9223372036854775807) :
        ExprValidCore subqueries params env scope (.literal (.int n)) (some ⟨.int64, false⟩) []
    | numericInt (large : 9223372036854775807 < n) :
        ExprValidCore subqueries params env scope (.literal (.int n)) (some ⟨.numeric [], false⟩) []
    | decimal (lexical : decimalLexeme lexeme = true) :
        ExprValidCore subqueries params env scope (.decimal lexeme) (some ⟨.numeric [], false⟩) []
    | minInt32 : ExprValidCore subqueries params env scope (.unary .neg (.literal (.int 2147483648)))
        (some ⟨.int32, false⟩) []
    | minInt64 : ExprValidCore subqueries params env scope (.unary .neg (.literal (.int 9223372036854775808)))
        (some ⟨.int64, false⟩) []
    | foldedInteger (folded : rawIntegerValue expr = some value) :
        ExprValidCore subqueries params env scope expr (some ⟨foldedIntegerType value, false⟩) []
    | text : ExprValidCore subqueries params env scope (.literal (.text value)) (some ⟨.text, false⟩) []
    | bool : ExprValidCore subqueries params env scope (.literal (.bool value)) (some ⟨.bool, false⟩) []
    | null : ExprValidCore subqueries params env scope .null none []
    | contextValue : ExprValidCore subqueries params env scope (.contextValue value) (some (contextValueType value)) []
    | parameter (present : binding ∈ params) (identity : binding.index = parameterIndex parameter)
        (supported : concreteType binding.type = some base) :
        ExprValidCore subqueries params env scope (.parameter parameter) (some ⟨base.unmodified, binding.nullable⟩) [parameter]
    | column (resolved : Resolves scope qualifier name column schema) :
        ExprValidCore subqueries params env scope (.column qualifier name schema) (some column.type) []
    | binary (left : ExprValidCore subqueries params env scope a ta ua) (right : ExprValidCore subqueries params env scope b tb ub)
        (signature : binarySignature op ta tb = some result) :
        ExprValidCore subqueries params env scope (.binary op a b) result (ua ++ ub)
    | concat (left : ExprValidCore subqueries params env scope a ta ua) (right : ExprValidCore subqueries params env scope b tb ub)
        (signature : concatSignature (scalarInput a ta) (scalarInput b tb) = some selected) :
        ExprValidCore subqueries params env scope (.concat a b)
          (some ⟨selected.output, (scalarInput a ta).nullable || (scalarInput b tb).nullable⟩)
          (ua ++ ub)
    | arrayConcat (left : ExprValidCore subqueries params env scope a ta ua) (right : ExprValidCore subqueries params env scope b tb ub)
        (signature : arrayConcatSignature (scalarInput a ta) (scalarInput b tb) = some selected) :
        ExprValidCore subqueries params env scope (.concat a b)
          (some ⟨selected.output,
            selected.operator.nullable (scalarInput a ta).nullable (scalarInput b tb).nullable⟩)
          (ua ++ ub)
    | rowComparison (left : ExprListValidCore subqueries params env scope a ta ua)
        (right : ExprListValidCore subqueries params env scope b tb ub)
        (signature : rowComparisonSignature op (scalarInputs a ta) (scalarInputs b tb) = some selected) :
        ExprValidCore subqueries params env scope (.binary op.toBinOp (.row a) (.row b))
          (some ⟨.bool, true⟩) (ua ++ ub)
    | distinctScalar (left : ExprValidCore subqueries params env scope a ta ua)
        (right : ExprValidCore subqueries params env scope b tb ub)
        (ordinaryLeft : OrdinaryDistinctOperand a) (ordinaryRight : OrdinaryDistinctOperand b)
        (signature : distinctSignature (scalarInput a ta) (scalarInput b tb) = some selected) :
        ExprValidCore subqueries params env scope (.distinctFrom a b negated) (some ⟨.bool, false⟩) (ua ++ ub)
    | distinctNullLeft (arg : ExprValidCore subqueries params env scope a ta uses) :
        ExprValidCore subqueries params env scope (.distinctFrom .null a negated) (some ⟨.bool, false⟩) uses
    | distinctNullRight (arg : ExprValidCore subqueries params env scope a ta uses) :
        ExprValidCore subqueries params env scope (.distinctFrom a .null negated) (some ⟨.bool, false⟩) uses
    | distinctRows (left : ExprListValidCore subqueries params env scope a ta ua)
        (right : ExprListValidCore subqueries params env scope b tb ub)
        (signature : rowDistinctSignature (scalarInputs a ta) (scalarInputs b tb) = some selected) :
        ExprValidCore subqueries params env scope (.distinctFrom (.row a) (.row b) negated)
          (some ⟨.bool, false⟩) (ua ++ ub)
    /-- The native raw-NULL rewrite tests the whole constructed row, not its fields. -/
    | distinctRowNullLeft (args : ExprListValidCore subqueries params env scope es ts uses) :
        ExprValidCore subqueries params env scope (.distinctFrom .null (.row es) negated) (some ⟨.bool, false⟩) uses
    | distinctRowNullRight (args : ExprListValidCore subqueries params env scope es ts uses) :
        ExprValidCore subqueries params env scope (.distinctFrom (.row es) .null negated) (some ⟨.bool, false⟩) uses
    | unary (arg : ExprValidCore subqueries params env scope a ta uses) (signature : unarySignature op ta = some result)
        (ordinary : OrdinaryUnary op a) :
        ExprValidCore subqueries params env scope (.unary op a) result uses
    | isNull (arg : ExprValidCore subqueries params env scope a ta uses) :
        ExprValidCore subqueries params env scope (.isNull a negated) (some ⟨.bool, false⟩) uses
    /-- Field-sensitive row null tests. The negated form is native IS NOT NULL,
    not Boolean negation of IS NULL when fields mix NULL and non-NULL values. -/
    | isNullRow (args : ExprListValidCore subqueries params env scope es ts uses) :
        ExprValidCore subqueries params env scope (.isNull (.row es) negated) (some ⟨.bool, false⟩) uses
    | pattern (arg : ExprValidCore subqueries params env scope a ta ua) (pattern : ExprValidCore subqueries params env scope b tb ub)
        (signature : patternSignature ta tb = some result) :
        ExprValidCore subqueries params env scope (.pattern a b false) result (ua ++ ub)
    | ilike (arg : ExprValidCore subqueries params env scope a ta ua) (pattern : ExprValidCore subqueries params env scope b tb ub)
        (signature : stringMatchSignature (scalarInput a ta) (scalarInput b tb) = some selected) :
        ExprValidCore subqueries params env scope (.pattern a b true)
          (some ⟨.bool, (scalarInput a ta).nullable || (scalarInput b tb).nullable⟩) (ua ++ ub)
    | regex (arg : ExprValidCore subqueries params env scope a ta ua) (pattern : ExprValidCore subqueries params env scope b tb ub)
        (signature : stringMatchSignature (scalarInput a ta) (scalarInput b tb) = some selected) :
        ExprValidCore subqueries params env scope (.regex a b insensitive negated)
          (some ⟨.bool, (scalarInput a ta).nullable || (scalarInput b tb).nullable⟩) (ua ++ ub)
    | extract (arg : ExprValidCore subqueries params env scope a ta uses)
        (signature : extractSignature (scalarInput a ta) = some selected) :
        ExprValidCore subqueries params env scope (.extract field a)
          (some ⟨selected.output, extractNullable (scalarInput a ta)⟩) uses
    | jsonAccess (arg : ExprValidCore subqueries params env scope a ta ua) (key : ExprValidCore subqueries params env scope b tb ub)
        (signature : jsonAccessSignature op (scalarInput a ta) (scalarInput b tb) = some selected) :
        ExprValidCore subqueries params env scope (.jsonAccess op a b) (some ⟨selected.output, true⟩) (ua ++ ub)
    | jsonExistence (arg : ExprValidCore subqueries params env scope a ta ua) (keys : ExprValidCore subqueries params env scope b tb ub)
        (signature : jsonExistenceSignature op (scalarInput a ta) (scalarInput b tb) = some selected) :
        ExprValidCore subqueries params env scope (.jsonExistence op a b)
          (some ⟨selected.output, (scalarInput a ta).nullable || (scalarInput b tb).nullable⟩) (ua ++ ub)
    | containment (left : ExprValidCore subqueries params env scope a ta ua) (right : ExprValidCore subqueries params env scope b tb ub)
        (signature : jsonContainmentSignature (scalarInput a ta) (scalarInput b tb) = some selected) :
        ExprValidCore subqueries params env scope (.containment a b containedBy)
          (some ⟨.bool, (scalarInput a ta).nullable || (scalarInput b tb).nullable⟩) (ua ++ ub)
    | arrayContainment (left : ExprValidCore subqueries params env scope a ta ua) (right : ExprValidCore subqueries params env scope b tb ub)
        (signature : arrayPredicateSignature (scalarInput a ta) (scalarInput b tb) = some selected) :
        ExprValidCore subqueries params env scope (.containment a b containedBy)
          (some ⟨.bool, (scalarInput a ta).nullable || (scalarInput b tb).nullable⟩) (ua ++ ub)
    | overlap (left : ExprValidCore subqueries params env scope a ta ua) (right : ExprValidCore subqueries params env scope b tb ub)
        (signature : arrayPredicateSignature (scalarInput a ta) (scalarInput b tb) = some selected) :
        ExprValidCore subqueries params env scope (.overlap a b)
          (some ⟨.bool, (scalarInput a ta).nullable || (scalarInput b tb).nullable⟩) (ua ++ ub)
    | cast (arg : ExprValidCore subqueries params env scope a ta uses) (supported : concreteType target = some base)
        (declaration : DataTypeWellFormed target) (allowed : castAllowed ta base = true)
        (ordinary : OrdinaryCast a target) :
        ExprValidCore subqueries params env scope (.cast a target) (castSignature ta base) uses
    /-- Name lookup and collatability are certified by the paired independent
    collation judgment. This judgment records only the preserved scalar type. -/
    | collate (arg : ExprValidCore subqueries params env scope a ta uses) :
        ExprValidCore subqueries params env scope (.collate a name) ta uses
    | array (args : ExprListValidCore subqueries params env scope es ts uses)
        (signature : arraySignature (scalarInputs es ts) = some result) :
        ExprValidCore subqueries params env scope (.array es) (some result) uses
    | castArray (args : ArrayValidCore subqueries params env scope base es uses)
        (supported : concreteType target = some base) (declaration : DataTypeWellFormed target) :
        ExprValidCore subqueries params env scope (.cast (.array es) target) (some ⟨base, false⟩) uses
    | substring (args : ExprListValidCore subqueries params env scope es ts uses)
        (arguments : SubstringArguments form (scalarInputs es ts) callInputs)
        (signature : resolveOverload substringCatalog callInputs = some selected) :
        ExprValidCore subqueries params env scope (.substring form es)
          (some ⟨selected.output, substringNullable selected callInputs⟩) uses
    | defaultCall (args : ExprListValidCore subqueries params env scope es ts uses)
        (callee : builtinName name = some "make_interval")
        (binding : ArgumentsBound makeIntervalParameters (es.map fun _ => none)
          (scalarInputs es ts) callInputs)
        (signature : makeIntervalSignature callInputs = some result) :
        ExprValidCore subqueries params env scope (.call name es) (some result) uses
    | namedCall (args : ExprListValidCore subqueries params env scope (arguments.map CallArgument.expression) ts uses)
        (callee : builtinName name = some "make_interval")
        (binding : ArgumentsBound makeIntervalParameters (arguments.map CallArgument.name?)
          (scalarInputs (arguments.map CallArgument.expression) ts) callInputs)
        (signature : makeIntervalSignature callInputs = some result) :
        ExprValidCore subqueries params env scope (.namedCall name arguments) (some result) uses
    | call (args : ExprListValidCore subqueries params env scope es ts uses)
        (signature : callSignature name (scalarInputs es ts) = some result) :
        ExprValidCore subqueries params env scope (.call name es) (some result) uses
    | coalesce (args : ExprListValidCore subqueries params env scope es ts uses)
        (signature : coalesceSignature (scalarInputs es ts) = some result) :
        ExprValidCore subqueries params env scope (.coalesce es) (some result) uses
    | greatest (args : ExprListValidCore subqueries params env scope es ts uses)
        (signature : extremumSignature (scalarInputs es ts) = some result) :
        ExprValidCore subqueries params env scope (.greatest es) (some result) uses
    | least (args : ExprListValidCore subqueries params env scope es ts uses)
        (signature : extremumSignature (scalarInputs es ts) = some result) :
        ExprValidCore subqueries params env scope (.least es) (some result) uses
    | nullIf (left : ExprValidCore subqueries params env scope a ta ua) (right : ExprValidCore subqueries params env scope b tb ub)
        (signature : nullIfSignature (scalarInput a ta) (scalarInput b tb) = some result) :
        ExprValidCore subqueries params env scope (.nullIf a b) (some result) (ua ++ ub)
    | caseExpr (operand : OptionalExprValidCore subqueries params env scope a ta ua)
        (branches : BranchesValidCore subqueries params env scope bs conditions results ub)
        (otherwise : OptionalExprValidCore subqueries params env scope e te ue)
        (signature : caseSignature (a.map fun expr => scalarInput expr ta)
          (scalarInputs (bs.map Prod.fst) conditions) (scalarInputs (bs.map Prod.snd) results)
          ((e.map fun expr => scalarInput expr te).getD (.unknown true)) = some result) :
        ExprValidCore subqueries params env scope (.caseExpr a bs e) (some result) (ua ++ ub ++ ue)
    | quantifiedComparison (left : ExprValidCore subqueries params env scope a ta ua)
        (right : ExprValidCore subqueries params env scope b tb ub)
        (signature : quantifiedComparisonSignature op (scalarInput a ta) (scalarInput b tb) = some selected) :
        ExprValidCore subqueries params env scope (.quantifiedComparison op quantifier a b)
          (some ⟨.bool, true⟩) (ua ++ ub)
    | subscript (base : ExprValidCore subqueries params env scope a (some ⟨.array element, nullable⟩) ua)
        (bounds : SubscriptsValidCore subqueries params env scope indices ui)
        (nonempty : indices ≠ []) (dimensions : indices.length ≤ 6) :
        ExprValidCore subqueries params env scope (.subscript a indices)
          (some ⟨if indices.any Advanced.Subscript.isSlice then .array element else element, true⟩)
          (ua ++ ui)
    | inList (arg : ExprValidCore subqueries params env scope a ta ua) (values : ExprListValidCore subqueries params env scope es ts us)
        (nonempty : es ≠ []) (signature : comparisonListSignature (ta :: ts) = some result) :
        ExprValidCore subqueries params env scope (.inList a es) result (ua ++ us)
    | exists (query : subqueries env child output uses) :
        ExprValidCore subqueries params env scope (.exists child) (some ⟨.bool, false⟩) uses
    | scalarQuery (query : subqueries env child [column] uses) :
        ExprValidCore subqueries params env scope (.scalarQuery child)
          (some ⟨column.type.base, true⟩) uses
    | inQuery (arg : ExprValidCore subqueries params env scope a ta ua)
        (query : subqueries env child [column] uq)
        (signature : equalityOverload (scalarInput a ta) (.known column.type) = some selected) :
        ExprValidCore subqueries params env scope (.inQuery a child)
          (some ⟨.bool, (scalarInput a ta).nullable || column.type.nullable⟩) (ua ++ uq)
    /-- A row SubLink compares already-transformed fields with the child's
    finalized output columns. Each field pair selects its own equality
    operator; no common type is chosen across different row positions. -/
    | inRowQuery (args : ExprListValidCore subqueries params env scope fields types ua)
        (query : subqueries env child output uq)
        (nonempty : fields ≠ []) (arity : fields.length = output.length)
        (signature : rowDistinctSignature (scalarInputs fields types)
          (output.map (fun column => ScalarInput.known column.type)) = some selected) :
        ExprValidCore subqueries params env scope (.inQuery (.row fields) child)
          (some ⟨.bool, true⟩) (ua ++ uq)
    | between (arg : ExprValidCore subqueries params env scope a ta ua) (lower : ExprValidCore subqueries params env scope b tb ub)
        (upper : ExprValidCore subqueries params env scope c tc uc)
        (signature : comparisonListSignature [ta, tb, tc] = some result) :
        ExprValidCore subqueries params env scope (.between a b c negated) result (ua ++ ub ++ uc)

  inductive ExprListValidCore (subqueries : SubqueryJudgment) (params : ParameterEnv) :
      CTEEnv → Scope → List Advanced.Expr → List ExprType → List Parameter → Prop where
    | nil : ExprListValidCore subqueries params env scope [] [] []
    | cons (head : ExprValidCore subqueries params env scope e t u) (tail : ExprListValidCore subqueries params env scope es ts us) :
        ExprListValidCore subqueries params env scope (e :: es) (t :: ts) (u ++ us)

  /-- Target-directed constructor elaboration. The target is the complete
  concrete array type, including its element modifiers. -/
  inductive ArrayValidCore (subqueries : SubqueryJudgment) (params : ParameterEnv) :
      CTEEnv → Scope →
      ScalarType → List Advanced.Expr → List Parameter → Prop where
    | targeted (args : ArrayElementsValidCore subqueries params env scope target es ts uses)
        (signature : arrayCastSignature target (scalarInputs es ts) = true) :
        ArrayValidCore subqueries params env scope target es uses

  inductive ArrayElementsValidCore (subqueries : SubqueryJudgment) (params : ParameterEnv) :
      CTEEnv → Scope →
      ScalarType → List Advanced.Expr → List ExprType → List Parameter → Prop where
    | nil : ArrayElementsValidCore subqueries params env scope target [] [] []
    | ordinary (category : OrdinaryArrayElement expr)
        (head : ExprValidCore subqueries params env scope expr type headUses)
        (tail : ArrayElementsValidCore subqueries params env scope target exprs types tailUses) :
        ArrayElementsValidCore subqueries params env scope target (expr :: exprs) (type :: types) (headUses ++ tailUses)
    | nested (head : ArrayValidCore subqueries params env scope target exprs headUses)
        (tail : ArrayElementsValidCore subqueries params env scope target rest types tailUses) :
        ArrayElementsValidCore subqueries params env scope target (.array exprs :: rest)
          (some ⟨target, false⟩ :: types) (headUses ++ tailUses)

  inductive OptionalExprValidCore (subqueries : SubqueryJudgment) (params : ParameterEnv) :
      CTEEnv → Scope →
      Option Advanced.Expr → ExprType → List Parameter → Prop where
    | absent : OptionalExprValidCore subqueries params env scope none none []
    | present (typed : ExprValidCore subqueries params env scope expr type uses) :
        OptionalExprValidCore subqueries params env scope (some expr) type uses

  /-- Adjacent dimensions belong to one operation. Bounds retain lexical
  lower-before-upper order; omitted endpoints consume no parameters. -/
  inductive SubscriptsValidCore (subqueries : SubqueryJudgment) (params : ParameterEnv) :
      CTEEnv → Scope →
      List Advanced.Subscript → List Parameter → Prop where
    | nil : SubscriptsValidCore subqueries params env scope [] []
    | index (bound : ExprValidCore subqueries params env scope expr type uses)
        (signature : subscriptBoundSignature (scalarInput expr type) = true)
        (tail : SubscriptsValidCore subqueries params env scope rest remaining) :
        SubscriptsValidCore subqueries params env scope (.index expr :: rest) (uses ++ remaining)
    | slice (lower : OptionalExprValidCore subqueries params env scope lo tl ul)
        (upper : OptionalExprValidCore subqueries params env scope hi th uh)
        (lowerSignature : optionalSubscriptBoundSignature lo tl = true)
        (upperSignature : optionalSubscriptBoundSignature hi th = true)
        (tail : SubscriptsValidCore subqueries params env scope rest remaining) :
        SubscriptsValidCore subqueries params env scope (.slice lo hi :: rest) (ul ++ uh ++ remaining)

  /-- WHEN and THEN occurrences remain interleaved in source order. -/
  inductive BranchesValidCore (subqueries : SubqueryJudgment) (params : ParameterEnv) :
      CTEEnv → Scope →
      List (Advanced.Expr × Advanced.Expr) → List ExprType → List ExprType → List Parameter → Prop where
    | nil : BranchesValidCore subqueries params env scope [] [] [] []
    | cons (conditionTyped : ExprValidCore subqueries params env scope condition tc uc)
        (resultTyped : ExprValidCore subqueries params env scope result tr ur)
        (tail : BranchesValidCore subqueries params env scope branches conditions results uses) :
        BranchesValidCore subqueries params env scope ((condition, result) :: branches)
          (tc :: conditions) (tr :: results) (uc ++ ur ++ uses)
end

abbrev ExprValid (params : ParameterEnv) (scope : Scope) (expr : Advanced.Expr) (type : ExprType) (uses : List Parameter)
    (subqueries : SubqueryJudgment := NoSubqueries) (env : CTEEnv := []) : Prop :=
  ExprValidCore subqueries params env scope expr type uses

namespace ExprValid
export ExprValidCore (int bigInt numericInt decimal minInt32 minInt64 foldedInteger text bool null contextValue parameter column binary concat arrayConcat rowComparison distinctScalar distinctNullLeft distinctNullRight distinctRows distinctRowNullLeft distinctRowNullRight unary isNull isNullRow pattern ilike regex extract jsonAccess jsonExistence containment arrayContainment overlap cast collate array castArray substring defaultCall namedCall call coalesce greatest least nullIf caseExpr quantifiedComparison subscript inList «exists» scalarQuery inQuery inRowQuery between)
end ExprValid

abbrev ExprListValid (params : ParameterEnv) (scope : Scope) (exprs : List Advanced.Expr) (types : List ExprType) (uses : List Parameter)
    (subqueries : SubqueryJudgment := NoSubqueries) (env : CTEEnv := []) : Prop :=
  ExprListValidCore subqueries params env scope exprs types uses

namespace ExprListValid
export ExprListValidCore (nil cons)
end ExprListValid

abbrev ArrayValid (params : ParameterEnv) (scope : Scope) (target : ScalarType) (exprs : List Advanced.Expr) (uses : List Parameter)
    (subqueries : SubqueryJudgment := NoSubqueries) (env : CTEEnv := []) : Prop :=
  ArrayValidCore subqueries params env scope target exprs uses

namespace ArrayValid
export ArrayValidCore (targeted)
end ArrayValid

abbrev ArrayElementsValid (params : ParameterEnv) (scope : Scope) (target : ScalarType) (exprs : List Advanced.Expr) (types : List ExprType) (uses : List Parameter)
    (subqueries : SubqueryJudgment := NoSubqueries) (env : CTEEnv := []) : Prop :=
  ArrayElementsValidCore subqueries params env scope target exprs types uses

namespace ArrayElementsValid
export ArrayElementsValidCore (nil ordinary nested)
end ArrayElementsValid

abbrev OptionalExprValid (params : ParameterEnv) (scope : Scope) (expr : Option Advanced.Expr) (type : ExprType) (uses : List Parameter)
    (subqueries : SubqueryJudgment := NoSubqueries) (env : CTEEnv := []) : Prop :=
  OptionalExprValidCore subqueries params env scope expr type uses

namespace OptionalExprValid
export OptionalExprValidCore (absent present)
end OptionalExprValid

abbrev SubscriptsValid (params : ParameterEnv) (scope : Scope) (indices : List Advanced.Subscript) (uses : List Parameter)
    (subqueries : SubqueryJudgment := NoSubqueries) (env : CTEEnv := []) : Prop :=
  SubscriptsValidCore subqueries params env scope indices uses

namespace SubscriptsValid
export SubscriptsValidCore (nil index slice)
end SubscriptsValid

abbrev BranchesValid (params : ParameterEnv) (scope : Scope) (branches : List (Advanced.Expr × Advanced.Expr)) (conditions results : List ExprType) (uses : List Parameter)
    (subqueries : SubqueryJudgment := NoSubqueries) (env : CTEEnv := []) : Prop :=
  BranchesValidCore subqueries params env scope branches conditions results uses

namespace BranchesValid
export BranchesValidCore (nil cons)
end BranchesValid



end SQLean.SelectContract
