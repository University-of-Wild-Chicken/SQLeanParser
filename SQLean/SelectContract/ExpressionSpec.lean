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

mutual
  inductive ExprValid (params : ParameterEnv) (scope : Scope) : Advanced.Expr → ExprType → List Parameter → Prop where
    | int (range : n ≤ 2147483647) : ExprValid params scope (.literal (.int n)) (some ⟨.int32, false⟩) []
    | bigInt (large : 2147483647 < n) (range : n ≤ 9223372036854775807) :
        ExprValid params scope (.literal (.int n)) (some ⟨.int64, false⟩) []
    | numericInt (large : 9223372036854775807 < n) :
        ExprValid params scope (.literal (.int n)) (some ⟨.numeric [], false⟩) []
    | decimal (lexical : decimalLexeme lexeme = true) :
        ExprValid params scope (.decimal lexeme) (some ⟨.numeric [], false⟩) []
    | minInt32 : ExprValid params scope (.unary .neg (.literal (.int 2147483648)))
        (some ⟨.int32, false⟩) []
    | minInt64 : ExprValid params scope (.unary .neg (.literal (.int 9223372036854775808)))
        (some ⟨.int64, false⟩) []
    | text : ExprValid params scope (.literal (.text value)) (some ⟨.text, false⟩) []
    | bool : ExprValid params scope (.literal (.bool value)) (some ⟨.bool, false⟩) []
    | null : ExprValid params scope .null none []
    | contextValue : ExprValid params scope (.contextValue value) (some (contextValueType value)) []
    | parameter (present : binding ∈ params) (identity : binding.index = parameterIndex parameter)
        (supported : concreteType binding.type = some base) :
        ExprValid params scope (.parameter parameter) (some ⟨base.unmodified, binding.nullable⟩) [parameter]
    | column (resolved : Resolves scope qualifier name column schema) :
        ExprValid params scope (.column qualifier name schema) (some column.type) []
    | binary (left : ExprValid params scope a ta ua) (right : ExprValid params scope b tb ub)
        (signature : binarySignature op ta tb = some result) :
        ExprValid params scope (.binary op a b) result (ua ++ ub)
    | concat (left : ExprValid params scope a ta ua) (right : ExprValid params scope b tb ub)
        (signature : concatSignature (scalarInput a ta) (scalarInput b tb) = some selected) :
        ExprValid params scope (.concat a b)
          (some ⟨selected.output, (scalarInput a ta).nullable || (scalarInput b tb).nullable⟩)
          (ua ++ ub)
    | arrayConcat (left : ExprValid params scope a ta ua) (right : ExprValid params scope b tb ub)
        (signature : arrayConcatSignature (scalarInput a ta) (scalarInput b tb) = some selected) :
        ExprValid params scope (.concat a b)
          (some ⟨selected.output,
            selected.operator.nullable (scalarInput a ta).nullable (scalarInput b tb).nullable⟩)
          (ua ++ ub)
    | rowComparison (left : ExprListValid params scope a ta ua)
        (right : ExprListValid params scope b tb ub)
        (signature : rowComparisonSignature op (scalarInputs a ta) (scalarInputs b tb) = some selected) :
        ExprValid params scope (.binary op.toBinOp (.row a) (.row b))
          (some ⟨.bool, true⟩) (ua ++ ub)
    | distinctScalar (left : ExprValid params scope a ta ua)
        (right : ExprValid params scope b tb ub)
        (ordinaryLeft : OrdinaryDistinctOperand a) (ordinaryRight : OrdinaryDistinctOperand b)
        (signature : distinctSignature (scalarInput a ta) (scalarInput b tb) = some selected) :
        ExprValid params scope (.distinctFrom a b negated) (some ⟨.bool, false⟩) (ua ++ ub)
    | distinctNullLeft (arg : ExprValid params scope a ta uses) :
        ExprValid params scope (.distinctFrom .null a negated) (some ⟨.bool, false⟩) uses
    | distinctNullRight (arg : ExprValid params scope a ta uses) :
        ExprValid params scope (.distinctFrom a .null negated) (some ⟨.bool, false⟩) uses
    | distinctRows (left : ExprListValid params scope a ta ua)
        (right : ExprListValid params scope b tb ub)
        (signature : rowDistinctSignature (scalarInputs a ta) (scalarInputs b tb) = some selected) :
        ExprValid params scope (.distinctFrom (.row a) (.row b) negated)
          (some ⟨.bool, false⟩) (ua ++ ub)
    /-- The native raw-NULL rewrite tests the whole constructed row, not its fields. -/
    | distinctRowNullLeft (args : ExprListValid params scope es ts uses) :
        ExprValid params scope (.distinctFrom .null (.row es) negated) (some ⟨.bool, false⟩) uses
    | distinctRowNullRight (args : ExprListValid params scope es ts uses) :
        ExprValid params scope (.distinctFrom (.row es) .null negated) (some ⟨.bool, false⟩) uses
    | unary (arg : ExprValid params scope a ta uses) (signature : unarySignature op ta = some result)
        (ordinary : OrdinaryUnary op a) :
        ExprValid params scope (.unary op a) result uses
    | isNull (arg : ExprValid params scope a ta uses) :
        ExprValid params scope (.isNull a negated) (some ⟨.bool, false⟩) uses
    /-- Field-sensitive row null tests. The negated form is native IS NOT NULL,
    not Boolean negation of IS NULL when fields mix NULL and non-NULL values. -/
    | isNullRow (args : ExprListValid params scope es ts uses) :
        ExprValid params scope (.isNull (.row es) negated) (some ⟨.bool, false⟩) uses
    | pattern (arg : ExprValid params scope a ta ua) (pattern : ExprValid params scope b tb ub)
        (signature : patternSignature ta tb = some result) :
        ExprValid params scope (.pattern a b false) result (ua ++ ub)
    | ilike (arg : ExprValid params scope a ta ua) (pattern : ExprValid params scope b tb ub)
        (signature : stringMatchSignature (scalarInput a ta) (scalarInput b tb) = some selected) :
        ExprValid params scope (.pattern a b true)
          (some ⟨.bool, (scalarInput a ta).nullable || (scalarInput b tb).nullable⟩) (ua ++ ub)
    | regex (arg : ExprValid params scope a ta ua) (pattern : ExprValid params scope b tb ub)
        (signature : stringMatchSignature (scalarInput a ta) (scalarInput b tb) = some selected) :
        ExprValid params scope (.regex a b insensitive negated)
          (some ⟨.bool, (scalarInput a ta).nullable || (scalarInput b tb).nullable⟩) (ua ++ ub)
    | extract (arg : ExprValid params scope a ta uses)
        (signature : extractSignature (scalarInput a ta) = some selected) :
        ExprValid params scope (.extract field a)
          (some ⟨selected.output, extractNullable (scalarInput a ta)⟩) uses
    | jsonAccess (arg : ExprValid params scope a ta ua) (key : ExprValid params scope b tb ub)
        (signature : jsonAccessSignature op (scalarInput a ta) (scalarInput b tb) = some selected) :
        ExprValid params scope (.jsonAccess op a b) (some ⟨selected.output, true⟩) (ua ++ ub)
    | jsonExistence (arg : ExprValid params scope a ta ua) (keys : ExprValid params scope b tb ub)
        (signature : jsonExistenceSignature op (scalarInput a ta) (scalarInput b tb) = some selected) :
        ExprValid params scope (.jsonExistence op a b)
          (some ⟨selected.output, (scalarInput a ta).nullable || (scalarInput b tb).nullable⟩) (ua ++ ub)
    | containment (left : ExprValid params scope a ta ua) (right : ExprValid params scope b tb ub)
        (signature : jsonContainmentSignature (scalarInput a ta) (scalarInput b tb) = some selected) :
        ExprValid params scope (.containment a b containedBy)
          (some ⟨.bool, (scalarInput a ta).nullable || (scalarInput b tb).nullable⟩) (ua ++ ub)
    | arrayContainment (left : ExprValid params scope a ta ua) (right : ExprValid params scope b tb ub)
        (signature : arrayPredicateSignature (scalarInput a ta) (scalarInput b tb) = some selected) :
        ExprValid params scope (.containment a b containedBy)
          (some ⟨.bool, (scalarInput a ta).nullable || (scalarInput b tb).nullable⟩) (ua ++ ub)
    | overlap (left : ExprValid params scope a ta ua) (right : ExprValid params scope b tb ub)
        (signature : arrayPredicateSignature (scalarInput a ta) (scalarInput b tb) = some selected) :
        ExprValid params scope (.overlap a b)
          (some ⟨.bool, (scalarInput a ta).nullable || (scalarInput b tb).nullable⟩) (ua ++ ub)
    | cast (arg : ExprValid params scope a ta uses) (supported : concreteType target = some base)
        (declaration : DataTypeWellFormed target) (allowed : castAllowed ta base = true)
        (ordinary : OrdinaryCast a target) :
        ExprValid params scope (.cast a target) (castSignature ta base) uses
    /-- Name lookup and collatability are certified by the paired independent
    collation judgment. This judgment records only the preserved scalar type. -/
    | collate (arg : ExprValid params scope a ta uses) :
        ExprValid params scope (.collate a name) ta uses
    | array (args : ExprListValid params scope es ts uses)
        (signature : arraySignature (scalarInputs es ts) = some result) :
        ExprValid params scope (.array es) (some result) uses
    | castArray (args : ArrayValid params scope base es uses)
        (supported : concreteType target = some base) (declaration : DataTypeWellFormed target) :
        ExprValid params scope (.cast (.array es) target) (some ⟨base, false⟩) uses
    | substring (args : ExprListValid params scope es ts uses)
        (arguments : SubstringArguments form (scalarInputs es ts) callInputs)
        (signature : resolveOverload substringCatalog callInputs = some selected) :
        ExprValid params scope (.substring form es)
          (some ⟨selected.output, substringNullable selected callInputs⟩) uses
    | defaultCall (args : ExprListValid params scope es ts uses)
        (callee : builtinName name = some "make_interval")
        (binding : ArgumentsBound makeIntervalParameters (es.map fun _ => none)
          (scalarInputs es ts) callInputs)
        (signature : makeIntervalSignature callInputs = some result) :
        ExprValid params scope (.call name es) (some result) uses
    | namedCall (args : ExprListValid params scope (arguments.map CallArgument.expression) ts uses)
        (callee : builtinName name = some "make_interval")
        (binding : ArgumentsBound makeIntervalParameters (arguments.map CallArgument.name?)
          (scalarInputs (arguments.map CallArgument.expression) ts) callInputs)
        (signature : makeIntervalSignature callInputs = some result) :
        ExprValid params scope (.namedCall name arguments) (some result) uses
    | call (args : ExprListValid params scope es ts uses)
        (signature : callSignature name (scalarInputs es ts) = some result) :
        ExprValid params scope (.call name es) (some result) uses
    | coalesce (args : ExprListValid params scope es ts uses)
        (signature : coalesceSignature (scalarInputs es ts) = some result) :
        ExprValid params scope (.coalesce es) (some result) uses
    | greatest (args : ExprListValid params scope es ts uses)
        (signature : extremumSignature (scalarInputs es ts) = some result) :
        ExprValid params scope (.greatest es) (some result) uses
    | least (args : ExprListValid params scope es ts uses)
        (signature : extremumSignature (scalarInputs es ts) = some result) :
        ExprValid params scope (.least es) (some result) uses
    | nullIf (left : ExprValid params scope a ta ua) (right : ExprValid params scope b tb ub)
        (signature : nullIfSignature (scalarInput a ta) (scalarInput b tb) = some result) :
        ExprValid params scope (.nullIf a b) (some result) (ua ++ ub)
    | caseExpr (operand : OptionalExprValid params scope a ta ua)
        (branches : BranchesValid params scope bs conditions results ub)
        (otherwise : OptionalExprValid params scope e te ue)
        (signature : caseSignature (a.map fun expr => scalarInput expr ta)
          (scalarInputs (bs.map Prod.fst) conditions) (scalarInputs (bs.map Prod.snd) results)
          ((e.map fun expr => scalarInput expr te).getD (.unknown true)) = some result) :
        ExprValid params scope (.caseExpr a bs e) (some result) (ua ++ ub ++ ue)
    | quantifiedComparison (left : ExprValid params scope a ta ua)
        (right : ExprValid params scope b tb ub)
        (signature : quantifiedComparisonSignature op (scalarInput a ta) (scalarInput b tb) = some selected) :
        ExprValid params scope (.quantifiedComparison op quantifier a b)
          (some ⟨.bool, true⟩) (ua ++ ub)
    | subscript (base : ExprValid params scope a (some ⟨.array element, nullable⟩) ua)
        (bounds : SubscriptsValid params scope indices ui)
        (nonempty : indices ≠ []) (dimensions : indices.length ≤ 6) :
        ExprValid params scope (.subscript a indices)
          (some ⟨if indices.any Advanced.Subscript.isSlice then .array element else element, true⟩)
          (ua ++ ui)
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

  /-- Target-directed constructor elaboration. The target is the complete
  concrete array type, including its element modifiers. -/
  inductive ArrayValid (params : ParameterEnv) (scope : Scope) :
      ScalarType → List Advanced.Expr → List Parameter → Prop where
    | targeted (args : ArrayElementsValid params scope target es ts uses)
        (signature : arrayCastSignature target (scalarInputs es ts) = true) :
        ArrayValid params scope target es uses

  inductive ArrayElementsValid (params : ParameterEnv) (scope : Scope) :
      ScalarType → List Advanced.Expr → List ExprType → List Parameter → Prop where
    | nil : ArrayElementsValid params scope target [] [] []
    | ordinary (category : OrdinaryArrayElement expr)
        (head : ExprValid params scope expr type headUses)
        (tail : ArrayElementsValid params scope target exprs types tailUses) :
        ArrayElementsValid params scope target (expr :: exprs) (type :: types) (headUses ++ tailUses)
    | nested (head : ArrayValid params scope target exprs headUses)
        (tail : ArrayElementsValid params scope target rest types tailUses) :
        ArrayElementsValid params scope target (.array exprs :: rest)
          (some ⟨target, false⟩ :: types) (headUses ++ tailUses)

  inductive OptionalExprValid (params : ParameterEnv) (scope : Scope) :
      Option Advanced.Expr → ExprType → List Parameter → Prop where
    | absent : OptionalExprValid params scope none none []
    | present (typed : ExprValid params scope expr type uses) :
        OptionalExprValid params scope (some expr) type uses

  /-- Adjacent dimensions belong to one operation. Bounds retain lexical
  lower-before-upper order; omitted endpoints consume no parameters. -/
  inductive SubscriptsValid (params : ParameterEnv) (scope : Scope) :
      List Advanced.Subscript → List Parameter → Prop where
    | nil : SubscriptsValid params scope [] []
    | index (bound : ExprValid params scope expr type uses)
        (signature : subscriptBoundSignature (scalarInput expr type) = true)
        (tail : SubscriptsValid params scope rest remaining) :
        SubscriptsValid params scope (.index expr :: rest) (uses ++ remaining)
    | slice (lower : OptionalExprValid params scope lo tl ul)
        (upper : OptionalExprValid params scope hi th uh)
        (lowerSignature : optionalSubscriptBoundSignature lo tl = true)
        (upperSignature : optionalSubscriptBoundSignature hi th = true)
        (tail : SubscriptsValid params scope rest remaining) :
        SubscriptsValid params scope (.slice lo hi :: rest) (ul ++ uh ++ remaining)

  /-- WHEN and THEN occurrences remain interleaved in source order. -/
  inductive BranchesValid (params : ParameterEnv) (scope : Scope) :
      List (Advanced.Expr × Advanced.Expr) → List ExprType → List ExprType → List Parameter → Prop where
    | nil : BranchesValid params scope [] [] [] []
    | cons (conditionTyped : ExprValid params scope condition tc uc)
        (resultTyped : ExprValid params scope result tr ur)
        (tail : BranchesValid params scope branches conditions results uses) :
        BranchesValid params scope ((condition, result) :: branches)
          (tc :: conditions) (tr :: results) (uc ++ ur ++ uses)
end


end SQLean.SelectContract
