import SQLean.SelectContract.ScalarSignatures

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
        (⟨col.name, ⟨base, columnNullable table col⟩⟩ :: bindings)

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
    | unary (arg : ExprValid params scope a ta uses) (signature : unarySignature op ta = some result)
        (ordinary : OrdinaryUnary op a) :
        ExprValid params scope (.unary op a) result uses
    | isNull (arg : ExprValid params scope a ta uses) :
        ExprValid params scope (.isNull a negated) (some ⟨.bool, false⟩) uses
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

/-- Constructor-derived labels survive explicit cast chains. -/
def arrayOrigin : Advanced.Expr → Bool
  | .array _ => true
  | .cast arg _ => arrayOrigin arg
  | _ => false

/-- Built-in names used by PostgreSQL's raw TypeName after grammar aliases
are normalized. Array suffixes and modifiers do not change the label. -/
def typeNameLabel : Advanced.TypeName → Name
  | .smallInt => "int2" | .int => "int4" | .bigInt => "int8"
  | .text => "text" | .varchar => "varchar" | .char => "bpchar"
  | .bool => "bool" | .real => "float4" | .doublePrecision => "float8"
  | .numeric => "numeric" | .date => "date" | .time => "time"
  | .timeTZ => "timetz" | .timestamp => "timestamp" | .timestampTZ => "timestamptz"
  | .interval | .intervalRange _ => "interval" | .uuid => "uuid" | .json => "json"
  | .jsonb => "jsonb" | .bytea => "bytea"
  | .array element => typeNameLabel element

/-- PostgreSQL FigureColnameInternal's strength distinction for the covered
expression forms: 0 is absent, 1 is a weak cast/CASE name, and 2 is inherited.
A cast replaces a weak name but retains a column/function/constructor name. -/
def outputLabel : Advanced.Expr → Nat × Name
  | .column _ name _ => (2, name)
  | .call name _ => (2, name.getLastD "?column?")
  | .array _ => (2, "array")
  | .row _ => (2, "row")
  | .extract .. => (2, "extract")
  | .substring .. => (2, "substring")
  | .cast arg target =>
      let inherited := outputLabel arg
      if inherited.1 ≤ 1 then (1, typeNameLabel target.name) else inherited
  | .subscript arg _ => outputLabel arg
  | .caseExpr _ _ otherwise =>
      let inherited := match otherwise with
        | none => (0, "?column?")
        | some expr => outputLabel expr
      if inherited.1 ≤ 1 then (1, "case") else inherited
  | .coalesce .. => (2, "coalesce")
  | .nullIf .. => (2, "nullif")
  | .greatest .. => (2, "greatest")
  | .least .. => (2, "least")
  | _ => (0, "?column?")

/-- Labels are independent of expression typing. Duplicate labels remain
ordered outputs, and an explicit alias overrides every inferred label. -/
def outputName (expr : Advanced.Expr) (alias : Option Name) : Name :=
  alias.getD (outputLabel expr).2

inductive ItemsValid (params : ParameterEnv) (scope : Scope) :
    List Advanced.SelectItem → List OutputColumn → List Parameter → Prop where
  | nil : ItemsValid params scope [] [] []
  | expression (typed : ExprValid params scope expr type uses)
      (aliasValid : ∀ name ∈ alias, name ≠ "")
      (tail : ItemsValid params scope items output remaining) :
      ItemsValid params scope (.expression expr alias :: items)
        (⟨outputName expr alias, projectedType type⟩ :: output) (uses ++ remaining)
  | all (bindings : scope.columns qualifier schema = selected)
      (nonempty : selected ≠ [])
      (tail : ItemsValid params scope items output uses) :
      ItemsValid params scope (.all qualifier schema :: items) (selected ++ output) uses

inductive PredicateValid (params : ParameterEnv) (scope : Scope) : Option Advanced.Expr → List Parameter → Prop where
  | absent : PredicateValid params scope none []
  | present (typed : ExprValid params scope expr type uses) (boolean : acceptsBase .bool type = true) :
      PredicateValid params scope (some expr) uses

/-- Outer joins add possible NULL rows without changing names, order, concrete
types, or declaration modifiers. Existing nullability is retained. -/
def nullableColumn (column : OutputColumn) : OutputColumn :=
  { column with type := { column.type with nullable := true } }

def nullableScope (scope : Scope) : Scope :=
  ⟨scope.relations.map (fun relation =>
      {relation with columns := relation.columns.map nullableColumn, nullable := true}),
    scope.output.map nullableColumn⟩

def joinScope (kind : JoinKind) (left right : Scope) : Scope :=
  (if kind == .right || kind == .full then nullableScope left else left) ++
  (if kind == .left || kind == .full then nullableScope right else right)

/-- Visible leaf relation names with the possibility of a NULL-extended row.
This is structural metadata, independent of column resolution or a checker. -/
def fromRelations : Advanced.From → List (Name × Bool)
  | .table name alias _ _ => [(alias.getD name, false)]
  | .derived _ alias _ _ => [(alias, false)]
  | .join kind left right _ =>
      (fromRelations left).map (fun relation =>
        (relation.1, relation.2 || kind == .right || kind == .full)) ++
      (fromRelations right).map (fun relation =>
        (relation.1, relation.2 || kind == .left || kind == .full))

def sourceRelations (source : Option Advanced.From) : List (Name × Bool) :=
  source.toList.flatMap fromRelations

def fromDerivedNames : Advanced.From → List Name
  | .table .. => []
  | .derived _ alias _ _ => [alias]
  | .join _ left right _ => fromDerivedNames left ++ fromDerivedNames right

def sourceDerivedNames (source : Option Advanced.From) : List Name :=
  source.toList.flatMap fromDerivedNames

/-- Equal visible names are legal only for distinct unaliased base relations.
Column lookup can still be ambiguous; the namespace itself remains well formed. -/
def NamespaceCompatible (left right : RelationNamespace) : Prop :=
  left.name ≠ right.name ∨
    (left.aliased = false ∧ right.aliased = false ∧
      left.origin.isSome = true ∧ right.origin.isSome = true ∧ left.origin ≠ right.origin)

instance (left right : RelationNamespace) : Decidable (NamespaceCompatible left right) := by
  unfold NamespaceCompatible
  infer_instance

def JoinAliasesDistinct (left right : Scope) : Prop :=
  ∀ l ∈ left.relations, ∀ r ∈ right.relations, NamespaceCompatible l r

instance (left right : Scope) : Decidable (JoinAliasesDistinct left right) := by
  unfold JoinAliasesDistinct
  infer_instance

/-- NATURAL discovers common names in the left exposed row's order. It does
not deduplicate names: ambiguous exposed keys must be rejected. -/
def naturalJoinKeys (left right : List OutputColumn) : List Name :=
  (left.filter (fun col => right.any (fun other => other.name == col.name))).map OutputColumn.name

/-- No equality-based nullability refinement is claimed. LEFT/RIGHT preserve
their retained side; INNER/FULL conservatively admit NULL from either input.
In particular FULL must not use COALESCE's pre-join conjunction rule. -/
def mergedKeyNullable (kind : JoinKind) (left right : ExactType) : Bool :=
  match kind with
  | .left => left.nullable
  | .right => right.nullable
  | _ => left.nullable || right.nullable

/-- Equality resolution and merged-column common-type resolution are separate
normative premises, as in PostgreSQL. Both inspect the original child types. -/
inductive JoinKeysValid (kind : JoinKind) (left right : List OutputColumn) :
    List Name → List OutputColumn → Prop where
  | nil : JoinKeysValid kind left right [] []
  | cons (leftResolved : left.filter (fun col => col.name == key) = [leftColumn])
      (rightResolved : right.filter (fun col => col.name == key) = [rightColumn])
      (equality : equalityOverload (.known leftColumn.type) (.known rightColumn.type) = some operator)
      (common : conditionalBase [.known leftColumn.type, .known rightColumn.type] = some base)
      (tail : JoinKeysValid kind left right keys merged) :
      JoinKeysValid kind left right (key :: keys)
        (⟨key, ⟨base, mergedKeyNullable kind leftColumn.type rightColumn.type⟩⟩ :: merged)

/-- Qualified columns retain both child namespaces and their original order.
Only the exposed row is merged: keys first, then left and right nonkeys. -/
def mergedJoinScope (kind : JoinKind) (left right : Scope)
    (keys : List Name) (merged : List OutputColumn) : Scope :=
  let joined := joinScope kind left right
  ⟨joined.relations, merged ++ joined.output.filter (fun col => !keys.contains col.name)⟩

/-- An alias list renames a positional prefix; unnamed remaining columns keep
their certified labels. Repeated labels are legal and remain ambiguous when
referenced by name. The separate length premise forbids excess aliases. -/
def renameOutput : List Name → List OutputColumn → List OutputColumn
  | [], output => output
  | name :: names, column :: output => { column with name } :: renameOutput names output
  | _ :: _, [] => []

def ColumnAliasesValid (names : List Name) (output : List OutputColumn) : Prop :=
  names.length ≤ output.length ∧ ∀ name ∈ names, name ≠ ""

instance (names : List Name) (output : List OutputColumn) : Decidable (ColumnAliasesValid names output) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Sort syntax categories are part of the name-resolution rule, not an
executable typing predicate. -/
def SortExpression : Advanced.Expr → Prop
  | .literal (.int _) | .column none _ none => False
  | _ => True

instance (expr : Advanced.Expr) : Decidable (SortExpression expr) := by
  unfold SortExpression
  split <;> infer_instance

def OrdinalOrderable (output : List OutputColumn) (n : Nat) : Prop :=
  ((output[n - 1]?).map (fun column => column.type.base.orderable)).getD false = true

instance (output : List OutputColumn) (n : Nat) : Decidable (OrdinalOrderable output n) :=
  inferInstanceAs (Decidable (_ = _))

def DistinctAllowed (distinct : Bool) (output : List OutputColumn) : Prop :=
  distinct = false ∨ ∀ column ∈ output, column.type.base.orderable = true

instance (distinct : Bool) (output : List OutputColumn) : Decidable (DistinctAllowed distinct output) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Output-name lookup takes precedence only for a bare name. Duplicate output
names are an error. Compound expressions see input bindings, not aliases. -/
inductive SortValid (params : ParameterEnv) (scope : Scope) (output : List OutputColumn) (distinct : Bool) :
    Advanced.Expr → List Parameter → Prop where
  | ordinal (positive : 0 < n) (inRange : n ≤ output.length) (orderable : OrdinalOrderable output n) :
      SortValid params scope output distinct (.literal (.int n)) []
  | outputName (resolved : output.filter (·.name == name) = [column])
      (orderable : column.type.base.orderable = true) :
      SortValid params scope output distinct (.column none name) []
  | inputName (noOutput : output.filter (·.name == name) = []) (ordinary : distinct = false)
      (typed : ExprValid params scope (.column none name) type uses)
      (orderable : type.orderable = true) :
      SortValid params scope output distinct (.column none name) uses
  | expression (ordinary : distinct = false) (typed : ExprValid params scope expr type uses)
      (category : SortExpression expr) (orderable : type.orderable = true) :
      SortValid params scope output distinct expr uses

inductive OrdersValid (params : ParameterEnv) (scope : Scope) (output : List OutputColumn) (distinct : Bool) :
    List Advanced.OrderBy → List Parameter → Prop where
  | nil : OrdersValid params scope output distinct [] []
  | cons (head : SortValid params scope output distinct item.expr uses)
      (tail : OrdersValid params scope output distinct items remaining) :
      OrdersValid params scope output distinct (item :: items) (uses ++ remaining)

/-- The pagination context supplies PostgreSQL's INT8 row-count target.
Integer widening is lossless; NUMERIC/REAL/DOUBLE use catalog assignment casts
whose rounding/range checks remain execution obligations. Unknown NULL acquires
the target type. These are contextual casts, not general operator signatures. -/
inductive RowCountCoercion : ExprType → Prop where
  | unknownNull : RowCountCoercion none
  | smallIntWiden (nullable : Bool) : RowCountCoercion (some ⟨.smallInt, nullable⟩)
  | int32Widen (nullable : Bool) : RowCountCoercion (some ⟨.int32, nullable⟩)
  | int64Identity (nullable : Bool) : RowCountCoercion (some ⟨.int64, nullable⟩)
  | numericAssignment (modifiers : List Nat) (nullable : Bool) :
      RowCountCoercion (some ⟨.numeric modifiers, nullable⟩)
  | realAssignment (nullable : Bool) : RowCountCoercion (some ⟨.real, nullable⟩)
  | doubleAssignment (nullable : Bool) : RowCountCoercion (some ⟨.doublePrecision, nullable⟩)

/-- Every successfully evaluated signed INT32 value embeds unchanged in the
signed INT8 target used by PostgreSQL pagination. This does not assert that
evaluation succeeds or that the value is nonnegative. -/
theorem int32_row_count_widening (value : Int)
    (lower : -2147483648 ≤ value) (upper : value ≤ 2147483647) :
    -9223372036854775808 ≤ value ∧ value ≤ 9223372036854775807 := by
  omega

/-- Pagination expressions have no local row or output-alias bindings.
This is a static typing judgment. Expression evaluation may still fail, and
non-NULL runtime values must satisfy PaginationValueAllowed. In PostgreSQL,
NULL LIMIT means no bound, and NULL OFFSET means zero. -/
inductive PaginationValid (params : ParameterEnv) :
    Option Advanced.Expr → List Parameter → Prop where
  | absent : PaginationValid params none []
  | present (typed : ExprValid params .empty expr type uses)
      (coercion : RowCountCoercion type) :
      PaginationValid params (some expr) uses

/-- A separate execution obligation on an evaluated row count. A static
certificate does not prove this predicate or successful expression evaluation. -/
def PaginationValueAllowed (value : Option Int) : Prop :=
  ∀ count ∈ value, 0 ≤ count

/-- A pagination-only judgment is useful even when other query clauses lack
independent rules. It records occurrences separately for LIMIT and OFFSET.
The two occurrence lists belong to their named bounds; their execution/source
ordering is not asserted here. It makes no assertion about the body, catalog,
output schema, or query-wide parameter notation, which requires occurrences
from every clause and the pagination-layout flag. -/
inductive PaginationBoundsValid (profile : Profile) (params : ParameterEnv)
    (query : Advanced.Query) : List Parameter → List Parameter → Prop where
  | bounds (environment : ParametersWellFormed params)
      (limit : PaginationValid params query.limit limitUses)
      (offset : PaginationValid params query.offset offsetUses) :
      PaginationBoundsValid profile params query limitUses offsetUses

structure PaginationBoundsCertificate (profile : Profile) (params : ParameterEnv)
    (query : Advanced.Query) where
  limitUses : List Parameter
  offsetUses : List Parameter
  valid : PaginationBoundsValid profile params query limitUses offsetUses

/-- The remaining value condition, to be checked after successful evaluation
and widening. The certificate supplies no proof of this execution obligation. -/
def PaginationBoundsCertificate.runtimeObligation
    (_certificate : PaginationBoundsCertificate profile params query)
    (limitValue offsetValue : Option Int) : Prop :=
  PaginationValueAllowed limitValue ∧ PaginationValueAllowed offsetValue

/-- PostgreSQL OF resolves the first matching visible relation in range-table
order. This deliberately differs from unique namespace resolution for columns. -/
def LockTarget (scope : Scope) (target : Name) : Prop :=
  target ≠ "" ∧ ∃ relation ∈ scope.relations.find? (fun relation => relation.name == target),
    relation.origin.isSome = true ∧ relation.nullable = false

instance (scope : Scope) (target : Name) : Decidable (LockTarget scope target) := by
  unfold LockTarget
  infer_instance

def LockTargets (scope : Scope) (targets : List Name) : Prop :=
  if targets = [] then ∀ relation ∈ scope.relations,
    relation.origin.isSome = true ∧ relation.nullable = false
  else ∀ target ∈ targets, LockTarget scope target

instance (scope : Scope) (targets : List Name) : Decidable (LockTargets scope targets) := by
  unfold LockTargets
  infer_instance

/-- This judgment checks target identity and null extension, not privileges,
lock acquisition, waits, or propagation into a selected derived relation. -/
inductive LockingValid (scope : Scope) (distinct : Bool) :
    List Advanced.LockingClause → Prop where
  | nil : LockingValid scope distinct []
  | cons (ordinary : distinct = false)
      (targets : LockTargets scope clause.targets)
      (tail : LockingValid scope distinct clauses) :
      LockingValid scope distinct (clause :: clauses)

mutual
  /-- Every ON predicate sees exactly its two child scopes, before this join's
  own NULL extension. Parameters are visited left source, right source, then ON.
  USING/NATURAL preserve separate qualified and exposed scopes. Non-LATERAL
  derived sources expose a certified child row without fabricating catalog metadata. -/
  inductive SourceValid (profile : Profile) (catalog : Catalog) (params : ParameterEnv) :
      Option Advanced.From → Scope → List Parameter → Prop where
    | empty : SourceValid profile catalog params none .empty []
    | table (present : table ∈ catalog) (resolved : table.matchesReference name schema = true)
        (aliasValid : ∀ aliasName ∈ alias, aliasName ≠ "")
        (columns : TableColumns table table.columns bindings) :
        SourceValid profile catalog params (some (.table name alias [] schema)) (Scope.ofTable table.identity alias bindings) []
    | tableRenamed (present : table ∈ catalog) (resolved : table.matchesReference name schema = true)
        (aliasValid : alias ≠ "")
        (columns : TableColumns table table.columns bindings)
        (aliasesValid : ColumnAliasesValid aliases bindings) :
        SourceValid profile catalog params (some (.table name (some alias) aliases schema))
          (Scope.ofTable table.identity (some alias) (renameOutput aliases bindings)) []
    | cross (leftValid : SourceValid profile catalog params (some left) leftScope leftUses)
        (rightValid : SourceValid profile catalog params (some right) rightScope rightUses)
        (aliases : JoinAliasesDistinct leftScope rightScope) :
        SourceValid profile catalog params (some (.join .cross left right .none))
          (leftScope ++ rightScope) (leftUses ++ rightUses)
    | on (leftValid : SourceValid profile catalog params (some left) leftScope leftUses)
        (rightValid : SourceValid profile catalog params (some right) rightScope rightUses)
        (aliases : JoinAliasesDistinct leftScope rightScope)
        (kindValid : kind ≠ .cross)
        (condition : PredicateValid params (leftScope ++ rightScope) (some expr) onUses) :
        SourceValid profile catalog params (some (.join kind left right (.on expr)))
          (joinScope kind leftScope rightScope) (leftUses ++ rightUses ++ onUses)
    | using (leftValid : SourceValid profile catalog params (some left) leftScope leftUses)
        (rightValid : SourceValid profile catalog params (some right) rightScope rightUses)
        (aliases : JoinAliasesDistinct leftScope rightScope)
        (kindValid : kind ≠ .cross) (nonempty : keys ≠ []) (unique : keys.Nodup)
        (keysValid : JoinKeysValid kind leftScope.output rightScope.output keys merged) :
        SourceValid profile catalog params (some (.join kind left right (.using keys)))
          (mergedJoinScope kind leftScope rightScope keys merged) (leftUses ++ rightUses)
    | natural (leftValid : SourceValid profile catalog params (some left) leftScope leftUses)
        (rightValid : SourceValid profile catalog params (some right) rightScope rightUses)
        (aliases : JoinAliasesDistinct leftScope rightScope)
        (kindValid : kind ≠ .cross)
        (unique : (naturalJoinKeys leftScope.output rightScope.output).Nodup)
        (keysValid : JoinKeysValid kind leftScope.output rightScope.output
          (naturalJoinKeys leftScope.output rightScope.output) merged) :
        SourceValid profile catalog params (some (.join kind left right .natural))
          (mergedJoinScope kind leftScope rightScope
            (naturalJoinKeys leftScope.output rightScope.output) merged) (leftUses ++ rightUses)
    | derived (queryValid : QueryValid profile catalog params query output uses)
        (aliasValid : alias ≠ "") (columnsValid : ColumnAliasesValid columns output)
        (nonLateral : lateral = false) :
        SourceValid profile catalog params (some (.derived query alias columns lateral))
          (Scope.ofOutput alias (renameOutput columns output)) uses

  /-- Internal query derivations collect complete lexical occurrences. Nested
  queries do not restart anonymous ordinals or assert global notation validity. -/
  inductive QueryValid (profile : Profile) (catalog : Catalog) (params : ParameterEnv) :
      Advanced.Query → List OutputColumn → List Parameter → Prop where
    | basic {select : Advanced.Select}
        (source : SourceValid profile catalog params select.source scope sourceUses)
        (items : ItemsValid params scope select.items output selectUses)
        (nonempty : output ≠ [])
        (distinctComparable : DistinctAllowed select.distinct output)
        (predicate : PredicateValid params scope select.whereClause whereUses)
        (orders : OrdersValid params scope output select.distinct orderBy orderUses)
        (limitValid : PaginationValid params limit limitUses)
        (offsetValid : PaginationValid params offset offsetUses)
        (lockingValid : LockingValid scope select.distinct locking)
        (noGrouping : select.groupBy = []) (noHaving : select.having = none)
        (noDistinctOn : select.distinctOn = []) :
        QueryValid profile catalog params
          ⟨.select select, [], false, orderBy, limit, offset, locking, offsetFirst⟩ output
          (if offsetFirst then selectUses ++ sourceUses ++ whereUses ++ orderUses ++ offsetUses ++ limitUses
           else selectUses ++ sourceUses ++ whereUses ++ orderUses ++ limitUses ++ offsetUses)
end

/-- The public judgment checks exact metadata and parameter notation once,
over the complete statement's occurrence list including all derived sources. -/
inductive SelectValid (profile : Profile) (catalog : Catalog) (params : ParameterEnv) :
    Advanced.Query → List OutputColumn → Prop where
  | certified (environment : WellFormedEnvironment catalog params)
      (supported : SupportedEnvironment catalog params)
      (query : QueryValid profile catalog params ast output uses)
      (parameterOrder : ParameterOrder uses) :
      SelectValid profile catalog params ast output

structure Certificate (profile : Profile) (catalog : Catalog) (params : ParameterEnv) (query : Advanced.Query) where
  output : List OutputColumn
  valid : SelectValid profile catalog params query output

def Certificate.outputCatalog (_certificate : Certificate profile catalog params query) : Catalog := catalog

@[simp] theorem Certificate.catalog_unchanged (certificate : Certificate profile catalog params query) :
    certificate.outputCatalog = catalog := rfl

end SQLean.SelectContract
