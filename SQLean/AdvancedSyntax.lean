import SQLean.SyntaxBase

/-! Typed syntax for the extended PostgreSQL subset. Numeric lexemes are retained
exactly; no floating-point conversion occurs during parsing or rendering. -/
namespace SQLean.Advanced

/-- The thirteen interval field ranges admitted by PostgreSQL's grammar.
Precision, where present, belongs to the final SECOND field. -/
inductive IntervalFields where
  | year | month | day | hour | minute | second
  | yearToMonth | dayToHour | dayToMinute | dayToSecond
  | hourToMinute | hourToSecond | minuteToSecond
  deriving Repr, BEq, DecidableEq, Inhabited

def IntervalFields.all : List IntervalFields :=
  [.year, .month, .day, .hour, .minute, .second, .yearToMonth,
   .dayToHour, .dayToMinute, .dayToSecond, .hourToMinute, .hourToSecond, .minuteToSecond]

def IntervalFields.allowsPrecision : IntervalFields → Bool
  | .second | .dayToSecond | .hourToSecond | .minuteToSecond => true
  | _ => false

/-- SQL-standard SUBSTRING spellings. Arguments remain in lexical order;
FOR ... FROM ... must not renumber anonymous parameter occurrences. -/
inductive SubstringForm where
  | from | fromFor | forFrom | forOnly | similar
  deriving Repr, BEq, DecidableEq, Inhabited

def SubstringForm.arity : SubstringForm → Nat
  | .from | .forOnly => 2
  | .fromFor | .forFrom | .similar => 3

/-- Bare PostgreSQL context forms retain their spelling and default output
label. Callable functions remain ordinary `Expr.call` nodes. -/
inductive ContextValue where
  | currentSchema | currentCatalog | currentUser | user | currentRole | sessionUser | systemUser
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Both PostgreSQL named-argument spellings are retained in source order. -/
inductive NamedArgumentNotation where
  | arrow | assignment
  deriving Repr, BEq, DecidableEq, Inhabited

inductive TypeName where
  | int | bigInt | text | varchar | bool | real | doublePrecision | numeric
  | smallInt | char | date | time | timeTZ | timestamp | timestampTZ
  | interval | uuid | json | jsonb | bytea | name
  | intervalRange (fields : IntervalFields)
  /-- Each wrapper retains one declared unsized array suffix. PostgreSQL does
  not use the declared dimension count as a distinct runtime type. -/
  | array (element : TypeName)
  deriving Repr, BEq, DecidableEq, Inhabited

structure DataType where
  name : TypeName
  modifiers : List Nat := []
  deriving Repr, BEq, DecidableEq, Inhabited

def TypeName.scalarBase : TypeName → TypeName
  | .array element => element.scalarBase
  | typeName => typeName

def TypeName.isArray : TypeName → Bool
  | .array _ => true
  | _ => false

def TypeName.sqlType : TypeName → SqlType
  | .smallInt | .int | .bigInt => .int
  | .text | .varchar | .char => .text
  | .bool => .bool
  | .real | .doublePrecision | .numeric => .real
  | .date => .opaque .date
  | .time => .opaque .time
  | .timeTZ => .opaque .timeTZ
  | .timestamp => .opaque .timestamp
  | .timestampTZ => .opaque .timestampTZ
  | .interval | .intervalRange _ => .opaque .interval
  | .uuid => .opaque .uuid
  | .json => .opaque .json
  | .jsonb => .opaque .jsonb
  | .bytea => .opaque .bytea
  | .name => .opaque .pgName
  | .array element =>
      match element.sqlType with
      | .array base => .array base
      | base => .array base

def DataType.sqlType (type : DataType) : SqlType := type.name.sqlType

/-- Anonymous ordinals count question marks in source order, beginning at one. -/
inductive Parameter where
  | numbered (index : Nat)
  | anonymous (ordinal : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive SetOp where
  | union | intersect | except
  deriving Repr, BEq, DecidableEq, Inhabited

inductive ComparisonOp where
  | eq | ne | lt | le | gt | ge
  deriving Repr, BEq, DecidableEq, Inhabited

def ComparisonOp.toBinOp : ComparisonOp → BinOp
  | .eq => .eq | .ne => .ne | .lt => .lt
  | .le => .le | .gt => .gt | .ge => .ge

/-- SOME is semantically ANY; retain its spelling in the typed syntax. -/
inductive ArrayQuantifier where
  | any | some | all
  deriving Repr, BEq, DecidableEq, Inhabited

/-- PostgreSQL field/element and path extraction retain JSON versus TEXT
result syntax; overload selection is an independent contract obligation. -/
inductive JsonAccessOp where
  | field | fieldText | path | pathText
  deriving Repr, BEq, DecidableEq, Inhabited

/-- PostgreSQL JSONB top-level existence operators. The question-mark token
is an operator only in infix position; anonymous binding identity is separate. -/
inductive JsonExistenceOp where
  | key | any | all
  deriving Repr, BEq, DecidableEq, Inhabited

inductive LockStrength where
  | update | noKeyUpdate | share | keyShare
  deriving Repr, BEq, DecidableEq, Inhabited

inductive LockWaitPolicy where
  | block | nowait | skipLocked
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Ordered PostgreSQL row-lock clauses. Names identify visible FROM aliases;
they are not expressions and do not consume parameter positions. -/
structure LockingClause where
  strength : LockStrength
  targets : List Name := []
  waitPolicy : LockWaitPolicy := .block
  deriving Repr, BEq, DecidableEq, Inhabited

mutual
  inductive Expr where
    | literal (value : Value)
    | null
    | contextValue (value : ContextValue)
    | decimal (lexeme : String)
    | parameter (parameter : Parameter)
    /-- Schema qualification retains decoded identifier components. A schema
    requires a relation qualifier; aliases always remain one plain Name. -/
    | column (qualifier : Option Name) (name : Name) (schema : Option Name := none)
    | binary (op : BinOp) (left right : Expr)
    /-- PostgreSQL's overloaded concatenation operator; its concrete operator
    family is resolved by the independent scalar contract. -/
    | concat (left right : Expr)
    | unary (op : UnOp) (arg : Expr)
    | countAll
    | aggregate (fn : AggregateFn) (arg : Expr) (distinct : Bool := false)
    | isNull (arg : Expr) (negated : Bool := false)
    | pattern (arg pattern : Expr) (insensitive : Bool := false)
    /-- PostgreSQL's four regular-expression match operators. Negation remains
    part of the selected operator rather than being rewritten into NOT. -/
    | regex (arg pattern : Expr) (insensitive negated : Bool := false)
    | jsonAccess (op : JsonAccessOp) (arg key : Expr)
    | jsonExistence (op : JsonExistenceOp) (arg keys : Expr)
    /-- `@>` or `<@`. The independent contract selects the operand-specific
    native family; broader array/range/geometric families may remain uncovered. -/
    | containment (left right : Expr) (containedBy : Bool := false)
    /-- PostgreSQL `&&`; the independent typing profile selects supported
    operand families separately from this structural syntax. -/
    | overlap (left right : Expr)
    /-- PostgreSQL EXTRACT special syntax. The field is a decoded SQL string,
    never an expression or an interpolated SQL fragment. -/
    | extract (field : String) (arg : Expr)
    | substring (form : SubstringForm) (args : List Expr)
    | cast (arg : Expr) (target : DataType)
    /-- PostgreSQL ARRAY[...] constructor. Nested bracket shorthand normalizes
    to nested constructors; declared dimensions remain runtime properties. -/
    | array (elements : List Expr)
    /-- Explicit ROW(...) and implicit multi-field tuples normalize to the
    same constructor. A one-field or empty row still requires ROW syntax. -/
    | row (elements : List Expr)
    /-- Comparison against elements of an array expression. Quantified
    subqueries are a separate SQL form and are not represented here. -/
    | quantifiedComparison (op : ComparisonOp) (quantifier : ArrayQuantifier) (left right : Expr)
    /-- One contiguous bracket group. Nested parenthesized extraction is a
    separate node, since `(a[1])[2]` differs from `a[1][2]`. -/
    | subscript (base : Expr) (indices : List Subscript)
    /-- Ordinary positional function call; name components retain quoting/case
    through the parser's ordinary identifier rules. -/
    | call (name : List Name) (args : List Expr)
    /-- At least one named argument is required by renderer admissibility.
    Binding and omitted defaults are separate static-validity obligations. -/
    | namedCall (name : List Name) (args : List CallArgument)
    | caseExpr (operand : Option Expr) (branches : List (Expr × Expr)) (otherwise : Option Expr)
    | coalesce (args : List Expr)
    | nullIf (left right : Expr)
    | greatest (args : List Expr)
    | least (args : List Expr)
    | filteredAggregate (aggregate predicate : Expr)
    | inList (arg : Expr) (values : List Expr)
    | between (arg lower upper : Expr) (negated : Bool := false)
    | inQuery (arg : Expr) (query : Query)
    | exists (query : Query)
    | scalarQuery (query : Query)
    deriving Repr, BEq, Inhabited

  inductive CallArgument where
    | positional (value : Expr)
    | named (name : Name) (value : Expr) (spelling : NamedArgumentNotation := .arrow)
    deriving Repr, BEq, Inhabited

  inductive Subscript where
    | index (expr : Expr)
    | slice (lower upper : Option Expr)
    deriving Repr, BEq, Inhabited

  inductive SelectItem where
    | all (qualifier : Option Name := none) (schema : Option Name := none)
    | expression (expr : Expr) (alias : Option Name := none)
    deriving Repr, BEq, Inhabited

  structure OrderBy where
    expr : Expr
    descending : Bool := false
    nullsFirst : Option Bool := none
    deriving Repr, BEq, Inhabited

  inductive JoinCondition where
    | none
    | on (expr : Expr)
    | using (columns : List Name)
    | natural
    deriving Repr, BEq, Inhabited

  inductive From where
    | table (name : Name) (alias : Option Name := none) (columns : List Name := [])
        (schema : Option Name := none)
    | derived (query : Query) (alias : Name) (columns : List Name := []) (lateral : Bool := false)
    | join (kind : JoinKind) (left right : From) (condition : JoinCondition)
    deriving Repr, BEq, Inhabited

  structure Select where
    items : List SelectItem
    source : Option From := none
    whereClause : Option Expr := none
    groupBy : List Expr := []
    having : Option Expr := none
    distinct : Bool := false
    distinctOn : List Expr := []
    deriving Repr, BEq, Inhabited

  inductive QueryBody where
    | select (select : Select)
    | set (op : SetOp) (all : Bool) (left right : Query)
    deriving Repr, BEq, Inhabited

  structure Query where
    body : QueryBody
    ctes : List CTE := []
    recursive : Bool := false
    orderBy : List OrderBy := []
    /-- PostgreSQL evaluates pagination expressions once, outside local row scope.
    Static typing does not establish nonnegative runtime values. -/
    limit : Option Expr := none
    offset : Option Expr := none
    locking : List LockingClause := []
    /-- Retain pagination spelling order, including anonymous parameter order. -/
    offsetFirst : Bool := false
    deriving Repr, BEq, Inhabited

  structure CTE where
    name : Name
    query : Query
    columns : List Name := []
    deriving Repr, BEq, Inhabited
end

def CallArgument.expression : CallArgument → Expr
  | .positional value | .named _ value _ => value

def CallArgument.name? : CallArgument → Option Name
  | .positional _ => none
  | .named name _ _ => some name

def Subscript.isSlice : Subscript → Bool
  | .index _ => false
  | .slice _ _ => true

/-- Present bound expressions in source order. -/
def Subscript.expressions : Subscript → List Expr
  | .index expr => [expr]
  | .slice lower upper => lower.toList ++ upper.toList

/-- Preserve numeric-literal construction of pagination fields in client code. -/
instance (n : Nat) : OfNat Expr n := ⟨.literal (.int n)⟩
instance : Coe Nat Expr := ⟨fun n => .literal (.int n)⟩

structure Assignment where
  column : Name
  value : Expr
  deriving Repr, BEq, Inhabited

inductive InsertSource where
  | values (rows : List (List Expr))
  | query (query : Query)
  | defaultValues
  deriving Repr, BEq, Inhabited

inductive ConflictTarget where
  | columns (names : List Name)
  | constraint (name : Name)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive ConflictAction where
  | nothing
  | update (assignments : List Assignment) (whereClause : Option Expr := none)
  deriving Repr, BEq, Inhabited

structure OnConflict where
  target : Option ConflictTarget := none
  action : ConflictAction
  deriving Repr, BEq, Inhabited

structure Insert where
  table : Name
  alias : Option Name := none
  columns : List Name := []
  source : InsertSource
  onConflict : Option OnConflict := none
  returning : List SelectItem := []
  deriving Repr, BEq, Inhabited

structure Update where
  table : Name
  alias : Option Name := none
  assignments : List Assignment
  whereClause : Option Expr := none
  returning : List SelectItem := []
  deriving Repr, BEq, Inhabited

structure Delete where
  table : Name
  alias : Option Name := none
  whereClause : Option Expr := none
  returning : List SelectItem := []
  deriving Repr, BEq, Inhabited

structure Column where
  name : Name
  type : DataType
  /-- none is the default nullable declaration; primary keys are non-null. -/
  nullable : Option Bool := none
  defaultValue : Option Expr := none
  primaryKey : Bool := false
  unique : Bool := false
  deriving Repr, BEq, Inhabited

inductive TableConstraint where
  | primaryKey (columns : List Name)
  | unique (columns : List Name)
  deriving Repr, BEq, DecidableEq, Inhabited

structure CreateTable where
  name : Name
  ifNotExists : Bool := false
  columns : List Column
  constraints : List TableConstraint := []
  deriving Repr, BEq, Inhabited

inductive AlterAction where
  | addColumn (column : Column) (ifNotExists : Bool := false)
  | dropColumn (name : Name) (ifExists : Bool := false) (cascade : Bool := false)
  | renameColumn (name newName : Name)
  | renameTable (newName : Name)
  | setType (name : Name) (type : DataType)
  | setNotNull (name : Name)
  | dropNotNull (name : Name)
  | setDefault (name : Name) (value : Expr)
  | dropDefault (name : Name)
  deriving Repr, BEq, Inhabited

inductive Statement where
  | query (query : Query)
  | insert (insert : Insert)
  | update (update : Update)
  | delete (delete : Delete)
  | createTable (create : CreateTable)
  | alterTable (name : Name) (actions : List AlterAction)
  | dropTable (name : Name) (ifExists : Bool := false) (cascade : Bool := false)
  deriving Repr, BEq, Inhabited

end SQLean.Advanced
