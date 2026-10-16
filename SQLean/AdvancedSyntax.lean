import SQLean.SyntaxBase

/-! Typed syntax for the extended PostgreSQL subset. Numeric lexemes are retained
exactly; no floating-point conversion occurs during parsing or rendering. -/
namespace SQLean.Advanced

inductive TypeName where
  | int | bigInt | text | varchar | bool | real | doublePrecision | numeric
  deriving Repr, BEq, DecidableEq, Inhabited

structure DataType where
  name : TypeName
  modifiers : List Nat := []
  deriving Repr, BEq, DecidableEq, Inhabited

def DataType.sqlType (type : DataType) : SqlType :=
  match type.name with
  | .int | .bigInt => .int
  | .text | .varchar => .text
  | .bool => .bool
  | .real | .doublePrecision | .numeric => .real

/-- Anonymous ordinals count question marks in source order, beginning at one. -/
inductive Parameter where
  | numbered (index : Nat)
  | anonymous (ordinal : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive SetOp where
  | union | intersect | except
  deriving Repr, BEq, DecidableEq, Inhabited

mutual
  inductive Expr where
    | literal (value : Value)
    | null
    | decimal (lexeme : String)
    | parameter (parameter : Parameter)
    | column (qualifier : Option Name) (name : Name)
    | binary (op : BinOp) (left right : Expr)
    | unary (op : UnOp) (arg : Expr)
    | countAll
    | aggregate (fn : AggregateFn) (arg : Expr) (distinct : Bool := false)
    | isNull (arg : Expr) (negated : Bool := false)
    | pattern (arg pattern : Expr) (insensitive : Bool := false)
    | cast (arg : Expr) (target : DataType)
    | filteredAggregate (aggregate predicate : Expr)
    | inList (arg : Expr) (values : List Expr)
    | between (arg lower upper : Expr) (negated : Bool := false)
    | inQuery (arg : Expr) (query : Query)
    | exists (query : Query)
    | scalarQuery (query : Query)
    deriving Repr, BEq, Inhabited

  inductive SelectItem where
    | all (qualifier : Option Name := none)
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
    limit : Option Nat := none
    offset : Option Nat := none
    deriving Repr, BEq, Inhabited

  structure CTE where
    name : Name
    query : Query
    columns : List Name := []
    deriving Repr, BEq, Inhabited
end

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
