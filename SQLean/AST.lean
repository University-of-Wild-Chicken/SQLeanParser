import Std

/-! Public syntax and schema interfaces for the SQLean SQL subset.
Identifiers are normalized by the lexer; manually built ASTs use exact names.
Base schema values are non-null. Advanced SELECT typing tracks nullable results
introduced by outer joins and aggregate functions.
-/

namespace SQLean

abbrev Name := String

inductive SqlType where
  | int | text | bool | real
  | nullable (base : SqlType)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Value where
  | int (value : Nat)
  | text (value : String)
  | bool (value : Bool)
  deriving Repr, BEq, DecidableEq, Inhabited

def Value.type : Value → SqlType
  | .int _ => .int
  | .text _ => .text
  | .bool _ => .bool

inductive BinOp where
  | eq | ne | lt | le | gt | ge
  | and | or
  | add | sub | mul | div
  deriving Repr, BEq, DecidableEq, Inhabited

inductive UnOp where
  | pos | neg | not
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Expr where
  | literal (value : Value)
  | column (name : Name)
  | binary (op : BinOp) (left right : Expr)
  | unary (op : UnOp) (arg : Expr)
  deriving Repr, BEq, DecidableEq, Inhabited

structure ColumnDef where
  name : Name
  type : SqlType
  deriving Repr, BEq, DecidableEq, Inhabited

structure TableDef where
  name : Name
  columns : List ColumnDef
  deriving Repr, BEq, DecidableEq, Inhabited

abbrev Schema := List TableDef

structure Query where
  table : Name
  selectList : List Expr
  whereClause : Option Expr := none
  deriving Repr, BEq, DecidableEq, Inhabited

/-- SELECT * or a nonempty list of selected expressions. -/
inductive Projection where
  | all
  | expressions (items : List Expr)
  deriving Repr, BEq, DecidableEq, Inhabited

structure OrderBy where
  expr : Expr
  descending : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The CRUD SELECT interface; `Query` retains the original MVP interface. -/
structure SelectQuery where
  table : Name
  projection : Projection
  whereClause : Option Expr := none
  distinct : Bool := false
  orderBy : List OrderBy := []
  limit : Option Nat := none
  offset : Option Nat := none
  deriving Repr, BEq, DecidableEq, Inhabited

def Query.toSelect (query : Query) : SelectQuery :=
  { table := query.table, projection := .expressions query.selectList,
    whereClause := query.whereClause }

structure InsertQuery where
  table : Name
  /-- `none` uses schema column order; `some` specifies the target order. -/
  columns : Option (List Name) := none
  rows : List (List Expr)
  deriving Repr, BEq, DecidableEq, Inhabited

structure Assignment where
  column : Name
  value : Expr
  deriving Repr, BEq, DecidableEq, Inhabited

structure UpdateQuery where
  table : Name
  assignments : List Assignment
  whereClause : Option Expr := none
  deriving Repr, BEq, DecidableEq, Inhabited

structure DeleteQuery where
  table : Name
  whereClause : Option Expr := none
  deriving Repr, BEq, DecidableEq, Inhabited

inductive AggregateFn where
  | count | sum | avg | min | max
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Expressions for joins and aggregation; the existing `Expr` API is unchanged. -/
inductive RelExpr where
  | literal (value : Value)
  | column (qualifier : Option Name) (name : Name)
  | binary (op : BinOp) (left right : RelExpr)
  | unary (op : UnOp) (arg : RelExpr)
  | countAll
  | aggregate (fn : AggregateFn) (arg : RelExpr) (distinct : Bool := false)
  | isNull (arg : RelExpr) (negated : Bool := false)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive JoinKind where
  | inner | left | right | full | cross
  deriving Repr, BEq, DecidableEq, Inhabited

inductive SelectItem where
  | all (qualifier : Option Name := none)
  | expression (expr : RelExpr) (alias : Option Name := none)
  deriving Repr, BEq, DecidableEq, Inhabited

structure RelOrderBy where
  expr : RelExpr
  descending : Bool := false
  deriving Repr, BEq, DecidableEq, Inhabited

mutual
  structure TableRef where
    name : Name
    alias : Option Name := none
    /-- A derived table has an empty `name` and a required alias. -/
    derived : Option RelQuery := none
    deriving Repr, BEq, Inhabited

  structure Join where
    kind : JoinKind
    table : TableRef
    on : Option RelExpr := none
    deriving Repr, BEq, Inhabited

  structure RelQuery where
    /-- An empty, unaliased, non-derived source denotes SELECT without FROM. -/
    source : TableRef
    selectList : List SelectItem
    joins : List Join := []
    whereClause : Option RelExpr := none
    groupBy : List RelExpr := []
    having : Option RelExpr := none
    distinct : Bool := false
    orderBy : List RelOrderBy := []
    limit : Option Nat := none
    offset : Option Nat := none
    ctes : List CTE := []
    /-- The WITH RECURSIVE modifier applies to this query's CTE list. -/
    recursive : Bool := false
    /-- Left-associated UNION/UNION ALL arms; sorting and pagination apply globally. -/
    unions : List UnionBranch := []
    deriving Repr, BEq, Inhabited

  structure CTE where
    name : Name
    query : RelQuery
    /-- Optional explicit output-column names, in projection order. -/
    columns : List Name := []
    deriving Repr, BEq, Inhabited

  structure UnionBranch where
    all : Bool := false
    query : RelQuery
    deriving Repr, BEq, Inhabited
end

inductive Statement where
  | select (query : SelectQuery)
  | insert (query : InsertQuery)
  | update (query : UpdateQuery)
  | delete (query : DeleteQuery)
  | relational (query : RelQuery)
  deriving Repr, BEq, Inhabited

def Schema.findTable (schema : Schema) (name : Name) : Option TableDef :=
  schema.find? (fun table => table.name == name)

def TableDef.findColumn (table : TableDef) (name : Name) : Option ColumnDef :=
  table.columns.find? (fun column => column.name == name)

structure SourcePos where
  offset : Nat := 0
  line : Nat := 1
  column : Nat := 1
  deriving Repr, BEq, DecidableEq, Inhabited

structure ParseError where
  position : SourcePos
  message : String
  deriving Repr, BEq, DecidableEq, Inhabited

instance : ToString ParseError where
  toString e := s!"{e.position.line}:{e.position.column}: {e.message}"

inductive TokenKind where
  | word (text : String)
  | quotedIdent (text : String)
  | number (value : Nat)
  | string (value : String)
  | symbol (text : String)
  | eof
  deriving Repr, BEq, DecidableEq, Inhabited

structure Token where
  kind : TokenKind
  position : SourcePos
  deriving Repr, BEq, DecidableEq, Inhabited

end SQLean
