import Std

/-! Public syntax and schema interfaces for the SQLean SQL subset.
Identifiers are normalized by the lexer; manually built ASTs use exact names.
All values are non-null. SQL NULL and three-valued logic are outside this subset.
-/

namespace SQLean

abbrev Name := String

inductive SqlType where
  | int | text | bool
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

inductive Statement where
  | select (query : SelectQuery)
  | insert (query : InsertQuery)
  | update (query : UpdateQuery)
  | delete (query : DeleteQuery)
  deriving Repr, BEq, DecidableEq, Inhabited

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
