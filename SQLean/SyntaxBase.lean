import Std

/-! Public syntax and schema interfaces for the SQLean SQL subset.
Identifiers are normalized by the lexer; manually built ASTs use exact names.
Base schema values are non-null. Advanced SELECT typing tracks nullable results
introduced by outer joins and aggregate functions.
-/

namespace SQLean

abbrev Name := String

inductive OpaqueType where
  | date | time | timeTZ | timestamp | timestampTZ | interval | uuid | json | jsonb | bytea
  deriving Repr, BEq, DecidableEq, Inhabited

def OpaqueType.name : OpaqueType → String
  | .date => "date" | .time => "time" | .timeTZ => "timetz"
  | .timestamp => "timestamp" | .timestampTZ => "timestamptz"
  | .interval => "interval" | .uuid => "uuid" | .json => "json"
  | .jsonb => "jsonb" | .bytea => "bytea"

inductive SqlType where
  | int | text | bool | real
  /-- Concrete nonnumeric built-in identity retained by the expanded checker.
  The independent contract additionally preserves declaration modifiers. -/
  | opaque (name : OpaqueType)
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

/-- Preserve cast precision even though static result types use numeric families. -/
inductive CastType where
  | int | text | bool | real | doublePrecision
  deriving Repr, BEq, DecidableEq, Inhabited

def CastType.resultType : CastType → SqlType
  | .int => .int
  | .text => .text
  | .bool => .bool
  | .real | .doublePrecision => .real

/-- Expressions for joins and aggregation; the existing `Expr` API is unchanged. -/
inductive RelExpr where
  | literal (value : Value)
  | column (qualifier : Option Name) (name : Name)
  | binary (op : BinOp) (left right : RelExpr)
  | unary (op : UnOp) (arg : RelExpr)
  | countAll
  | aggregate (fn : AggregateFn) (arg : RelExpr) (distinct : Bool := false)
  | isNull (arg : RelExpr) (negated : Bool := false)
  /-- PostgreSQL LIKE/ILIKE; NOT is represented by the ordinary unary operator. -/
  | pattern (arg pattern : RelExpr) (insensitive : Bool := false)
  | cast (arg : RelExpr) (target : CastType)
  /-- The first operand must be COUNT(*) or an aggregate call. -/
  | filteredAggregate (aggregate predicate : RelExpr)
  /-- Retain IN so PostgreSQL applies common-type coercion across all operands. -/
  | inList (arg : RelExpr) (values : List RelExpr)
  deriving Repr, BEq, Inhabited

/- Computable structural equality for the nested expression datatype. -/
mutual
  private def relExprDecEq : (left right : RelExpr) → Decidable (left = right)
    | .literal value₁, .literal value₂ =>
      decidable_of_iff (value₁ = value₂) (by simp)
    | .column qualifier₁ name₁, .column qualifier₂ name₂ =>
      decidable_of_iff (qualifier₁ = qualifier₂ ∧ name₁ = name₂) (by simp)
    | .binary op₁ left₁ right₁, .binary op₂ left₂ right₂ =>
      letI : Decidable (left₁ = left₂) := relExprDecEq left₁ left₂
      letI : Decidable (right₁ = right₂) := relExprDecEq right₁ right₂
      decidable_of_iff (op₁ = op₂ ∧ left₁ = left₂ ∧ right₁ = right₂) (by simp)
    | .unary op₁ arg₁, .unary op₂ arg₂ =>
      letI : Decidable (arg₁ = arg₂) := relExprDecEq arg₁ arg₂
      decidable_of_iff (op₁ = op₂ ∧ arg₁ = arg₂) (by simp)
    | .countAll, .countAll =>
      isTrue rfl
    | .aggregate fn₁ arg₁ distinct₁, .aggregate fn₂ arg₂ distinct₂ =>
      letI : Decidable (arg₁ = arg₂) := relExprDecEq arg₁ arg₂
      decidable_of_iff (fn₁ = fn₂ ∧ arg₁ = arg₂ ∧ distinct₁ = distinct₂) (by simp)
    | .isNull arg₁ negated₁, .isNull arg₂ negated₂ =>
      letI : Decidable (arg₁ = arg₂) := relExprDecEq arg₁ arg₂
      decidable_of_iff (arg₁ = arg₂ ∧ negated₁ = negated₂) (by simp)
    | .pattern arg₁ pat₁ insensitive₁, .pattern arg₂ pat₂ insensitive₂ =>
      letI : Decidable (arg₁ = arg₂) := relExprDecEq arg₁ arg₂
      letI : Decidable (pat₁ = pat₂) := relExprDecEq pat₁ pat₂
      decidable_of_iff (arg₁ = arg₂ ∧ pat₁ = pat₂ ∧ insensitive₁ = insensitive₂) (by simp)
    | .cast arg₁ target₁, .cast arg₂ target₂ =>
      letI : Decidable (arg₁ = arg₂) := relExprDecEq arg₁ arg₂
      decidable_of_iff (arg₁ = arg₂ ∧ target₁ = target₂) (by simp)
    | .filteredAggregate call₁ predicate₁, .filteredAggregate call₂ predicate₂ =>
      letI : Decidable (call₁ = call₂) := relExprDecEq call₁ call₂
      letI : Decidable (predicate₁ = predicate₂) := relExprDecEq predicate₁ predicate₂
      decidable_of_iff (call₁ = call₂ ∧ predicate₁ = predicate₂) (by simp)
    | .inList arg₁ values₁, .inList arg₂ values₂ =>
      letI : Decidable (arg₁ = arg₂) := relExprDecEq arg₁ arg₂
      letI : Decidable (values₁ = values₂) := relExprListDecEq values₁ values₂
      decidable_of_iff (arg₁ = arg₂ ∧ values₁ = values₂) (by simp)
    | .literal _, .column _ _ => isFalse (by intro equality; cases equality)
    | .literal _, .binary _ _ _ => isFalse (by intro equality; cases equality)
    | .literal _, .unary _ _ => isFalse (by intro equality; cases equality)
    | .literal _, .countAll => isFalse (by intro equality; cases equality)
    | .literal _, .aggregate _ _ _ => isFalse (by intro equality; cases equality)
    | .literal _, .isNull _ _ => isFalse (by intro equality; cases equality)
    | .literal _, .pattern _ _ _ => isFalse (by intro equality; cases equality)
    | .literal _, .cast _ _ => isFalse (by intro equality; cases equality)
    | .literal _, .filteredAggregate _ _ => isFalse (by intro equality; cases equality)
    | .literal _, .inList _ _ => isFalse (by intro equality; cases equality)
    | .column _ _, .literal _ => isFalse (by intro equality; cases equality)
    | .column _ _, .binary _ _ _ => isFalse (by intro equality; cases equality)
    | .column _ _, .unary _ _ => isFalse (by intro equality; cases equality)
    | .column _ _, .countAll => isFalse (by intro equality; cases equality)
    | .column _ _, .aggregate _ _ _ => isFalse (by intro equality; cases equality)
    | .column _ _, .isNull _ _ => isFalse (by intro equality; cases equality)
    | .column _ _, .pattern _ _ _ => isFalse (by intro equality; cases equality)
    | .column _ _, .cast _ _ => isFalse (by intro equality; cases equality)
    | .column _ _, .filteredAggregate _ _ => isFalse (by intro equality; cases equality)
    | .column _ _, .inList _ _ => isFalse (by intro equality; cases equality)
    | .binary _ _ _, .literal _ => isFalse (by intro equality; cases equality)
    | .binary _ _ _, .column _ _ => isFalse (by intro equality; cases equality)
    | .binary _ _ _, .unary _ _ => isFalse (by intro equality; cases equality)
    | .binary _ _ _, .countAll => isFalse (by intro equality; cases equality)
    | .binary _ _ _, .aggregate _ _ _ => isFalse (by intro equality; cases equality)
    | .binary _ _ _, .isNull _ _ => isFalse (by intro equality; cases equality)
    | .binary _ _ _, .pattern _ _ _ => isFalse (by intro equality; cases equality)
    | .binary _ _ _, .cast _ _ => isFalse (by intro equality; cases equality)
    | .binary _ _ _, .filteredAggregate _ _ => isFalse (by intro equality; cases equality)
    | .binary _ _ _, .inList _ _ => isFalse (by intro equality; cases equality)
    | .unary _ _, .literal _ => isFalse (by intro equality; cases equality)
    | .unary _ _, .column _ _ => isFalse (by intro equality; cases equality)
    | .unary _ _, .binary _ _ _ => isFalse (by intro equality; cases equality)
    | .unary _ _, .countAll => isFalse (by intro equality; cases equality)
    | .unary _ _, .aggregate _ _ _ => isFalse (by intro equality; cases equality)
    | .unary _ _, .isNull _ _ => isFalse (by intro equality; cases equality)
    | .unary _ _, .pattern _ _ _ => isFalse (by intro equality; cases equality)
    | .unary _ _, .cast _ _ => isFalse (by intro equality; cases equality)
    | .unary _ _, .filteredAggregate _ _ => isFalse (by intro equality; cases equality)
    | .unary _ _, .inList _ _ => isFalse (by intro equality; cases equality)
    | .countAll, .literal _ => isFalse (by intro equality; cases equality)
    | .countAll, .column _ _ => isFalse (by intro equality; cases equality)
    | .countAll, .binary _ _ _ => isFalse (by intro equality; cases equality)
    | .countAll, .unary _ _ => isFalse (by intro equality; cases equality)
    | .countAll, .aggregate _ _ _ => isFalse (by intro equality; cases equality)
    | .countAll, .isNull _ _ => isFalse (by intro equality; cases equality)
    | .countAll, .pattern _ _ _ => isFalse (by intro equality; cases equality)
    | .countAll, .cast _ _ => isFalse (by intro equality; cases equality)
    | .countAll, .filteredAggregate _ _ => isFalse (by intro equality; cases equality)
    | .countAll, .inList _ _ => isFalse (by intro equality; cases equality)
    | .aggregate _ _ _, .literal _ => isFalse (by intro equality; cases equality)
    | .aggregate _ _ _, .column _ _ => isFalse (by intro equality; cases equality)
    | .aggregate _ _ _, .binary _ _ _ => isFalse (by intro equality; cases equality)
    | .aggregate _ _ _, .unary _ _ => isFalse (by intro equality; cases equality)
    | .aggregate _ _ _, .countAll => isFalse (by intro equality; cases equality)
    | .aggregate _ _ _, .isNull _ _ => isFalse (by intro equality; cases equality)
    | .aggregate _ _ _, .pattern _ _ _ => isFalse (by intro equality; cases equality)
    | .aggregate _ _ _, .cast _ _ => isFalse (by intro equality; cases equality)
    | .aggregate _ _ _, .filteredAggregate _ _ => isFalse (by intro equality; cases equality)
    | .aggregate _ _ _, .inList _ _ => isFalse (by intro equality; cases equality)
    | .isNull _ _, .literal _ => isFalse (by intro equality; cases equality)
    | .isNull _ _, .column _ _ => isFalse (by intro equality; cases equality)
    | .isNull _ _, .binary _ _ _ => isFalse (by intro equality; cases equality)
    | .isNull _ _, .unary _ _ => isFalse (by intro equality; cases equality)
    | .isNull _ _, .countAll => isFalse (by intro equality; cases equality)
    | .isNull _ _, .aggregate _ _ _ => isFalse (by intro equality; cases equality)
    | .isNull _ _, .pattern _ _ _ => isFalse (by intro equality; cases equality)
    | .isNull _ _, .cast _ _ => isFalse (by intro equality; cases equality)
    | .isNull _ _, .filteredAggregate _ _ => isFalse (by intro equality; cases equality)
    | .isNull _ _, .inList _ _ => isFalse (by intro equality; cases equality)
    | .pattern _ _ _, .literal _ => isFalse (by intro equality; cases equality)
    | .pattern _ _ _, .column _ _ => isFalse (by intro equality; cases equality)
    | .pattern _ _ _, .binary _ _ _ => isFalse (by intro equality; cases equality)
    | .pattern _ _ _, .unary _ _ => isFalse (by intro equality; cases equality)
    | .pattern _ _ _, .countAll => isFalse (by intro equality; cases equality)
    | .pattern _ _ _, .aggregate _ _ _ => isFalse (by intro equality; cases equality)
    | .pattern _ _ _, .isNull _ _ => isFalse (by intro equality; cases equality)
    | .pattern _ _ _, .cast _ _ => isFalse (by intro equality; cases equality)
    | .pattern _ _ _, .filteredAggregate _ _ => isFalse (by intro equality; cases equality)
    | .pattern _ _ _, .inList _ _ => isFalse (by intro equality; cases equality)
    | .cast _ _, .literal _ => isFalse (by intro equality; cases equality)
    | .cast _ _, .column _ _ => isFalse (by intro equality; cases equality)
    | .cast _ _, .binary _ _ _ => isFalse (by intro equality; cases equality)
    | .cast _ _, .unary _ _ => isFalse (by intro equality; cases equality)
    | .cast _ _, .countAll => isFalse (by intro equality; cases equality)
    | .cast _ _, .aggregate _ _ _ => isFalse (by intro equality; cases equality)
    | .cast _ _, .isNull _ _ => isFalse (by intro equality; cases equality)
    | .cast _ _, .pattern _ _ _ => isFalse (by intro equality; cases equality)
    | .cast _ _, .filteredAggregate _ _ => isFalse (by intro equality; cases equality)
    | .cast _ _, .inList _ _ => isFalse (by intro equality; cases equality)
    | .filteredAggregate _ _, .literal _ => isFalse (by intro equality; cases equality)
    | .filteredAggregate _ _, .column _ _ => isFalse (by intro equality; cases equality)
    | .filteredAggregate _ _, .binary _ _ _ => isFalse (by intro equality; cases equality)
    | .filteredAggregate _ _, .unary _ _ => isFalse (by intro equality; cases equality)
    | .filteredAggregate _ _, .countAll => isFalse (by intro equality; cases equality)
    | .filteredAggregate _ _, .aggregate _ _ _ => isFalse (by intro equality; cases equality)
    | .filteredAggregate _ _, .isNull _ _ => isFalse (by intro equality; cases equality)
    | .filteredAggregate _ _, .pattern _ _ _ => isFalse (by intro equality; cases equality)
    | .filteredAggregate _ _, .cast _ _ => isFalse (by intro equality; cases equality)
    | .filteredAggregate _ _, .inList _ _ => isFalse (by intro equality; cases equality)
    | .inList _ _, .literal _ => isFalse (by intro equality; cases equality)
    | .inList _ _, .column _ _ => isFalse (by intro equality; cases equality)
    | .inList _ _, .binary _ _ _ => isFalse (by intro equality; cases equality)
    | .inList _ _, .unary _ _ => isFalse (by intro equality; cases equality)
    | .inList _ _, .countAll => isFalse (by intro equality; cases equality)
    | .inList _ _, .aggregate _ _ _ => isFalse (by intro equality; cases equality)
    | .inList _ _, .isNull _ _ => isFalse (by intro equality; cases equality)
    | .inList _ _, .pattern _ _ _ => isFalse (by intro equality; cases equality)
    | .inList _ _, .cast _ _ => isFalse (by intro equality; cases equality)
    | .inList _ _, .filteredAggregate _ _ => isFalse (by intro equality; cases equality)
  termination_by left right => sizeOf left + sizeOf right
  decreasing_by all_goals simp_all; omega

  private def relExprListDecEq : (left right : List RelExpr) → Decidable (left = right)
    | [], [] => isTrue rfl
    | [], _ :: _ => isFalse (by intro equality; cases equality)
    | _ :: _, [] => isFalse (by intro equality; cases equality)
    | head :: tail, head' :: tail' =>
      letI : Decidable (head = head') := relExprDecEq head head'
      letI : Decidable (tail = tail') := relExprListDecEq tail tail'
      decidable_of_iff (head = head' ∧ tail = tail') (by simp)
  termination_by left right => sizeOf left + sizeOf right
  decreasing_by all_goals simp_all; omega
end

instance : DecidableEq RelExpr := relExprDecEq




/-- Build a finite IN expression. Validation requires a nonempty list. -/
def RelExpr.inValues (arg : RelExpr) (values : List RelExpr) : RelExpr :=
  .inList arg values

/-- Normalize BETWEEN to its two inclusive comparisons. -/
def RelExpr.between (arg lower upper : RelExpr) : RelExpr :=
  .binary .and (.binary .ge arg lower) (.binary .le arg upper)

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
  /-- none follows the database's default; some true is NULLS FIRST. -/
  nullsFirst : Option Bool := none
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
    /-- Nonempty DISTINCT ON keys; mutually exclusive with ordinary DISTINCT. -/
    distinctOn : List RelExpr := []
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

inductive Mutation where
  | insert (query : InsertQuery)
  | update (query : UpdateQuery)
  | delete (query : DeleteQuery)
  deriving Repr, BEq, DecidableEq, Inhabited

def Mutation.table : Mutation → Name
  | .insert query => query.table
  | .update query => query.table
  | .delete query => query.table

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
