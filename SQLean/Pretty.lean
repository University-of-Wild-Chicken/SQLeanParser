import SQLean.AST

/-! Canonical SQL rendering. Identifiers are quoted and strings use doubled-quote
escaping. Rendering does not validate a manually constructed AST.
-/

namespace SQLean

class ToSql (α : Type) where
  toSql : α → String

export ToSql (toSql)

def quoteIdent (name : Name) : String :=
  "\"" ++ name.replace "\"" "\"\"" ++ "\""

instance : ToSql SqlType where
  toSql
    | .int => "INTEGER"
    | .text => "TEXT"
    | .bool => "BOOLEAN"

instance : ToSql Value where
  toSql
    | .int n => toString n
    | .text s => "'" ++ s.replace "'" "''" ++ "'"
    | .bool true => "TRUE"
    | .bool false => "FALSE"

instance : ToSql BinOp where
  toSql
    | .eq => "="
    | .ne => "<>"
    | .lt => "<"
    | .le => "<="
    | .gt => ">"
    | .ge => ">="
    | .and => "AND"
    | .or => "OR"
    | .add => "+"
    | .sub => "-"
    | .mul => "*"
    | .div => "/"

def Expr.toSql : Expr → String
  | .literal value => SQLean.toSql value
  | .column name => quoteIdent name
  | .binary op left right =>
      "(" ++ left.toSql ++ " " ++ SQLean.toSql op ++ " " ++ right.toSql ++ ")"
  | .unary .pos arg => "(+ " ++ arg.toSql ++ ")"
  | .unary .neg arg => "(- " ++ arg.toSql ++ ")"
  | .unary .not arg => "(NOT " ++ arg.toSql ++ ")"

instance : ToSql Expr := ⟨Expr.toSql⟩

instance : ToSql Query where
  toSql query :=
    "SELECT " ++ String.intercalate ", " (query.selectList.map toSql) ++
      " FROM " ++ quoteIdent query.table ++
      (match query.whereClause with
       | none => ""
       | some predicate => " WHERE " ++ toSql predicate) ++ ";"

private def commaSep (items : List String) : String := String.intercalate ", " items

private def whereSql : Option Expr → String
  | none => ""
  | some predicate => " WHERE " ++ toSql predicate

instance : ToSql Projection where
  toSql
    | .all => "*"
    | .expressions items => commaSep (items.map toSql)

instance : ToSql OrderBy where
  toSql order := toSql order.expr ++ (if order.descending then " DESC" else " ASC")

instance : ToSql SelectQuery where
  toSql query :=
    "SELECT " ++ (if query.distinct then "DISTINCT " else "") ++
      toSql query.projection ++ " FROM " ++ quoteIdent query.table ++
      whereSql query.whereClause ++
      (if query.orderBy.isEmpty then "" else " ORDER BY " ++ commaSep (query.orderBy.map toSql)) ++
      (match query.limit with | none => "" | some n => s!" LIMIT {n}") ++
      (match query.offset with | none => "" | some n => s!" OFFSET {n}") ++ ";"

instance : ToSql InsertQuery where
  toSql query :=
    "INSERT INTO " ++ quoteIdent query.table ++
      (match query.columns with
       | none => ""
       | some names => " (" ++ commaSep (names.map quoteIdent) ++ ")") ++
      " VALUES " ++ commaSep (query.rows.map fun row => "(" ++ commaSep (row.map toSql) ++ ")") ++ ";"

instance : ToSql Assignment where
  toSql assignment := quoteIdent assignment.column ++ " = " ++ toSql assignment.value

instance : ToSql UpdateQuery where
  toSql query := "UPDATE " ++ quoteIdent query.table ++ " SET " ++
    commaSep (query.assignments.map toSql) ++ whereSql query.whereClause ++ ";"

instance : ToSql DeleteQuery where
  toSql query := "DELETE FROM " ++ quoteIdent query.table ++ whereSql query.whereClause ++ ";"

instance : ToSql Statement where
  toSql
    | .select query => toSql query
    | .insert query => toSql query
    | .update query => toSql query
    | .delete query => toSql query

end SQLean
