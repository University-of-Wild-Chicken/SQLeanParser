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

def SqlType.toSql : SqlType → String
  | .int => "INTEGER"
  | .text => "TEXT"
  | .bool => "BOOLEAN"
  | .real => "REAL"
  | .nullable base => "NULLABLE(" ++ base.toSql ++ ")"

instance : ToSql SqlType := ⟨SqlType.toSql⟩

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

instance : ToSql AggregateFn where
  toSql
    | .count => "COUNT"
    | .sum => "SUM"
    | .avg => "AVG"
    | .min => "MIN"
    | .max => "MAX"

def RelExpr.toSql : RelExpr → String
  | .literal value => SQLean.toSql value
  | .column qualifier name =>
    (qualifier.map (fun q => quoteIdent q ++ ".")).getD "" ++ quoteIdent name
  | .binary op left right =>
    "(" ++ left.toSql ++ " " ++ SQLean.toSql op ++ " " ++ right.toSql ++ ")"
  | .unary .pos arg => "(+ " ++ arg.toSql ++ ")"
  | .unary .neg arg => "(- " ++ arg.toSql ++ ")"
  | .unary .not arg => "(NOT " ++ arg.toSql ++ ")"
  | .countAll => "COUNT(*)"
  | .aggregate fn arg distinct =>
    SQLean.toSql fn ++ "(" ++ (if distinct then "DISTINCT " else "") ++ arg.toSql ++ ")"
  | .isNull arg negated =>
    "(" ++ arg.toSql ++ (if negated then " IS NOT NULL)" else " IS NULL)")

instance : ToSql RelExpr := ⟨RelExpr.toSql⟩

instance : ToSql SelectItem where
  toSql
    | .all qualifier => (qualifier.map (fun q => quoteIdent q ++ ".")).getD "" ++ "*"
    | .expression expr alias => toSql expr ++ (alias.map (fun a => " AS " ++ quoteIdent a)).getD ""

instance : ToSql RelOrderBy where
  toSql order := toSql order.expr ++ (if order.descending then " DESC" else " ASC")

instance : ToSql JoinKind where
  toSql
    | .inner => "INNER JOIN"
    | .left => "LEFT JOIN"
    | .right => "RIGHT JOIN"
    | .full => "FULL JOIN"
    | .cross => "CROSS JOIN"

mutual
  /-- Render a query body without a terminator, for embedding as a subquery. -/
  def RelQuery.toSqlBody (query : RelQuery) : String :=
    (if query.ctes.isEmpty then "" else "WITH " ++ (if query.recursive then "RECURSIVE " else "") ++ commaSep (query.ctes.attach.map fun (cte : {c : CTE // c ∈ query.ctes}) =>
      have : sizeOf cte.val < sizeOf query.ctes := List.sizeOf_lt_of_mem cte.property
      CTE.toSqlBody cte.val) ++ " ") ++
    "SELECT " ++ (if query.distinct then "DISTINCT " else "") ++
    commaSep (query.selectList.map toSql) ++
    (if query.source.name.isEmpty && query.source.alias.isNone && query.source.derived.isNone
      then "" else " FROM " ++ query.source.toSql) ++
    String.join (query.joins.attach.map fun (join : {j : Join // j ∈ query.joins}) =>
      have : sizeOf join.val < sizeOf query.joins := List.sizeOf_lt_of_mem join.property
      " " ++ join.val.toSql) ++
    (query.whereClause.map (fun e => " WHERE " ++ toSql e)).getD "" ++
    (if query.groupBy.isEmpty then "" else " GROUP BY " ++ commaSep (query.groupBy.map toSql)) ++
    (query.having.map (fun e => " HAVING " ++ toSql e)).getD "" ++
    String.join (query.unions.attach.map fun (branch : {b : UnionBranch // b ∈ query.unions}) =>
      have : sizeOf branch.val < sizeOf query.unions := List.sizeOf_lt_of_mem branch.property
      have : sizeOf branch.val.query < sizeOf branch.val := by cases branch.val; simp
      (if branch.val.all then " UNION ALL " else " UNION ") ++ branch.val.query.toSqlBody) ++
    (if query.orderBy.isEmpty then "" else " ORDER BY " ++ commaSep (query.orderBy.map toSql)) ++
    (query.limit.map (fun n => s!" LIMIT {n}")).getD "" ++
    (query.offset.map (fun n => s!" OFFSET {n}")).getD ""
  termination_by sizeOf query
  decreasing_by all_goals cases query; simp_all; omega

  def TableRef.toSql (table : TableRef) : String :=
    (match _h : table.derived with
     | none => quoteIdent table.name
     | some query => "(" ++ query.toSqlBody ++ ")") ++
    (table.alias.map (fun alias => " AS " ++ quoteIdent alias)).getD ""
  termination_by sizeOf table
  decreasing_by all_goals cases table; simp_all; omega

  def Join.toSql (join : Join) : String :=
    SQLean.toSql join.kind ++ " " ++ join.table.toSql ++
    (join.on.map (fun e => " ON " ++ SQLean.toSql e)).getD ""
  termination_by sizeOf join
  decreasing_by all_goals cases join; simp_all; omega

  def CTE.toSqlBody (cte : CTE) : String :=
    quoteIdent cte.name ++
    (if cte.columns.isEmpty then "" else " (" ++ commaSep (cte.columns.map quoteIdent) ++ ")") ++
    " AS (" ++ cte.query.toSqlBody ++ ")"
  termination_by sizeOf cte
  decreasing_by all_goals cases cte; simp_all; omega
end

instance : ToSql RelQuery where
  toSql query := query.toSqlBody ++ ";"

instance : ToSql Statement where
  toSql
    | .select query => toSql query
    | .insert query => toSql query
    | .update query => toSql query
    | .delete query => toSql query
    | .relational query => toSql query

end SQLean
