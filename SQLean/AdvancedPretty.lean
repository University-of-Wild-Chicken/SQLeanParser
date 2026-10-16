import SQLean.AdvancedSyntax

/-! Canonical SQL serialization. Every set-operation operand is parenthesized to
preserve both precedence and the scope of ORDER BY/LIMIT and WITH clauses. -/
namespace SQLean.Advanced

private def quoteName (s : String) : String := "\"" ++ s.replace "\"" "\"\"" ++ "\""
private def quoteText (s : String) : String := "'" ++ s.replace "'" "''" ++ "'"
private def comma (xs : List String) : String := String.intercalate ", " xs
private def paren (s : String) : String := "(" ++ s ++ ")"
private def nameList (xs : List Name) : String := paren (comma (xs.map quoteName))

def DataType.toSql (type : DataType) : String :=
  (match type.name with
   | .int => "INTEGER" | .bigInt => "BIGINT" | .text => "TEXT" | .varchar => "VARCHAR"
   | .bool => "BOOLEAN" | .real => "REAL" | .doublePrecision => "DOUBLE PRECISION" | .numeric => "NUMERIC") ++
  if type.modifiers.isEmpty then "" else paren (comma (type.modifiers.map toString))
private def binSql : BinOp → String
  | .eq => "=" | .ne => "<>" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .and => "AND" | .or => "OR" | .add => "+" | .sub => "-" | .mul => "*" | .div => "/"
private def aggregateSql : AggregateFn → String
  | .count => "COUNT" | .sum => "SUM" | .avg => "AVG" | .min => "MIN" | .max => "MAX"
private def joinSql : JoinKind → String
  | .inner => "INNER JOIN" | .left => "LEFT JOIN" | .right => "RIGHT JOIN"
  | .full => "FULL JOIN" | .cross => "CROSS JOIN"
private def setSql : SetOp → String
  | .union => "UNION" | .intersect => "INTERSECT" | .except => "EXCEPT"

private def totalDepth (xs : List Nat) : Nat := xs.foldl (· + ·) 0

mutual
  private def exprDepth (expr : Expr) : Nat :=
    4 + match expr with
    | .binary _ left right | .pattern left right _ | .filteredAggregate left right =>
        exprDepth left + exprDepth right
    | .unary _ arg | .aggregate _ arg _ | .isNull arg _ | .cast arg _ => exprDepth arg
    | .inList arg values => exprDepth arg + totalDepth (values.attach.map fun (value : {v : Expr // v ∈ values}) =>
        have : sizeOf value.val < sizeOf values := List.sizeOf_lt_of_mem value.property
        exprDepth value.val)
    | .between arg lower upper _ => exprDepth arg + exprDepth lower + exprDepth upper
    | .inQuery arg query => exprDepth arg + queryDepth query
    | .exists query | .scalarQuery query => queryDepth query
    | _ => 0
  termination_by sizeOf expr
  decreasing_by all_goals (simp_all <;> omega)

  private def itemDepth (item : SelectItem) : Nat :=
    4 + match item with
    | .all _ => 0
    | .expression expr _ => exprDepth expr
  termination_by sizeOf item
  decreasing_by all_goals (simp_all <;> omega)

  private def sourceDepth (source : From) : Nat :=
    4 + match source with
    | .table .. => 0
    | .derived query .. => queryDepth query
    | .join _ left right condition => sourceDepth left + sourceDepth right +
        (match condition with | .on expr => exprDepth expr | _ => 0)
  termination_by sizeOf source
  decreasing_by all_goals (simp_all <;> omega)

  private def selectDepth (select : Select) : Nat :=
    4 + totalDepth (select.items.attach.map fun (item : {i : SelectItem // i ∈ select.items}) =>
      have : sizeOf item.val < sizeOf select.items := List.sizeOf_lt_of_mem item.property
      itemDepth item.val) +
    (match _h : select.source with | none => 0 | some source => sourceDepth source) +
    (match _h : select.whereClause with | none => 0 | some expr => exprDepth expr) +
    totalDepth (select.groupBy.attach.map fun (expr : {e : Expr // e ∈ select.groupBy}) =>
      have : sizeOf expr.val < sizeOf select.groupBy := List.sizeOf_lt_of_mem expr.property
      exprDepth expr.val) +
    (match _h : select.having with | none => 0 | some expr => exprDepth expr) +
    totalDepth (select.distinctOn.attach.map fun (expr : {e : Expr // e ∈ select.distinctOn}) =>
      have : sizeOf expr.val < sizeOf select.distinctOn := List.sizeOf_lt_of_mem expr.property
      exprDepth expr.val)
  termination_by sizeOf select
  decreasing_by all_goals cases select; simp_all; omega

  private def queryDepth (query : Query) : Nat :=
    4 + (match _h : query.body with
      | .select select => selectDepth select
      | .set _ _ left right => queryDepth left + queryDepth right) +
    totalDepth (query.ctes.attach.map fun (cte : {c : CTE // c ∈ query.ctes}) =>
      have : sizeOf cte.val < sizeOf query.ctes := List.sizeOf_lt_of_mem cte.property
      have : sizeOf cte.val.query < sizeOf cte.val := by cases cte.val; simp; omega
      queryDepth cte.val.query) +
    totalDepth (query.orderBy.attach.map fun (order : {o : OrderBy // o ∈ query.orderBy}) =>
      have : sizeOf order.val < sizeOf query.orderBy := List.sizeOf_lt_of_mem order.property
      have : sizeOf order.val.expr < sizeOf order.val := by cases order.val; simp; omega
      exprDepth order.val.expr)
  termination_by sizeOf query
  decreasing_by all_goals cases query; simp_all; omega
end

mutual
  private def exprSql : Nat → Bool → Expr → String
    | 0, _, _ => "NULL"
    | fuel + 1, pg, expr =>
      match expr with
      | .literal (.int n) => toString n
      | .literal (.text s) => quoteText s
      | .literal (.bool b) => if b then "TRUE" else "FALSE"
      | .null => "NULL"
      | .decimal raw => raw
      | .parameter (.numbered index) => "$" ++ toString index
      | .parameter (.anonymous index) => if pg then "$" ++ toString index else "?"
      | .column qualifier name => (qualifier.map (fun q => quoteName q ++ ".")).getD "" ++ quoteName name
      | .binary op l r => paren (exprSql fuel pg l ++ " " ++ binSql op ++ " " ++ exprSql fuel pg r)
      | .unary op arg => paren ((match op with | .pos => "+" | .neg => "-" | .not => "NOT ") ++ exprSql fuel pg arg)
      | .countAll => "COUNT(*)"
      | .aggregate fn arg distinct => aggregateSql fn ++ paren ((if distinct then "DISTINCT " else "") ++ exprSql fuel pg arg)
      | .isNull arg negated => paren (exprSql fuel pg arg ++ if negated then " IS NOT NULL" else " IS NULL")
      | .pattern arg pattern insensitive => paren (exprSql fuel pg arg ++ (if insensitive then " ILIKE " else " LIKE ") ++ exprSql fuel pg pattern)
      | .cast arg type => "CAST(" ++ exprSql fuel pg arg ++ " AS " ++ type.toSql ++ ")"
      | .filteredAggregate aggregate predicate => exprSql fuel pg aggregate ++ " FILTER (WHERE " ++ exprSql fuel pg predicate ++ ")"
      | .inList arg values => paren (exprSql fuel pg arg ++ " IN " ++ paren (comma (values.map (exprSql fuel pg))))
      | .between arg lower upper negated => paren (exprSql fuel pg arg ++
          (if negated then " NOT BETWEEN " else " BETWEEN ") ++ exprSql fuel pg lower ++ " AND " ++ exprSql fuel pg upper)
      | .inQuery arg query => paren (exprSql fuel pg arg ++ " IN " ++ paren (querySql fuel pg query))
      | .exists query => "EXISTS " ++ paren (querySql fuel pg query)
      | .scalarQuery query => paren (querySql fuel pg query)

  private def itemSql : Nat → Bool → SelectItem → String
    | 0, _, _ => "NULL"
    | _ + 1, _, .all qualifier => (qualifier.map (fun q => quoteName q ++ ".")).getD "" ++ "*"
    | fuel + 1, pg, .expression expr alias => exprSql fuel pg expr ++ (alias.map (fun a => " AS " ++ quoteName a)).getD ""

  private def sourceSql : Nat → Bool → From → String
    | 0, _, _ => ""
    | fuel + 1, pg, source =>
      match source with
      | .table name alias columns => quoteName name ++
        (alias.map (fun a => " AS " ++ quoteName a)).getD "" ++ (if columns.isEmpty then "" else nameList columns)
      | .derived query alias columns lateral => (if lateral then "LATERAL " else "") ++
        paren (querySql fuel pg query) ++ " AS " ++ quoteName alias ++ (if columns.isEmpty then "" else nameList columns)
      | .join kind left right condition => paren (sourceSql fuel pg left ++ " " ++
        (match condition with | .natural => "NATURAL " | _ => "") ++ joinSql kind ++ " " ++ sourceSql fuel pg right ++
        (match condition with
         | .none | .natural => ""
         | .on expr => " ON " ++ exprSql fuel pg expr
         | .using names => " USING " ++ nameList names))

  private def selectSql : Nat → Bool → Select → String
    | 0, _, _ => "SELECT NULL"
    | fuel + 1, pg, select =>
      "SELECT " ++ (if select.distinct then "DISTINCT " else if select.distinctOn.isEmpty then ""
        else "DISTINCT ON " ++ paren (comma (select.distinctOn.map (exprSql fuel pg))) ++ " ") ++
      comma (select.items.map (itemSql fuel pg)) ++
      (select.source.map (fun source => " FROM " ++ sourceSql fuel pg source)).getD "" ++
      (select.whereClause.map (fun expr => " WHERE " ++ exprSql fuel pg expr)).getD "" ++
      (if select.groupBy.isEmpty then "" else " GROUP BY " ++ comma (select.groupBy.map (exprSql fuel pg))) ++
      (select.having.map (fun expr => " HAVING " ++ exprSql fuel pg expr)).getD ""

  private def querySql : Nat → Bool → Query → String
    | 0, _, _ => "SELECT NULL"
    | fuel + 1, pg, query =>
      (if query.ctes.isEmpty then "" else "WITH " ++ (if query.recursive then "RECURSIVE " else "") ++
        comma (query.ctes.map (fun cte => quoteName cte.name ++
          (if cte.columns.isEmpty then "" else nameList cte.columns) ++ " AS " ++ paren (querySql fuel pg cte.query))) ++ " ") ++
      (match query.body with
       | .select select => selectSql fuel pg select
       | .set op all left right => paren (querySql fuel pg left) ++ " " ++ setSql op ++
           (if all then " ALL " else " ") ++ paren (querySql fuel pg right)) ++
      (if query.orderBy.isEmpty then "" else " ORDER BY " ++ comma (query.orderBy.map fun order =>
        exprSql fuel pg order.expr ++ (if order.descending then " DESC" else " ASC") ++
        (order.nullsFirst.map (fun first => if first then " NULLS FIRST" else " NULLS LAST")).getD "")) ++
      (query.limit.map (fun n => " LIMIT " ++ toString n)).getD "" ++
      (query.offset.map (fun n => " OFFSET " ++ toString n)).getD ""
end

/-- Render an expression exactly, optionally translating anonymous bindings to PostgreSQL. -/
def Expr.toSql (expr : Expr) (postgresParameters : Bool := false) : String :=
  exprSql (exprDepth expr) postgresParameters expr
/-- Render a query without a statement terminator. -/
def Query.toSql (query : Query) (postgresParameters : Bool := false) : String :=
  querySql (queryDepth query) postgresParameters query
private def projection (items : List SelectItem) (pg : Bool) : String :=
  comma (items.map fun item => itemSql (itemDepth item) pg item)
private def assignmentSql (assignment : Assignment) (pg : Bool) : String :=
  quoteName assignment.column ++ " = " ++ assignment.value.toSql pg
private def returningSql (items : List SelectItem) (pg : Bool) : String :=
  if items.isEmpty then "" else " RETURNING " ++ projection items pg
private def columnSql (column : Column) (pg : Bool) : String :=
  quoteName column.name ++ " " ++ column.type.toSql ++
  (column.nullable.map (fun n => if n then " NULL" else " NOT NULL")).getD "" ++
  (column.defaultValue.map (fun e => " DEFAULT " ++ e.toSql pg)).getD "" ++
  (if column.primaryKey then " PRIMARY KEY" else "") ++ (if column.unique then " UNIQUE" else "")
private def constraintSql : TableConstraint → String
  | .primaryKey columns => "PRIMARY KEY " ++ nameList columns
  | .unique columns => "UNIQUE " ++ nameList columns
private def alterSql (action : AlterAction) (pg : Bool) : String :=
  match action with
  | .addColumn column ifNotExists => "ADD COLUMN " ++ (if ifNotExists then "IF NOT EXISTS " else "") ++ columnSql column pg
  | .dropColumn name ifExists cascade => "DROP COLUMN " ++ (if ifExists then "IF EXISTS " else "") ++ quoteName name ++ (if cascade then " CASCADE" else "")
  | .renameColumn name newName => "RENAME COLUMN " ++ quoteName name ++ " TO " ++ quoteName newName
  | .renameTable newName => "RENAME TO " ++ quoteName newName
  | .setType name type => "ALTER COLUMN " ++ quoteName name ++ " TYPE " ++ type.toSql
  | .setNotNull name => "ALTER COLUMN " ++ quoteName name ++ " SET NOT NULL"
  | .dropNotNull name => "ALTER COLUMN " ++ quoteName name ++ " DROP NOT NULL"
  | .setDefault name value => "ALTER COLUMN " ++ quoteName name ++ " SET DEFAULT " ++ value.toSql pg
  | .dropDefault name => "ALTER COLUMN " ++ quoteName name ++ " DROP DEFAULT"

private def statementSql (statement : Statement) (pg : Bool) : String :=
  match statement with
  | .query query => query.toSql pg
  | .insert insert => "INSERT INTO " ++ quoteName insert.table ++
      (insert.alias.map (fun a => " AS " ++ quoteName a)).getD "" ++
      (if insert.columns.isEmpty then "" else " " ++ nameList insert.columns) ++
      (match insert.source with
       | .defaultValues => " DEFAULT VALUES"
       | .values rows => " VALUES " ++ comma (rows.map fun row => paren (comma (row.map (fun e => e.toSql pg))))
       | .query query => " " ++ query.toSql pg) ++
      (insert.onConflict.map (fun conflict => " ON CONFLICT" ++
        (conflict.target.map (fun
          | .columns columns => " " ++ nameList columns
          | .constraint name => " ON CONSTRAINT " ++ quoteName name)).getD "" ++
        (match conflict.action with
         | .nothing => " DO NOTHING"
         | .update assignments predicate => " DO UPDATE SET " ++ comma (assignments.map (fun a => assignmentSql a pg)) ++
             (predicate.map (fun p => " WHERE " ++ p.toSql pg)).getD ""))).getD "" ++ returningSql insert.returning pg
  | .update update => "UPDATE " ++ quoteName update.table ++
      (update.alias.map (fun a => " AS " ++ quoteName a)).getD "" ++
      " SET " ++ comma (update.assignments.map (fun a => assignmentSql a pg)) ++
      (update.whereClause.map (fun e => " WHERE " ++ e.toSql pg)).getD "" ++ returningSql update.returning pg
  | .delete delete => "DELETE FROM " ++ quoteName delete.table ++
      (delete.alias.map (fun a => " AS " ++ quoteName a)).getD "" ++
      (delete.whereClause.map (fun e => " WHERE " ++ e.toSql pg)).getD "" ++ returningSql delete.returning pg
  | .createTable create => "CREATE TABLE " ++ (if create.ifNotExists then "IF NOT EXISTS " else "") ++
      quoteName create.name ++ " " ++ paren (comma (create.columns.map (fun c => columnSql c pg) ++ create.constraints.map constraintSql))
  | .alterTable name actions => "ALTER TABLE " ++ quoteName name ++ " " ++ comma (actions.map (fun a => alterSql a pg))
  | .dropTable name ifExists cascade => "DROP TABLE " ++ (if ifExists then "IF EXISTS " else "") ++ quoteName name ++ (if cascade then " CASCADE" else "")

/-- Canonical SQL retaining the source parameter style. -/
def render (statement : Statement) : String := statementSql statement false ++ ";"
/-- Canonical PostgreSQL SQL: anonymous `?` parameters become numbered `$n`. -/
def renderPostgres (statement : Statement) : String := statementSql statement true ++ ";"

end SQLean.Advanced
