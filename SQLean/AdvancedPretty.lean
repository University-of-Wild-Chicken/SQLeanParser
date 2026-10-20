import SQLean.AdvancedSyntax

/-! Canonical SQL serialization. Every set-operation operand is parenthesized to
preserve both precedence and the scope of ORDER BY/LIMIT and WITH clauses. -/
namespace SQLean.Advanced

private def quoteName (s : String) : String := "\"" ++ s.replace "\"" "\"\"" ++ "\""
private def quoteText (s : String) : String := "'" ++ s.replace "'" "''" ++ "'"
private def comma (xs : List String) : String := String.intercalate ", " xs
private def paren (s : String) : String := "(" ++ s ++ ")"
private def nameList (xs : List Name) : String := paren (comma (xs.map quoteName))

def lockingClauseSql (clause : LockingClause) : String :=
  "FOR " ++ (match clause.strength with
    | .update => "UPDATE" | .noKeyUpdate => "NO KEY UPDATE"
    | .share => "SHARE" | .keyShare => "KEY SHARE") ++
  (if clause.targets.isEmpty then "" else " OF " ++ comma (clause.targets.map quoteName)) ++
  (match clause.waitPolicy with
    | .block => "" | .nowait => " NOWAIT" | .skipLocked => " SKIP LOCKED")

def lockingSql (clauses : List LockingClause) : String :=
  String.join (clauses.map fun clause => " " ++ lockingClauseSql clause)

def IntervalFields.toSql : IntervalFields → String
  | .year => "YEAR" | .month => "MONTH" | .day => "DAY"
  | .hour => "HOUR" | .minute => "MINUTE" | .second => "SECOND"
  | .yearToMonth => "YEAR TO MONTH" | .dayToHour => "DAY TO HOUR"
  | .dayToMinute => "DAY TO MINUTE" | .dayToSecond => "DAY TO SECOND"
  | .hourToMinute => "HOUR TO MINUTE" | .hourToSecond => "HOUR TO SECOND"
  | .minuteToSecond => "MINUTE TO SECOND"

/-- Render lexical argument order exactly. The checked boundary rejects a
malformed argument count before this total printer is used for a certificate. -/
def substringSql (form : SubstringForm) (args : List String) : String :=
  "SUBSTRING(" ++ (match form, args with
    | .from, [subject, start] => subject ++ " FROM " ++ start
    | .forOnly, [subject, count] => subject ++ " FOR " ++ count
    | .fromFor, [subject, start, count] => subject ++ " FROM " ++ start ++ " FOR " ++ count
    | .forFrom, [subject, count, start] => subject ++ " FOR " ++ count ++ " FROM " ++ start
    | .similar, [subject, pattern, escape] => subject ++ " SIMILAR " ++ pattern ++ " ESCAPE " ++ escape
    | _, _ => comma args) ++ ")"

def ContextValue.toSql : ContextValue → String
  | .currentSchema => "CURRENT_SCHEMA" | .currentCatalog => "CURRENT_CATALOG"
  | .currentUser => "CURRENT_USER" | .user => "USER" | .currentRole => "CURRENT_ROLE"
  | .sessionUser => "SESSION_USER" | .systemUser => "SYSTEM_USER"

/-- Modifiers belong to the scalar element declaration. Array brackets follow
the complete declaration, including any time-zone qualifier. -/
def TypeName.toSql (typeName : TypeName) (modifiers : List Nat) : String :=
  let suffix := if modifiers.isEmpty then "" else paren (comma (modifiers.map toString))
  match typeName with
  | .array element => element.toSql modifiers ++ "[]"
  | .smallInt => "SMALLINT" ++ suffix | .int => "INTEGER" ++ suffix
  | .bigInt => "BIGINT" ++ suffix | .text => "TEXT" ++ suffix
  | .name => "NAME" ++ suffix
  | .varchar => "VARCHAR" ++ suffix | .char => "CHAR" ++ suffix
  | .bool => "BOOLEAN" ++ suffix | .real => "REAL" ++ suffix
  | .doublePrecision => "DOUBLE PRECISION" ++ suffix | .numeric => "NUMERIC" ++ suffix
  | .date => "DATE" ++ suffix | .time => "TIME" ++ suffix
  | .timeTZ => "TIME" ++ suffix ++ " WITH TIME ZONE"
  | .timestamp => "TIMESTAMP" ++ suffix
  | .timestampTZ => "TIMESTAMP" ++ suffix ++ " WITH TIME ZONE"
  | .interval => "INTERVAL" ++ suffix | .uuid => "UUID" ++ suffix
  | .intervalRange fields => "INTERVAL " ++ fields.toSql ++ suffix
  | .json => "JSON" ++ suffix | .jsonb => "JSONB" ++ suffix | .bytea => "BYTEA" ++ suffix

def DataType.toSql (type : DataType) : String :=
  type.name.toSql type.modifiers
private def binSql : BinOp → String
  | .eq => "=" | .ne => "<>" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .and => "AND" | .or => "OR" | .add => "+" | .sub => "-" | .mul => "*" | .div => "/"
def ComparisonOp.toSql : ComparisonOp → String
  | .eq => "=" | .ne => "<>" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="

def ArrayQuantifier.toSql : ArrayQuantifier → String
  | .any => "ANY" | .some => "SOME" | .all => "ALL"

def regexOperatorSql (insensitive negated : Bool) : String :=
  (if negated then "!~" else "~") ++ (if insensitive then "*" else "")

def JsonAccessOp.toSql : JsonAccessOp → String
  | .field => "->" | .fieldText => "->>"
  | .path => "#>" | .pathText => "#>>"

def JsonExistenceOp.toSql : JsonExistenceOp → String
  | .key => "?" | .any => "?|" | .all => "?&"

private def aggregateSql : AggregateFn → String
  | .count => "COUNT" | .sum => "SUM" | .avg => "AVG" | .min => "MIN" | .max => "MAX"
private def joinSql : JoinKind → String
  | .inner => "INNER JOIN" | .left => "LEFT JOIN" | .right => "RIGHT JOIN"
  | .full => "FULL JOIN" | .cross => "CROSS JOIN"
private def setSql : SetOp → String
  | .union => "UNION" | .intersect => "INTERSECT" | .except => "EXCEPT"

/- The mutually recursive printer follows strict AST subterms. The size measures
below are used only to prove termination and are erased from executable code.
There is no fuel, truncation, or replacement SQL on any rendering branch.
The five recursion helpers expose equations for structural serialization proofs;
applications should prefer Expr.toSql, Query.toSql, or the checked render API. -/
mutual
  def exprSql (pg : Bool) (expr : Expr) : String :=
    match expr with
    | .literal (.int n) => toString n
    | .literal (.text s) => quoteText s
    | .literal (.bool b) => if b then "TRUE" else "FALSE"
    | .null => "NULL"
    | .contextValue value => value.toSql
    | .decimal raw => raw
    | .parameter (.numbered index) => "$" ++ toString index
    | .parameter (.anonymous index) => if pg then "$" ++ toString index else "?"
    | .column qualifier name schema => (schema.map (fun s => quoteName s ++ ".")).getD "" ++ (qualifier.map (fun q => quoteName q ++ ".")).getD "" ++ quoteName name
    | .binary op l r => paren (exprSql pg l ++ " " ++ binSql op ++ " " ++ exprSql pg r)
    | .concat left right => paren (exprSql pg left ++ " || " ++ exprSql pg right)
    | .quantifiedComparison op quantifier left right =>
        paren (exprSql pg left ++ " " ++ op.toSql ++ " " ++ quantifier.toSql ++
          paren (exprSql pg right))
    | .unary op arg => paren ((match op with | .pos => "+" | .neg => "-" | .not => "NOT ") ++ exprSql pg arg)
    | .countAll => "COUNT(*)"
    | .aggregate fn arg distinct => aggregateSql fn ++ paren ((if distinct then "DISTINCT " else "") ++ exprSql pg arg)
    | .isNull arg negated => paren (exprSql pg arg ++ if negated then " IS NOT NULL" else " IS NULL")
    | .pattern arg pattern insensitive => paren (exprSql pg arg ++ (if insensitive then " ILIKE " else " LIKE ") ++ exprSql pg pattern)
    | .regex arg pattern insensitive negated =>
        paren (exprSql pg arg ++ " " ++ regexOperatorSql insensitive negated ++ " " ++ exprSql pg pattern)
    | .jsonAccess op arg key => paren (exprSql pg arg ++ " " ++ op.toSql ++ " " ++ exprSql pg key)
    | .jsonExistence op arg key => paren (exprSql pg arg ++ " " ++ op.toSql ++ " " ++ exprSql pg key)
    | .containment left right containedBy =>
        paren (exprSql pg left ++ (if containedBy then " <@ " else " @> ") ++ exprSql pg right)
    | .overlap left right => paren (exprSql pg left ++ " && " ++ exprSql pg right)
    | .extract field arg => "EXTRACT(" ++ quoteText field ++ " FROM " ++ exprSql pg arg ++ ")"
    | .substring form args => substringSql form
        (args.attach.map fun (arg : {v : Expr // v ∈ args}) =>
          have : sizeOf arg.val < sizeOf args := List.sizeOf_lt_of_mem arg.property
          exprSql pg arg.val)
    | .cast arg type => "CAST(" ++ exprSql pg arg ++ " AS " ++ type.toSql ++ ")"
    | .subscript base subscripts => paren (exprSql pg base) ++ String.join
        (subscripts.attach.map fun (subscript : {s : Subscript // s ∈ subscripts}) =>
          have : sizeOf subscript.val < sizeOf subscripts := List.sizeOf_lt_of_mem subscript.property
          subscriptSql pg subscript.val)
    | .array elements => "ARRAY[" ++ comma
        (elements.attach.map fun (element : {v : Expr // v ∈ elements}) =>
          have : sizeOf element.val < sizeOf elements := List.sizeOf_lt_of_mem element.property
          exprSql pg element.val) ++ "]"
    | .row elements => "ROW" ++ paren (comma
        (elements.attach.map fun (element : {v : Expr // v ∈ elements}) =>
          have : sizeOf element.val < sizeOf elements := List.sizeOf_lt_of_mem element.property
          exprSql pg element.val))
    | .call name args => String.intercalate "." (name.map quoteName) ++ paren (comma
        (args.attach.map fun (arg : {v : Expr // v ∈ args}) =>
          have : sizeOf arg.val < sizeOf args := List.sizeOf_lt_of_mem arg.property
          exprSql pg arg.val))
    | .namedCall name args => String.intercalate "." (name.map quoteName) ++ paren (comma
        (args.attach.map fun (arg : {v : CallArgument // v ∈ args}) =>
          have : sizeOf arg.val < sizeOf args := List.sizeOf_lt_of_mem arg.property
          callArgumentSql pg arg.val))
    | .coalesce args => "COALESCE" ++ paren (comma
        (args.attach.map fun (arg : {v : Expr // v ∈ args}) =>
          have : sizeOf arg.val < sizeOf args := List.sizeOf_lt_of_mem arg.property
          exprSql pg arg.val))
    | .greatest args => "GREATEST" ++ paren (comma
        (args.attach.map fun (arg : {v : Expr // v ∈ args}) =>
          have : sizeOf arg.val < sizeOf args := List.sizeOf_lt_of_mem arg.property
          exprSql pg arg.val))
    | .least args => "LEAST" ++ paren (comma
        (args.attach.map fun (arg : {v : Expr // v ∈ args}) =>
          have : sizeOf arg.val < sizeOf args := List.sizeOf_lt_of_mem arg.property
          exprSql pg arg.val))
    | .nullIf left right => "NULLIF(" ++ exprSql pg left ++ ", " ++ exprSql pg right ++ ")"
    | .caseExpr operand branches otherwise => paren ("CASE" ++
        (match _h : operand with | none => "" | some arg => " " ++ exprSql pg arg) ++
        String.join (branches.attach.map fun (branch : {b : Expr × Expr // b ∈ branches}) =>
          have : sizeOf branch.val < sizeOf branches := List.sizeOf_lt_of_mem branch.property
          have : sizeOf branch.val.1 < sizeOf branch.val := by cases branch.val; simp; omega
          have : sizeOf branch.val.2 < sizeOf branch.val := by cases branch.val; simp; omega
          " WHEN " ++ exprSql pg branch.val.1 ++ " THEN " ++ exprSql pg branch.val.2) ++
        (match _h : otherwise with | none => "" | some arg => " ELSE " ++ exprSql pg arg) ++ " END")
    | .filteredAggregate aggregate predicate => exprSql pg aggregate ++ " FILTER (WHERE " ++ exprSql pg predicate ++ ")"
    | .inList arg values => paren (exprSql pg arg ++ " IN " ++ paren (comma
        (values.attach.map fun (value : {v : Expr // v ∈ values}) =>
          have : sizeOf value.val < sizeOf values := List.sizeOf_lt_of_mem value.property
          exprSql pg value.val)))
    | .between arg lower upper negated => paren (exprSql pg arg ++
        (if negated then " NOT BETWEEN " else " BETWEEN ") ++ exprSql pg lower ++ " AND " ++ exprSql pg upper)
    | .inQuery arg query => paren (exprSql pg arg ++ " IN " ++ paren (querySql pg query))
    | .exists query => "EXISTS " ++ paren (querySql pg query)
    | .scalarQuery query => paren (querySql pg query)
  termination_by sizeOf expr
  decreasing_by all_goals (simp_all <;> omega)

  /-- One contiguous bracket group belongs to one expression node. Parentheses
  around the base keep nested nodes distinct from adjacent dimensions. -/
  def callArgumentSql (pg : Bool) (arg : CallArgument) : String :=
    match arg with
    | .positional value => exprSql pg value
    | .named name value spelling => quoteName name ++
        (match spelling with | .arrow => " => " | .assignment => " := ") ++ exprSql pg value
  termination_by sizeOf arg
  decreasing_by all_goals (simp_all <;> omega)

  def subscriptSql (pg : Bool) (subscript : Subscript) : String :=
    match subscript with
    | .index expr => "[" ++ exprSql pg expr ++ "]"
    | .slice lower upper => "[" ++
        (match _h : lower with | none => "" | some expr => exprSql pg expr) ++ ":" ++
        (match _h : upper with | none => "" | some expr => exprSql pg expr) ++ "]"
  termination_by sizeOf subscript
  decreasing_by all_goals (simp_all <;> omega)

  def itemSql (pg : Bool) (item : SelectItem) : String :=
    match item with
    | .all qualifier schema => (schema.map (fun s => quoteName s ++ ".")).getD "" ++ (qualifier.map (fun q => quoteName q ++ ".")).getD "" ++ "*"
    | .expression expr alias => exprSql pg expr ++ (alias.map (fun a => " AS " ++ quoteName a)).getD ""
  termination_by sizeOf item
  decreasing_by all_goals (simp_all <;> omega)

  def sourceSql (pg : Bool) (source : From) : String :=
    match source with
    | .table name alias columns schema => (schema.map (fun s => quoteName s ++ ".")).getD "" ++ quoteName name ++
      (alias.map (fun a => " AS " ++ quoteName a)).getD "" ++ (if columns.isEmpty then "" else nameList columns)
    | .derived query alias columns lateral => (if lateral then "LATERAL " else "") ++
      paren (querySql pg query) ++ " AS " ++ quoteName alias ++ (if columns.isEmpty then "" else nameList columns)
    | .join kind left right condition => paren (sourceSql pg left ++ " " ++
      (match condition with | .natural => "NATURAL " | _ => "") ++ joinSql kind ++ " " ++ sourceSql pg right ++
      (match condition with
       | .none | .natural => ""
       | .on expr => " ON " ++ exprSql pg expr
       | .using names => " USING " ++ nameList names))
  termination_by sizeOf source
  decreasing_by all_goals (simp_all <;> omega)

  def selectSql (pg : Bool) (select : Select) : String :=
    "SELECT " ++ (if select.distinct then "DISTINCT " else if select.distinctOn.isEmpty then ""
      else "DISTINCT ON " ++ paren (comma (select.distinctOn.attach.map
        fun (expr : {e : Expr // e ∈ select.distinctOn}) =>
          have : sizeOf expr.val < sizeOf select.distinctOn := List.sizeOf_lt_of_mem expr.property
          exprSql pg expr.val)) ++ " ") ++
    comma (select.items.attach.map fun (item : {i : SelectItem // i ∈ select.items}) =>
      have : sizeOf item.val < sizeOf select.items := List.sizeOf_lt_of_mem item.property
      itemSql pg item.val) ++
    (match _h : select.source with | none => "" | some source => " FROM " ++ sourceSql pg source) ++
    (match _h : select.whereClause with | none => "" | some expr => " WHERE " ++ exprSql pg expr) ++
    (if select.groupBy.isEmpty then "" else " GROUP BY " ++ comma
      (select.groupBy.attach.map fun (expr : {e : Expr // e ∈ select.groupBy}) =>
        have : sizeOf expr.val < sizeOf select.groupBy := List.sizeOf_lt_of_mem expr.property
        exprSql pg expr.val)) ++
    (match _h : select.having with | none => "" | some expr => " HAVING " ++ exprSql pg expr)
  termination_by sizeOf select
  decreasing_by all_goals cases select; simp_all; omega

  def querySql (pg : Bool) (query : Query) : String :=
    (if query.ctes.isEmpty then "" else "WITH " ++ (if query.recursive then "RECURSIVE " else "") ++
      comma (query.ctes.attach.map fun (cte : {c : CTE // c ∈ query.ctes}) =>
        have : sizeOf cte.val < sizeOf query.ctes := List.sizeOf_lt_of_mem cte.property
        have : sizeOf cte.val.query < sizeOf cte.val := by cases cte.val; simp; omega
        quoteName cte.val.name ++ (if cte.val.columns.isEmpty then "" else nameList cte.val.columns) ++
          " AS " ++ paren (querySql pg cte.val.query)) ++ " ") ++
    (match _h : query.body with
     | .select select => selectSql pg select
     | .set op all left right => paren (querySql pg left) ++ " " ++ setSql op ++
         (if all then " ALL " else " ") ++ paren (querySql pg right)) ++
    (if query.orderBy.isEmpty then "" else " ORDER BY " ++ comma
      (query.orderBy.attach.map fun (order : {o : OrderBy // o ∈ query.orderBy}) =>
        have : sizeOf order.val < sizeOf query.orderBy := List.sizeOf_lt_of_mem order.property
        have : sizeOf order.val.expr < sizeOf order.val := by cases order.val; simp; omega
        exprSql pg order.val.expr ++ (if order.val.descending then " DESC" else " ASC") ++
        (order.val.nullsFirst.map (fun first => if first then " NULLS FIRST" else " NULLS LAST")).getD "")) ++
    (if query.offsetFirst then
      (match _h : query.offset with | none => "" | some expr => " OFFSET " ++ exprSql pg expr) ++
      (match _h : query.limit with | none => "" | some expr => " LIMIT " ++ exprSql pg expr)
     else
      (match _h : query.limit with | none => "" | some expr => " LIMIT " ++ exprSql pg expr) ++
      (match _h : query.offset with | none => "" | some expr => " OFFSET " ++ exprSql pg expr)) ++
    lockingSql query.locking
  termination_by sizeOf query
  decreasing_by all_goals cases query; simp_all; omega
end

/-- Render an expression exactly, optionally translating anonymous bindings to PostgreSQL. -/
def Expr.toSql (expr : Expr) (postgresParameters : Bool := false) : String :=
  exprSql postgresParameters expr
/-- Render a query without a statement terminator. -/
def Query.toSql (query : Query) (postgresParameters : Bool := false) : String :=
  querySql postgresParameters query
private def projection (items : List SelectItem) (pg : Bool) : String :=
  comma (items.map fun item => itemSql pg item)
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
