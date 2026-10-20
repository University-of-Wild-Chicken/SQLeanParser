import SQLean.AdvancedPretty

/-! SQLite serialization of the independently restricted representable domain.
Compound operators are printed as left-associated flat sequences; the checked
boundary rejects right-nested operands and operand-owned clauses rather than
rewriting them into derived SELECTs. Numbered slots use native SQLite ?NNN. -/
namespace SQLean.Advanced.SQLite

private def quoteName (s : String) : String := "\"" ++ s.replace "\"" "\"\"" ++ "\""
private def quoteText (s : String) : String := "'" ++ s.replace "'" "''" ++ "'"
private def comma (xs : List String) : String := String.intercalate ", " xs
private def paren (s : String) : String := "(" ++ s ++ ")"
private def nameList (xs : List Name) : String := paren (comma (xs.map quoteName))

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

/- The mutually recursive printer follows strict AST subterms. The size measures
below are used only to prove termination and are erased from executable code.
There is no fuel, truncation, or replacement SQL on any rendering branch.
The five recursion helpers expose equations for structural serialization proofs;
applications should prefer Expr.toSql, Query.toSql, or the checked render API. -/
mutual
  def exprSql (expr : Expr) : String :=
    match expr with
    | .literal (.int n) => toString n
    | .literal (.text s) => quoteText s
    | .literal (.bool b) => if b then "TRUE" else "FALSE"
    | .null => "NULL"
    | .decimal raw => raw
    | .parameter (.numbered index) => "?" ++ toString index
    | .parameter (.anonymous index) => "?" ++ toString index
    | .column qualifier name => (qualifier.map (fun q => quoteName q ++ ".")).getD "" ++ quoteName name
    | .binary op l r => paren (exprSql l ++ " " ++ binSql op ++ " " ++ exprSql r)
    | .concat left right => paren (exprSql left ++ " || " ++ exprSql right)
    -- Excluded by the checked SQLite profile; the total spelling is retained
    -- solely for structural laws over every finite advanced AST.
    | .quantifiedComparison op quantifier left right =>
        paren (exprSql left ++ " " ++ op.toSql ++ " " ++ quantifier.toSql ++ paren (exprSql right))
    | .unary op arg => paren ((match op with | .pos => "+" | .neg => "-" | .not => "NOT ") ++ exprSql arg)
    | .countAll => "COUNT(*)"
    | .aggregate fn arg distinct => aggregateSql fn ++ paren ((if distinct then "DISTINCT " else "") ++ exprSql arg)
    | .isNull arg negated => paren (exprSql arg ++ if negated then " IS NOT NULL" else " IS NULL")
    | .pattern arg pattern insensitive => paren (exprSql arg ++ (if insensitive then " ILIKE " else " LIKE ") ++ exprSql pattern)
    -- Kept total for structural serialization laws; checked SQLite rendering
    -- excludes PostgreSQL regex operators before exposing this spelling.
    | .regex arg pattern insensitive negated =>
        paren (exprSql arg ++ " " ++ regexOperatorSql insensitive negated ++ " " ++ exprSql pattern)
    -- The PostgreSQL extraction operators require a separate SQLite contract,
    -- even where SQLite recognizes the same arrow spelling.
    | .jsonAccess op arg key => paren (exprSql arg ++ " " ++ op.toSql ++ " " ++ exprSql key)
    | .cast arg type => "CAST(" ++ exprSql arg ++ " AS " ++ type.toSql ++ ")"
    -- Excluded by SQLite admissibility; this total structural spelling is only
    -- used by serialization laws over arbitrary finite ASTs.
    | .subscript base subscripts => paren (exprSql base) ++ String.join
        (subscripts.attach.map fun (subscript : {s : Subscript // s ∈ subscripts}) =>
          have : sizeOf subscript.val < sizeOf subscripts := List.sizeOf_lt_of_mem subscript.property
          subscriptSql subscript.val)
    -- The checked SQLite boundary excludes this constructor. Keeping a total,
    -- structural spelling here does not assert SQLite syntax support.
    | .array elements => "ARRAY[" ++ comma
        (elements.attach.map fun (element : {v : Expr // v ∈ elements}) =>
          have : sizeOf element.val < sizeOf elements := List.sizeOf_lt_of_mem element.property
          exprSql element.val) ++ "]"
    | .row elements => paren (comma
        (elements.attach.map fun (element : {v : Expr // v ∈ elements}) =>
          have : sizeOf element.val < sizeOf elements := List.sizeOf_lt_of_mem element.property
          exprSql element.val))
    | .call name args => String.intercalate "." (name.map quoteName) ++ paren (comma
        (args.attach.map fun (arg : {v : Expr // v ∈ args}) =>
          have : sizeOf arg.val < sizeOf args := List.sizeOf_lt_of_mem arg.property
          exprSql arg.val))
    | .coalesce args => "COALESCE" ++ paren (comma
        (args.attach.map fun (arg : {v : Expr // v ∈ args}) =>
          have : sizeOf arg.val < sizeOf args := List.sizeOf_lt_of_mem arg.property
          exprSql arg.val))
    | .greatest args => "GREATEST" ++ paren (comma
        (args.attach.map fun (arg : {v : Expr // v ∈ args}) =>
          have : sizeOf arg.val < sizeOf args := List.sizeOf_lt_of_mem arg.property
          exprSql arg.val))
    | .least args => "LEAST" ++ paren (comma
        (args.attach.map fun (arg : {v : Expr // v ∈ args}) =>
          have : sizeOf arg.val < sizeOf args := List.sizeOf_lt_of_mem arg.property
          exprSql arg.val))
    | .nullIf left right => "NULLIF(" ++ exprSql left ++ ", " ++ exprSql right ++ ")"
    | .caseExpr operand branches otherwise => paren ("CASE" ++
        (match _h : operand with | none => "" | some arg => " " ++ exprSql arg) ++
        String.join (branches.attach.map fun (branch : {b : Expr × Expr // b ∈ branches}) =>
          have : sizeOf branch.val < sizeOf branches := List.sizeOf_lt_of_mem branch.property
          have : sizeOf branch.val.1 < sizeOf branch.val := by cases branch.val; simp; omega
          have : sizeOf branch.val.2 < sizeOf branch.val := by cases branch.val; simp; omega
          " WHEN " ++ exprSql branch.val.1 ++ " THEN " ++ exprSql branch.val.2) ++
        (match _h : otherwise with | none => "" | some arg => " ELSE " ++ exprSql arg) ++ " END")
    | .filteredAggregate aggregate predicate => exprSql aggregate ++ " FILTER (WHERE " ++ exprSql predicate ++ ")"
    | .inList arg values => paren (exprSql arg ++ " IN " ++ paren (comma
        (values.attach.map fun (value : {v : Expr // v ∈ values}) =>
          have : sizeOf value.val < sizeOf values := List.sizeOf_lt_of_mem value.property
          exprSql value.val)))
    | .between arg lower upper negated => paren (exprSql arg ++
        (if negated then " NOT BETWEEN " else " BETWEEN ") ++ exprSql lower ++ " AND " ++ exprSql upper)
    | .inQuery arg query => paren (exprSql arg ++ " IN " ++ paren (querySql query))
    | .exists query => "EXISTS " ++ paren (querySql query)
    | .scalarQuery query => paren (querySql query)
  termination_by sizeOf expr
  decreasing_by all_goals (simp_all <;> omega)

  def subscriptSql (subscript : Subscript) : String :=
    match subscript with
    | .index expr => "[" ++ exprSql expr ++ "]"
    | .slice lower upper => "[" ++
        (match _h : lower with | none => "" | some expr => exprSql expr) ++ ":" ++
        (match _h : upper with | none => "" | some expr => exprSql expr) ++ "]"
  termination_by sizeOf subscript
  decreasing_by all_goals (simp_all <;> omega)

  def itemSql (item : SelectItem) : String :=
    match item with
    | .all qualifier => (qualifier.map (fun q => quoteName q ++ ".")).getD "" ++ "*"
    | .expression expr alias => exprSql expr ++ (alias.map (fun a => " AS " ++ quoteName a)).getD ""
  termination_by sizeOf item
  decreasing_by all_goals (simp_all <;> omega)

  def sourceSql (source : From) : String :=
    match source with
    | .table name alias columns => quoteName name ++
      (alias.map (fun a => " AS " ++ quoteName a)).getD "" ++ (if columns.isEmpty then "" else nameList columns)
    | .derived query alias columns lateral => (if lateral then "LATERAL " else "") ++
      paren (querySql query) ++ " AS " ++ quoteName alias ++ (if columns.isEmpty then "" else nameList columns)
    | .join kind left right condition => paren (sourceSql left ++ " " ++
      (match condition with | .natural => "NATURAL " | _ => "") ++ joinSql kind ++ " " ++ sourceSql right ++
      (match condition with
       | .none | .natural => ""
       | .on expr => " ON " ++ exprSql expr
       | .using names => " USING " ++ nameList names))
  termination_by sizeOf source
  decreasing_by all_goals (simp_all <;> omega)

  def selectSql (select : Select) : String :=
    "SELECT " ++ (if select.distinct then "DISTINCT " else if select.distinctOn.isEmpty then ""
      else "DISTINCT ON " ++ paren (comma (select.distinctOn.attach.map
        fun (expr : {e : Expr // e ∈ select.distinctOn}) =>
          have : sizeOf expr.val < sizeOf select.distinctOn := List.sizeOf_lt_of_mem expr.property
          exprSql expr.val)) ++ " ") ++
    comma (select.items.attach.map fun (item : {i : SelectItem // i ∈ select.items}) =>
      have : sizeOf item.val < sizeOf select.items := List.sizeOf_lt_of_mem item.property
      itemSql item.val) ++
    (match _h : select.source with | none => "" | some source => " FROM " ++ sourceSql source) ++
    (match _h : select.whereClause with | none => "" | some expr => " WHERE " ++ exprSql expr) ++
    (if select.groupBy.isEmpty then "" else " GROUP BY " ++ comma
      (select.groupBy.attach.map fun (expr : {e : Expr // e ∈ select.groupBy}) =>
        have : sizeOf expr.val < sizeOf select.groupBy := List.sizeOf_lt_of_mem expr.property
        exprSql expr.val)) ++
    (match _h : select.having with | none => "" | some expr => " HAVING " ++ exprSql expr)
  termination_by sizeOf select
  decreasing_by all_goals cases select; simp_all; omega

  def querySql (query : Query) : String :=
    (if query.ctes.isEmpty then "" else "WITH " ++ (if query.recursive then "RECURSIVE " else "") ++
      comma (query.ctes.attach.map fun (cte : {c : CTE // c ∈ query.ctes}) =>
        have : sizeOf cte.val < sizeOf query.ctes := List.sizeOf_lt_of_mem cte.property
        have : sizeOf cte.val.query < sizeOf cte.val := by cases cte.val; simp; omega
        quoteName cte.val.name ++ (if cte.val.columns.isEmpty then "" else nameList cte.val.columns) ++
          " AS " ++ paren (querySql cte.val.query)) ++ " ") ++
    (match _h : query.body with
     | .select select => selectSql select
     | .set op all left right => querySql left ++ " " ++ setSql op ++
         (if all then " ALL " else " ") ++ querySql right) ++
    (if query.orderBy.isEmpty then "" else " ORDER BY " ++ comma
      (query.orderBy.attach.map fun (order : {o : OrderBy // o ∈ query.orderBy}) =>
        have : sizeOf order.val < sizeOf query.orderBy := List.sizeOf_lt_of_mem order.property
        have : sizeOf order.val.expr < sizeOf order.val := by cases order.val; simp; omega
        exprSql order.val.expr ++ (if order.val.descending then " DESC" else " ASC") ++
        (order.val.nullsFirst.map (fun first => if first then " NULLS FIRST" else " NULLS LAST")).getD "")) ++
    (if query.offsetFirst then
      (match _h : query.offset with | none => "" | some expr => " OFFSET " ++ exprSql expr) ++
      (match _h : query.limit with | none => "" | some expr => " LIMIT " ++ exprSql expr)
     else
      (match _h : query.limit with | none => "" | some expr => " LIMIT " ++ exprSql expr) ++
      (match _h : query.offset with | none => "" | some expr => " OFFSET " ++ exprSql expr)) ++
    lockingSql query.locking
  termination_by sizeOf query
  decreasing_by all_goals cases query; simp_all; omega
end


end SQLean.Advanced.SQLite

namespace SQLean.Advanced

/-- Low-level SQLite query printer; use RenderContract.check for coverage evidence. -/
def Query.toSQLite (query : Query) : String := SQLite.querySql query

def renderSQLite (query : Query) : String := query.toSQLite ++ ";"

end SQLean.Advanced
