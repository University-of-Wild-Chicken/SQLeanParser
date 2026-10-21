import SQLean.RenderContract.Profile

/-! Independent SQLite 3.39+ representation domain. No parser, serializer or
catalog validator is imported. This restricts syntax/representation, not SQL
execution semantics or PostgreSQL/SQLite semantic equivalence. -/
namespace SQLean.RenderContract
open Advanced

private def unsupported (feature : String) : Except Failure Unit :=
  .error (.unsupported ⟨"coverage.sqlite." ++ feature,
    "this SQLite rendering profile cannot preserve " ++ feature ++ " without an AST rewrite"⟩)

/-- Compound operands cannot own WITH, ORDER BY, LIMIT, OFFSET or locking in the flat
SQLite syntax. Those clauses may still belong to the enclosing compound. -/
def sqliteBareOperand (query : Advanced.Query) : Bool :=
  query.ctes.isEmpty && !query.recursive && query.orderBy.isEmpty &&
    query.limit.isNone && query.offset.isNone && query.locking.isEmpty && !query.offsetFirst

/-- SQLite assigns native affinity to common numeric/character type spellings.
PostgreSQL temporal, identifier, JSON and binary types are excluded instead of
being silently interpreted as SQLite NUMERIC affinity. -/
def checkSQLiteDataType (type : DataType) : Except Failure Unit :=
  match type.name with
  | .array _ => unsupported "array-type"
  | .date | .time | .timeTZ | .timestamp | .timestampTZ | .interval | .intervalRange _
  | .uuid | .json | .jsonb | .bytea | .name => unsupported "PostgreSQL-type"
  | _ => pure ()

private def sqliteRowOperand : Advanced.Expr → Bool
  | .row _ => true
  | _ => false

mutual
  def checkSQLiteExpr (expr : Advanced.Expr) : Except Failure Unit := do
    match expr with
    | .contextValue _ => unsupported "context-value"
    | .column _ _ schema =>
        if schema.isSome then unsupported "schema-qualification" else pure ()
    | .quantifiedComparison .. => unsupported "array-quantified-comparison"
    | .quantifiedQuery .. => unsupported "query-quantified-comparison"
    | .regex .. => unsupported "regex"
    | .jsonExistence .. => unsupported "json-existence"
    | .jsonAccess .. => unsupported "json-extraction"
    | .containment .. => unsupported "containment"
    | .overlap .. => unsupported "overlap"
    | .extract .. => unsupported "extract"
    | .substring .. => unsupported "substring"
    | .collate .. => unsupported "collation"
    | .binary _ left right | .concat left right | .filteredAggregate left right =>
        checkSQLiteExpr left; checkSQLiteExpr right
    | .pattern left right insensitive =>
        if insensitive then unsupported "ILIKE"
        else checkSQLiteExpr left; checkSQLiteExpr right
    | .distinctFrom left right _ =>
        if sqliteRowOperand left || sqliteRowOperand right then unsupported "row-distinct"
        else checkSQLiteExpr left; checkSQLiteExpr right
    | .isNull arg _ =>
        if sqliteRowOperand arg then unsupported "row-null-test"
        else checkSQLiteExpr arg
    | .unary _ arg | .aggregate _ arg _ =>
        checkSQLiteExpr arg
    | .cast arg type => checkSQLiteDataType type; checkSQLiteExpr arg
    | .array _ => unsupported "array-constructor"
    | .row elements =>
        if elements.length < 2 then unsupported "row-arity"
        else elements.attach.forM fun (element : {v : Advanced.Expr // v ∈ elements}) =>
          have : sizeOf element.val < sizeOf elements := List.sizeOf_lt_of_mem element.property
          checkSQLiteExpr element.val
    | .subscript .. => unsupported "array-subscripting"
    | .namedCall .. => unsupported "named-function-arguments"
    | .call .. | .greatest .. | .least .. => unsupported "scalar-function-signatures"
    | .coalesce args =>
        if args.length < 2 then unsupported "single-argument-COALESCE"
        else args.attach.forM fun (arg : {v : Advanced.Expr // v ∈ args}) =>
          have : sizeOf arg.val < sizeOf args := List.sizeOf_lt_of_mem arg.property
          checkSQLiteExpr arg.val
    | .nullIf left right => checkSQLiteExpr left; checkSQLiteExpr right
    | .caseExpr operand branches otherwise =>
        match _h : operand with | none => pure () | some arg => checkSQLiteExpr arg
        branches.attach.forM fun (branch : {b : Advanced.Expr × Advanced.Expr // b ∈ branches}) => do
          have : sizeOf branch.val < sizeOf branches := List.sizeOf_lt_of_mem branch.property
          have : sizeOf branch.val.1 < sizeOf branch.val := by cases branch.val; simp; omega
          have : sizeOf branch.val.2 < sizeOf branch.val := by cases branch.val; simp; omega
          checkSQLiteExpr branch.val.1
          checkSQLiteExpr branch.val.2
        match _h : otherwise with | none => pure () | some arg => checkSQLiteExpr arg
    | .inList arg values =>
        checkSQLiteExpr arg
        values.attach.forM fun (value : {v : Advanced.Expr // v ∈ values}) =>
          have : sizeOf value.val < sizeOf values := List.sizeOf_lt_of_mem value.property
          checkSQLiteExpr value.val
    | .between arg lower upper _ =>
        checkSQLiteExpr arg; checkSQLiteExpr lower; checkSQLiteExpr upper
    | .inQuery arg query => checkSQLiteExpr arg; checkSQLiteQuery query
    | .exists query | .scalarQuery query => checkSQLiteQuery query
    | _ => pure ()
  termination_by sizeOf expr
  decreasing_by all_goals (simp_all <;> omega)

  def checkSQLiteSource (source : From) : Except Failure Unit := do
    match source with
    | .table _ _ columns schema =>
        if schema.isSome then unsupported "schema-qualification"
        else if columns.isEmpty then pure () else unsupported "relation-column-aliases"
    | .derived query _ columns lateral =>
        if lateral then unsupported "LATERAL"
        else if !columns.isEmpty then unsupported "relation-column-aliases"
        else checkSQLiteQuery query
    | .join _ left right condition =>
        checkSQLiteSource left
        checkSQLiteSource right
        match condition with | .on expr => checkSQLiteExpr expr | _ => pure ()
  termination_by sizeOf source
  decreasing_by all_goals (simp_all <;> omega)

  def checkSQLiteSelect (select : Select) : Except Failure Unit := do
    if !select.distinctOn.isEmpty then unsupported "DISTINCT-ON"
    else
      select.items.attach.forM fun (item : {i : Advanced.SelectItem // i ∈ select.items}) =>
        have : sizeOf item.val < sizeOf select.items := List.sizeOf_lt_of_mem item.property
        match _h : item.val with
        | .all _ schema =>
            if schema.isSome then unsupported "schema-qualification" else pure ()
        | .expression expr _ => checkSQLiteExpr expr
      match _h : select.source with
      | none => pure () | some source => checkSQLiteSource source
      match _h : select.whereClause with
      | none => pure () | some expr => checkSQLiteExpr expr
      select.groupBy.attach.forM fun (expr : {e : Advanced.Expr // e ∈ select.groupBy}) =>
        have : sizeOf expr.val < sizeOf select.groupBy := List.sizeOf_lt_of_mem expr.property
        checkSQLiteExpr expr.val
      match _h : select.having with
      | none => pure () | some expr => checkSQLiteExpr expr
  termination_by sizeOf select
  decreasing_by all_goals cases select; simp_all; omega

  def checkSQLiteQuery (query : Advanced.Query) : Except Failure Unit := do
    if !query.locking.isEmpty then unsupported "row-locking"
    else if query.offsetFirst then unsupported "OFFSET-first"
    else if query.offset.isSome && query.limit.isNone then unsupported "OFFSET-without-LIMIT"
    else
      query.ctes.attach.forM fun (cte : {c : Advanced.CTE // c ∈ query.ctes}) =>
        have : sizeOf cte.val < sizeOf query.ctes := List.sizeOf_lt_of_mem cte.property
        have : sizeOf cte.val.query < sizeOf cte.val := by cases cte.val; simp; omega
        checkSQLiteQuery cte.val.query
      match _h : query.body with
      | .select select => checkSQLiteSelect select
      | .set op all left right =>
          if all && op != .union then unsupported "INTERSECT-or-EXCEPT-ALL"
          else if !sqliteBareOperand left || !sqliteBareOperand right then
            unsupported "operand-local-clauses"
          else
            match right.body with
            | .set .. => unsupported "right-nested-compound"
            | .select _ =>
                checkSQLiteQuery left
                checkSQLiteQuery right
      query.orderBy.attach.forM fun (order : {o : Advanced.OrderBy // o ∈ query.orderBy}) =>
        have : sizeOf order.val < sizeOf query.orderBy := List.sizeOf_lt_of_mem order.property
        have : sizeOf order.val.expr < sizeOf order.val := by cases order.val; simp; omega
        checkSQLiteExpr order.val.expr
      match _h : query.limit with
      | none => pure () | some expr => checkSQLiteExpr expr
      match _h : query.offset with
      | none => pure () | some expr => checkSQLiteExpr expr
  termination_by sizeOf query
  decreasing_by all_goals cases query; simp_all; omega
end

end SQLean.RenderContract
