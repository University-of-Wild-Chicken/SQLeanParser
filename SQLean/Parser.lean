import SQLean.Lexer

/-! Total, position-aware parsers for the SELECT, CRUD, and relational grammars in `SQLean.AST`.
Recursion is bounded by a budget derived from the token count. The public entry
points consume the entire input, including at most one optional semicolon.
-/

namespace SQLean
namespace Parser

private abbrev P (α : Type) := StateT (List Token) (Except ParseError) α

private def peek : P Token := do
  return (← get).headD ⟨.eof, {}⟩

private def fail (message : String) : P α := do
  let token ← peek
  throw ⟨token.position, message⟩

private def advance : P Unit := modify List.tail

private def accept (kind : TokenKind) : P Bool := do
  if (← peek).kind == kind then
    advance
    return true
  return false

private def expect (kind : TokenKind) (description : String) : P Unit := do
  unless ← accept kind do
    fail s!"expected {description}"

private def keyword (word : String) : P Unit := expect (.word word) s!"'{word}'"
private def symbol (text : String) : P Unit := expect (.symbol text) s!"'{text}'"

/-- SQL keywords and unsupported literal names cannot be unquoted identifiers. -/
def reservedWords : List String :=
  ["select", "from", "where", "and", "or", "not", "true", "false", "null",
   "create", "table", "drop", "insert", "into", "values", "update", "set",
   "delete", "begin", "transaction", "commit", "rollback", "int", "integer",
   "text", "bool", "boolean"]

/-- Additional reserved words in the CRUD grammar. The original SELECT parser
keeps its original identifier rules. -/
def crudReservedWords : List String :=
  reservedWords ++ ["distinct", "order", "by", "asc", "desc", "limit", "offset", "default"]

/-- Clause and join keywords for the relational SELECT grammar. -/
def relationalReservedWords : List String :=
  crudReservedWords ++ ["as", "join", "inner", "left", "right", "full", "outer", "cross",
    "on", "group", "having", "is", "natural", "using", "with", "recursive",
    "union", "all", "intersect", "except"]

private def relationalIdentifier : P Name := do
  match (← peek).kind with
  | .quotedIdent name => advance; return name
  | .word name =>
    if relationalReservedWords.contains name then
      fail s!"expected identifier; '{name}' is reserved (use double quotes)"
    else
      advance
      return name
  | _ => fail "expected identifier"

private def identifier (extended : Bool := false) : P Name := do
  match (← peek).kind with
  | .quotedIdent name => advance; return name
  | .word name =>
    if (if extended then crudReservedWords else reservedWords).contains name then
      fail s!"expected identifier; '{name}' is reserved (use double quotes)"
    else
      advance
      return name
  | _ => fail "expected identifier"

private def binaryOperator (extended : Bool) : TokenKind → Option (BinOp × Nat)
  | .word "or" => some (.or, 1)
  | .word "and" => some (.and, 2)
  | .symbol "=" => some (.eq, 3)
  | .symbol "<>" => some (.ne, 3)
  | .symbol "!=" => if extended then some (.ne, 3) else none
  | .symbol "<" => some (.lt, 3)
  | .symbol "<=" => some (.le, 3)
  | .symbol ">" => some (.gt, 3)
  | .symbol ">=" => some (.ge, 3)
  | .symbol "+" => some (.add, 4)
  | .symbol "-" => some (.sub, 4)
  | .symbol "*" => some (.mul, 5)
  | .symbol "/" => some (.div, 5)
  | _ => none

mutual
  private def expression (fuel : Nat) (minPrecedence : Nat := 0)
      (extended : Bool := false) : P Expr :=
    match fuel with
    | 0 => fail "expression nesting exceeds parser budget"
    | fuel + 1 => do
      let first ← primary fuel minPrecedence extended
      binaryTail fuel minPrecedence false first extended

  private def primary (fuel minPrecedence : Nat) (extended : Bool) : P Expr :=
    match fuel with
    | 0 => fail "expression nesting exceeds parser budget"
    | fuel + 1 => do
      match (← peek).kind with
      | .number value => advance; return .literal (.int value)
      | .string value => advance; return .literal (.text value)
      | .word "true" | .word "false" =>
        if extended then
          let value := (← peek).kind == .word "true"
          advance
          return .literal (.bool value)
        else return .column (← identifier)
      | .word "not" =>
        if extended && minPrecedence <= 3 then
          advance
          return .unary .not (← expression fuel 3 extended)
        else return .column (← identifier extended)
      | .symbol "+" | .symbol "-" =>
        if extended then
          let op := if (← peek).kind == .symbol "+" then UnOp.pos else UnOp.neg
          advance
          return .unary op (← expression fuel 6 extended)
        else fail "expected identifier, integer, string, or parenthesized expression"
      | .symbol "(" =>
        advance
        let inner ← expression fuel 0 extended
        symbol ")"
        return inner
      | .word _ | .quotedIdent _ => return .column (← identifier extended)
      | _ => fail "expected identifier, integer, string, or parenthesized expression"

  private def binaryTail (fuel : Nat) (minPrecedence : Nat) (seenComparison : Bool)
      (left : Expr) (extended : Bool) : P Expr :=
    match fuel with
    | 0 => fail "expression length exceeds parser budget"
    | fuel + 1 => do
      match binaryOperator extended (← peek).kind with
      | some (op, precedence) =>
        if precedence < minPrecedence then return left
        if precedence == 3 && seenComparison then
          fail "comparison operators cannot be chained; use parentheses or AND"
        advance
        let right ← expression fuel (precedence + 1) extended
        binaryTail fuel minPrecedence (seenComparison || precedence == 3)
          (.binary op left right) extended
      | none => return left
end

private def selectTail (fuel : Nat) (expressionBudget : Nat)
    (reversed : List Expr) : P (List Expr) :=
  match fuel with
  | 0 => fail "select list length exceeds parser budget"
  | fuel + 1 => do
    if ← accept (.symbol ",") then
      let value ← expression expressionBudget
      selectTail fuel expressionBudget (value :: reversed)
    else
      return reversed.reverse

private def query (budget : Nat) : P Query := do
  keyword "select"
  let first ← expression budget
  let selectList ← selectTail budget budget [first]
  keyword "from"
  let table ← identifier
  let whereClause ← if ← accept (.word "where") then
    pure (some (← expression budget))
  else pure none
  let _ ← accept (.symbol ";")
  unless (← peek).kind == .eof do
    fail "expected end of input after SELECT query"
  return ⟨table, selectList, whereClause⟩

private def commaTail (description : String) (fuel : Nat) (item : P α)
    (reversed : List α) : P (List α) :=
  match fuel with
  | 0 => fail s!"{description} length exceeds parser budget"
  | fuel + 1 => do
    if ← accept (.symbol ",") then
      let next ← item
      commaTail description fuel item (next :: reversed)
    else
      return reversed.reverse

private def commaList (description : String) (budget : Nat) (item : P α) : P (List α) := do
  let first ← item
  commaTail description budget item [first]

private def whereClause (budget : Nat) : P (Option Expr) := do
  if ← accept (.word "where") then
    return some (← expression budget 0 true)
  return none

private def natural (description : String) : P Nat := do
  match (← peek).kind with
  | .number value => advance; return value
  | _ => fail s!"expected nonnegative integer for {description}"

private def orderItem (budget : Nat) : P OrderBy := do
  let expr ← expression budget 0 true
  let descending ← if ← accept (.word "desc") then pure true else do
    let _ ← accept (.word "asc")
    pure false
  return { expr, descending }

private def selectStatement (budget : Nat) : P SelectQuery := do
  keyword "select"
  let distinct ← accept (.word "distinct")
  let projection : Projection ← if ← accept (.symbol "*") then pure Projection.all else do
    pure (.expressions (← commaList "select list" budget (expression budget 0 true)))
  keyword "from"
  let table ← identifier true
  let whereClause ← whereClause budget
  let orderBy ← if ← accept (.word "order") then do
    keyword "by"
    commaList "ORDER BY list" budget (orderItem budget)
  else pure []
  let limit ← if ← accept (.word "limit") then
    pure (some (← natural "LIMIT"))
  else pure none
  let offset ← if limit.isSome && (← accept (.word "offset")) then
    pure (some (← natural "OFFSET"))
  else pure none
  return { table, projection, whereClause, distinct, orderBy, limit, offset }

private def aggregateFn : String → Option AggregateFn
  | "count" => some .count
  | "sum" => some .sum
  | "avg" => some .avg
  | "min" => some .min
  | "max" => some .max
  | _ => none

mutual
  private def relationalExpression (fuel : Nat) (minPrecedence : Nat := 0) : P RelExpr :=
    match fuel with
    | 0 => fail "expression nesting exceeds parser budget"
    | fuel + 1 => do
      let first ← relationalPrimary fuel minPrecedence
      relationalBinaryTail fuel minPrecedence false first

  private def relationalPrimary (fuel minPrecedence : Nat) : P RelExpr :=
    match fuel with
    | 0 => fail "expression nesting exceeds parser budget"
    | fuel + 1 => do
      match (← peek).kind with
      | .number value => advance; return .literal (.int value)
      | .string value => advance; return .literal (.text value)
      | .word "true" | .word "false" =>
        let value := (← peek).kind == .word "true"
        advance
        return .literal (.bool value)
      | .word "not" =>
        if minPrecedence <= 3 then
          advance
          return .unary .not (← relationalExpression fuel 3)
        else fail "NOT must precede a comparison or parenthesized expression"
      | .symbol "+" | .symbol "-" =>
        let op := if (← peek).kind == .symbol "+" then UnOp.pos else UnOp.neg
        advance
        return .unary op (← relationalExpression fuel 6)
      | .symbol "(" =>
        advance
        let inner ← relationalExpression fuel
        symbol ")"
        return inner
      | .word name =>
        let next := ((← get).drop 1).headD ⟨.eof, {}⟩
        match aggregateFn name with
        | some fn =>
          if next.kind == .symbol "(" then
            advance
            symbol "("
            let distinct ← accept (.word "distinct")
            if ← accept (.symbol "*") then
              if fn != .count || distinct then
                fail "only COUNT(*) accepts a wildcard, without DISTINCT"
              symbol ")"
              return .countAll
            let arg ← relationalExpression fuel
            symbol ")"
            return .aggregate fn arg distinct
          else relationalColumn
        | none => relationalColumn
      | .quotedIdent _ => relationalColumn
      | _ => fail "expected column, literal, aggregate, or parenthesized expression"

  private def relationalBinaryTail (fuel : Nat) (minPrecedence : Nat)
      (seenComparison : Bool) (left : RelExpr) : P RelExpr :=
    match fuel with
    | 0 => fail "expression length exceeds parser budget"
    | fuel + 1 => do
      if (← peek).kind == .word "is" then
        if minPrecedence > 3 then return left
        if seenComparison then
          fail "comparison operators cannot be chained; use parentheses or AND"
        advance
        let negated ← accept (.word "not")
        keyword "null"
        relationalBinaryTail fuel minPrecedence true (.isNull left negated)
      else
        match binaryOperator true (← peek).kind with
        | some (op, precedence) =>
          if precedence < minPrecedence then return left
          if precedence == 3 && seenComparison then
            fail "comparison operators cannot be chained; use parentheses or AND"
          advance
          let right ← relationalExpression fuel (precedence + 1)
          relationalBinaryTail fuel minPrecedence (seenComparison || precedence == 3)
            (.binary op left right)
        | none => return left

  private def relationalColumn : P RelExpr := do
    let first ← relationalIdentifier
    if ← accept (.symbol ".") then
      return .column (some first) (← relationalIdentifier)
    return .column none first
end

private def optionalAlias : P (Option Name) := do
  if ← accept (.word "as") then return some (← relationalIdentifier)
  match (← peek).kind with
  | .quotedIdent _ => return some (← relationalIdentifier)
  | .word name =>
    if relationalReservedWords.contains name then return none
    return some (← relationalIdentifier)
  | _ => return none

private def relationalSelectItem (budget : Nat) : P SelectItem := do
  if ← accept (.symbol "*") then return .all none
  let tokens ← get
  match tokens with
  | first :: dot :: star :: _ =>
    let isName := match first.kind with
      | .word _ | .quotedIdent _ => true
      | _ => false
    if isName && dot.kind == .symbol "." && star.kind == .symbol "*" then
      let qualifier ← relationalIdentifier
      symbol "."
      symbol "*"
      return .all (some qualifier)
  | _ => pure ()
  let expr ← relationalExpression budget
  return .expression expr (← optionalAlias)

private def joinKind : P (Option JoinKind) := do
  if ← accept (.word "join") then return some .inner
  if ← accept (.word "inner") then
    keyword "join"
    return some .inner
  if ← accept (.word "cross") then
    keyword "join"
    return some .cross
  let kind ← match (← peek).kind with
    | .word "left" => advance; pure (some JoinKind.left)
    | .word "right" => advance; pure (some JoinKind.right)
    | .word "full" => advance; pure (some JoinKind.full)
    | _ => pure none
  match kind with
  | none => return none
  | some kind =>
    let _ ← accept (.word "outer")
    keyword "join"
    return some kind

private def relationalOrderItem (budget : Nat) : P RelOrderBy := do
  let expr ← relationalExpression budget
  let descending ← if ← accept (.word "desc") then pure true else do
    let _ ← accept (.word "asc")
    pure false
  return { expr, descending }

mutual
  private def relationalSelect (fuel : Nat) : P RelQuery :=
    match fuel with
    | 0 => fail "query nesting exceeds parser budget"
    | budget + 1 => do
      let (recursive, ctes) ← if ← accept (.word "with") then do
        let recursive ← accept (.word "recursive")
        pure (recursive, ← cteList budget [])
      else pure (false, [])
      let first ← relationalSelectCore budget
      let unions ← relationalUnionTail budget []
      let orderBy ← if ← accept (.word "order") then do
        keyword "by"
        commaList "ORDER BY list" budget (relationalOrderItem budget)
      else pure []
      let limit ← if ← accept (.word "limit") then
        pure (some (← natural "LIMIT"))
      else pure none
      let offset ← if limit.isSome && (← accept (.word "offset")) then
        pure (some (← natural "OFFSET"))
      else pure none
      return { first with ctes, recursive, unions, orderBy, limit, offset }

  /-- An arm stops before set operations and final sorting/pagination. -/
  private def relationalSelectCore (fuel : Nat) : P RelQuery :=
    match fuel with
    | 0 => fail "query nesting exceeds parser budget"
    | budget + 1 => do
      keyword "select"
      let distinct ← accept (.word "distinct")
      let selectList ← commaList "select list" budget (relationalSelectItem budget)
      let hasFrom ← accept (.word "from")
      let source ← if hasFrom then relationalTableRef budget else pure { name := "" }
      let joins ← if hasFrom then relationalJoinTail budget [] else pure []
      let whereClause ← if ← accept (.word "where") then
        pure (some (← relationalExpression budget))
      else pure none
      let groupBy ← if ← accept (.word "group") then do
        keyword "by"
        commaList "GROUP BY list" budget (relationalExpression budget)
      else pure []
      let having ← if ← accept (.word "having") then
        pure (some (← relationalExpression budget))
      else pure none
      return { source, selectList, joins, whereClause, groupBy, having, distinct }

  private def relationalUnionTail (fuel : Nat) (reversed : List UnionBranch) : P (List UnionBranch) :=
    match fuel with
    | 0 => fail "UNION list length exceeds parser budget"
    | fuel + 1 => do
      if ← accept (.word "union") then
        let all ← accept (.word "all")
        let query ← relationalSelectCore fuel
        relationalUnionTail fuel ({ all, query } :: reversed)
      else return reversed.reverse

  private def relationalTableRef (fuel : Nat) : P TableRef :=
    match fuel with
    | 0 => fail "table expression nesting exceeds parser budget"
    | fuel + 1 => do
      if ← accept (.symbol "(") then
        let derived ← relationalSelect fuel
        symbol ")"
        let alias ← optionalAlias
        if alias.isNone then fail "derived tables require an alias"
        return { name := "", alias, derived := some derived }
      let name ← relationalIdentifier
      return { name, alias := ← optionalAlias }

  private def relationalJoinTail (fuel : Nat) (reversed : List Join) : P (List Join) :=
    match fuel with
    | 0 => fail "join list length exceeds parser budget"
    | fuel + 1 => do
      match ← joinKind with
      | none => return reversed.reverse
      | some kind =>
        let table ← relationalTableRef fuel
        let on ← if kind == .cross then pure none else do
          keyword "on"
          pure (some (← relationalExpression fuel))
        relationalJoinTail fuel ({ kind, table, on } :: reversed)

  private def cteList (fuel : Nat) (reversed : List CTE) : P (List CTE) :=
    match fuel with
    | 0 => fail "CTE list length exceeds parser budget"
    | fuel + 1 => do
      let cte ← cteItem fuel
      if ← accept (.symbol ",") then cteList fuel (cte :: reversed)
      else return (cte :: reversed).reverse

  private def cteItem (fuel : Nat) : P CTE :=
    match fuel with
    | 0 => fail "CTE nesting exceeds parser budget"
    | fuel + 1 => do
      let name ← relationalIdentifier
      let columns ← if ← accept (.symbol "(") then do
        let columns ← commaList "CTE columns" fuel relationalIdentifier
        symbol ")"
        pure columns
      else pure []
      keyword "as"
      symbol "("
      let query ← relationalSelect fuel
      symbol ")"
      return { name, query, columns }
end

private def relationalQuery (budget : Nat) : P RelQuery := do
  let result ← relationalSelect budget
  let _ ← accept (.symbol ";")
  unless (← peek).kind == .eof do
    fail "expected end of input after relational SELECT query"
  return result

private def insertRow (budget : Nat) : P (List Expr) := do
  symbol "("
  let values ← commaList "VALUES row" budget (expression budget 0 true)
  symbol ")"
  return values

private def insertStatement (budget : Nat) : P InsertQuery := do
  keyword "insert"
  keyword "into"
  let table ← identifier true
  let columns ← if ← accept (.symbol "(") then do
    let names ← commaList "INSERT columns" budget (identifier true)
    symbol ")"
    pure (some names)
  else pure none
  keyword "values"
  let rows ← commaList "VALUES rows" budget (insertRow budget)
  return { table, columns, rows }

private def assignment (budget : Nat) : P Assignment := do
  let column ← identifier true
  symbol "="
  return { column, value := ← expression budget 0 true }

private def updateStatement (budget : Nat) : P UpdateQuery := do
  keyword "update"
  let table ← identifier true
  keyword "set"
  let assignments ← commaList "SET assignments" budget (assignment budget)
  return { table, assignments, whereClause := ← whereClause budget }

private def deleteStatement (budget : Nat) : P DeleteQuery := do
  keyword "delete"
  keyword "from"
  let table ← identifier true
  return { table, whereClause := ← whereClause budget }

private def statement (budget : Nat) : P Statement := do
  let result ← match (← peek).kind with
    | .word "select" => pure (Statement.select (← selectStatement budget))
    | .word "insert" => pure (Statement.insert (← insertStatement budget))
    | .word "update" => pure (Statement.update (← updateStatement budget))
    | .word "delete" => pure (Statement.delete (← deleteStatement budget))
    | _ => fail "expected SELECT, INSERT, UPDATE, or DELETE"
  let _ ← accept (.symbol ";")
  unless (← peek).kind == .eof do
    fail "expected end of input after SQL statement"
  return result

/-- Parse a token stream containing exactly one final EOF token. -/
def parseTokens (tokens : List Token) : Except ParseError Query := do
  match tokens.reverse with
  | { kind := .eof, .. } :: rest =>
    if rest.any (fun token => token.kind == .eof) then
      throw ⟨{}, "unexpected EOF token before end of token stream"⟩
    let (result, remaining) ← (query (4 * tokens.length + 16)).run tokens
    match remaining with
    | [{ kind := .eof, .. }] => return result
    | _ => throw ⟨remaining.headD ⟨.eof, {}⟩ |>.position, "unexpected remaining tokens"⟩
  | _ => throw ⟨{}, "token stream must end with EOF"⟩

private def parseLegacyStatementTokens (tokens : List Token) : Except ParseError Statement := do
  match tokens.reverse with
  | { kind := .eof, .. } :: rest =>
    if rest.any (fun token => token.kind == .eof) then
      throw ⟨{}, "unexpected EOF token before end of token stream"⟩
    let (result, remaining) ← (statement (4 * tokens.length + 16)).run tokens
    match remaining with
    | [{ kind := .eof, .. }] => return result
    | _ => throw ⟨remaining.headD ⟨.eof, {}⟩ |>.position, "unexpected remaining tokens"⟩
  | _ => throw ⟨{}, "token stream must end with EOF"⟩

/-- Parse exactly one relational SELECT from a token stream with one final EOF. -/
def parseRelQueryTokens (tokens : List Token) : Except ParseError RelQuery := do
  match tokens.reverse with
  | { kind := .eof, .. } :: rest =>
    if rest.any (fun token => token.kind == .eof) then
      throw ⟨{}, "unexpected EOF token before end of token stream"⟩
    let (result, remaining) ← (relationalQuery (4 * tokens.length + 16)).run tokens
    match remaining with
    | [{ kind := .eof, .. }] => return result
    | _ => throw ⟨remaining.headD ⟨.eof, {}⟩ |>.position, "unexpected remaining tokens"⟩
  | _ => throw ⟨{}, "token stream must end with EOF"⟩

/-- Parse one CRUD or relational SELECT statement. Legacy SELECT queries retain
their original AST, including the original identifier rules. -/
def parseStatementTokens (tokens : List Token) : Except ParseError Statement :=
  match parseLegacyStatementTokens tokens with
  | .ok statement => .ok statement
  | .error error =>
    if [.word "select", .word "with"].contains (tokens.headD ⟨.eof, {}⟩).kind then
      Statement.relational <$> parseRelQueryTokens tokens
    else .error error

end Parser

/-- Parse exactly one SELECT query, optionally followed by one semicolon. -/
def parseQuery (input : String) : Except ParseError Query := do
  Parser.parseTokens (← lex input)

/-- Alias for `parseQuery`. -/
def parse := parseQuery

/-- Parse exactly one SELECT (including WITH), INSERT, UPDATE, or DELETE
statement, with one optional trailing semicolon. `parseQuery` preserves the
original MVP grammar, and legacy SELECT inputs retain their original AST. -/
def parseStatement (input : String) : Except ParseError Statement := do
  Parser.parseStatementTokens (← lex input)

/-- Parse a SELECT into the relational AST, including simple queries, joins,
aggregation, derived tables, compound UNION queries, and WITH [RECURSIVE] clauses. -/
def parseRelQuery (input : String) : Except ParseError RelQuery := do
  Parser.parseRelQueryTokens (← lex input)

end SQLean
