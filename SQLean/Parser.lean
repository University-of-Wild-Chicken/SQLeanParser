import SQLean.Lexer

/-! Total, position-aware parsers for the SELECT and CRUD grammars in `SQLean.AST`.
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

/-- Parse exactly one CRUD statement from a token stream with one final EOF. -/
def parseStatementTokens (tokens : List Token) : Except ParseError Statement := do
  match tokens.reverse with
  | { kind := .eof, .. } :: rest =>
    if rest.any (fun token => token.kind == .eof) then
      throw ⟨{}, "unexpected EOF token before end of token stream"⟩
    let (result, remaining) ← (statement (4 * tokens.length + 16)).run tokens
    match remaining with
    | [{ kind := .eof, .. }] => return result
    | _ => throw ⟨remaining.headD ⟨.eof, {}⟩ |>.position, "unexpected remaining tokens"⟩
  | _ => throw ⟨{}, "token stream must end with EOF"⟩

end Parser

/-- Parse exactly one SELECT query, optionally followed by one semicolon. -/
def parseQuery (input : String) : Except ParseError Query := do
  Parser.parseTokens (← lex input)

/-- Alias for `parseQuery`. -/
def parse := parseQuery

/-- Parse exactly one SELECT, INSERT, UPDATE, or DELETE statement, with one
optional trailing semicolon. `parseQuery` preserves the original MVP grammar. -/
def parseStatement (input : String) : Except ParseError Statement := do
  Parser.parseStatementTokens (← lex input)

end SQLean
