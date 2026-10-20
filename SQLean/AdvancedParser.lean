import SQLean.AdvancedSyntax

/-! A total, source-positioned recursive descent parser for the extended syntax.
The fuel bound grows with source length; decimal literals remain exact strings. -/
namespace SQLean.Advanced

private inductive Lexeme where
  | word (value : String) | quoted (value : String) | number (value : String)
  | text (value : String) | symbol (value : String) | parameter (value : Parameter) | eof
  deriving Repr, BEq, Inhabited

/-- Keyword recognition is case-insensitive in both dialects. SQLite keeps the
original spelling for identifiers; PostgreSQL folds unquoted identifiers. -/
private def Lexeme.keyword : Lexeme → Lexeme
  | .word value => .word value.toLower
  | other => other

private structure LexToken where
  kind : Lexeme
  position : SourcePos
  deriving Repr, Inhabited

private def advance (p : SourcePos) (c : Char) : SourcePos :=
  if c == '\n' then { offset := p.offset + 1, line := p.line + 1, column := 1 }
  else { p with offset := p.offset + 1, column := p.column + 1 }
private def digit (c : Char) : Bool := c >= '0' && c <= '9'
private def wordStart (c : Char) : Bool :=
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_'
private def wordChar (c : Char) : Bool := wordStart c || digit c || c == '$'
private def readWhile (pred : Char → Bool) : List Char → SourcePos → List Char → String × List Char × SourcePos
  | [], p, acc => (String.ofList acc.reverse, [], p)
  | c :: cs, p, acc => if pred c then readWhile pred cs (advance p c) (c :: acc)
    else (String.ofList acc.reverse, c :: cs, p)
private def quoted (delimiter : Char) (opening : SourcePos) :
    List Char → SourcePos → List Char → Except ParseError (String × List Char × SourcePos)
  | [], _, _ => .error { position := opening, message := "unterminated quoted value" }
  | c :: cs, p, acc =>
    if c == delimiter then
      match cs with
      | d :: ds => if d == delimiter then quoted delimiter opening ds (advance (advance p c) d) (c :: acc)
        else .ok (String.ofList acc.reverse, cs, advance p c)
      | [] => .ok (String.ofList acc.reverse, [], advance p c)
    else quoted delimiter opening cs (advance p c) (c :: acc)
private def skipLine : List Char → SourcePos → List Char × SourcePos
  | [], p => ([], p)
  | c :: cs, p => if c == '\n' then (cs, advance p c) else skipLine cs (advance p c)
private def skipBlock (nested : Bool) :
    Nat → Nat → List Char → SourcePos → Except ParseError (List Char × SourcePos)
  | 0, _, _, p => .error { position := p, message := "unterminated block comment" }
  | _ + 1, _, [], p => .error { position := p, message := "unterminated block comment" }
  | fuel + 1, depth, c :: cs, p =>
    match cs with
    | d :: ds =>
      if nested && c == '/' && d == '*' then skipBlock nested fuel (depth + 1) ds (advance (advance p c) d)
      else if c == '*' && d == '/' then
        if depth == 1 then .ok (ds, advance (advance p c) d)
        else skipBlock nested fuel (depth - 1) ds (advance (advance p c) d)
      else skipBlock nested fuel depth cs (advance p c)
    | [] => skipBlock nested fuel depth cs (advance p c)

private def readNumeric (input : List Char) (p : SourcePos) :
    Except ParseError (String × List Char × SourcePos) := do
  let (whole, rest, p') := readWhile digit input p []
  let (mantissa, rest, p') := match rest with
    | '.' :: tail =>
      let (fraction, tail, p'') := readWhile digit tail (advance p' '.') []
      (whole ++ "." ++ fraction, tail, p'')
    | _ => (whole, rest, p')
  let (raw, rest, p') ← match rest with
    | e :: tail =>
      if e == 'e' || e == 'E' then do
        let (sign, tail, p'') := match tail with
          | s :: ss => if s == '+' || s == '-' then (String.singleton s, ss, advance (advance p' e) s)
            else ("", tail, advance p' e)
          | [] => ("", [], advance p' e)
        let (exponent, tail, p''') := readWhile digit tail p'' []
        if exponent.isEmpty then throw { position := p, message := "numeric exponent requires digits" }
        pure (mantissa ++ String.singleton e ++ sign ++ exponent, tail, p''')
      else pure (mantissa, rest, p')
    | [] => pure (mantissa, rest, p')
  match rest with
  | c :: _ => if wordChar c || c == '.' then
      throw { position := p', message := "invalid numeric literal suffix" }
  | [] => pure ()
  pure (raw, rest, p')

private def lexLoop (sqlite : Bool) : Nat → List Char → SourcePos → Nat → Bool → List LexToken → Except ParseError (List LexToken)
  | 0, _, p, _, _, _ => .error { position := p, message := "lexer input bound exceeded" }
  | fuel + 1, input, p, anonymous, numbered, acc => do
    match input with
    | [] => pure (({kind := .eof, position := p} :: acc).reverse)
    | c :: cs =>
      if c == ' ' || c == '\t' || c == '\r' || c == '\n' then
        lexLoop sqlite fuel cs (advance p c) anonymous numbered acc
      else if wordStart c then
        let (name, rest, next) := readWhile wordChar cs (advance p c) [c]
        let spelling := if sqlite then name else name.toLower
        lexLoop sqlite fuel rest next anonymous numbered ({kind := .word spelling, position := p} :: acc)
      else if digit c || (c == '.' && cs.head?.any digit) then
        let (raw, rest, next) ← readNumeric input p
        lexLoop sqlite fuel rest next anonymous numbered ({kind := .number raw, position := p} :: acc)
      else if c == '\'' || c == '"' then
        let (value, rest, next) ← quoted c p cs (advance p c) []
        if c == '"' && value.isEmpty then throw {position := p, message := "empty identifier"}
        let kind := if c == '\'' then Lexeme.text value else .quoted value
        lexLoop sqlite fuel rest next anonymous numbered ({kind, position := p} :: acc)
      else if c == '?' then
        if cs.head?.any digit then
          if !sqlite then throw {position := p, message := "?NNN parameters require the SQLite parser interface"}
          if anonymous > 0 then throw {position := p, message := "cannot mix ? and ?NNN parameter styles"}
          let (raw, rest, next) := readWhile digit cs (advance p c) []
          let some index := raw.toNat? | throw {position := p, message := "expected positive parameter index"}
          if index == 0 then throw {position := p, message := "parameter indexes begin at one"}
          if rest.head?.any wordChar then throw {position := next, message := "invalid parameter suffix"}
          lexLoop sqlite fuel rest next anonymous true
            ({kind := .parameter (.numbered index), position := p} :: acc)
        else
          if numbered then throw {position := p, message := "cannot mix anonymous and numbered parameter styles"}
          lexLoop sqlite fuel cs (advance p c) (anonymous + 1) numbered
            ({kind := .parameter (.anonymous (anonymous + 1)), position := p} :: acc)
      else if c == '$' then
        if sqlite then throw {position := p, message := "SQLite named $ parameters are outside this profile; use ?NNN"}
        if anonymous > 0 then throw {position := p, message := "cannot mix ? and $n parameter styles"}
        let (raw, rest, next) := readWhile digit cs (advance p c) []
        let some index := raw.toNat? | throw {position := p, message := "expected positive parameter index"}
        if index == 0 then throw {position := p, message := "parameter indexes begin at one"}
        if rest.head?.any wordChar then throw {position := next, message := "invalid parameter suffix"}
        lexLoop sqlite fuel rest next anonymous true ({kind := .parameter (.numbered index), position := p} :: acc)
      else
        match cs with
        | d :: ds =>
          if c == '-' && d == '-' then
            let (rest, next) := skipLine ds (advance (advance p c) d)
            lexLoop sqlite fuel rest next anonymous numbered acc
          else if c == '/' && d == '*' then
            let (rest, next) ← skipBlock (!sqlite) (input.length + 1) 1 ds (advance (advance p c) d)
            lexLoop sqlite fuel rest next anonymous numbered acc
          else if (c == '<' && (d == '>' || d == '=')) || (c == '>' && d == '=') ||
              (c == '!' && d == '=') || (c == ':' && d == ':') then
            lexLoop sqlite fuel ds (advance (advance p c) d) anonymous numbered
              ({kind := .symbol (String.ofList [c,d]), position := p} :: acc)
          else if "(),;*./+-=<>".contains c then
            lexLoop sqlite fuel cs (advance p c) anonymous numbered ({kind := .symbol (String.singleton c), position := p} :: acc)
          else throw {position := p, message := s!"unsupported character '{c}'"}
        | [] =>
          if "(),;*./+-=<>".contains c then
            lexLoop sqlite fuel cs (advance p c) anonymous numbered ({kind := .symbol (String.singleton c), position := p} :: acc)
          else throw {position := p, message := s!"unsupported character '{c}'"}

private abbrev Parser := ReaderT Bool (StateT (List LexToken) (Except ParseError))
private def peek : Parser LexToken := do pure ((← get).headD {kind := .eof, position := {}})
private def pop : Parser LexToken := do
  let token ← peek
  modify List.tail
  pure token
private def fail {α : Type} (message : String) : Parser α := do
  throw { position := (← peek).position, message }
private def isAt (value : String) : Parser Bool := do
  pure (match (← peek).kind.keyword with | .word s | .symbol s => s == value | _ => false)
private def eat (value : String) : Parser Bool := do
  if ← isAt value then let _ ← pop; pure true else pure false
private def expect (value : String) : Parser Unit := do
  unless ← eat value do fail s!"expected {value}"
private def reserved : List String :=
  ["select", "from", "where", "group", "by", "having", "order", "limit", "offset", "asc", "desc",
   "nulls", "distinct", "on", "as", "join", "inner", "left", "right", "full", "outer", "cross", "natural",
   "using", "lateral", "union", "intersect", "except", "with", "recursive", "all", "and", "or", "not",
   "is", "null", "true", "false", "in", "exists", "between", "like", "ilike", "filter", "cast",
   "insert", "into", "values", "default", "update", "set", "delete", "returning", "conflict", "do",
   "nothing", "constraint", "create", "alter", "drop", "table", "if", "primary", "key", "unique",
   "column", "add", "rename", "to", "type", "references", "check", "foreign", "cascade", "restrict"]
private def identifier : Parser Name := do
  match (← pop).kind with
  | .quoted s => pure s
  | .word s => if reserved.contains s.toLower then fail s!"reserved identifier {s}" else pure s
  | _ => fail "expected identifier"
private def alias? : Parser (Option Name) := do
  if ← eat "as" then return some (← identifier)
  match (← peek).kind with
  | .quoted _ => return some (← identifier)
  | .word s => if !reserved.contains s.toLower then return some (← identifier) else pure none
  | _ => pure none
private def natural : Parser Nat := do
  match (← pop).kind with
  | .number s => match s.toNat? with | some n => pure n | none => fail "expected nonnegative integer"
  | _ => fail "expected nonnegative integer"
private def separated {α : Type} (item : Parser α) : Nat → Parser (List α)
  | 0 => fail "list input bound exceeded"
  | fuel + 1 => do
    let first ← item
    if ← eat "," then return first :: (← separated item fuel) else pure [first]
private def names (fuel : Nat) : Parser (List Name) := do
  expect "("
  let values ← separated identifier fuel
  expect ")"
  pure values
private def optionalNames (fuel : Nat) : Parser (List Name) := do
  if ← isAt "(" then names fuel else pure []

private def dataType (fuel : Nat) : Parser DataType := do
  let token ← pop
  let name ← match token.kind.keyword with
    | .word "int" | .word "integer" | .word "int4" => pure TypeName.int
    | .word "bigint" | .word "int8" => pure .bigInt
    | .word "text" => pure .text
    | .word "varchar" => pure .varchar
    | .word "character" => do expect "varying"; pure .varchar
    | .word "bool" | .word "boolean" => pure .bool
    | .word "real" | .word "float4" => pure .real
    | .word "double" => do expect "precision"; pure .doublePrecision
    | .word "float8" => pure .doublePrecision
    | .word "numeric" | .word "decimal" => pure .numeric
    | _ => fail "unsupported SQL type"
  let modifiers ← if ← eat "(" then do
    let values ← separated natural fuel
    expect ")"
    pure values
    else pure []
  match name, modifiers with
  | _, [] => pure ()
  | .varchar, [n] => if n == 0 then fail "VARCHAR length must be positive"
  | .numeric, [p] => if p == 0 || p > 1000 then fail "NUMERIC precision must be between 1 and 1000"
  | .numeric, [p,s] => if p == 0 || p > 1000 || s > 1000 then fail "unsupported NUMERIC precision/scale"
  | _, _ => fail "invalid type modifiers"
  pure {name, modifiers}

private def binInfo (token : Lexeme) : Option (BinOp × Nat) := match token.keyword with
  | .word "or" => some (.or, 1) | .word "and" => some (.and, 2)
  | .symbol "=" => some (.eq, 4) | .symbol "<>" | .symbol "!=" => some (.ne, 4)
  | .symbol "<" => some (.lt, 4) | .symbol "<=" => some (.le, 4)
  | .symbol ">" => some (.gt, 4) | .symbol ">=" => some (.ge, 4)
  | .symbol "+" => some (.add, 5) | .symbol "-" => some (.sub, 5)
  | .symbol "*" => some (.mul, 6) | .symbol "/" => some (.div, 6)
  | _ => none
private def aggregateFn : String → Option AggregateFn
  | "count" => some .count | "sum" => some .sum | "avg" => some .avg
  | "min" => some .min | "max" => some .max | _ => none
/-- Try complete alternatives from the same token position. A parenthesized
SELECT prefix is ambiguous with a scalar expression or a derived-first join;
only consuming the complete enclosing production can disambiguate it. -/
private def alternative (first second : Parser α) : Parser α := fun sqlite tokens =>
  match first sqlite tokens with
  | .ok result => .ok result
  | .error firstError =>
    match second sqlite tokens with
    | .ok result => .ok result
    | .error secondError =>
      .error (if firstError.position.offset ≥ secondError.position.offset then firstError else secondError)

/-- This is a lookahead hint, not proof that the entire group is a query. -/
private def queryStart : Parser Bool := do
  let tokens := (← get).dropWhile (fun t => t.kind == .symbol "(")
  pure (match tokens.head? with
    | some token => token.kind.keyword == .word "select" || token.kind.keyword == .word "with"
    | none => false)

private def parseJoinKind : Parser (Option JoinKind) := do
  if ← eat "left" then
    let _ ← eat "outer"
    expect "join"
    return some JoinKind.left
  if ← eat "right" then
    let _ ← eat "outer"
    expect "join"
    return some JoinKind.right
  if ← eat "full" then
    let _ ← eat "outer"
    expect "join"
    return some JoinKind.full
  if ← eat "inner" then
    expect "join"
    return some JoinKind.inner
  if ← eat "cross" then
    expect "join"
    return some JoinKind.cross
  if ← eat "join" then return some JoinKind.inner
  return none


mutual
  private def expression : Nat → Nat → Parser Expr
    | 0, _ => fail "expression nesting bound exceeded"
    | fuel + 1, minPrec => do
      let left ← atom fuel
      tailExpr fuel minPrec left false

  private def atom : Nat → Parser Expr
    | 0 => fail "expression nesting bound exceeded"
    | fuel + 1 => do
      if ← eat "not" then return .unary .not (← expression fuel 4)
      if ← eat "+" then return .unary .pos (← expression fuel 7)
      if ← eat "-" then return .unary .neg (← expression fuel 7)
      if ← eat "null" then return .null
      if ← eat "true" then return .literal (.bool true)
      if ← eat "false" then return .literal (.bool false)
      if ← eat "exists" then
        expect "("
        let q ← query fuel
        expect ")"
        return .exists q
      if ← eat "cast" then
        expect "("
        let value ← expression fuel 0
        expect "as"
        let type ← dataType fuel
        expect ")"
        return .cast value type
      if ← eat "(" then
        let grouped : Parser Expr := do
          let value ← expression fuel 0
          expect ")"
          pure value
        if ← queryStart then
          return ← alternative (do
            let q ← query fuel
            expect ")"
            pure (.scalarQuery q)) grouped
        return ← grouped
      match (← peek).kind with
      | .number raw =>
        let _ ← pop
        match raw.toNat? with
        | some n => return .literal (.int n)
        | none => return .decimal raw
      | .text value => let _ ← pop; return .literal (.text value)
      | .parameter value => let _ ← pop; return .parameter value
      | .word word =>
        match aggregateFn word.toLower with
        | some fn =>
          let _ ← pop
          if ← eat "(" then
            let distinct ← eat "distinct"
            let value ← if fn == .count && (← eat "*") then
              if distinct then fail "COUNT(DISTINCT *) is unsupported" else pure Expr.countAll
              else do pure (.aggregate fn (← expression fuel 0) distinct)
            expect ")"
            let value ← if ← eat "filter" then do
              expect "("
              expect "where"
              let predicate ← expression fuel 0
              expect ")"
              pure (.filteredAggregate value predicate)
              else pure value
            return value
          if ← eat "." then return .column (some word) (← identifier)
          return .column none word
        | none =>
          let name ← identifier
          if ← eat "." then return .column (some name) (← identifier)
          return .column none name
      | .quoted _ =>
        let name ← identifier
        if ← eat "." then return .column (some name) (← identifier)
        return .column none name
      | _ => fail "expected expression"

  private def tailExpr : Nat → Nat → Expr → Bool → Parser Expr
    | 0, _, _, _ => fail "expression input bound exceeded"
    | fuel + 1, minPrec, left, compared => do
      if minPrec <= 8 && (← eat "::") then
        let type ← dataType fuel
        return ← tailExpr fuel minPrec (.cast left type) compared
      let notPredicate := match (← get) with
        | first :: next :: _ =>
          first.kind.keyword == .word "not" &&
            match next.kind.keyword with
            | .word "in" | .word "between" | .word "like" | .word "ilike" => true
            | _ => false
        | _ => false
      let predStart := (← isAt "is") || (← isAt "in") || (← isAt "between") ||
        (← isAt "like") || (← isAt "ilike") || notPredicate
      if minPrec <= 4 && predStart then
        if compared then fail "parenthesize chained comparisons"
        let negated ← eat "not"
        let result ← if ← eat "is" then do
          if negated then fail "expected IN, BETWEEN, LIKE or ILIKE after NOT"
          let notNull ← eat "not"
          expect "null"
          pure (.isNull left notNull)
          else if ← eat "in" then do
            expect "("
            let valueList : Parser Expr := do
              let values ← separated (expression fuel 0) fuel
              expect ")"
              pure (.inList left values)
            let result ← if ← queryStart then
              alternative (do
                let q ← query fuel
                expect ")"
                pure (.inQuery left q)) valueList
              else valueList
            pure (if negated then .unary .not result else result)
          else if ← eat "between" then do
            let lower ← expression fuel 5
            expect "and"
            let upper ← expression fuel 5
            pure (Expr.between left lower upper negated)
          else do
            let insensitive ← eat "ilike"
            unless insensitive do expect "like"
            let result := Expr.pattern left (← expression fuel 5) insensitive
            pure (if negated then .unary .not result else result)
        tailExpr fuel minPrec result true
      else
        match binInfo (← peek).kind with
        | some (op, prec) =>
          if prec < minPrec then return left
          if prec == 4 && compared then fail "parenthesize chained comparisons"
          let _ ← pop
          let right ← expression fuel (prec + 1)
          tailExpr fuel minPrec (.binary op left right) (prec == 4)
        | none => pure left

  private def selectItem : Nat → Parser SelectItem
    | 0 => fail "projection nesting bound exceeded"
    | fuel + 1 => do
      if ← eat "*" then return .all none
      let tokens ← get
      match tokens with
      | a :: {kind := .symbol ".", ..} :: {kind := .symbol "*", ..} :: rest =>
        match a.kind with
        | .word name | .quoted name =>
          set rest
          return .all (some name)
        | _ => pure ()
      | _ => pure ()
      let value ← expression fuel 0
      let alias ← alias?
      return .expression value alias

  private def fromAtom : Nat → Parser From
    | 0 => fail "FROM nesting bound exceeded"
    | fuel + 1 => do
      let lateral ← eat "lateral"
      if ← eat "(" then
        let grouped : Parser From := do
          if lateral then fail "LATERAL requires a subquery"
          let source ← fromExpr fuel
          expect ")"
          pure source
        if ← queryStart then
          return ← alternative (do
            let q ← query fuel
            expect ")"
            let some alias ← alias? | fail "derived tables require an alias"
            let columns ← optionalNames fuel
            pure (.derived q alias columns lateral)) grouped
        return ← grouped
      if lateral then fail "LATERAL requires a derived table"
      let name ← identifier
      let alias ← alias?
      let columns ← if alias.isSome then optionalNames fuel else pure []
      pure (.table name alias columns)

  private def fromExpr : Nat → Parser From
    | 0 => fail "FROM nesting bound exceeded"
    | fuel + 1 => do
      let first ← fromAtom fuel
      if ← read then sqliteSourceTail fuel first
      else
        let first ← joinTail fuel first
        commaTail fuel first

  /-- SQLite evaluates comma joins and explicit JOINs at the same precedence,
  from left to right. Parenthesized sources still preserve explicit grouping. -/
  private def sqliteSourceTail : Nat → From → Parser From
    | 0, _ => fail "FROM input bound exceeded"
    | fuel + 1, left => do
      if ← eat "," then
        let right ← fromAtom fuel
        return ← sqliteSourceTail fuel (.join .cross left right .none)
      let naturalJoin ← eat "natural"
      let kind ← parseJoinKind
      match kind with
      | none => if naturalJoin then fail "expected JOIN after NATURAL" else pure left
      | some kind =>
        if naturalJoin && kind == .cross then fail "NATURAL CROSS JOIN is invalid"
        let right ← fromAtom fuel
        let condition ← if naturalJoin then pure JoinCondition.natural
          else if kind == .cross then pure .none
          else if ← eat "on" then pure (.on (← expression fuel 0))
          else if ← eat "using" then pure (.using (← names fuel))
          else fail "JOIN requires ON or USING"
        sqliteSourceTail fuel (.join kind left right condition)

  private def commaTail : Nat → From → Parser From
    | 0, _ => fail "FROM input bound exceeded"
    | fuel + 1, left => do
      if ← eat "," then
        let right ← fromAtom fuel
        let right ← joinTail fuel right
        commaTail fuel (.join .cross left right .none)
      else pure left

  private def joinTail : Nat → From → Parser From
    | 0, _ => fail "JOIN input bound exceeded"
    | fuel + 1, left => do
      let naturalJoin ← eat "natural"
      let kind ← parseJoinKind
      match kind with
      | none => if naturalJoin then fail "expected JOIN after NATURAL" else pure left
      | some kind =>
        if naturalJoin && kind == .cross then fail "NATURAL CROSS JOIN is invalid"
        let right ← fromAtom fuel
        let condition ← if naturalJoin then pure JoinCondition.natural
          else if kind == .cross then pure .none
          else if ← eat "on" then pure (.on (← expression fuel 0))
          else if ← eat "using" then pure (.using (← names fuel))
          else fail "JOIN requires ON or USING"
        joinTail fuel (.join kind left right condition)

  private def selectCore : Nat → Parser Query
    | 0 => fail "SELECT nesting bound exceeded"
    | fuel + 1 => do
      expect "select"
      let distinct ← eat "distinct"
      let distinctOn ← if distinct && (← eat "on") then do
        expect "("
        let keys ← separated (expression fuel 0) fuel
        expect ")"
        pure keys
        else pure []
      unless distinct do let _ ← eat "all"; pure ()
      let items ← separated (selectItem fuel) fuel
      let source ← if ← eat "from" then pure (some (← fromExpr fuel)) else pure none
      let whereClause ← if ← eat "where" then pure (some (← expression fuel 0)) else pure none
      let groupBy ← if ← eat "group" then do expect "by"; separated (expression fuel 0) fuel else pure []
      let having ← if ← eat "having" then pure (some (← expression fuel 0)) else pure none
      let select : Select := {
        items := items, source := source, whereClause := whereClause,
        groupBy := groupBy, having := having, distinct := (distinct && distinctOn.isEmpty),
        distinctOn := distinctOn}
      pure {body := .select select}

  private def queryAtom : Nat → Parser Query
    | 0 => fail "query nesting bound exceeded"
    | fuel + 1 => do
      if ← eat "(" then
        let q ← query fuel
        expect ")"
        pure q
      else selectCore fuel

  private def intersectTail : Nat → Query → Parser Query
    | 0, _ => fail "set operation input bound exceeded"
    | fuel + 1, left => do
      if ← eat "intersect" then
        let all ← eat "all"
        unless all do let _ ← eat "distinct"; pure ()
        let right ← queryAtom fuel
        intersectTail fuel {body := .set .intersect all left right}
      else pure left

  private def unionTail : Nat → Query → Parser Query
    | 0, _ => fail "set operation input bound exceeded"
    | fuel + 1, left => do
      let op ← if ← eat "union" then pure (some SetOp.union)
        else if ← eat "except" then pure (some .except) else pure none
      match op with
      | none => pure left
      | some op =>
        let all ← eat "all"
        unless all do let _ ← eat "distinct"; pure ()
        let right ← queryAtom fuel
        let right ← intersectTail fuel right
        unionTail fuel {body := .set op all left right}

  /-- SQLite compound operators have equal precedence and associate leftward. -/
  private def sqliteSetTail : Nat → Query → Parser Query
    | 0, _ => fail "set operation input bound exceeded"
    | fuel + 1, left => do
      let op ← if ← eat "union" then pure (some SetOp.union)
        else if ← eat "intersect" then pure (some .intersect)
        else if ← eat "except" then pure (some .except) else pure none
      match op with
      | none => pure left
      | some op =>
        let all ← eat "all"
        if all && op != .union then fail "SQLite supports ALL only with UNION"
        let right ← selectCore fuel
        sqliteSetTail fuel {body := .set op all left right}

  private def orderItem : Nat → Parser OrderBy
    | 0 => fail "ORDER BY nesting bound exceeded"
    | fuel + 1 => do
      let expr ← expression fuel 0
      let descending ← eat "desc"
      unless descending do let _ ← eat "asc"; pure ()
      let nullsFirst ← if ← eat "nulls" then do
        if ← eat "first" then pure (some true) else do expect "last"; pure (some false)
        else pure none
      pure {expr, descending, nullsFirst}

  private def cte : Nat → Parser CTE
    | 0 => fail "CTE nesting bound exceeded"
    | fuel + 1 => do
      let name ← identifier
      let columns ← optionalNames fuel
      expect "as"
      expect "("
      let q ← query fuel
      expect ")"
      pure {name, columns, query := q}

  private def query : Nat → Parser Query
    | 0 => fail "query nesting bound exceeded"
    | fuel + 1 => do
      let withClause ← eat "with"
      let recursive ← if withClause then eat "recursive" else pure false
      let ctes ← if withClause then separated (cte fuel) fuel else pure []
      let q ← queryAtom fuel
      let sqlite ← read
      let q ← if sqlite then sqliteSetTail fuel q else do
        let q ← intersectTail fuel q
        unionTail fuel q
      let orderBy ← if ← eat "order" then do expect "by"; separated (orderItem fuel) fuel else pure []
      let (limit, commaOffset) ← if ← eat "limit" then do
        let first ← natural
        if sqlite && (← eat ",") then
          pure (some (← natural), some first)
        else pure (some first, none)
        else pure (none, none)
      let offset ← if ← eat "offset" then do
        if sqlite && (limit.isNone || commaOffset.isSome) then
          fail "SQLite OFFSET requires LIMIT and cannot follow comma LIMIT"
        pure (some (← natural))
        else pure commaOffset
      let outerModifiers := !orderBy.isEmpty || limit.isSome || offset.isSome
      let innerModifiers := !q.orderBy.isEmpty || q.limit.isSome || q.offset.isSome
      if (outerModifiers && innerModifiers) || (!ctes.isEmpty && !q.ctes.isEmpty) then
        fail "nested query modifiers require a derived table"
      pure {q with
        ctes := (ctes ++ q.ctes), recursive := (recursive || q.recursive),
        orderBy := (if orderBy.isEmpty then q.orderBy else orderBy),
        limit := limit.or q.limit, offset := offset.or q.offset}
end

private def assignment (fuel : Nat) : Parser Assignment := do
  let column ← identifier
  expect "="
  let value ← expression fuel 0
  pure {column, value}
private def returningItems (fuel : Nat) : Parser (List SelectItem) := do
  if ← eat "returning" then separated (selectItem fuel) fuel else pure []
private def insertStatement (fuel : Nat) : Parser Statement := do
  expect "into"
  let table ← identifier
  let alias ← if ← eat "as" then pure (some (← identifier)) else pure none
  let columns ← optionalNames fuel
  let source ← if ← eat "values" then do
    let rows ← separated (do
      expect "("
      let values ← separated (expression fuel 0) fuel
      expect ")"
      pure values) fuel
    pure (InsertSource.values rows)
    else if ← eat "default" then do expect "values"; pure .defaultValues
    else pure (.query (← query fuel))
  let onConflict ← if ← eat "on" then do
    expect "conflict"
    let target ← if ← isAt "(" then pure (some (ConflictTarget.columns (← names fuel)))
      else if ← eat "on" then do expect "constraint"; pure (some (.constraint (← identifier)))
      else pure none
    expect "do"
    let action ← if ← eat "nothing" then pure ConflictAction.nothing else do
      if target.isNone then fail "ON CONFLICT DO UPDATE requires a conflict target"
      expect "update"
      expect "set"
      let assignments ← separated (assignment fuel) fuel
      let whereClause ← if ← eat "where" then pure (some (← expression fuel 0)) else pure none
      pure (.update assignments whereClause)
    pure (some {target, action})
    else pure none
  let returning ← returningItems fuel
  pure (.insert {table, alias, columns, source, onConflict, returning})
private def updateStatement (fuel : Nat) : Parser Statement := do
  let table ← identifier
  let alias ← alias?
  expect "set"
  let assignments ← separated (assignment fuel) fuel
  let whereClause ← if ← eat "where" then pure (some (← expression fuel 0)) else pure none
  let returning ← returningItems fuel
  pure (.update {table, alias, assignments, whereClause, returning})
private def deleteStatement (fuel : Nat) : Parser Statement := do
  expect "from"
  let table ← identifier
  let alias ← alias?
  let whereClause ← if ← eat "where" then pure (some (← expression fuel 0)) else pure none
  let returning ← returningItems fuel
  pure (.delete {table, alias, whereClause, returning})

private def columnConstraints : Nat → Column → Parser Column
  | 0, _ => fail "column definition input bound exceeded"
  | fuel + 1, column => do
    if ← eat "null" then
      if column.nullable.isSome then fail "duplicate column nullability"
      columnConstraints fuel {column with nullable := some true}
    else if ← eat "not" then
      expect "null"
      if column.nullable.isSome then fail "duplicate column nullability"
      columnConstraints fuel {column with nullable := some false}
    else if ← eat "primary" then
      expect "key"
      if column.primaryKey then fail "duplicate PRIMARY KEY"
      columnConstraints fuel {column with primaryKey := true}
    else if ← eat "unique" then
      if column.unique then fail "duplicate UNIQUE"
      columnConstraints fuel {column with unique := true}
    else if ← eat "default" then
      if column.defaultValue.isSome then fail "duplicate DEFAULT"
      let value ← expression fuel 0
      columnConstraints fuel {column with defaultValue := some value}
    else pure column
private def columnDefinition (fuel : Nat) : Parser Column := do
  let name ← identifier
  let type ← dataType fuel
  columnConstraints fuel {name, type}
private def createStatement (fuel : Nat) : Parser Statement := do
  expect "table"
  let ifNotExists ← if ← eat "if" then do expect "not"; expect "exists"; pure true else pure false
  let name ← identifier
  expect "("
  let entries ← separated (do
    if ← eat "primary" then do
      expect "key"
      pure (Sum.inr (TableConstraint.primaryKey (← names fuel)))
    else if ← eat "unique" then pure (Sum.inr (TableConstraint.unique (← names fuel)))
    else pure (Sum.inl (← columnDefinition fuel))) fuel
  expect ")"
  let columns := entries.filterMap fun | .inl column => some column | _ => none
  let constraints := entries.filterMap fun | .inr constraint => some constraint | _ => none
  if columns.isEmpty then fail "CREATE TABLE requires at least one column"
  pure (.createTable {name, ifNotExists, columns, constraints})
private def dropMode : Parser Bool := do
  let cascade ← eat "cascade"
  unless cascade do let _ ← eat "restrict"; pure ()
  pure cascade
private def alterAction (fuel : Nat) : Parser AlterAction := do
  if ← eat "add" then
    let _ ← eat "column"
    let ifNotExists ← if ← eat "if" then do expect "not"; expect "exists"; pure true else pure false
    return .addColumn (← columnDefinition fuel) ifNotExists
  if ← eat "drop" then
    let _ ← eat "column"
    let ifExists ← if ← eat "if" then do expect "exists"; pure true else pure false
    let name ← identifier
    return .dropColumn name ifExists (← dropMode)
  if ← eat "rename" then
    if ← eat "to" then return .renameTable (← identifier)
    let _ ← eat "column"
    let name ← identifier
    expect "to"
    return .renameColumn name (← identifier)
  expect "alter"
  let _ ← eat "column"
  let name ← identifier
  if ← eat "type" then return .setType name (← dataType fuel)
  if ← eat "set" then
    if ← eat "default" then return .setDefault name (← expression fuel 0)
    if ← eat "data" then do expect "type"; return .setType name (← dataType fuel)
    expect "not"
    expect "null"
    return .setNotNull name
  expect "drop"
  if ← eat "default" then return .dropDefault name
  expect "not"
  expect "null"
  return .dropNotNull name
private def statement (fuel : Nat) : Parser Statement := do
  if ← eat "insert" then return ← insertStatement fuel
  if ← eat "update" then return ← updateStatement fuel
  if ← eat "delete" then return ← deleteStatement fuel
  if ← eat "create" then return ← createStatement fuel
  if ← eat "alter" then
    expect "table"
    let name ← identifier
    let actions ← separated (alterAction fuel) fuel
    if actions.length > 1 && actions.any (fun
      | .renameColumn .. | .renameTable .. => true | _ => false) then
      fail "RENAME must be a standalone ALTER TABLE action"
    return .alterTable name actions
  if ← eat "drop" then
    expect "table"
    let ifExists ← if ← eat "if" then do expect "exists"; pure true else pure false
    let name ← identifier
    return .dropTable name ifExists (← dropMode)
  return .query (← query fuel)

private def runComplete {α : Type} (source : String) (parser : Nat → Parser α)
    (sqlite : Bool := false) : Except ParseError α := do
  let chars := source.toList
  let tokens ← lexLoop sqlite (chars.length + 1) chars {} 0 false []
  let (result, _) ← (do
    let value ← parser (tokens.length * 12 + 64)
    let _ ← eat ";"
    match (← peek).kind with
    | .eof => pure value
    | _ => fail "unexpected trailing SQL input").run sqlite |>.run tokens
  pure result

/-- Parse one statement. Mixing numbered and anonymous parameters is rejected. -/
def parse (source : String) : Except ParseError Statement := runComplete source statement
/-- Parse a scalar expression, including explicit casts and nested queries. -/
def parseExpression (source : String) : Except ParseError Expr :=
  runComplete source (fun fuel => expression fuel 0)
/-- Uniform query entry point, independent of legacy SELECT AST dispatch. -/
def parseQuery (source : String) : Except ParseError Query := runComplete source query

/-- SQLite parameter identities, preserved identifier spelling, non-nesting
comments, and left-associative compound/join precedence. Target-profile
coverage is checked separately by the rendering boundary. -/
def parseSQLiteQuery (source : String) : Except ParseError Query := runComplete source query true

def parseSQLite (source : String) : Except ParseError Statement := runComplete source statement true

end SQLean.Advanced
