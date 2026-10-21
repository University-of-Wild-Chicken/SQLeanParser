import SQLean.AdvancedSyntax
import SQLean.PostgresGrammar.Generated.Symbols

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

/-- PostgreSQL scans maximal operator runs, including question marks. Runs
containing a question mark are resolved by parser role: native infix operators
versus the separately documented anonymous-template compatibility extension. -/
private def pgOperatorChar (c : Char) : Bool := "~!@#^&|`?+-*/%<>=".contains c

private def pgOperatorPrefix : List Char → List Char
  | [] => []
  | c :: cs =>
    if (c == '/' && cs.head? == some '*') || (c == '-' && cs.head? == some '-') then []
    else if pgOperatorChar c then c :: pgOperatorPrefix cs
    else []

private def supportedPgOperators : List String :=
  ["->>", "#>>", "!~*", "=>", "<=", ">=", "<>", "!=", "||", "&&", "~*", "!~",
   "->", "#>", "@>", "<@", "?|", "?&", "+", "-", "*", "/", "=", "<", ">", "~", "?"]

private def readPgOperator (input : List Char) (p : SourcePos) :
    Except ParseError (String × List Char × SourcePos) := do
  let raw := pgOperatorPrefix input
  -- scan.l strips trailing +/− only from SQL-style operator runs. The
  -- nonstandard characters in `||-`, `~-`, `!=+`, etc. prevent stripping.
  let stripped := if raw.any (fun c => "~!@#^&|`?%".contains c) then raw
    else (raw.reverse.dropWhile (fun c => c == '+' || c == '-')).reverse
  let chars := if stripped.isEmpty then raw.take 1 else stripped
  let operator := String.ofList chars
  if !supportedPgOperators.contains operator && !operator.contains '?' then
    throw {position := p, message := s!"unsupported PostgreSQL operator '{operator}'"}
  pure (operator, input.drop chars.length, chars.foldl advance p)

private def lexLoop (sqlite : Bool) : Nat → List Char → SourcePos → List LexToken → Except ParseError (List LexToken)
  | 0, _, p, _ => .error { position := p, message := "lexer input bound exceeded" }
  | fuel + 1, input, p, acc => do
    match input with
    | [] => pure (({kind := .eof, position := p} :: acc).reverse)
    | c :: cs =>
      if c == ' ' || c == '\t' || c == '\r' || c == '\n' then
        lexLoop sqlite fuel cs (advance p c) acc
      else if wordStart c then
        let (name, rest, next) := readWhile wordChar cs (advance p c) [c]
        let spelling := if sqlite then name else name.toLower
        lexLoop sqlite fuel rest next ({kind := .word spelling, position := p} :: acc)
      else if digit c || (c == '.' && cs.head?.any digit) then
        let (raw, rest, next) ← readNumeric input p
        lexLoop sqlite fuel rest next ({kind := .number raw, position := p} :: acc)
      else if c == '\'' || c == '"' then
        let (value, rest, next) ← quoted c p cs (advance p c) []
        if c == '"' && value.isEmpty then throw {position := p, message := "empty identifier"}
        let kind := if c == '\'' then Lexeme.text value else .quoted value
        lexLoop sqlite fuel rest next ({kind, position := p} :: acc)
      else if c == '?' then
        if !sqlite then
          let (operator, rest, next) ← readPgOperator input p
          lexLoop sqlite fuel rest next
            ({kind := .symbol operator, position := p} :: acc)
        else if cs.head?.any digit then
          let (raw, rest, next) := readWhile digit cs (advance p c) []
          let some index := raw.toNat? | throw {position := p, message := "expected positive parameter index"}
          if index == 0 then throw {position := p, message := "parameter indexes begin at one"}
          if rest.head?.any wordChar then throw {position := next, message := "invalid parameter suffix"}
          lexLoop sqlite fuel rest next
            ({kind := .parameter (.numbered index), position := p} :: acc)
        else if cs.head? == some '|' || cs.head? == some '&' then
          let operator := String.ofList (c :: cs.take 1)
          lexLoop sqlite fuel (cs.drop 1) ((cs.take 1).foldl advance (advance p c))
            ({kind := .symbol operator, position := p} :: acc)
        else
          lexLoop sqlite fuel cs (advance p c)
            ({kind := .symbol "?", position := p} :: acc)
      else if c == '$' then
        if sqlite then throw {position := p, message := "SQLite named $ parameters are outside this profile; use ?NNN"}
        let (raw, rest, next) := readWhile digit cs (advance p c) []
        let some index := raw.toNat? | throw {position := p, message := "expected positive parameter index"}
        if index == 0 then throw {position := p, message := "parameter indexes begin at one"}
        if rest.head?.any wordChar then throw {position := next, message := "invalid parameter suffix"}
        lexLoop sqlite fuel rest next ({kind := .parameter (.numbered index), position := p} :: acc)
      else
        match cs with
        | d :: ds =>
          if c == '-' && d == '-' then
            let (rest, next) := skipLine ds (advance (advance p c) d)
            lexLoop sqlite fuel rest next acc
          else if c == '/' && d == '*' then
            let (rest, next) ← skipBlock (!sqlite) (input.length + 1) 1 ds (advance (advance p c) d)
            lexLoop sqlite fuel rest next acc
          else if !sqlite && pgOperatorChar c then
            let (operator, rest, next) ← readPgOperator input p
            lexLoop sqlite fuel rest next
              ({kind := .symbol operator, position := p} :: acc)
          else if c == '!' && d == '~' then
            match ds with
            | '*' :: rest =>
              lexLoop sqlite fuel rest (advance (advance (advance p c) d) '*')
                ({kind := .symbol "!~*", position := p} :: acc)
            | _ =>
              lexLoop sqlite fuel ds (advance (advance p c) d)
                ({kind := .symbol "!~", position := p} :: acc)
          else if (c == '<' && (d == '>' || d == '=')) || (c == '>' && d == '=') ||
              (c == '!' && d == '=') || (c == ':' && (d == ':' || d == '=')) || (c == '|' && d == '|') ||
              (c == '~' && d == '*') then
            lexLoop sqlite fuel ds (advance (advance p c) d)
              ({kind := .symbol (String.ofList [c,d]), position := p} :: acc)
          else if "(),;*./+-=<>[]:~".contains c then
            lexLoop sqlite fuel cs (advance p c) ({kind := .symbol (String.singleton c), position := p} :: acc)
          else throw {position := p, message := s!"unsupported character '{c}'"}
        | [] =>
          if "(),;*./+-=<>[]:~".contains c then
            lexLoop sqlite fuel cs (advance p c) ({kind := .symbol (String.singleton c), position := p} :: acc)
          else throw {position := p, message := s!"unsupported character '{c}'"}

/-- The entire state is restored by parser alternatives. Only a consumed
primary parameter changes the binding counters; infix question operators and
metadata nullability suffixes never consume a slot. -/
private structure ParseState where
  tokens : List LexToken
  anonymousCount : Nat := 0
  numberedSeen : Bool := false

private abbrev Parser := ReaderT Bool (StateT ParseState (Except ParseError))
private def peek : Parser LexToken := do pure ((← get).tokens.headD {kind := .eof, position := {}})
private def pop : Parser LexToken := do
  let token ← peek
  modify fun state => {state with tokens := state.tokens.tail}
  pure token
private def fail {α : Type} (message : String) : Parser α := do
  throw { position := (← peek).position, message }
/-- Splitting is confined to the explicit anonymous-template extension.
Native infix runs such as ?-, ?!, ?|| and ||- remain maximal and unsupported.
In primary position ?+? / ?||? denote bindings; in infix position 1=? and id+?
keep their established interpretation. Positions advance by the exact prefix. -/
private def splitSymbol (piece : String) : Parser Unit := do
  let token ← peek
  match token.kind with
  | .symbol raw =>
      let rest := String.ofList (raw.toList.drop piece.length)
      unless rest.isEmpty do
        modify fun state => {state with tokens :=
          {token with kind := .symbol piece} ::
          {kind := .symbol rest, position := piece.toList.foldl advance token.position} ::
          state.tokens.tail}
  | _ => pure ()

private def preparePrimaryOperator : Parser Unit := do
  if ← read then return
  match (← peek).kind with
  | .symbol raw =>
      if raw.startsWith "?" &&
          (!raw.startsWith "?|" || raw.startsWith "?||") &&
          (!raw.startsWith "?&" || raw.startsWith "?&&") then
        splitSymbol "?"
      else if raw.contains '?' && (raw.startsWith "+" || raw.startsWith "-") then
        splitSymbol (String.ofList (raw.toList.take 1))
  | _ => pure ()

private def prepareInfixOperator : Parser Unit := do
  if ← read then return
  match (← peek).kind with
  | .symbol raw =>
      if raw.contains '?' && !supportedPgOperators.contains raw then
        match supportedPgOperators.find? (fun op => raw.startsWith (op ++ "?")) with
        | some piece => splitSymbol piece
        | none => fail s!"unsupported PostgreSQL operator '{raw}'"
  | _ => pure ()

private def consumeParameter (parameter : Parameter) : Parser Parameter := do
  let state ← get
  match parameter with
  | .anonymous _ =>
      if state.numberedSeen then fail "cannot mix anonymous and numbered parameter styles"
      let ordinal := state.anonymousCount + 1
      modify fun state => {state with anonymousCount := ordinal}
      pure (.anonymous ordinal)
  | .numbered _ =>
      if state.anonymousCount > 0 then fail "cannot mix anonymous and numbered parameter styles"
      modify fun state => {state with numberedSeen := true}
      pure parameter

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
   "case", "when", "then", "else", "end", "coalesce", "nullif", "greatest", "least", "array", "any", "some",
   "current_date", "current_time", "current_timestamp", "localtime", "localtimestamp",
   "current_user", "session_user", "system_user", "current_role", "current_catalog", "current_schema", "user",
   "isnull", "notnull", "collate", "only", "for",
   "insert", "into", "values", "default", "update", "set", "delete", "returning", "conflict", "do",
   "nothing", "constraint", "create", "alter", "drop", "table", "if", "primary", "key", "unique",
   "column", "add", "rename", "to", "type", "references", "check", "foreign", "cascade", "restrict"]
private def identifier : Parser Name := do
  match (← pop).kind with
  | .quoted s => pure s
  | .word s =>
      -- The legacy clause-boundary list also contains ordinary PostgreSQL
      -- identifiers such as KEY, ADD and TYPE. Use the pinned grammar category
      -- for these words; SQLite retains its existing identifier boundary.
      let unreserved := !(← read) && (SQLean.PostgresGrammar.Generated.keyword s.toLower).any
        (fun keyword => keyword.category == "UNRESERVED_KEYWORD")
      if reserved.contains s.toLower && !unreserved then fail s!"reserved identifier {s}" else pure s
  | _ => fail "expected identifier"

/-- PostgreSQL's `attr_name = ColLabel` permits keywords after a dot.
Each decoded component remains separate from its punctuation. -/
private def attributeName : Parser Name := do
  match (← pop).kind with
  | .quoted name | .word name => pure name
  | _ => fail "expected name component after dot"

private def invalidQualifiedHead (token : LexToken) : Bool :=
  match token.kind with
  | .word name => (SQLean.PostgresGrammar.Generated.keyword name.toLower).any fun keyword =>
      keyword.category == "RESERVED_KEYWORD" || keyword.category == "TYPE_FUNC_NAME_KEYWORD"
  | _ => false

/-- Column-alias lists use ColId rather than the clause-boundary keyword
heuristic. For example KEY is an ordinary unreserved PostgreSQL identifier. -/
private def columnIdentifier : Parser Name := do
  if ← read then return ← identifier
  let token ← pop
  match token.kind with
  | .quoted name => pure name
  | .word name =>
      if invalidQualifiedHead token then fail s!"reserved column identifier {name}"
      else pure name
  | _ => fail "expected column identifier"

/-- PostgreSQL param_name is type_function_name, not ColId or ColLabel. -/
private def argumentName : Parser Name := do
  match (← pop).kind with
  | .quoted name => pure name
  | .word name =>
      let category := (SQLean.PostgresGrammar.Generated.keyword name.toLower).map (·.category)
      if category == some "RESERVED_KEYWORD" || category == some "COL_NAME_KEYWORD" then
        fail "invalid named-argument identifier"
      else pure name
  | _ => fail "expected named-argument identifier"

private def nameTail : Nat → Parser (List Name)
  | 0 => fail "qualified name input bound exceeded"
  | fuel + 1 => do
      if !(← eat ".") then return []
      let name ← attributeName
      pure (name :: (← nameTail fuel))

/-- `extract_arg` is IDENT, Sconst, or six specifically listed keywords.
Other PostgreSQL keywords cannot be treated as identifiers in this position.
Decoded fields always serialize as strings; identifier truncation is excluded. -/
private def extractField : Parser String := do
  match (← pop).kind with
  | .text value => pure value
  | .quoted value =>
      if value.isEmpty || value.utf8ByteSize > 63 then
        fail "EXTRACT identifier fields require 1 to 63 UTF-8 bytes"
      else pure value
  | .word value =>
      if value.utf8ByteSize > 63 then
        fail "EXTRACT identifier fields cannot exceed 63 UTF-8 bytes"
      else if (["year", "month", "day", "hour", "minute", "second"] : List String).contains value ||
          (SQLean.PostgresGrammar.Generated.keyword value).isNone then
        pure value
      else fail "PostgreSQL keyword is not an EXTRACT field"
  | _ => fail "expected EXTRACT field identifier or string"
private def alias? (columnLabel : Bool := false) : Parser (Option Name) := do
  if ← eat "as" then
    return some (← if columnLabel && !(← read) then attributeName else identifier)
  match (← peek).kind with
  | .quoted _ => return some (← identifier)
  | .word s =>
      if columnLabel && !(← read) then
        if (SQLean.PostgresGrammar.Generated.keyword s.toLower).any (fun keyword => !keyword.bareLabel) then
          return none
        return some (← attributeName)
      if !reserved.contains s.toLower then return some (← identifier) else pure none
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
  let values ← separated columnIdentifier fuel
  expect ")"
  pure values
private def optionalNames (fuel : Nat) : Parser (List Name) := do
  if ← isAt "(" then names fuel else pure []

private def intervalFieldsStart : Parser Bool := do
  pure (match (← peek).kind.keyword with
    | .word name => (["year", "month", "day", "hour", "minute", "second"] : List String).contains name
    | _ => false)

/-- Only the thirteen `opt_interval` alternatives are represented. The optional
precision follows SECOND and is never a leading-field width. -/
private def intervalQualifier : Parser (Option (IntervalFields × List Nat)) := do
  unless ← intervalFieldsStart do return none
  let first ← pop
  let fields ← match first.kind.keyword with
    | .word "year" =>
        if ← eat "to" then do expect "month"; pure IntervalFields.yearToMonth else pure .year
    | .word "month" => pure .month
    | .word "day" =>
        if ← eat "to" then
          match (← pop).kind.keyword with
          | .word "hour" => pure .dayToHour
          | .word "minute" => pure .dayToMinute
          | .word "second" => pure .dayToSecond
          | _ => fail "DAY interval range must end in HOUR, MINUTE or SECOND"
        else pure .day
    | .word "hour" =>
        if ← eat "to" then
          match (← pop).kind.keyword with
          | .word "minute" => pure .hourToMinute
          | .word "second" => pure .hourToSecond
          | _ => fail "HOUR interval range must end in MINUTE or SECOND"
        else pure .hour
    | .word "minute" =>
        if ← eat "to" then do expect "second"; pure .minuteToSecond else pure .minute
    | .word "second" => pure .second
    | _ => fail "expected interval field"
  let modifiers ← if fields.allowsPrecision && (← eat "(") then do
    let precision ← natural
    expect ")"
    pure [precision]
    else pure []
  return some (fields, modifiers)

private def arraySuffixes : Nat → TypeName → Parser TypeName
  | 0, _ => fail "array type nesting exceeds parser budget"
  | fuel + 1, typeName => do
      if ← eat "[" then
        if ← read then fail "array types are not supported by the SQLite profile"
        expect "]"
        arraySuffixes fuel (.array typeName)
      else pure typeName

private def dataType (fuel : Nat) : Parser DataType := do
  let token ← pop
  let typeName ← match token.kind.keyword with
    | .word "smallint" | .word "int2" => pure TypeName.smallInt
    | .word "int" | .word "integer" | .word "int4" => pure TypeName.int
    | .word "bigint" | .word "int8" => pure .bigInt
    | .word "text" => pure .text
    | .word "name" => pure .name
    | .word "varchar" => pure .varchar
    | .word "character" | .word "char" =>
        do if ← eat "varying" then pure .varchar else pure .char
    | .word "bool" | .word "boolean" => pure .bool
    | .word "real" | .word "float4" => pure .real
    | .word "double" => do expect "precision"; pure .doublePrecision
    | .word "float8" => pure .doublePrecision
    | .word "numeric" | .word "decimal" => pure .numeric
    | .word "date" => pure .date
    | .word "time" => pure .time
    | .word "timetz" => pure .timeTZ
    | .word "timestamp" => pure .timestamp
    | .word "timestamptz" => pure .timestampTZ
    | .word "interval" => pure .interval
    | .word "uuid" => pure .uuid
    | .word "json" => pure .json
    | .word "jsonb" => pure .jsonb
    | .word "bytea" => pure .bytea
    | _ => fail "unsupported SQL type"
  let modifiers ← if ← eat "(" then do
    let values ← separated natural fuel
    expect ")"
    pure values
    else pure []
  let (typeName, modifiers) ← if typeName == .interval && modifiers.isEmpty then do
    match ← intervalQualifier with
    | some (fields, precision) => pure (TypeName.intervalRange fields, precision)
    | none => pure (typeName, modifiers)
    else pure (typeName, modifiers)
  let typeName ← if typeName == .time || typeName == .timestamp then do
    if ← eat "with" then
      expect "time"
      expect "zone"
      pure (if typeName == .time then .timeTZ else .timestampTZ)
    else if ← eat "without" then
      expect "time"
      expect "zone"
      pure typeName
    else pure typeName
    else pure typeName
  match typeName, modifiers with
  | _, [] => pure ()
  | .varchar, [n] => if n == 0 then fail "VARCHAR length must be positive"
  | .char, [n] =>
      if n == 0 || n > 10485760 then fail "character length must be between 1 and 10485760"
  | .numeric, [p] => if p == 0 || p > 1000 then fail "NUMERIC precision must be between 1 and 1000"
  | .numeric, [p,s] => if p == 0 || p > 1000 || s > 1000 then fail "unsupported NUMERIC precision/scale"
  | .time, [p] | .timeTZ, [p] | .timestamp, [p] | .timestampTZ, [p] | .interval, [p] =>
      if p > 6 then fail "fractional-second precision must be between 0 and 6"
  | .intervalRange fields, [_] =>
      if !fields.allowsPrecision then fail "invalid interval field precision"
  | _, _ => fail "invalid type modifiers"
  let typeName ← arraySuffixes fuel typeName
  pure {name := typeName, modifiers}

private def binInfo (token : Lexeme) : Option (BinOp × Nat) := match token.keyword with
  | .word "or" => some (.or, 1) | .word "and" => some (.and, 2)
  | .symbol "=" => some (.eq, 4) | .symbol "<>" | .symbol "!=" => some (.ne, 4)
  | .symbol "<" => some (.lt, 4) | .symbol "<=" => some (.le, 4)
  | .symbol ">" => some (.gt, 4) | .symbol ">=" => some (.ge, 4)
  | .symbol "+" => some (.add, 6) | .symbol "-" => some (.sub, 6)
  | .symbol "*" => some (.mul, 7) | .symbol "/" => some (.div, 7)
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

private def typeWord (word : String) : Bool :=
  ["smallint", "int2", "int", "integer", "int4", "bigint", "int8", "text", "varchar",
   "character", "char", "bool", "boolean", "real", "float4", "double", "float8",
   "numeric", "decimal", "date", "time", "timetz", "timestamp", "timestamptz",
   "interval", "uuid", "json", "jsonb", "bytea", "name"].contains word

/-- PostgreSQL typed string constants are represented by the same cast tree as
CAST(string AS type). Bare CHARACTER constants are excluded: unlike a bare
CHAR cast they do not supply an implicit length of one. -/
private def typedString (fuel : Nat) : Parser Expr := do
  if ← eat "interval" then
    let prefixPrecision ← if ← eat "(" then do
      let precision ← natural
      expect ")"
      if precision > 6 then fail "fractional-second precision must be between 0 and 6"
      pure (some precision)
      else pure none
    let value ← match (← pop).kind with
      | .text value => pure value
      | _ => fail "INTERVAL requires a string before its field qualifier"
    let type ← match prefixPrecision with
      | some precision =>
          if ← intervalFieldsStart then fail "INTERVAL prefix precision cannot combine with a field qualifier"
          pure (⟨.interval, [precision]⟩ : DataType)
      | none =>
          match ← intervalQualifier with
          | some (fields, precision) => pure ⟨.intervalRange fields, precision⟩
          | none => pure ⟨.interval, []⟩
    return .cast (.literal (.text value)) type
  let type ← dataType fuel
  if type.name.isArray then
    fail "array typed-string constants require CAST or ::"
  let value ← match (← pop).kind with
    | .text value => pure value
    | _ => fail "expected string after SQL type"
  if type.name == .char && type.modifiers.isEmpty then
    fail "bare CHAR typed strings require an unbounded-character type; use an explicit length"
  pure (.cast (.literal (.text value)) type)

/-- This is a lookahead hint, not proof that the entire group is a query. -/
private def queryStart : Parser Bool := do
  let tokens := (← get).tokens.dropWhile (fun t => t.kind == .symbol "(")
  pure (match tokens.head? with
    | some token => token.kind.keyword == .word "select" || token.kind.keyword == .word "with" || token.kind.keyword == .word "values"
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
  -- PostgreSQL's BETWEEN lower bound is b_expr: an unparenthesized
  -- COLLATE is excluded, while function arguments and grouped expressions
  -- re-enter ordinary a_expr. Keep that distinction independent of precedence.
  private def expression (fuel minPrec : Nat) (collateAllowed : Bool := true) : Parser Expr :=
    match fuel with
    | 0 => fail "expression nesting bound exceeded"
    | fuel + 1 => do
      let left ← atom fuel collateAllowed
      tailExpr fuel minPrec left 0 collateAllowed

  private def atom (fuel : Nat) (collateAllowed : Bool := true) : Parser Expr :=
    match fuel with
    | 0 => fail "expression nesting bound exceeded"
    | fuel + 1 => do
      preparePrimaryOperator
      if ← eat "not" then return .unary .not (← expression fuel 3 collateAllowed)
      if ← eat "+" then return .unary .pos (← expression fuel 10 collateAllowed)
      if ← eat "-" then return .unary .neg (← expression fuel 10 collateAllowed)
      if ← eat "null" then return .null
      if ← eat "true" then return .literal (.bool true)
      if ← eat "false" then return .literal (.bool false)
      -- SQL value functions are distinct from ordinary quoted/qualified calls.
      -- CURRENT_SCHEMA is also a type/function keyword and may head a call.
      if ← eat "current_schema" then
        if ← eat "(" then
          return ← callBody fuel ["current_schema"]
        return .contextValue .currentSchema
      if ← eat "current_catalog" then return .contextValue .currentCatalog
      if ← eat "current_user" then return .contextValue .currentUser
      if ← eat "user" then return .contextValue .user
      if ← eat "current_role" then return .contextValue .currentRole
      if ← eat "session_user" then return .contextValue .sessionUser
      if ← eat "system_user" then return .contextValue .systemUser
      if ← eat "array" then
        if ← read then fail "array constructors are not supported by the SQLite profile"
        return ← arrayBracket fuel
      if (← isAt "row") && ((← get).tokens.drop 1).head?.any (fun t => t.kind == .symbol "(") then
        let _ ← pop
        if ← read then fail "ROW constructors require tuple syntax in the SQLite profile"
        expect "("
        let fields ← if ← eat ")" then pure [] else do
          let fields ← separated (expression fuel 0) fuel
          expect ")"
          pure fields
        return .row fields
      if (← isAt "extract") && ((← get).tokens.drop 1).head?.any (fun t => t.kind == .symbol "(") then
        let _ ← pop
        if ← read then fail "EXTRACT is not supported by the SQLite profile"
        expect "("
        let field ← extractField
        expect "from"
        let arg ← expression fuel 0
        expect ")"
        return .extract field arg
      if (← isAt "substring") && ((← get).tokens.drop 1).head?.any (fun t => t.kind == .symbol "(") then
        let _ ← pop
        expect "("
        return ← alternative (callBody fuel ["substring"]) (substringBody fuel)
      if ← eat "case" then
        let operand ← if ← isAt "when" then pure none else do pure (some (← expression fuel 0))
        let branches ← caseBranches fuel
        let otherwise ← if ← eat "else" then do pure (some (← expression fuel 0)) else pure none
        expect "end"
        return .caseExpr operand branches otherwise
      if ← eat "coalesce" then
        expect "("
        let args ← separated (expression fuel 0) fuel
        expect ")"
        return .coalesce args
      if ← eat "greatest" then
        expect "("
        let args ← separated (expression fuel 0) fuel
        expect ")"
        return .greatest args
      if ← eat "least" then
        expect "("
        let args ← separated (expression fuel 0) fuel
        expect ")"
        return .least args
      if ← eat "nullif" then
        expect "("
        let left ← expression fuel 0
        expect ","
        let right ← expression fuel 0
        expect ")"
        return .nullIf left right
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
        let grouped : Parser (Expr × Bool) := do
          let value ← expression fuel 0
          if ← eat "," then
            let fields ← separated (expression fuel 0) fuel
            expect ")"
            return (.row (value :: fields), false)
          expect ")"
          pure (value, true)
        if ← queryStart then
          let (value, indirect) ← alternative (do
            let q ← query fuel
            expect ")"
            pure (.scalarQuery q, true)) grouped
          return ← if indirect then subscriptTail fuel value else pure value
        let (value, indirect) ← grouped
        return ← if indirect then subscriptTail fuel value else pure value
      match (← peek).kind with
      | .number raw =>
        let _ ← pop
        match raw.toNat? with
        | some n => return .literal (.int n)
        | none => return .decimal raw
      | .text value => let _ ← pop; return .literal (.text value)
      | .symbol "?" =>
          let token ← pop
          if !(← read) && (← peek).position.offset == token.position.offset + 1 then
            if let .number _ := (← peek).kind then
              fail "?NNN parameters require the SQLite parser interface"
          let value ← consumeParameter (.anonymous 0)
          return ← subscriptTail fuel (.parameter value)
      | .parameter value =>
          let _ ← pop
          let value ← consumeParameter value
          return ← subscriptTail fuel (.parameter value)
      | .word word =>
        if typeWord word.toLower then
          return ← alternative (typedString fuel) (namedAtom fuel)
        match aggregateFn word.toLower with
        | some fn =>
          let original ← get
          let _ ← pop
          if ← eat "(" then
            -- Ordinary func_application also admits named notation for names
            -- that otherwise take the aggregate path. Binding remains separate.
            let named ← alternative (do
              let value ← callBody fuel [word]
              match value with
              | .namedCall .. => pure (some value)
              | _ => fail "ordinary aggregate call") (pure none)
            if let some value := named then return value
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
          set original
          return ← namedAtom fuel
        | none =>
          namedAtom fuel
      | .quoted _ =>
        namedAtom fuel
      | _ => fail "expected expression"

  private def arrayBracket : Nat → Parser Expr
    | 0 => fail "array constructor nesting bound exceeded"
    | fuel + 1 => do
      expect "["
      if ← eat "]" then return .array []
      -- PostgreSQL's raw nested bracket list is a separate production from
      -- its expression list. Bare brackets are never general expressions.
      let elements ← if ← isAt "[" then separated (arrayBracket fuel) fuel
        else separated (expression fuel 0) fuel
      expect "]"
      pure (.array elements)

  /-- Only columns, parameters and parenthesized expressions call this parser.
  It consumes exactly one contiguous bracket run; parentheses keep runs apart. -/
  private def subscriptTail : Nat → Expr → Parser Expr
    | 0, _ => fail "array subscript nesting bound exceeded"
    | fuel + 1, base => do
      unless ← isAt "[" do return base
      if ← read then fail "array subscripts are not supported by the SQLite profile"
      pure (.subscript base (← subscriptGroups fuel))

  private def subscriptGroups : Nat → Parser (List Subscript)
    | 0 => fail "array subscript input bound exceeded"
    | fuel + 1 => do
      expect "["
      let bound ← if ← eat ":" then do
        let upper ← if ← isAt "]" then pure none else do pure (some (← expression fuel 0))
        pure (Subscript.slice none upper)
        else do
          let lower ← expression fuel 0
          if ← eat ":" then
            let upper ← if ← isAt "]" then pure none else do pure (some (← expression fuel 0))
            pure (.slice (some lower) upper)
          else pure (.index lower)
      expect "]"
      let rest ← if ← isAt "[" then subscriptGroups fuel else pure []
      pure (bound :: rest)

  private def callArgument : Nat → Parser CallArgument
    | 0 => fail "function argument input bound exceeded"
    | fuel + 1 => alternative (do
        let name ← argumentName
        prepareInfixOperator
        let spelling ← if ← eat "=>" then pure NamedArgumentNotation.arrow
          else do expect ":="; pure .assignment
        if ← read then fail "named function arguments are outside the SQLite profile"
        pure (.named name (← expression fuel 0) spelling))
      (do pure (.positional (← expression fuel 0)))

  private def callBody : Nat → List Name → Parser Expr
    | 0, _ => fail "function argument input bound exceeded"
    | fuel + 1, name => do
        let args ← if ← eat ")" then pure [] else do
          let args ← separated (callArgument fuel) fuel
          expect ")"
          pure args
        if args.any (fun arg => arg.name?.isSome) then return .namedCall name args
        return .call name (args.map CallArgument.expression)

  private def substringBody : Nat → Parser Expr
    | 0 => fail "SUBSTRING input bound exceeded"
    | fuel + 1 => do
      let subject ← expression fuel 0
      if ← read then fail "SQL-standard SUBSTRING syntax is not supported by the SQLite profile"
      let (form, args) ← if ← eat "from" then do
        let start ← expression fuel 0
        if ← eat "for" then
          pure (SubstringForm.fromFor, [subject, start, ← expression fuel 0])
        else pure (.from, [subject, start])
        else if ← eat "for" then do
          let count ← expression fuel 0
          if ← eat "from" then
            pure (.forFrom, [subject, count, ← expression fuel 0])
          else pure (.forOnly, [subject, count])
        else do
          expect "similar"
          let pattern ← expression fuel 0
          expect "escape"
          pure (.similar, [subject, pattern, ← expression fuel 0])
      expect ")"
      return .substring form args

  private def namedAtom : Nat → Parser Expr
    | 0 => fail "qualified expression input bound exceeded"
    | fuel + 1 => do
      let names ← qualifiedName fuel
      if ← eat "(" then return ← callBody fuel names
      namedColumn fuel names

  private def namedColumn : Nat → List Name → Parser Expr
    | 0, _ => fail "column reference input bound exceeded"
    | fuel + 1, names => do
      match names with
      | [name] => subscriptTail fuel (.column none name)
      | [qualifier, name] => subscriptTail fuel (.column (some qualifier) name)
      | [schema, qualifier, name] =>
          subscriptTail fuel (.column (some qualifier) name (some schema))
      | _ => fail "column references support at most schema, relation and column components"

  private def qualifiedName : Nat → Parser (List Name)
    | 0 => fail "qualified name input bound exceeded"
    | fuel + 1 => do
      let first ← peek
      -- PostgreSQL type_function_name admits TYPE_FUNC_NAME_KEYWORD as an
      -- unqualified function head. The same token is not a ColId and cannot
      -- become a bare column or the first component of a qualified path.
      let functionKeyword := !(← read) && match first.kind with
        | .word name => (SQLean.PostgresGrammar.Generated.keyword name.toLower).any
            (fun keyword => keyword.category == "TYPE_FUNC_NAME_KEYWORD")
        | _ => false
      let name ← if functionKeyword then attributeName else identifier
      let tail ← nameTail fuel
      if functionKeyword && (!tail.isEmpty || !(← isAt "(")) then
        fail "type/function keyword requires an unqualified function call"
      if !(← read) && !tail.isEmpty && invalidQualifiedHead first then
        fail "the first qualified-name component must be a column identifier"
      pure (name :: tail)

  private def caseBranches : Nat → Parser (List (Expr × Expr))
    | 0 => fail "CASE input bound exceeded"
    | fuel + 1 => do
      expect "when"
      let condition ← expression fuel 0
      expect "then"
      let value ← expression fuel 0
      if ← isAt "when" then return (condition, value) :: (← caseBranches fuel)
      pure [(condition, value)]

  /-- The final argument records a preceding non-associative comparison level.
  PostgreSQL IS predicates bind below ordinary comparisons; postfix null tests
  may repeat and restart comparison parsing. SQLite DISTINCT is left-associative
  at the shared equality/predicate precedence, as are its postfix null aliases. -/
  private def tailExpr (fuel minPrec : Nat) (left : Expr) (compared : Nat)
      (collateAllowed : Bool := true) : Parser Expr :=
    match fuel with
    | 0 => fail "expression input bound exceeded"
    | fuel + 1 => do
      prepareInfixOperator
      let sqlite ← read
      if minPrec <= 11 && (← eat "::") then
        let type ← dataType fuel
        return ← tailExpr (collateAllowed := collateAllowed) fuel minPrec (.cast left type) compared
      let collatePrec := if sqlite then 9 else 8
      if minPrec <= collatePrec && (← isAt "collate") then
        unless collateAllowed do fail "parenthesize COLLATE in a BETWEEN lower bound"
        expect "collate"
        let first ← columnIdentifier
        let rest ← nameTail fuel
        return ← tailExpr fuel minPrec (.collate left (first :: rest)) compared collateAllowed
      let isPredicate ← isAt "is"
      let postfixNull := (← isAt "isnull") || (← isAt "notnull")
      let nullPrec := if sqlite then 4 else 3
      if (isPredicate || postfixNull) && minPrec <= nullPrec then
        if !sqlite && compared == 3 then fail "parenthesize chained IS comparisons"
        if postfixNull then
          let negated ← eat "notnull"
          unless negated do expect "isnull"
          return ← tailExpr (collateAllowed := collateAllowed) fuel minPrec (.isNull left negated) 0
        expect "is"
        let negated ← eat "not"
        if ← eat "distinct" then
          expect "from"
          let right ← expression fuel (nullPrec + 1) collateAllowed
          return ← tailExpr (collateAllowed := collateAllowed) fuel minPrec (.distinctFrom left right negated) (if sqlite then 0 else 3)
        if sqlite then
          -- SQLite IS is an equality-precedence binary operator. A higher
          -- precedence tail belongs to its right operand, even after NULL.
          -- Its documented DISTINCT aliases also preserve TRUE/FALSE handling.
          let right ← expression fuel 5 collateAllowed
          let result := match right with
            | .null => .isNull left negated
            | _ => .distinctFrom left right (!negated)
          return ← tailExpr (collateAllowed := collateAllowed) fuel minPrec result 0
        expect "null"
        return ← tailExpr (collateAllowed := collateAllowed) fuel minPrec (.isNull left negated) 0
      let notPredicate := match (← get).tokens with
        | first :: next :: _ =>
          first.kind.keyword == .word "not" &&
            match next.kind.keyword with
            | .word "in" | .word "between" | .word "like" | .word "ilike" => true
            | _ => false
        | _ => false
      let predStart := (← isAt "in") || (← isAt "between") ||
        (← isAt "like") || (← isAt "ilike") || notPredicate
      if minPrec <= 4 && predStart then
        if !sqlite && compared == 4 then fail "parenthesize chained comparisons"
        let negated ← eat "not"
        let result ← if ← eat "in" then do
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
            let lower ← expression fuel 5 sqlite
            expect "and"
            let upper ← expression fuel 5 collateAllowed
            pure (Expr.between left lower upper negated)
          else do
            let insensitive ← eat "ilike"
            unless insensitive do expect "like"
            let result := Expr.pattern left (← expression fuel 5 collateAllowed) insensitive
            pure (if negated then .unary .not result else result)
        tailExpr (collateAllowed := collateAllowed) fuel minPrec result 4
      else
        let existenceOperator := match (← peek).kind with
          | .symbol "?" => some JsonExistenceOp.key
          | .symbol "?|" => some JsonExistenceOp.any
          | .symbol "?&" => some JsonExistenceOp.all
          | _ => none
        if let some op := existenceOperator then
          if minPrec > 5 then return left
          let _ ← pop
          let right ← expression fuel 6 collateAllowed
          return ← tailExpr (collateAllowed := collateAllowed) fuel minPrec (.jsonExistence op left right) 0
        if ← isAt "&&" then
          if minPrec > 5 then return left
          if ← read then fail "PostgreSQL overlap is not supported by the SQLite profile"
          let _ ← pop
          let right ← expression fuel 6 collateAllowed
          return ← tailExpr (collateAllowed := collateAllowed) fuel minPrec (.overlap left right) 0
        if (← isAt "@>") || (← isAt "<@") then
          if minPrec > 5 then return left
          if ← read then fail "PostgreSQL containment is not supported by the SQLite profile"
          let containedBy ← isAt "<@"
          let _ ← pop
          let right ← expression fuel 6 collateAllowed
          return ← tailExpr (collateAllowed := collateAllowed) fuel minPrec (.containment left right containedBy) 0
        let jsonOperator := match (← peek).kind with
          | .symbol "->" => some JsonAccessOp.field
          | .symbol "->>" => some JsonAccessOp.fieldText
          | .symbol "#>" => some JsonAccessOp.path
          | .symbol "#>>" => some JsonAccessOp.pathText
          | _ => none
        if let some op := jsonOperator then
          if minPrec > 5 then return left
          if ← read then fail "PostgreSQL JSON extraction is not supported by the SQLite profile"
          let _ ← pop
          let right ← expression fuel 6 collateAllowed
          return ← tailExpr (collateAllowed := collateAllowed) fuel minPrec (.jsonAccess op left right) 0
        let regexFlags := match (← peek).kind with
          | .symbol "~" => some (false, false)
          | .symbol "~*" => some (true, false)
          | .symbol "!~" => some (false, true)
          | .symbol "!~*" => some (true, true)
          | _ => none
        if let some (insensitive, negated) := regexFlags then
          if minPrec > 5 then return left
          if ← read then fail "PostgreSQL regular-expression operators are not supported by the SQLite profile"
          let _ ← pop
          let right ← expression fuel 6 collateAllowed
          return ← tailExpr (collateAllowed := collateAllowed) fuel minPrec (.regex left right insensitive negated) 0
        if ← isAt "||" then
          -- PostgreSQL places general operators below arithmetic, whereas
          -- SQLite concatenation binds more tightly than multiplication.
          let prec := if ← read then 8 else 5
          if prec < minPrec then return left
          let _ ← pop
          let right ← expression fuel (prec + 1) collateAllowed
          return ← tailExpr (collateAllowed := collateAllowed) fuel minPrec (.concat left right) 0
        match binInfo (← peek).kind with
        | some (op, ordinaryPrec) =>
          -- Native SQLite inequalities bind above equality/IS/DISTINCT;
          -- its equality, LIKE, BETWEEN and IN family shares one level.
          -- PostgreSQL keeps all six comparisons at the same level.
          let prec := if sqlite && [.lt, .le, .gt, .ge].contains op then 5 else ordinaryPrec
          if prec < minPrec then return left
          if !sqlite && prec == 4 && compared == 4 then fail "parenthesize chained comparisons"
          let _ ← pop
          if ordinaryPrec == 4 && ((← isAt "any") || (← isAt "some") || (← isAt "all")) then
            if ← read then fail "quantified array comparisons are not supported by the SQLite profile"
            let comparison ← match op with
              | .eq => pure ComparisonOp.eq | .ne => pure ComparisonOp.ne
              | .lt => pure ComparisonOp.lt | .le => pure ComparisonOp.le
              | .gt => pure ComparisonOp.gt | .ge => pure ComparisonOp.ge
              | _ => fail "expected comparison operator"
            let quantifier ← if ← eat "any" then pure ArrayQuantifier.any
              else if ← eat "some" then pure ArrayQuantifier.some
              else do expect "all"; pure ArrayQuantifier.all
            expect "("
            let arrayExpression : Parser Expr := do
              let right ← expression fuel 0
              expect ")"
              -- Extra parentheses around a bare SELECT retain SubLink syntax;
              -- an explicit cast or other expression wrapper selects the array form.
              pure (match right with
                | .scalarQuery child => .quantifiedQuery comparison quantifier left child
                | _ => .quantifiedComparison comparison quantifier left right)
            let result ← if ← queryStart then
              alternative (do
                let child ← query fuel
                expect ")"
                pure (.quantifiedQuery comparison quantifier left child)) arrayExpression
              else arrayExpression
            return ← tailExpr (collateAllowed := collateAllowed) fuel minPrec result 4
          let right ← expression fuel (prec + 1) collateAllowed
          tailExpr (collateAllowed := collateAllowed) fuel minPrec (.binary op left right) (if prec == 4 then 4 else 0)
        | none => pure left

  private def selectItem : Nat → Parser SelectItem
    | 0 => fail "projection nesting bound exceeded"
    | fuel + 1 => do
      if ← eat "*" then return .all none
      alternative (do
        let head ← peek
        let first ← identifier
        expect "."
        if !(← read) && invalidQualifiedHead head then
          fail "the first qualified-name component must be a column identifier"
        if ← eat "*" then return .all (some first)
        let second ← attributeName
        expect "."
        expect "*"
        pure (.all (some second) (some first))) (do
        let value ← expression fuel 0
        let alias ← alias? true
        return .expression value alias)

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
            match ← alias? with
            | none => pure (.derivedAnonymous q lateral)
            | some alias =>
              let columns ← optionalNames fuel
              pure (.derived q alias columns lateral)) grouped
        return ← grouped
      if lateral then fail "LATERAL requires a derived table"
      let parts ← qualifiedName fuel
      let (name, schema) ← match parts with
        | [name] => pure (name, none)
        | [schema, name] => pure (name, some schema)
        | _ => fail "relations support at most schema and relation components"
      let alias ← alias?
      let columns ← if alias.isSome then optionalNames fuel else pure []
      pure (.table name alias columns schema)

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
      else if ← eat "values" then
        let row := do
          expect "("
          let cells ← separated (expression fuel 0) fuel
          expect ")"
          pure cells
        let rows ← separated row fuel
        pure {body := .values rows}
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

  private def lockingClauses : Nat → Parser (List LockingClause)
    | 0 => fail "locking clause bound exceeded"
    | fuel + 1 => do
      if !(← eat "for") then return []
      if ← read then fail "SQLite does not support row-locking clauses"
      let strength ←
        if ← eat "update" then pure LockStrength.update
        else if ← eat "no" then do expect "key"; expect "update"; pure .noKeyUpdate
        else if ← eat "share" then pure .share
        else do expect "key"; expect "share"; pure .keyShare
      let targets ← if ← eat "of" then separated identifier fuel else pure []
      let waitPolicy ←
        if ← eat "nowait" then pure LockWaitPolicy.nowait
        else if ← eat "skip" then do expect "locked"; pure .skipLocked
        else pure .block
      let rest ← lockingClauses fuel
      pure (⟨strength, targets, waitPolicy⟩ :: rest)

  private def pagination (fuel : Nat) : Parser (Option Expr × Option Expr × Bool) := do
    let sqlite ← read
    if ← eat "limit" then
      let first ← expression fuel 0
      let (limit, commaOffset) ← if sqlite && (← eat ",") then
        -- Comma LIMIT remains literal-only so rendering never reorders bindings.
        match first with
        | .literal (.int _) => pure (some (.literal (.int (← natural))), some first)
        | _ => fail "SQLite comma LIMIT requires natural-number literals; use LIMIT expression OFFSET expression"
        else pure (some first, none)
      let offset ← if ← eat "offset" then do
        if commaOffset.isSome then fail "OFFSET cannot follow comma LIMIT"
        pure (some (← expression fuel 0))
        else pure commaOffset
      return (limit, offset, false)
    else if ← eat "offset" then
      if sqlite then fail "SQLite OFFSET requires LIMIT first"
      let offset ← expression fuel 0
      let limit ← if ← eat "limit" then pure (some (← expression fuel 0)) else pure none
      return (limit, some offset, limit.isSome)
    else return (none, none, false)

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
      let leadingLocks ← lockingClauses fuel
      let (limit, offset, offsetFirst) ← pagination fuel
      let trailingLocks ← if leadingLocks.isEmpty then lockingClauses fuel else pure []
      let locking := leadingLocks ++ trailingLocks
      let outerModifiers := !orderBy.isEmpty || limit.isSome || offset.isSome || !locking.isEmpty
      let innerModifiers := !q.orderBy.isEmpty || q.limit.isSome || q.offset.isSome || !q.locking.isEmpty
      if (outerModifiers && innerModifiers) || (!ctes.isEmpty && !q.ctes.isEmpty) then
        fail "nested query modifiers require a derived table"
      pure {q with
        ctes := (ctes ++ q.ctes), recursive := (recursive || q.recursive),
        orderBy := (if orderBy.isEmpty then q.orderBy else orderBy),
        limit := limit.or q.limit, offset := offset.or q.offset,
        locking := locking ++ q.locking,
        offsetFirst := if limit.isSome then offsetFirst else q.offsetFirst}
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
  let tokens ← lexLoop sqlite (chars.length + 1) chars {} []
  let (result, _) ← (do
    let value ← parser (max tokens.length chars.length * 12 + 64)
    let _ ← eat ";"
    match (← peek).kind with
    | .eof => pure value
    | _ => fail "unexpected trailing SQL input").run sqlite |>.run {tokens}
  pure result

/-- Parse one statement. Mixing numbered and anonymous parameters is rejected. -/
def parse (source : String) : Except ParseError Statement := runComplete source statement
/-- Parse a scalar expression, including explicit casts and nested queries. -/
def parseExpression (source : String) : Except ParseError Expr :=
  runComplete source (fun fuel => expression fuel 0)
/-- Parse one supported concrete type, preserving its type modifiers. -/
def parseDataType (source : String) : Except ParseError DataType :=
  runComplete source dataType

/-- Parse comma-separated concrete parameter declarations. A trailing `?`
marks a nullable declaration; commas inside type modifiers stay inside the
type. This is metadata syntax, not SQL parameter-value interpolation. -/
def parseParameterDeclarations (source : String) : Except ParseError (List (DataType × Bool)) :=
  runComplete source fun fuel => do
    if (← peek).kind == .eof then return []
    separated (do
      let type ← alternative (dataType fuel) (do
        let typeName ← match (← pop).kind.keyword with
          | .word "int32" => pure TypeName.int
          | .word "int64" => pure .bigInt
          | .word "float32" => pure .real
          | .word "float64" | .word "double" => pure .doublePrecision
          | _ => fail "unsupported parameter type"
        pure {name := typeName})
      let nullable ← match (← peek).kind with
        | .symbol "?" => do let _ ← pop; pure true
        | _ => pure false
      pure (type, nullable)) fuel
/-- Uniform query entry point, independent of legacy SELECT AST dispatch. -/
def parseQuery (source : String) : Except ParseError Query := runComplete source query

/-- SQLite parameter identities, preserved identifier spelling, non-nesting
comments, and left-associative compound/join precedence. Target-profile
coverage is checked separately by the rendering boundary. -/
def parseSQLiteQuery (source : String) : Except ParseError Query := runComplete source query true

def parseSQLite (source : String) : Except ParseError Statement := runComplete source statement true

end SQLean.Advanced
