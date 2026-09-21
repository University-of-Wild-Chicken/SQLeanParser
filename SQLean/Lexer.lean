import SQLean.AST

/-! SQL tokens, comments, escaping, and character-based source positions.

Unquoted identifiers are ASCII and folded to lowercase. Double-quoted
identifiers preserve spelling. Both identifier and string quotes are escaped
by doubling their delimiter. Block comments are not nested.
-/

namespace SQLean

private def advance (pos : SourcePos) (c : Char) : SourcePos :=
  if c == '\n' then
    { offset := pos.offset + 1, line := pos.line + 1, column := 1 }
  else
    { pos with offset := pos.offset + 1, column := pos.column + 1 }

private def isDigit (c : Char) : Bool := c >= '0' && c <= '9'

private def isWordStart (c : Char) : Bool :=
  (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_'

private def isWordContinue (c : Char) : Bool := isWordStart c || isDigit c

private def isWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

private def readWord : List Char → SourcePos → List Char → String × List Char × SourcePos
  | [], pos, acc => (String.ofList acc.reverse, [], pos)
  | c :: rest, pos, acc =>
    if isWordContinue c then
      readWord rest (advance pos c) (c.toLower :: acc)
    else
      (String.ofList acc.reverse, c :: rest, pos)

private def readNumber : List Char → SourcePos → Nat → Nat × List Char × SourcePos
  | [], pos, value => (value, [], pos)
  | c :: rest, pos, value =>
    if isDigit c then
      readNumber rest (advance pos c) (value * 10 + (c.toNat - '0'.toNat))
    else
      (value, c :: rest, pos)

private def skipLine : List Char → SourcePos → List Char × SourcePos
  | [], pos => ([], pos)
  | c :: rest, pos =>
    if c == '\n' then (rest, advance pos c)
    else skipLine rest (advance pos c)

private def skipBlock (opening : SourcePos) :
    List Char → SourcePos → Except ParseError (List Char × SourcePos)
  | [], _ => .error { position := opening, message := "unterminated block comment" }
  | c :: rest, pos =>
    match rest with
    | d :: tail =>
      if c == '*' && d == '/' then
        .ok (tail, advance (advance pos c) d)
      else skipBlock opening rest (advance pos c)
    | [] => skipBlock opening rest (advance pos c)

private def readQuoted (delimiter : Char) (opening : SourcePos) (description : String) :
    List Char → SourcePos → List Char → Except ParseError (String × List Char × SourcePos)
  | [], _, _ => .error { position := opening, message := "unterminated " ++ description }
  | c :: rest, pos, acc =>
    if c == delimiter then
      match rest with
      | d :: tail =>
        if d == delimiter then
          readQuoted delimiter opening description tail (advance (advance pos c) d) (c :: acc)
        else .ok (String.ofList acc.reverse, rest, advance pos c)
      | [] => .ok (String.ofList acc.reverse, [], advance pos c)
    else readQuoted delimiter opening description rest (advance pos c) (c :: acc)

private def isSingleSymbol (c : Char) : Bool :=
  c == '(' || c == ')' || c == ',' || c == ';' || c == '*' ||
  c == '/' || c == '+' || c == '-' || c == '=' || c == '<' || c == '>'

private def isDoubleSymbol (c d : Char) : Bool :=
  (c == '<' && (d == '=' || d == '>')) ||
  ((c == '>' || c == '!') && d == '=')

private def lexLoop : Nat → List Char → SourcePos → List Token → Except ParseError (List Token)
  | 0, _, pos, _ => .error { position := pos, message := "lexer exhausted its input bound" }
  | fuel + 1, input, pos, acc => do
    match input with
    | [] => return ({ kind := .eof, position := pos } :: acc).reverse
    | c :: rest =>
      if isWhitespace c then
        lexLoop fuel rest (advance pos c) acc
      else if isWordStart c then
        let (word, remaining, nextPos) := readWord rest (advance pos c) [c.toLower]
        lexLoop fuel remaining nextPos ({ kind := .word word, position := pos } :: acc)
      else if isDigit c then
        let (value, remaining, nextPos) := readNumber rest (advance pos c) (c.toNat - '0'.toNat)
        lexLoop fuel remaining nextPos ({ kind := .number value, position := pos } :: acc)
      else if c == '\'' then
        let (value, remaining, nextPos) ← readQuoted '\'' pos "string literal" rest (advance pos c) []
        lexLoop fuel remaining nextPos ({ kind := .string value, position := pos } :: acc)
      else if c == '"' then
        let (value, remaining, nextPos) ← readQuoted '"' pos "quoted identifier" rest (advance pos c) []
        if value.isEmpty then
          throw { position := pos, message := "quoted identifiers must not be empty" }
        lexLoop fuel remaining nextPos ({ kind := .quotedIdent value, position := pos } :: acc)
      else
        match rest with
        | d :: tail =>
          if c == '-' && d == '-' then
            let (remaining, nextPos) := skipLine tail (advance (advance pos c) d)
            lexLoop fuel remaining nextPos acc
          else if c == '/' && d == '*' then
            let (remaining, nextPos) ← skipBlock pos tail (advance (advance pos c) d)
            lexLoop fuel remaining nextPos acc
          else if isDoubleSymbol c d then
            lexLoop fuel tail (advance (advance pos c) d)
              ({ kind := .symbol (String.ofList [c, d]), position := pos } :: acc)
          else if isSingleSymbol c then
            lexLoop fuel rest (advance pos c)
              ({ kind := .symbol (String.singleton c), position := pos } :: acc)
          else
            throw { position := pos, message := s!"unsupported character '{c}'" }
        | [] =>
          if isSingleSymbol c then
            lexLoop fuel rest (advance pos c)
              ({ kind := .symbol (String.singleton c), position := pos } :: acc)
          else
            throw { position := pos, message := s!"unsupported character '{c}'" }

/-- Tokenize SQL, ending successful results with exactly one end-of-input token.
Positions count characters (not UTF-8 bytes), beginning at line 1, column 1.
The finite recursion budget is the character count plus one; each loop consumes
at least one character before recurring.
-/
def lex (source : String) : Except ParseError (List Token) :=
  let chars := source.toList
  lexLoop (chars.length + 1) chars {} []

end SQLean
