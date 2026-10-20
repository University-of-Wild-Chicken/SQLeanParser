import SQLean.PostgresGrammar.Generated.Symbols

/-! PostgreSQL 16 lexical forms, for UTF-8 SQL with
`standard_conforming_strings = on`. Raw spelling and UTF-8 byte positions are
retained. This scanner does not resolve names or interpret literal SQL values.
The certificate proves lossless source reconstruction; PostgreSQL's literal
input functions and grammar C semantic actions are separate obligations. -/
namespace SQLean.PostgresGrammar
set_option maxRecDepth 2048

structure LexError where
  offset : Nat
  message : String
  deriving Repr, BEq, DecidableEq

structure SourcePiece where
  trivia : String
  token : Token
  deriving Repr, BEq, DecidableEq

def reconstruct (pieces : List SourcePiece) (trailing : String) : String :=
  pieces.foldr (fun piece rest => piece.trivia ++ piece.token.lexeme ++ rest) trailing

structure Lexed (source : String) where
  pieces : List SourcePiece
  trailing : String
  preserved : reconstruct pieces trailing = source

def Lexed.tokens {source : String} (result : Lexed source) : List Token :=
  result.pieces.map SourcePiece.token

private def space (c : Char) : Bool := " \t\n\r\u000c".contains c
private def newline (c : Char) : Bool := c == '\n' || c == '\r'
private def digit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
private def wordStart (c : Char) : Bool :=
  c.isAlpha || c == '_' || c.toNat ≥ 128
private def wordCont (c : Char) : Bool := wordStart c || digit c || c == '$'
private def operatorChar (c : Char) : Bool := "~!@#^&|`?+-*/%<>=".contains c
private def selfChar (c : Char) : Bool := ",()[].;:+-*/%^<>=".contains c
private def hexDigit (c : Char) : Bool :=
  digit c || ('a' ≤ c.toLower && c.toLower ≤ 'f')

private def startsWith (pattern input : List Char) : Bool :=
  input.take pattern.length == pattern

private def blockComment : Nat → List Char → Nat → Nat → Except String Nat
  | 0, _, _, _ => .error "unterminated block comment"
  | fuel + 1, input, depth, consumed =>
      if startsWith ['/', '*'] input then
        blockComment fuel (input.drop 2) (depth + 1) (consumed + 2)
      else if startsWith ['*', '/'] input then
        if depth == 1 then .ok (consumed + 2)
        else blockComment fuel (input.drop 2) (depth - 1) (consumed + 2)
      else match input with
        | [] => .error "unterminated block comment"
        | _ :: rest => blockComment fuel rest depth (consumed + 1)

private def trivia : Nat → List Char → Nat → Except String Nat
  | 0, _, _ => .error "trivia scanner exhausted its input bound"
  | fuel + 1, input, consumed => do
      if startsWith ['-', '-'] input then
        let count := (input.takeWhile (!newline ·)).length
        trivia fuel (input.drop count) (consumed + count)
      else if startsWith ['/', '*'] input then
        let count ← blockComment (input.length + 1) (input.drop 2) 1 2
        trivia fuel (input.drop count) (consumed + count)
      else match input with
        | c :: rest =>
            if space c then trivia fuel rest (consumed + 1) else pure consumed
        | [] => pure consumed

/-- String continuation allows whitespace and line comments, but not block
comments. At least one newline must separate the quoted segments. -/
private def continuation : Nat → List Char → Nat → Bool → Option Nat
  | 0, _, _, _ => none
  | fuel + 1, input, consumed, sawNewline =>
      if startsWith ['-', '-'] input then
        let count := (input.takeWhile (!newline ·)).length
        continuation fuel (input.drop count) (consumed + count) sawNewline
      else match input with
        | c :: rest =>
            if space c then
              continuation fuel rest (consumed + 1) (sawNewline || newline c)
            else if c == '\'' && sawNewline then some (consumed + 1)
            else none
        | [] => none

private def quoted (delimiter : Char) (backslash doubled continueString : Bool) :
    Nat → List Char → Nat → Except String Nat
  | 0, _, _ => .error "unterminated quoted token"
  | fuel + 1, input, consumed =>
      match input with
      | [] => .error "unterminated quoted token"
      | c :: rest =>
          if c == '\u0000' then .error "NUL is not permitted in SQL source"
          else if backslash && c == '\\' then
            match rest with
            | [] => .error "unterminated escape string"
            | '\u0000' :: _ => .error "NUL is not permitted in SQL source"
            | escaped :: tail =>
                if escaped == 'u' || escaped == 'U' then
                  let count := if escaped == 'u' then 4 else 8
                  if (tail.take count).length != count || !(tail.take count).all hexDigit then
                    .error "invalid Unicode escape in escape string"
                  else quoted delimiter backslash doubled continueString fuel
                    (tail.drop count) (consumed + 2 + count)
                else quoted delimiter backslash doubled continueString fuel tail (consumed + 2)
          else if c == delimiter then
            if doubled && rest.head? == some delimiter then
              quoted delimiter backslash doubled continueString fuel (rest.drop 1) (consumed + 2)
            else if continueString then
              match continuation (rest.length + 1) rest 0 false with
              | some count =>
                  quoted delimiter backslash doubled continueString fuel
                    (rest.drop count) (consumed + 1 + count)
              | none => .ok (consumed + 1)
            else .ok (consumed + 1)
          else quoted delimiter backslash doubled continueString fuel rest (consumed + 1)

private def dollarEnd (delimiter : List Char) :
    Nat → List Char → Nat → Except String Nat
  | 0, _, _ => .error "unterminated dollar-quoted string"
  | fuel + 1, input, consumed =>
      if startsWith delimiter input then .ok (consumed + delimiter.length)
      else match input with
        | [] => .error "unterminated dollar-quoted string"
        | '\u0000' :: _ => .error "NUL is not permitted in SQL source"
        | _ :: rest => dollarEnd delimiter fuel rest (consumed + 1)

private def digits (allowed : Char → Bool) : List Char → Nat
  | [] => 0
  | c :: rest =>
      if allowed c then 1 + digits allowed rest
      else match rest with
        | d :: tail => if c == '_' && allowed d then 2 + digits allowed tail else 0
        | [] => 0

private def integerValue (base : Nat) (input : List Char) : Nat :=
  input.foldl (fun value c =>
    if c == '_' then value else
    let n := if digit c then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
    value * base + n) 0

private inductive QuoteMode where
  | plain
  | escaped
  | unicode (escape : Char)

private def unicodeUnit (mode : QuoteMode) (input : List Char) :
    Except String (Nat × Nat) := do
  let (skip, count) ← match mode with
    | .escaped => match input.head? with
      | some 'u' => pure (1, 4)
      | some 'U' => pure (1, 8)
      | _ => throw "Unicode surrogate must be followed by a Unicode escape"
    | .unicode _ => pure (if input.head? == some '+' then (1, 6) else (0, 4))
    | .plain => throw "Unicode escape in ordinary string"
  let digits := (input.drop skip).take count
  if digits.length != count || !digits.all hexDigit then throw "invalid Unicode escape"
  pure (integerValue 16 digits, skip + count)

private def unicodeBytes (mode : QuoteMode) (escape : Char) (input : List Char) :
    Except String (List UInt8 × Nat) := do
  let (value, count) ← unicodeUnit mode input
  let (scalar, consumed) ←
    if 0xD800 ≤ value && value ≤ 0xDBFF then do
      let remaining := input.drop count
      if remaining.head? != some escape then throw "invalid Unicode surrogate pair"
      let (second, nextCount) ← unicodeUnit mode (remaining.drop 1)
      if second < 0xDC00 || second > 0xDFFF then throw "invalid Unicode surrogate pair"
      pure (0x10000 + (value - 0xD800) * 1024 + (second - 0xDC00), count + 1 + nextCount)
    else if 0xDC00 ≤ value && value ≤ 0xDFFF then throw "invalid Unicode surrogate pair"
    else pure (value, count)
  if scalar == 0 || scalar > 0x10FFFF then throw "invalid Unicode code point"
  pure (String.utf8EncodeChar (Char.ofNat scalar), consumed)

private def escapedBytes (input : List Char) : Except String (List UInt8 × Nat) := do
  let c := input.headD '\u0000'
  if c == 'u' || c == 'U' then return ← unicodeBytes .escaped '\\' input
  let octal := (input.takeWhile (fun d => '0' ≤ d && d ≤ '7')).take 3
  if !octal.isEmpty then return ([UInt8.ofNat (integerValue 8 octal)], octal.length)
  if c == 'x' then
    let hex := ((input.drop 1).takeWhile hexDigit).take 2
    if !hex.isEmpty then return ([UInt8.ofNat (integerValue 16 hex)], hex.length + 1)
  let decoded := match c with
    | 'b' => '\u0008' | 'f' => '\u000c' | 'n' => '\n' | 'r' => '\r' | 't' => '\t'
    | _ => c
  pure (String.utf8EncodeChar decoded, 1)

private def decodeQuoted (delimiter : Char) (mode : QuoteMode) :
    Nat → List Char → List UInt8 → Except String String
  | 0, _, _ => .error "unterminated literal"
  | fuel + 1, input, acc => do
      let c := input.headD '\u0000'
      if c == delimiter then
        if (input.drop 1).head? == some delimiter then
          return ← decodeQuoted delimiter mode fuel (input.drop 2) ((String.utf8EncodeChar c).reverse ++ acc)
        else
          let remaining := input.drop 1
          match if delimiter == '\'' then continuation (remaining.length + 1) remaining 0 false
              else none with
          | some count => return ← decodeQuoted delimiter mode fuel (remaining.drop count) acc
          | none =>
              if acc.contains 0 then throw "NUL is not permitted in string values"
              match String.fromUTF8? acc.reverse.toByteArray with
              | some value => pure value
              | none => throw "escape string is not valid UTF-8"
      else if c == '\u0000' then throw "unterminated literal"
      else match mode with
        | .escaped =>
            if c == '\\' then
              let (bytes, count) ← escapedBytes (input.drop 1)
              return ← decodeQuoted delimiter mode fuel (input.drop (count + 1)) (bytes.reverse ++ acc)
            else return ← decodeQuoted delimiter mode fuel (input.drop 1) ((String.utf8EncodeChar c).reverse ++ acc)
        | .unicode escape =>
            if c == escape then
              if (input.drop 1).head? == some escape then
                return ← decodeQuoted delimiter mode fuel (input.drop 2)
                  ((String.utf8EncodeChar c).reverse ++ acc)
              else
                let (bytes, count) ← unicodeBytes mode escape (input.drop 1)
                return ← decodeQuoted delimiter mode fuel (input.drop (count + 1)) (bytes.reverse ++ acc)
            else return ← decodeQuoted delimiter mode fuel (input.drop 1) ((String.utf8EncodeChar c).reverse ++ acc)
        | .plain => return ← decodeQuoted delimiter mode fuel (input.drop 1) ((String.utf8EncodeChar c).reverse ++ acc)

private def stringValue (raw : String) : Except String String := do
  let input := raw.toList
  if input.head? == some '$' then
    let delimiter := '$' :: ((input.drop 1).takeWhile (· != '$')) ++ ['$']
    return String.ofList ((input.drop delimiter.length).take (input.length - 2 * delimiter.length))
  let escaped := input.head?.any (fun c => c == 'e' || c == 'E')
  decodeQuoted '\'' (if escaped then .escaped else .plain) (input.length + 1)
    (input.drop (if escaped then 2 else 1)) []

private def unicodeValue (raw : String) (escape : Char) : Except String String :=
  let input := raw.toList
  decodeQuoted (input[2]!) (.unicode escape) (input.length + 1) (input.drop 3) []

private def numeric (input : List Char) : Except String (String × Nat) := do
  let (base, allowed) : Nat × (Char → Bool) :=
    if startsWith ['0', 'x'] input || startsWith ['0', 'X'] input then (16, hexDigit)
    else if startsWith ['0', 'o'] input || startsWith ['0', 'O'] input then
      (8, fun c => '0' ≤ c && c ≤ '7')
    else if startsWith ['0', 'b'] input || startsWith ['0', 'B'] input then
      (2, fun c => c == '0' || c == '1')
    else (10, digit)
  if base != 10 then
    let count := digits allowed (input.drop 2)
    if count == 0 then throw "invalid base-startsWithed integer"
    if (input.drop (count + 2)).head?.any (fun c => wordStart c || digit c) then
      throw "trailing junk after integer"
    let value := integerValue base ((input.drop 2).take count)
    return (if value ≤ 2147483647 then "ICONST" else "FCONST", count + 2)
  let before := digits digit input
  let rest := input.drop before
  let hasDot := rest.head? == some '.' && !startsWith ['.', '.'] rest
  let after := if hasDot && (rest.drop 1).head?.any digit then digits digit (rest.drop 1) else 0
  let count := before + (if hasDot then 1 + after else 0)
  let exponent := (input.drop count).head?.any (fun c => c == 'e' || c == 'E')
  let count ← if exponent then do
      let sign := (input.drop (count + 1)).head?.any (fun c => c == '+' || c == '-')
      let offset := count + 1 + (if sign then 1 else 0)
      let expDigits := digits digit (input.drop offset)
      if expDigits == 0 || !(input.drop offset).head?.any digit then
        throw "invalid exponent"
      pure (offset + expDigits)
    else pure count
  if (input.drop count).head?.any wordStart then throw "trailing junk after numeric literal"
  let floating := hasDot || exponent || integerValue 10 (input.take count) > 2147483647
  return (if floating then "FCONST" else "ICONST", count)

private def operatorLength : List Char → Nat
  | [] => 0
  | c :: rest =>
      if startsWith ['/', '*'] (c :: rest) || startsWith ['-', '-'] (c :: rest) then 0
      else if operatorChar c then 1 + operatorLength rest else 0

private def operatorToken (input : List Char) : Except String (String × Nat) := do
  let raw := input.take (operatorLength input)
  let special := raw.any (fun c => "~!@#^&|`?%".contains c)
  let trimmed := if special then raw else
    let kept := (raw.reverse.dropWhile (fun c => c == '+' || c == '-')).reverse
    if kept.isEmpty then raw.take 1 else kept
  if trimmed.length ≥ 64 then throw "operator too long"
  let text := String.ofList trimmed
  let name := match text with
    | "=>" => "EQUALS_GREATER"
    | "<=" => "LESS_EQUALS"
    | ">=" => "GREATER_EQUALS"
    | "<>" | "!=" => "NOT_EQUALS"
    | _ => if trimmed.length == 1 && trimmed.head?.any selfChar then
        "'" ++ text ++ "'" else "Op"
  return (name, trimmed.length)

private def tokenShape (input : List Char) : Except String (String × Nat) := do
  let c := input.headD '\u0000'
  if c == '\'' then
    return ("SCONST", ← quoted '\'' false true true (input.length + 1) (input.drop 1) 1)
  if c == '"' then
    let count ← quoted '"' false true false (input.length + 1) (input.drop 1) 1
    if count == 2 then throw "zero-length delimited identifier"
    return ("IDENT", count)
  if (c == 'u' || c == 'U') && (startsWith ['&', '\''] (input.drop 1) ||
      startsWith ['&', '"'] (input.drop 1)) then
    let delim := input[2]!
    let count ← quoted delim false true (delim == '\'') (input.length + 1) (input.drop 3) 3
    if delim == '"' && count == 4 then throw "zero-length delimited identifier"
    return (if delim == '"' then "UIDENT" else "USCONST", count)
  if (c.toLower == 'e' || c.toLower == 'b' || c.toLower == 'x') &&
      (input.drop 1).head? == some '\'' then
    let name := if c.toLower == 'b' then "BCONST" else
      if c.toLower == 'x' then "XCONST" else "SCONST"
    let escaped := c.toLower == 'e'
    return (name, ← quoted '\'' escaped escaped true (input.length + 1) (input.drop 2) 2)
  if c.toLower == 'n' && (input.drop 1).head? == some '\'' then return ("NCHAR", 1)
  if wordStart c then
    let word := input.takeWhile wordCont
    let lower := (String.ofList word).toLower
    match Generated.keyword lower with
    | some keyword =>
        match Generated.terminals.find? (fun info => info.symbol == keyword.symbol) with
        | some info => return (info.name, word.length)
        | none => throw "generated keyword is missing its terminal"
    | none => return ("IDENT", word.length)
  if digit c || (c == '.' && (input.drop 1).head?.any digit) then return ← numeric input
  if c == '$' then
    let rest := input.drop 1
    if rest.head?.any digit then
      let count := (rest.takeWhile digit).length + 1
      if (input.drop count).head?.any wordStart then throw "trailing junk after parameter"
      return ("PARAM", count)
    let tag := if rest.head?.any wordStart then
      rest.takeWhile (fun ch => wordStart ch || digit ch) else []
    if (rest.drop tag.length).head? == some '$' then
      let delimiter := '$' :: (tag ++ ['$'])
      return ("SCONST", ← dollarEnd delimiter (input.length + 1)
        (input.drop delimiter.length) delimiter.length)
    throw "invalid dollar-quoted delimiter"
  if startsWith [':', ':'] input then return ("TYPECAST", 2)
  if startsWith [':', '='] input then return ("COLON_EQUALS", 2)
  if startsWith ['.', '.'] input then return ("DOT_DOT", 2)
  if operatorChar c then return ← operatorToken input
  if selfChar c then return ("'" ++ String.singleton c ++ "'", 1)
  throw s!"unexpected character {repr c}"

private def lexRaw : Nat → List Char → Nat → List SourcePiece →
    Except LexError (List SourcePiece × String)
  | 0, _, offset, _ => .error ⟨offset, "lexer exhausted its input bound"⟩
  | fuel + 1, input, offset, acc => do
      let count ← (trivia (input.length + 1) input 0).mapError (⟨offset, ·⟩)
      let gap := String.ofList (input.take count)
      let rest := input.drop count
      let start := offset + gap.utf8ByteSize
      if rest.isEmpty then return (acc.reverse, gap)
      let (name, length) ← (tokenShape rest).mapError (⟨start, ·⟩)
      if length == 0 then throw ⟨start, "token scanner made no progress"⟩
      let some kind := Generated.tokenKind name
        | throw ⟨start, s!"generated terminal missing: {name}"⟩
      let raw := String.ofList (rest.take length)
      let finish := start + raw.utf8ByteSize
      let token : Token := ⟨kind, raw, start, finish⟩
      lexRaw fuel (rest.drop length) finish (⟨gap, token⟩ :: acc)

private def hasKind (token : Token) (name : String) : Bool :=
  Generated.tokenKind name == some token.kind

private def withKind (piece : SourcePiece) (name : String) : SourcePiece :=
  { piece with token.kind := (Generated.tokenKind name).getD piece.token.kind }

private def lookaheadName (token : Token) (next : Token) : Option String :=
  if hasKind token "FORMAT" && hasKind next "JSON" then some "FORMAT_LA"
  else if hasKind token "NOT" && ["BETWEEN", "IN_P", "LIKE", "ILIKE", "SIMILAR"].any
      (hasKind next ·) then some "NOT_LA"
  else if hasKind token "NULLS_P" && ["FIRST_P", "LAST_P"].any (hasKind next ·) then
    some "NULLS_LA"
  else if hasKind token "WITH" && ["TIME", "ORDINALITY"].any (hasKind next ·) then
    some "WITH_LA"
  else if hasKind token "WITHOUT" && hasKind next "TIME" then some "WITHOUT_LA"
  else none

private def unicodeEscapeChar (value : String) : Option Char :=
  match value.toList with
  | [c] =>
      if hexDigit c || c == '+' || c == '\'' || c == '"' || space c then none else some c
  | _ => none

private def filterTokens : Nat → List SourcePiece → Except LexError (List SourcePiece)
  | 0, _ => .error ⟨0, "token filter exhausted its input bound"⟩
  | _ + 1, [] => pure []
  | fuel + 1, piece :: rest => do
      if hasKind piece.token "UIDENT" || hasKind piece.token "USCONST" then
        let name := if hasKind piece.token "UIDENT" then "IDENT" else "SCONST"
        match rest with
        | escape :: value :: tail =>
            if hasKind escape.token "UESCAPE" then
              if !hasKind value.token "SCONST" then
                throw ⟨value.token.startOffset, "UESCAPE requires a simple string literal"⟩
              let decoded ← (stringValue value.token.lexeme).mapError (⟨value.token.startOffset, ·⟩)
              let some escapeChar := unicodeEscapeChar decoded
                | throw ⟨value.token.startOffset, "invalid Unicode escape character"⟩
              if escapeChar.utf8Size != 1 then
                throw ⟨value.token.startOffset, "invalid Unicode escape character"⟩
              let _ ← (unicodeValue piece.token.lexeme escapeChar).mapError
                (⟨piece.token.startOffset, ·⟩)
              let renamed := withKind piece name
              let raw := piece.token.lexeme ++ escape.trivia ++ escape.token.lexeme ++
                value.trivia ++ value.token.lexeme
              let merged := { renamed with token := { renamed.token with
                lexeme := raw
                endOffset := value.token.endOffset } }
              return merged :: (← filterTokens fuel tail)
            else
              let _ ← (unicodeValue piece.token.lexeme '\\').mapError (⟨piece.token.startOffset, ·⟩)
              return withKind piece name :: (← filterTokens fuel rest)
        | [escape] =>
            if hasKind escape.token "UESCAPE" then
              throw ⟨escape.token.endOffset, "UESCAPE requires a simple string literal"⟩
            else
              let _ ← (unicodeValue piece.token.lexeme '\\').mapError (⟨piece.token.startOffset, ·⟩)
              return withKind piece name :: (← filterTokens fuel rest)
        | [] =>
            let _ ← (unicodeValue piece.token.lexeme '\\').mapError (⟨piece.token.startOffset, ·⟩)
            return [withKind piece name]
      else
        if hasKind piece.token "SCONST" then
          let _ ← (stringValue piece.token.lexeme).mapError (⟨piece.token.startOffset, ·⟩)
        let head := match rest.head? with
          | some next => match lookaheadName piece.token next.token with
            | some name => withKind piece name
            | none => piece
          | none => piece
        return head :: (← filterTokens fuel rest)

/-- Scan and apply PostgreSQL's contextual token substitutions. The returned
proof binds exact source bytes, including all comments and whitespace. -/
def lex (source : String) : Except LexError (Lexed source) := do
  if source.contains '\u0000' then throw ⟨0, "NUL is not permitted in SQL source"⟩
  let (raw, trailing) ← lexRaw (source.length + 1) source.toList 0 []
  let pieces ← filterTokens (raw.length + 1) raw
  if preserved : reconstruct pieces trailing = source then
    pure ⟨pieces, trailing, preserved⟩
  else throw ⟨0, "source reconstruction check failed"⟩

theorem lex_source_preserved {source : String} (result : Lexed source) :
    reconstruct result.pieces result.trailing = source :=
  result.preserved

end SQLean.PostgresGrammar
