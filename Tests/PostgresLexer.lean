import SQLean.PostgresGrammar.Lexer
import Tests.Support

namespace SQLean.Tests
open PostgresGrammar

private def lexicalCases : List (String × List String) := [
  ("select 1", ["SELECT", "ICONST"]),
  ("SeLeCt α, \"select\", _x$x FROM t", ["SELECT", "IDENT", "','", "IDENT", "','", "IDENT", "FROM", "IDENT"]),
  ("/* outer /* inner */ end */ SELECT -- line\n 1;", ["SELECT", "ICONST", "';'"]),
  ("'a''b'", ["SCONST"]),
  ("'a'\n'b'", ["SCONST"]),
  ("'a' -- continuation\n 'b'", ["SCONST"]),
  ("'a' 'b'", ["SCONST", "SCONST"]),
  ("'a' /*\n*/ 'b'", ["SCONST", "SCONST"]),
  ("E'a\\'b'", ["SCONST"]),
  ("e'\\u0041\\U00000042'", ["SCONST"]),
  ("B'0101'\n'10'", ["BCONST"]),
  ("x'ff00'", ["XCONST"]),
  ("N'hello'", ["NCHAR", "SCONST"]),
  ("$$a ' $1 /*x*/$$", ["SCONST"]),
  ("$tag$a$other$b$tag$", ["SCONST"]),
  ("$λ$x$λ$", ["SCONST"]),
  ("U&'d\\0061t'", ["SCONST"]),
  ("U&\"d\\0061t\"", ["IDENT"]),
  ("U&'d!0061t' UESCAPE '!'", ["SCONST"]),
  ("U&'d!0061t' UESCAPE E'\\x21'", ["SCONST"]),
  ("U&'d!0061t' UESCAPE $$!$$", ["SCONST"]),
  ("U&'\\D83D\\DE00 \\+01F600'", ["SCONST"]),
  ("E'\\uD83D\\uDE00 \\U0001F600 \\xC3\\xA9'", ["SCONST"]),
  ("0 2147483647 2147483648", ["ICONST", "ICONST", "FCONST"]),
  ("0xFF 0X_7fff_ffff 0x80000000", ["ICONST", "ICONST", "FCONST"]),
  ("0o77 0b_1010 1_000", ["ICONST", "ICONST", "ICONST"]),
  (".5 1. 1.5 1e2 1e-2 1.2E+3", List.replicate 6 "FCONST"),
  ("1..10", ["ICONST", "DOT_DOT", "ICONST"]),
  ("$1 $001 $0", ["PARAM", "PARAM", "PARAM"]),
  (":: := => <= >= <> !=", ["TYPECAST", "COLON_EQUALS", "EQUALS_GREATER",
    "LESS_EQUALS", "GREATER_EQUALS", "NOT_EQUALS", "NOT_EQUALS"]),
  ("+- +/*x*/- +-- line\n-", ["'+'", "'-'", "'+'", "'-'", "'+'", "'-'"]),
  ("<=-1", ["LESS_EQUALS", "'-'", "ICONST"]),
  ("? ?| ?& @> <@ #>> ->> || ~~ !~~* @- ++ @@@", List.replicate 11 "Op" ++ ["'+'", "'+'", "Op"]),
  ("(),[].;:+-*/%^<>=", ["'('", "')'", "','", "'['", "']'", "'.'", "';'", "':'", "Op"]),
  ("x NOT IN (1)", ["IDENT", "NOT_LA", "IN_P", "'('", "ICONST", "')'"]),
  ("x NOT BETWEEN 1 AND 2", ["IDENT", "NOT_LA", "BETWEEN", "ICONST", "AND", "ICONST"]),
  ("x NOT LIKE y", ["IDENT", "NOT_LA", "LIKE", "IDENT"]),
  ("x NOT ILIKE y", ["IDENT", "NOT_LA", "ILIKE", "IDENT"]),
  ("x NOT SIMILAR TO y", ["IDENT", "NOT_LA", "SIMILAR", "TO", "IDENT"]),
  ("NOT x", ["NOT", "IDENT"]),
  ("NULLS FIRST NULLS LAST NULLS x", ["NULLS_LA", "FIRST_P", "NULLS_LA", "LAST_P", "NULLS_P", "IDENT"]),
  ("WITH TIME WITH ORDINALITY WITH x", ["WITH_LA", "TIME", "WITH_LA", "ORDINALITY", "WITH", "IDENT"]),
  ("WITHOUT TIME WITHOUT x", ["WITHOUT_LA", "TIME", "WITHOUT", "IDENT"]),
  ("FORMAT JSON FORMAT x", ["FORMAT_LA", "JSON", "FORMAT", "IDENT"])
]

private def badLexicalCases : List String := [
  "'", "\"", "\"\"", "E'a\\", "$tag$unterminated", "/* /* */",
  "0x", "0x_", "0o8", "0b2", "1e", "1e+", "1abc", "1.2abc", "$1abc", "1__2", "1._2",
  "U&\"\"", "U&'x' UESCAPE", "U&'x' UESCAPE '0'", "U&'x' UESCAPE 'xx'",
  "E'\\u0'", "E'\\u0000'", "E'\\U00110000'", "E'\\uD800'", "E'\\uDC00'",
  "E'\\xFF'", "E'\\000'", "U&'\\0000'", "U&'\\+110000'", "U&'\\D800x'",
  "U&'\\DC00'", "U&'\\qqqq'", "U&'x' UESCAPE 'λ'", "\u0000", "{",
  String.ofList (List.replicate 64 '@')
]

def postgresLexerTests : IO Nat := do
  for (source, expected) in lexicalCases do
    let result ← expectOk s!"PostgreSQL lexical {source}" ((lex source).mapError reprStr)
    have _source : reconstruct result.pieces result.trailing = source := result.preserved
    let actual := result.tokens.map fun token =>
      (Generated.terminals.find? (fun info => info.symbol == token.kind)).map (·.name) |>.getD "unknown"
    SQLean.Tests.assert (actual == expected)
      s!"PostgreSQL token kinds: {source}: got {reprStr actual}, expected {reprStr expected}"
    let mut offset := 0
    for piece in result.pieces do
      offset := offset + piece.trivia.utf8ByteSize
      SQLean.Tests.assert (piece.token.startOffset == offset) "incorrect token start byte offset"
      offset := offset + piece.token.lexeme.utf8ByteSize
      SQLean.Tests.assert (piece.token.endOffset == offset) "incorrect token end byte offset"
    SQLean.Tests.assert (offset + result.trailing.utf8ByteSize == source.utf8ByteSize)
      "incorrect final source byte offset"
  for source in badLexicalCases do
    match lex source with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError s!"invalid lexical source accepted: {source}")
  for keyword in Generated.keywords do
    let result ← expectOk s!"keyword {keyword.spelling}" ((lex keyword.spelling).mapError reprStr)
    SQLean.Tests.assert (result.tokens.map (·.kind) == [keyword.symbol]) "keyword table disagreement"
  pure (lexicalCases.length + badLexicalCases.length + Generated.keywords.size)

end SQLean.Tests
