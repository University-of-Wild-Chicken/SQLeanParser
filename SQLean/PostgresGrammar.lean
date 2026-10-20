import SQLean.PostgresGrammar.Lexer
import SQLean.PostgresGrammar.Parser
import SQLean.PostgresGrammar.Generated

/-! The PostgreSQL 16 grammar API returns a concrete syntax tree and a
kernel-checked derivation over the pinned productions. Its source renderer
preserves the input exactly. SQL typing, name resolution, C semantic actions,
and execution remain distinct from this grammar-level certificate. -/
namespace SQLean.PostgresGrammar

inductive ParseFailure where
  | lexical (error : LexError)
  | grammatical (error : Failure)
  deriving Repr

structure Parsed (source : String) where
  lexical : Lexed source
  grammatical : Certificate Generated.grammar lexical.tokens

def parse (source : String) (fuel : Nat := 1000000) :
    Except ParseFailure (Parsed source) := do
  let lexical ← (lex source).mapError .lexical
  let grammatical ← (parseTokens Generated.grammar Generated.tables lexical.tokens fuel).mapError
    .grammatical
  pure ⟨lexical, grammatical⟩

def Parsed.render {source : String} (parsed : Parsed source) : String :=
  reconstruct parsed.lexical.pieces parsed.lexical.trailing

theorem Parsed.render_exact {source : String} (parsed : Parsed source) :
    parsed.render = source :=
  parsed.lexical.preserved

theorem Parsed.grammar_valid {source : String} (parsed : Parsed source) :
    Derives Generated.grammar (.nonterminal Generated.grammar.startSymbol)
      parsed.lexical.tokens parsed.grammatical.tree :=
  parsed.grammatical.valid

end SQLean.PostgresGrammar
