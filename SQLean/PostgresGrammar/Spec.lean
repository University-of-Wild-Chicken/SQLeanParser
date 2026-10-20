import SQLean.PostgresGrammar.Syntax

/-! Independent context-free derivations. These judgments refer only to
production membership and ordered children, never an LR table or a checker.
They make no claim about PostgreSQL C actions, SQL typing, or execution. -/
namespace SQLean.PostgresGrammar

mutual
  inductive Derives (grammar : Grammar) : Symbol → List Token → GrammarTree → Prop where
    | terminal (token : Token) :
        Derives grammar (.terminal token.kind) [token] (.terminal token)
    | rule (production : Nat) (definition : Production)
        (member : grammar.productions[production]? = some definition)
        (children : DerivesList grammar definition.rhs tokens trees) :
        Derives grammar (.nonterminal definition.lhs) tokens (.rule production trees)

  inductive DerivesList (grammar : Grammar) :
      List Symbol → List Token → List GrammarTree → Prop where
    | nil : DerivesList grammar [] [] []
    | cons (head : Derives grammar symbol first tree)
        (tail : DerivesList grammar symbols remaining trees) :
        DerivesList grammar (symbol :: symbols) (first ++ remaining) (tree :: trees)
end

structure Certificate (grammar : Grammar) (tokens : List Token) where
  tree : GrammarTree
  valid : Derives grammar (.nonterminal grammar.startSymbol) tokens tree

end SQLean.PostgresGrammar
