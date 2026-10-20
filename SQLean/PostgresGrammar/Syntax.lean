import Std

/-! Data for grammar recognition. Tokens retain caller-supplied raw lexemes and
offsets. This layer does not establish that those bytes were lexed correctly. -/
namespace SQLean.PostgresGrammar

structure Token where
  /-- Bison internal terminal symbol number, not its external token code. -/
  kind : Nat
  lexeme : String := ""
  startOffset : Nat := 0
  endOffset : Nat := 0
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Symbol where
  | terminal (kind : Nat)
  | nonterminal (kind : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

structure Production where
  lhs : Nat
  rhs : List Symbol
  deriving Repr, BEq, DecidableEq, Inhabited

structure Grammar where
  productions : Array Production
  startSymbol : Nat
  terminalKinds : Array Nat
  eofKind : Nat := 0

inductive GrammarTree where
  | terminal (token : Token)
  | rule (production : Nat) (children : List GrammarTree)
  deriving Repr, Inhabited

inductive Action where
  | shift (state : Nat)
  | reduce (production : Nat)
  | accept
  | reject
  deriving Repr, BEq, DecidableEq, Inhabited

structure State where
  shiftRow : Nat
  reductions : Array (Nat × Nat) := #[]
  defaultAction : Action := .reject
  errors : Array Nat := #[]
  gotos : Array (Nat × Nat) := #[]
  deriving Repr, Inhabited

structure Tables where
  shiftRows : Array (Array (Nat × Nat))
  states : Array State
  initialState : Nat := 0

structure TerminalInfo where
  name : String
  symbol : Nat
  externalCode : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

structure KeywordInfo where
  spelling : String
  symbol : Nat
  category : String
  bareLabel : Bool
  deriving Repr, BEq, DecidableEq, Inhabited

end SQLean.PostgresGrammar
