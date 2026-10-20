import SQLean.PostgresGrammar.Spec

/-! A total bounded LR interpreter. The tables guide execution but do not
define its certificate: every reduction constructs the independent derivation
from Spec, and acceptance checks the complete original token sequence. -/
namespace SQLean.PostgresGrammar

inductive Failure where
  | syntax (state : Nat) (lookahead : Token)
  | invalidToken (token : Token)
  | inconclusive
  | invalidTables (message : String)
  deriving Repr, BEq, DecidableEq

private structure Entry (grammar : Grammar) where
  state : Nat
  symbol : Symbol
  tokens : List Token
  tree : GrammarTree
  valid : Derives grammar symbol tokens tree

private structure Children (grammar : Grammar) (symbols : List Symbol) where
  tokens : List Token
  trees : List GrammarTree
  valid : DerivesList grammar symbols tokens trees

private def children (grammar : Grammar) :
    (symbols : List Symbol) → List (Entry grammar) → Except Failure (Children grammar symbols)
  | [], [] => .ok ⟨[], [], .nil⟩
  | symbol :: symbols, entry :: entries => do
      if same : entry.symbol = symbol then
        let tail ← children grammar symbols entries
        let head : Derives grammar symbol entry.tokens entry.tree := by
          rw [← same]
          exact entry.valid
        pure ⟨entry.tokens ++ tail.tokens, entry.tree :: tail.trees, .cons head tail.valid⟩
      else .error (.invalidTables "reduction does not match the production's right-hand side")
  | _, _ => .error (.invalidTables "reduction has the wrong number of children")

private def lookup (entries : Array (Nat × Nat)) (key : Nat) : Option Nat :=
  (entries.find? (fun pair => pair.1 == key)).map Prod.snd

private def action (tables : Tables) (state : State) (kind : Nat) : Except Failure Action := do
  if state.errors.contains kind then return .reject
  let some shifts := tables.shiftRows[state.shiftRow]?
    | .error (.invalidTables "state refers to a missing shift row")
  if let some destination := lookup shifts kind then return .shift destination
  if let some production := lookup state.reductions kind then return .reduce production
  pure state.defaultAction

private def finish (grammar : Grammar) (input : List Token) (eof : Token)
    (remaining : List Token) (stack : List (Entry grammar)) :
    Except Failure (Certificate grammar input) := do
  if !remaining.isEmpty then
    throw (.invalidTables "acceptance left unconsumed input")
  match stack with
  | [marker, root] =>
      if marker.symbol != .terminal grammar.eofKind || marker.tokens != [eof] then
        throw (.invalidTables "acceptance lacks the private EOF marker")
      if start : root.symbol = .nonterminal grammar.startSymbol then
        if complete : root.tokens = input then
          pure ⟨root.tree, by rw [← start, ← complete]; exact root.valid⟩
        else .error (.invalidTables "accepted derivation does not cover exactly the input")
      else .error (.invalidTables "accepted derivation has the wrong start symbol")
  | _ => .error (.invalidTables "acceptance has an unexpected parser stack")

private def run (grammar : Grammar) (tables : Tables) (input : List Token) (eof : Token) :
    Nat → List Token → List (Entry grammar) → Except Failure (Certificate grammar input)
  | 0, _, _ => .error .inconclusive
  | fuel + 1, remaining, stack => do
      let stateNumber := match stack with | [] => tables.initialState | head :: _ => head.state
      let some state := tables.states[stateNumber]?
        | .error (.invalidTables "parser state is outside the generated table")
      let lookahead := remaining.headD eof
      match ← action tables state lookahead.kind with
      | .reject => .error (.syntax stateNumber lookahead)
      | .accept => finish grammar input eof remaining stack
      | .shift destination =>
          match remaining with
          | [] => .error (.invalidTables "shift requested after the private EOF marker")
          | token :: rest =>
              let entry : Entry grammar :=
                ⟨destination, .terminal token.kind, [token], .terminal token, .terminal token⟩
              run grammar tables input eof fuel rest (entry :: stack)
      | .reduce production =>
          match member : grammar.productions[production]? with
          | none => .error (.invalidTables "reduction refers to an absent production")
          | some definition =>
              if definition.rhs.length > stack.length then
                throw (.invalidTables "reduction exceeds the parser stack")
              let reduced ← children grammar definition.rhs (stack.take definition.rhs.length).reverse
              let rest := stack.drop definition.rhs.length
              let previous := match rest with | [] => tables.initialState | head :: _ => head.state
              let some prior := tables.states[previous]?
                | .error (.invalidTables "goto base state is outside the generated table")
              let some destination := lookup prior.gotos definition.lhs
                | .error (.invalidTables "no goto for the reduced nonterminal")
              let entry : Entry grammar :=
                ⟨destination, .nonterminal definition.lhs, reduced.tokens,
                 .rule production reduced.trees, .rule production definition member reduced.valid⟩
              run grammar tables input eof fuel remaining (entry :: rest)

/-- Recognize an already-lexed stream, excluding EOF. Tokens retain exact caller
payloads. The private EOF sentinel never enters the returned start derivation.
Fuel bounds transitions/reductions; exhaustion is not a syntax rejection. -/
def parseTokens (grammar : Grammar) (tables : Tables) (tokens : List Token)
    (fuel : Nat := 1000000) : Except Failure (Certificate grammar tokens) := do
  for token in tokens do
    if token.kind == grammar.eofKind || token.kind == 1 || token.kind == 2 ||
        !grammar.terminalKinds.contains token.kind then
      throw (.invalidToken token)
  let endOffset := (tokens.getLast?).map Token.endOffset |>.getD 0
  let eof : Token := ⟨grammar.eofKind, "", endOffset, endOffset⟩
  run grammar tables tokens eof fuel (tokens ++ [eof]) []

/-- Success carries a grammar derivation independent of all parser tables. -/
theorem parseTokens_sound (grammar : Grammar) (tables : Tables) (tokens : List Token)
    (fuel : Nat) (certificate : Certificate grammar tokens)
    (_success : parseTokens grammar tables tokens fuel = .ok certificate) :
    Derives grammar (.nonterminal grammar.startSymbol) tokens certificate.tree :=
  certificate.valid

end SQLean.PostgresGrammar
