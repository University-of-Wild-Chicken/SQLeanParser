import SQLean.PostgresGrammar.Parser
import SQLean.PostgresGrammar.Generated
import Tests.Support

/-! Grammar recognition witnesses, deliberately separate from typed SQL AST
certificates. Upstream C action checks and source lexing are not exercised here. -/
namespace SQLean.Tests
open PostgresGrammar

private def tinyGrammar : Grammar := {
  productions := #[⟨10, [.terminal 3]⟩]
  startSymbol := 10
  terminalKinds := #[0, 1, 3] }

private def tinyTables : Tables := {
  shiftRows := #[#[(3, 1)], #[], #[(0, 3)]]
  states := #[
    {shiftRow := 0, gotos := #[(10, 2)]},
    {shiftRow := 1, defaultAction := .reduce 0},
    {shiftRow := 2},
    {shiftRow := 1, defaultAction := .accept}] }

private def sampleToken : PostgresGrammar.Token := ⟨3, "exact raw payload 'quoted'", 7, 33⟩

/-- Nonvacuity of the independent specification does not call the interpreter
or rely on generated tables or a compiled proof shortcut. -/
example : Derives tinyGrammar (.nonterminal 10) [sampleToken]
    (.rule 0 [.terminal sampleToken]) :=
  .rule 0 ⟨10, [.terminal 3]⟩ rfl (.cons (.terminal sampleToken) .nil)

private def grammarTokens (names : List String) : IO (List PostgresGrammar.Token) :=
  names.zipIdx.mapM fun (name, index) => do
    let some kind := Generated.tokenKind name
      | throw (IO.userError s!"unknown pinned grammar token: {name}")
    pure ⟨kind, s!"raw:{name}", index * 10, index * 10 + 5⟩

private def examples : List (String × List String) := [
  ("empty default statement list", []),
  ("scalar SELECT", ["SELECT", "ICONST", "';'"]),
  ("table projection", ["SELECT", "'*'", "FROM", "IDENT", "';'"]),
  ("conditional expression", ["SELECT", "CASE", "WHEN", "TRUE_P", "THEN", "ICONST",
    "ELSE", "ICONST", "END_P", "';'"]),
  ("array constructor", ["SELECT", "ARRAY", "'['", "ICONST", "','", "ICONST", "']'", "';'"]),
  ("row constructor", ["SELECT", "ROW", "'('", "ICONST", "','", "SCONST", "')'", "';'"]),
  ("function call", ["SELECT", "IDENT", "'('", "ICONST", "','", "SCONST", "')'", "';'"]),
  ("window invocation", ["SELECT", "IDENT", "'('", "')'", "OVER", "'('", "')'", "FROM", "IDENT", "';'"]),
  ("CTE", ["WITH", "IDENT", "AS", "'('", "SELECT", "ICONST", "')'", "SELECT", "'*'", "FROM", "IDENT", "';'"]),
  ("VALUES query", ["VALUES", "'('", "ICONST", "','", "SCONST", "')'", "';'"]),
  ("row locking", ["SELECT", "'*'", "FROM", "IDENT", "FOR", "UPDATE", "SKIP", "LOCKED", "';'"]),
  ("INSERT", ["INSERT", "INTO", "IDENT", "VALUES", "'('", "ICONST", "')'", "';'"]),
  ("UPDATE FROM", ["UPDATE", "IDENT", "SET", "IDENT", "'='", "ICONST", "FROM", "IDENT", "';'"]),
  ("DELETE USING", ["DELETE_P", "FROM", "IDENT", "USING", "IDENT", "';'"]),
  ("MERGE", ["MERGE", "INTO", "IDENT", "USING", "IDENT", "ON", "TRUE_P",
    "WHEN", "MATCHED", "THEN", "DELETE_P", "';'"]),
  ("CREATE TABLE", ["CREATE", "TABLE", "IDENT", "'('", "IDENT", "INTEGER", "')'", "';'"]),
  ("CREATE VIEW", ["CREATE", "VIEW", "IDENT", "AS", "SELECT", "ICONST", "';'"]),
  ("CREATE ROLE", ["CREATE", "ROLE", "IDENT", "';'"]),
  ("DROP INDEX", ["DROP", "INDEX", "IDENT", "';'"]),
  ("ALTER TABLE", ["ALTER", "TABLE", "IDENT", "ADD_P", "COLUMN", "IDENT", "INTEGER", "';'"]),
  ("transaction", ["BEGIN_P", "';'", "COMMIT", "';'"]),
  ("prepared statement", ["PREPARE", "IDENT", "AS", "SELECT", "PARAM", "';'"]),
  ("EXECUTE", ["EXECUTE", "IDENT", "'('", "ICONST", "')'", "';'"]),
  ("EXPLAIN", ["EXPLAIN", "SELECT", "ICONST", "';'"]),
  ("VACUUM", ["VACUUM", "IDENT", "';'"]),
  ("COPY", ["COPY", "IDENT", "FROM", "STDIN", "';'"]),
  ("GRANT", ["GRANT", "ALL", "ON", "IDENT", "TO", "IDENT", "';'"]),
  ("NOTIFY", ["NOTIFY", "IDENT", "','", "SCONST", "';'"]),
  ("DO", ["DO", "SCONST", "';'"]),
  -- PostgreSQL's C action rejects this grammar production. The certificate
  -- intentionally says only that this token stream has a CFG derivation.
  ("action-level rejection is outside CFG evidence",
    ["CREATE", "ASSERTION", "IDENT", "CHECK", "'('", "TRUE_P", "')'", "';'"])
]

def postgresGrammarTests : IO Nat := do
  let mut count := 0
  let accepted ← expectOk "tiny grammar" ((parseTokens tinyGrammar tinyTables [sampleToken]).mapError reprStr)
  have _independent : Derives tinyGrammar (.nonterminal 10) [sampleToken] accepted.tree := accepted.valid
  count := count + 1
  match parseTokens tinyGrammar tinyTables [sampleToken] 0 with
  | .error .inconclusive => pure ()
  | _ => throw (IO.userError "zero parser fuel must be inconclusive")
  count := count + 1
  for kind in [0, 1, 2, 99] do
    match parseTokens tinyGrammar tinyTables [{sampleToken with kind}] with
    | .error (.invalidToken _) => pure ()
    | _ => throw (IO.userError "invalid caller token kind was not rejected")
    count := count + 1
  let badReduction : Tables := {
    tinyTables with
    states := tinyTables.states.modify 1 (fun _ => {shiftRow := 1, defaultAction := .reduce 99}) }
  let badRhs := {tinyGrammar with productions := #[⟨10, [.terminal 4]⟩]}
  let missingGoto := {tinyTables with states := tinyTables.states.modify 0 (fun _ => {shiftRow := 0})}
  let prematureAccept : Tables := {
    tinyTables with
    states := tinyTables.states.modify 1 (fun _ => {shiftRow := 1, defaultAction := .accept}) }
  for (grammar, tables) in [(tinyGrammar, badReduction), (badRhs, tinyTables),
      (tinyGrammar, missingGoto), (tinyGrammar, prematureAccept)] do
    match parseTokens grammar tables [sampleToken] with
    | .error (.invalidTables _) => pure ()
    | _ => throw (IO.userError "malformed tables acquired a grammar certificate")
    count := count + 1
  for (label, names) in examples do
    let tokens ← grammarTokens names
    let certificate ← expectOk label
      ((parseTokens Generated.grammar Generated.tables tokens).mapError reprStr)
    have _exact : Derives Generated.grammar (.nonterminal Generated.grammar.startSymbol)
        tokens certificate.tree := certificate.valid
    count := count + 1
  for names in [
      ["SELECT", "FROM", "';'"],
      ["SELECT", "ICONST", "SELECT", "ICONST"],
      ["CREATE", "TABLE", "IDENT", "'('"],
      ["INSERT", "INTO", "IDENT"],
      ["SELECT", "ICONST", "WHERE"]] do
    let tokens ← grammarTokens names
    match parseTokens Generated.grammar Generated.tables tokens with
    | .error (.«syntax» _ _) => pure ()
    | .error error => throw (IO.userError s!"malformed grammar stream misclassified: {reprStr error}")
    | .ok _ => throw (IO.userError "malformed grammar stream acquired a certificate")
    count := count + 1
  pure count

end SQLean.Tests
