import SQLean.PostgresGrammar
import Lean.Data.Json

namespace SQLean.PostgresGrammar
open Lean (toJson)
set_option maxRecDepth 8192

def GrammarTree.productionIds : GrammarTree → List Nat
  | .terminal _ => []
  | .rule production children => production :: children.flatMap GrammarTree.productionIds

private def nonterminalName (names : Array (String × Nat)) (symbol : Nat) : String :=
  (names.find? (fun pair => pair.2 == symbol)).map Prod.fst |>.getD "unknown"

/-- Stop at each outer stmt so function-body statements are not miscounted
as additional top-level source examples. Empty statements contribute no family. -/
def GrammarTree.statementFamilies (grammar : Grammar) (names : Array (String × Nat)) :
    GrammarTree → List String
  | .terminal _ => []
  | .rule production children =>
      match grammar.productions[production]? with
      | none => []
      | some definition =>
          let name := nonterminalName names definition.lhs
          if name == "stmt" then definition.rhs.filterMap fun symbol => match symbol with
            | .nonterminal kind => some (nonterminalName names kind)
            | .terminal _ => none
          else if name == "TransactionStmtLegacy" then [name]
          else if ["parse_toplevel", "stmtmulti", "toplevel_stmt"].contains name then
            children.flatMap (GrammarTree.statementFamilies grammar names)
          else []

/-- JSON is an inspectable report of an in-process proof-carrying result,
not an independently serialized proof object. -/
def report (source : String) (fuel : Nat := 1000000) : Lean.Json × UInt32 :=
  let common : List (String × Lean.Json) := [
    ("profile", toJson "postgresql-16.15-grammar-v0.1"),
    ("postgresqlCommit", toJson "f0595c3d839debdb140903621c1b44a4f4d86256"),
    ("staticValidity", toJson "not-checked"),
    ("grammarSemanticActions", toJson "not-checked")]
  match parse source fuel with
  | .ok parsed =>
      let tokens := parsed.lexical.tokens.map fun token => Lean.Json.mkObj [
        ("kind", toJson ((Generated.terminals.find?
          (fun info => info.symbol == token.kind)).map (·.name) |>.getD "unknown")),
        ("lexeme", toJson token.lexeme), ("start", toJson token.startOffset),
        ("end", toJson token.endOffset)]
      (Lean.Json.mkObj (common ++ [
        ("status", toJson "grammar-accepted"),
        ("evidence", toJson "context-free-derivation"),
        ("productionIds", toJson parsed.grammatical.tree.productionIds.eraseDups),
        ("statementFamilies", toJson (parsed.grammatical.tree.statementFamilies
          Generated.grammar Generated.nonterminals)),
        ("sourcePreservation", toJson "exact"),
        ("sql", toJson parsed.render), ("tokens", toJson tokens)]), 0)
  | .error error =>
      let inconclusive := match error with
        | .grammatical .inconclusive => true
        | _ => false
      (Lean.Json.mkObj (common ++ [
        ("status", toJson (if inconclusive then "inconclusive" else "grammar-rejected")),
        ("evidence", toJson "none"), ("diagnostic", toJson (reprStr error))]),
        if inconclusive then 4 else 1)

end SQLean.PostgresGrammar
