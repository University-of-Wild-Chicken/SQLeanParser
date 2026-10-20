import SQLean.ScopeContract.Embedding
import SQLean.AdvancedParser
import SQLean.AdvancedEquality
import SQLean.AdvancedQueryValidation

namespace SQLean.Tests.ScopeContract
open SQLean.ScopeContract

private def schema : Schema := [
  ⟨"users", [⟨"id", .int⟩, ⟨"age", .int⟩, ⟨"name", .text⟩, ⟨"city", .text⟩]⟩,
  ⟨"orders", [⟨"id", .int⟩, ⟨"user_id", .int⟩, ⟨"amount", .int⟩, ⟨"status", .text⟩]⟩,
  ⟨"profiles", [⟨"id", .int⟩, ⟨"city", .text⟩, ⟨"rating", .nullable .real⟩]⟩]

private def u : Source := ⟨"users", some "u"⟩
private def o : Source := ⟨"orders", some "o"⟩
private def p : Source := ⟨"profiles", some "p"⟩
private def col (q n : String) : SQLean.ScopeContract.Expr := .column (some q) n
private def bare (n : String) : SQLean.ScopeContract.Expr := .column none n
private def one : SQLean.ScopeContract.Expr := .literal (.int 1)
private def eq (a b : SQLean.ScopeContract.Expr) : SQLean.ScopeContract.Expr := .binary .eq a b
private def query (ss : List Source) (es : List SQLean.ScopeContract.Expr) (w : Option SQLean.ScopeContract.Expr := none) : SQLean.ScopeContract.Query :=
  ⟨ss, es.map (·, none), w⟩
private def existsQ (q : SQLean.ScopeContract.Query) : SQLean.ScopeContract.Expr := .exists q.sources q.items q.predicate
private def correlated : SQLean.ScopeContract.Query := query [u] [col "u" "id"]
  (some (existsQ (query [o] [one] (some (eq (col "o" "user_id") (col "u" "id"))))))

/-- These are kernel-reduced concrete derivations/refutations, not native_decide. -/
theorem correlated_valid : NameValid schema correlated := by decide +kernel
theorem missing_invalid : ¬ NameValid schema (query [u] [col "u" "missing"]) := by decide +kernel
theorem ambiguous_invalid : ¬ NameValid schema (query [u, p] [bare "id"]) := by decide +kernel
theorem shadow_missing_invalid : ¬ NameValid schema (query [u] [existsQ (query [⟨"profiles", some "u"⟩]
    [col "u" "age"])]) := by decide +kernel
theorem two_level_valid : NameValid schema (query [u] [existsQ (query [o]
    [existsQ (query [p] [col "u" "age"])])]) := by decide +kernel

private def cases : List (String × SQLean.ScopeContract.Query × Bool) := [
  ("SELECT u.id FROM users u WHERE EXISTS (SELECT 1 FROM orders o WHERE o.user_id=u.id)", correlated, true),
  ("SELECT u.missing FROM users u", query [u] [col "u" "missing"], false),
  ("SELECT id FROM users u CROSS JOIN profiles p", query [u,p] [bare "id"], false),
  ("SELECT users.id FROM users u", query [u] [col "users" "id"], false),
  ("SELECT u.id FROM users u CROSS JOIN profiles u", query [u,⟨"profiles",some "u"⟩] [col "u" "id"], false),
  ("SELECT EXISTS (SELECT u.age FROM profiles u) FROM users u", query [u] [existsQ (query [⟨"profiles",some "u"⟩] [col "u" "age"])], false),
  ("SELECT EXISTS (SELECT age FROM orders o) FROM users u", query [u] [existsQ (query [o] [bare "age"])], true),
  ("SELECT EXISTS (SELECT id FROM orders o CROSS JOIN profiles p) FROM users u", query [u] [existsQ (query [o,p] [bare "id"])], false),
  ("SELECT EXISTS (SELECT EXISTS (SELECT u.age FROM profiles p) FROM orders o) FROM users u", query [u] [existsQ (query [o] [existsQ (query [p] [col "u" "age"])])], true),
  ("SELECT o.id FROM users u WHERE EXISTS (SELECT 1 FROM orders o)", query [u] [col "o" "id"] (some (existsQ (query [o] [one]))), false),
  ("SELECT EXISTS (SELECT o.id), EXISTS (SELECT 1 FROM orders o) FROM users u", query [u] [existsQ (query [] [col "o" "id"]), existsQ (query [o] [one])], false),
  ("SELECT u.id AS k FROM users u WHERE k=1", ⟨[u],[(col "u" "id",some "k")],some (eq (bare "k") one)⟩, false),
  ("SELECT u.id AS k, k FROM users u", ⟨[u],[(col "u" "id",some "k"),(bare "k",none)],none⟩, false),
  ("SELECT EXISTS (SELECT u.id) FROM users u", query [u] [existsQ (query [] [col "u" "id"])], true),
  ("SELECT x.id FROM missing x", query [⟨"missing",some "x"⟩] [col "x" "id"], false),
  ("SELECT id FROM users", query [⟨"users",none⟩] [bare "id"], true),
  ("SELECT 1", query [] [one], true),
  ("SELECT u.id FROM users u CROSS JOIN profiles p", query [u,p] [col "u" "id"], true)]

private def require (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

/-- Adapter is test-only and makes NO grouped/USING/NATURAL-join claim. -/
private def toScope (f : Frame) : Advanced.Scope := {
  qualified := f.flatMap (fun r => r.columns.map (fun n => ⟨r.qualifier,n,.int⟩))
  output := f.flatMap (fun r => r.columns.map (fun n => ⟨some r.qualifier,n,.int⟩)) }

private def actual (fs : Stack) (q : Option Name) (n : Name) : Option Target :=
  match Advanced.resolveColumn (fs.map toScope) q n with
  | .error _ => none
  | .ok (b,d) => some ⟨d,b.qualifier.getD "",b.name⟩

/-- Deliberately wrong resolvers, used only to demonstrate test discrimination. -/
private def mutant (mode : Nat) : Stack → Option Name → Name → Option Target
  | [], _, _ => none
  | f :: fs, q, n =>
    let cs := candidates f q n
    let next := (mutant mode fs q n).map (fun t => ⟨t.depth+1,t.qualifier,t.column⟩)
    if mode == 1 && next.isSome then next -- outer-first
    else match cs with
    | [r] => some ⟨0,r,n⟩
    | r :: _ => if mode == 0 then some ⟨0,r,n⟩ -- ambiguity: choose first
        else if mode == 4 then next else none -- ambiguity: fall through
    | [] => if mode == 2 then none -- disable correlation
        else if mode == 3 then next -- ignore alias barrier
        else if MayPass f q n then next else none

private def frames : List Frame := [[],
  [⟨"u",["id","age"]⟩], [⟨"o",["id","user_id"]⟩],
  [⟨"u",["id"]⟩], [⟨"u",["id"]⟩,⟨"p",["id"]⟩], [⟨"p",["id"]⟩]]
private def stacks : Nat → List Stack
  | 0 => [[]]
  | n+1 => [] :: frames.flatMap (fun f => (stacks n).map (f :: ·))

/-- General Advanced checker/refinement theorems are intentionally NOT assumed. -/
def run : IO Unit := do
  for (sql,q,expected) in cases do
    require (decide (NameValid schema q) == expected) s!"independent contract: {sql}"
    match Advanced.parse sql with
    | .ok (.query parsed) =>
      require (decide (parsed = q.toAdvanced)) s!"fixture/parsed AST mismatch: {sql}"
      require ((Advanced.checkQuery schema [] parsed).isOk == expected) s!"advanced checker mismatch: {sql}"
    | _ => throw (IO.userError s!"parse failed: {sql}")
  -- Name-valid does not imply type-valid. This is an intentional scope boundary.
  let badType := query [] [.binary .add (.literal (.bool true)) one]
  require (decide (NameValid schema badType)) "name/type separation: spec"
  require (!(Advanced.checkQuery schema [] badType.toAdvanced).isOk) "name/type separation: checker"
  let mut count := 0
  let mut kills := Array.replicate 5 0
  for fs in stacks 3 do
    for q in [none, some "u", some "o", some "p"] do
      for n in ["id", "age", "user_id", "missing"] do
        let wanted := resolve fs q n
        require (actual fs q n == wanted) s!"binding/depth mismatch: {repr (fs,q,n,wanted)}"
        for mode in [:5] do
          if mutant mode fs q n != wanted then
            kills := kills.modify mode (· + 1)
        count := count + 1
  for mode in [:5] do
    require (kills[mode]! > 0) s!"surviving mutant {mode}"
  IO.println s!"PASS: {cases.length} SQL/embedding/spec/checker cases; 1 name/type boundary case"
  IO.println s!"PASS: {count} exact binding/depth comparisons; mutant kills {kills}"

end SQLean.Tests.ScopeContract
