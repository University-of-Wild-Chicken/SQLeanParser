import SQLean.AdvancedSyntax

/-! Independent name/scope contract. Only immutable syntax and Std are imported.
This is name validity, NOT expression typing or SQL execution validity. -/
namespace SQLean.ScopeContract

structure Source where
  table : Name
  alias : Option Name := none
  deriving Repr, BEq, DecidableEq

def Source.visible (s : Source) : Name := s.alias.getD s.table

/-- A frame retains relation declarations, even before inspecting any column. -/
structure Relation where
  qualifier : Name
  columns : List Name
  deriving Repr, BEq, DecidableEq
abbrev Frame := List Relation
abbrev Stack := List Frame

/-- Binding identity is lexical depth, visible relation name, and column name. -/
structure Target where
  depth : Nat
  qualifier : Name
  column : Name
  deriving Repr, BEq, DecidableEq

/-- A finite mathematical collection, not a call to a name resolver. -/
def candidates (frame : Frame) (q : Option Name) (n : Name) : List Name :=
  frame.flatMap fun r =>
    if q = none ∨ q = some r.qualifier then
      (r.columns.filter (· == n)).map (fun _ => r.qualifier)
    else []

def MayPass (frame : Frame) (q : Option Name) (n : Name) : Prop :=
  candidates frame q n = [] ∧ ∀ r ∈ frame, q ≠ some r.qualifier

instance (f : Frame) (q : Option Name) (n : Name) : Decidable (MayPass f q n) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- No rule resolves ambiguity; no outer rule bypasses a declared qualifier. -/
inductive Resolves : Stack → Option Name → Name → Target → Prop where
  | here (unique : candidates f q n = [r]) : Resolves (f :: fs) q n ⟨0, r, n⟩
  | outer (absent : MayPass f q n) (resolved : Resolves fs q n t) :
      Resolves (f :: fs) q n ⟨t.depth + 1, t.qualifier, t.column⟩

/-- Executable decision function for the above independent inference rules. -/
def resolve : Stack → Option Name → Name → Option Target
  | [], _, _ => none
  | f :: fs, q, n =>
      match candidates f q n with
      | [r] => some ⟨0, r, n⟩
      | _ => if MayPass f q n then
          (resolve fs q n).map fun t => ⟨t.depth + 1, t.qualifier, t.column⟩
        else none

theorem resolve_sound {fs q n t} (h : resolve fs q n = some t) : Resolves fs q n t := by
  induction fs generalizing t with
  | nil => simp [resolve] at h
  | cons f fs ih =>
    unfold resolve at h
    split at h
    · cases h
      exact .here ‹_›
    · split at h
      · cases hr : resolve fs q n with
        | none => simp [hr] at h
        | some u =>
          simp [hr] at h
          cases h
          exact .outer ‹_› (ih hr)
      · simp at h

theorem resolve_complete {fs q n t} (h : Resolves fs q n t) : resolve fs q n = some t := by
  induction h with
  | here unique => simp [resolve, unique]
  | outer absent _ ih => simp [resolve, absent.1, absent, ih]

theorem resolve_iff {fs q n t} : resolve fs q n = some t ↔ Resolves fs q n t :=
  ⟨resolve_sound, resolve_complete⟩

theorem resolves_unique {fs q n a b} (ha : Resolves fs q n a) (hb : Resolves fs q n b) : a = b := by
  have h := (resolve_complete ha).symm.trans (resolve_complete hb)
  exact Option.some.inj h

/-- Negatives are refutations of derivability, not just rejected executions. -/
theorem resolve_none_iff {fs q n} : resolve fs q n = none ↔ ¬ ∃ t, Resolves fs q n t := by
  constructor
  · intro h ⟨t, ht⟩
    have hc := resolve_complete ht
    simp [h] at hc
  · intro h
    cases hr : resolve fs q n with
    | none => rfl
    | some t => exact False.elim (h ⟨t, resolve_sound hr⟩)

instance (fs : Stack) (q : Option Name) (n : Name) : Decidable (∃ t, Resolves fs q n t) :=
  match h : resolve fs q n with
  | some t => isTrue ⟨t, resolve_sound h⟩
  | none => isFalse (resolve_none_iff.mp h)

/-- Names are exact normalized AST strings; types are intentionally irrelevant. -/
def SchemaWF (schema : Schema) : Prop :=
  (schema.map TableDef.name).Nodup ∧
  ∀ t ∈ schema, t.name ≠ "" ∧ t.columns ≠ [] ∧
    (t.columns.map ColumnDef.name).Nodup ∧ ∀ c ∈ t.columns, c.name ≠ ""
instance (s : Schema) : Decidable (SchemaWF s) := inferInstanceAs (Decidable (_ ∧ _))

def SourcesWF (schema : Schema) (sources : List Source) : Prop :=
  (sources.map Source.visible).Nodup ∧
  ∀ s ∈ sources, s.visible ≠ "" ∧ ∃ t ∈ schema, t.name = s.table
instance (s : Schema) (ss : List Source) : Decidable (SourcesWF s ss) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Catalog restriction/renaming. SchemaWF guarantees unique table definitions. -/
def frame (schema : Schema) (sources : List Source) : Frame :=
  sources.flatMap fun s => (schema.filter (·.name == s.table)).map fun t =>
    ⟨s.visible, t.columns.map ColumnDef.name⟩

/-- Minimal grammar: literals, references, binary/unary expressions, and EXISTS.
The EXISTS constructor contains SELECT expressions and an optional WHERE.
Projection labels are allowed but never become input bindings. -/
inductive Expr where
  | literal (v : Value)
  | column (q : Option Name) (n : Name)
  | binary (op : BinOp) (a b : Expr)
  | unary (op : UnOp) (a : Expr)
  | exists (sources : List Source) (items : List (Expr × Option Name)) (predicate : Option Expr)
  deriving Repr, BEq

/-- Structural declarative name validity; no expression inference/checker calls.
Column validity is existence of a derivation in Resolves. -/
def ExprValid (schema : Schema) (stack : Stack) : Expr → Prop
  | .literal _ => True
  | .column q n => ∃ t, Resolves stack q n t
  | .binary _ a b => ExprValid schema stack a ∧ ExprValid schema stack b
  | .unary _ a => ExprValid schema stack a
  | .exists sources items predicate =>
      SourcesWF schema sources ∧ items ≠ [] ∧
      (∀ item ∈ items, (∀ label ∈ item.2, label ≠ "") ∧
        ExprValid schema (frame schema sources :: stack) item.1) ∧
      ∀ p ∈ predicate, ExprValid schema (frame schema sources :: stack) p
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try omega
  · have h := List.sizeOf_lt_of_mem ‹item ∈ items›
    cases item
    simp only [Prod.mk.sizeOf_spec] at h ⊢
    omega
  · cases predicate <;> simp_all
    omega

private def decideAll (xs : List α) (p : α → Prop)
    (d : ∀ x ∈ xs, Decidable (p x)) : Decidable (∀ x ∈ xs, p x) :=
  match xs with
  | [] => isTrue (by simp)
  | x :: xs => by
    have := d x (by simp)
    have := decideAll xs p (fun y h => d y (by simp [h]))
    exact decidable_of_iff (p x ∧ ∀ y ∈ xs, p y) (by simp)

private def weight : Expr → Nat
  | .literal _ | .column _ _ => 1
  | .binary _ a b => 1 + weight a + weight b
  | .unary _ a => 1 + weight a
  | .exists _ items predicate =>
      1 + (items.map (fun item => weight item.1)).sum + (match predicate with | none => 0 | some p => weight p)
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try omega
  · have h := List.sizeOf_lt_of_mem ‹item ∈ items›
    cases item
    simp only [Prod.mk.sizeOf_spec] at h ⊢
    omega

private theorem member_le_sum (xs : List α) (f : α → Nat) (x : α) (h : x ∈ xs) :
    f x ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    simp only [List.mem_cons] at h
    simp only [List.map_cons, List.sum_cons]
    rcases h with h | h
    · subst x; omega
    · have := ih h; omega

/-- Structural recursion on a sufficient size bound; no resource cutoff is exposed.
The bound is always chosen as weight e + 1 by the public Decidable instance. -/
private def decideExpr (fuel : Nat) (schema : Schema) (stack : Stack) (e : Expr)
    (bound : weight e < fuel) : Decidable (ExprValid schema stack e) :=
  match fuel with
  | 0 => False.elim (by omega)
  | fuel + 1 => match e with
    | .literal _ => isTrue (by simp only [ExprValid])
    | .column q n => decidable_of_iff (∃ t, Resolves stack q n t) (by simp only [ExprValid])
    | .binary op a b => by
      have := decideExpr fuel schema stack a (by simp_all only [weight]; omega)
      have := decideExpr fuel schema stack b (by simp_all only [weight]; omega)
      exact decidable_of_iff (ExprValid schema stack a ∧ ExprValid schema stack b) (by simp only [ExprValid])
    | .unary op a => by
      have := decideExpr fuel schema stack a (by simp_all only [weight]; omega)
      exact decidable_of_iff (ExprValid schema stack a) (by simp only [ExprValid])
    | .exists sources items predicate => by
      have : Decidable (∀ item ∈ items, (∀ label ∈ item.2, label ≠ "") ∧
          ExprValid schema (frame schema sources :: stack) item.1) :=
        decideAll items _ (fun item hm => by
          have := decideExpr fuel schema (frame schema sources :: stack) item.1 (by
            have hs := member_le_sum items (fun item => weight item.1) item hm
            cases predicate <;> simp_all only [weight] <;> omega)
          exact inferInstance)
      have : Decidable (∀ p ∈ predicate, ExprValid schema (frame schema sources :: stack) p) :=
        match predicate with
        | none => isTrue (by simp)
        | some p => by
          have := decideExpr fuel schema (frame schema sources :: stack) p (by
            simp_all only [weight]
            omega)
          exact decidable_of_iff (ExprValid schema (frame schema sources :: stack) p) (by simp)
      exact decidable_of_iff (SourcesWF schema sources ∧ items ≠ [] ∧
        (∀ item ∈ items, (∀ label ∈ item.2, label ≠ "") ∧
          ExprValid schema (frame schema sources :: stack) item.1) ∧
        ∀ p ∈ predicate, ExprValid schema (frame schema sources :: stack) p)
        (by simp only [ExprValid])

instance (schema : Schema) (stack : Stack) (e : Expr) : Decidable (ExprValid schema stack e) :=
  decideExpr (weight e + 1) schema stack e (by omega)

structure Query where
  sources : List Source := []
  items : List (Expr × Option Name)
  predicate : Option Expr := none
  deriving Repr, BEq

/-- Closed-query validity includes metadata and source well-formedness. -/
def NameValid (schema : Schema) (query : Query) : Prop :=
  SchemaWF schema ∧ ExprValid schema [] (.exists query.sources query.items query.predicate)
instance (schema : Schema) (query : Query) : Decidable (NameValid schema query) :=
  inferInstanceAs (Decidable (_ ∧ _))

end SQLean.ScopeContract
