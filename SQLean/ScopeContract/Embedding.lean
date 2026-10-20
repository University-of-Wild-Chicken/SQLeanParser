import SQLean.ScopeContract.Spec

/-! A syntax-only embedding. No existing checker is imported. This is deliberately
not a partial decoder that might silently drop unsupported Advanced AST fields. -/
namespace SQLean.ScopeContract

def Source.toAdvanced (s : Source) : Advanced.From := .table s.table s.alias []

def sourcesToAdvanced : List Source → Option Advanced.From
  | [] => none
  | s :: ss => some (ss.foldl (fun left right =>
      .join .cross left right.toAdvanced .none) s.toAdvanced)

def Expr.toAdvanced : Expr → Advanced.Expr
  | .literal v => .literal v
  | .column q n => .column q n
  | .binary op a b => .binary op a.toAdvanced b.toAdvanced
  | .unary op a => .unary op a.toAdvanced
  | .exists sources items predicate => .exists {
      body := .select {
        items := items.map (fun item => .expression item.1.toAdvanced item.2)
        source := sourcesToAdvanced sources
        whereClause := match predicate with | none => none | some p => some p.toAdvanced } }
termination_by e => sizeOf e
decreasing_by
  all_goals simp_wf
  all_goals try omega
  · have h := List.sizeOf_lt_of_mem ‹item ∈ items›
    cases item
    simp only [Prod.mk.sizeOf_spec] at h ⊢
    omega

def Query.toAdvanced (q : Query) : Advanced.Query := {
  body := .select {
    items := q.items.map (fun item => .expression item.1.toAdvanced item.2)
    source := sourcesToAdvanced q.sources
    whereClause := q.predicate.map Expr.toAdvanced } }

/-- A precise proposition to use as the future bridge theorem's conclusion. -/
def AdvancedNameValid (schema : Schema) (q : Advanced.Query) : Prop :=
  ∃ fragment : Query, fragment.toAdvanced = q ∧ NameValid schema fragment

theorem embedding_valid {schema q} (h : NameValid schema q) :
    AdvancedNameValid schema q.toAdvanced := ⟨q, rfl, h⟩

end SQLean.ScopeContract
