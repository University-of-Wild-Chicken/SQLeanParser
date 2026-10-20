import SQLean.RenderContract.ValidityPreservation

/-! Constructive JOIN validity and preservation witnesses.

These examples import no parser or executable validity checker. They build
independent derivations directly, with kernel reduction for finite side
conditions. In particular, the whole-query witness orders the SELECT parameter
before the ON parameter, keeps the nullable side's exact output type, and locks
only the preserved side of a LEFT JOIN.
-/
namespace SQLean.Tests.JoinPreservation
open Advanced SelectContract RenderContract

private def leftTable : CatalogTable := {
  name := "left_table"
  columns := [{name := "id", type := ⟨.int, []⟩, nullable := some false}] }

private def rightTable : CatalogTable := {
  name := "right_table"
  columns := [{name := "id", type := ⟨.int, []⟩, nullable := some false}] }

private def catalog : Catalog := [leftTable, rightTable]
private def params : SelectContract.ParameterEnv :=
  [⟨1, ⟨.int, []⟩, false⟩, ⟨2, ⟨.bool, []⟩, false⟩]

private def leftSource : Advanced.From := .table "left_table" (some "l")
private def rightSource : Advanced.From := .table "right_table" (some "r")
private def leftScope : Scope := .ofBindings [⟨"l", ⟨"id", ⟨.int32, false⟩⟩⟩]
private def rightScope : Scope := .ofBindings [⟨"r", ⟨"id", ⟨.int32, false⟩⟩⟩]
private def nullableRight : Scope := .ofBindings [⟨"r", ⟨"id", ⟨.int32, true⟩⟩⟩]
private def anon (index : Nat) : Advanced.Expr := .parameter (.anonymous index)

private theorem left_valid :
    SourceValid .basicV11 catalog params (some leftSource) leftScope [] :=
  .table (table := leftTable) (by simp [catalog]) rfl (by simp) (.cons rfl .nil)

private theorem right_valid :
    SourceValid .basicV11 catalog params (some rightSource) rightScope [] :=
  .table (table := rightTable) (by simp [catalog]) rfl (by simp) (.cons rfl .nil)

private theorem on_valid (scope : Scope) :
    PredicateValid params scope (some (anon 2)) [.anonymous 2] :=
  .present (.parameter (binding := ⟨2, ⟨.bool, []⟩, false⟩)
    (by simp [params]) rfl rfl) rfl

private def joined (kind : JoinKind) : Advanced.From :=
  .join kind leftSource rightSource (.on (anon 2))

private theorem joined_valid (kind : JoinKind) (ordinary : kind ≠ .cross) :
    SourceValid .basicV11 catalog params (some (joined kind))
      (joinScope kind leftScope rightScope) [.anonymous 2] := by
  exact .on left_valid right_valid (by decide) ordinary (on_valid _)

example : SourceValid .basicV11 catalog params
    (some (.join .cross leftSource rightSource .none))
    (leftScope.append rightScope) [] :=
  .cross left_valid right_valid (by decide)

example : SourceValid .basicV11 catalog params (some (joined .inner))
    (leftScope.append rightScope) [.anonymous 2] :=
  joined_valid .inner (by decide)

example : SourceValid .basicV11 catalog params (some (joined .left))
    (leftScope.append nullableRight) [.anonymous 2] :=
  joined_valid .left (by decide)

example : SourceValid .basicV11 catalog params (some (joined .right))
    ((nullableScope leftScope).append rightScope) [.anonymous 2] :=
  joined_valid .right (by decide)

example : SourceValid .basicV11 catalog params (some (joined .full))
    ((nullableScope leftScope).append nullableRight) [.anonymous 2] :=
  joined_valid .full (by decide)

example : SourceValid .basicV11 catalog params (some (translateSource (joined .left)))
    (leftScope.append nullableRight) [.numbered 2] :=
  source_valid_translated (joined_valid .left (by decide))

example : LockTargets (some (joined .left)) ["l"] := by decide
example : ¬ LockTargets (some (joined .left)) ["r"] := by decide
example : ¬ LockTargets (some (joined .left)) [] := by decide
example : ¬ LockTargets (some (joined .full)) ["l"] := by decide

/-- NULL extension propagates through ancestors, including nested joins that
do not themselves add NULL rows to that child. -/
example : fromRelations
    (.join .right (joined .left) (.table "left_table" (some "z")) (.on (.literal (.bool true)))) =
      [("l", true), ("r", true), ("z", false)] := by decide

private def query : Advanced.Query := {
  body := .select {
    items := [.expression (anon 1) (some "selected"), .all none]
    source := some (joined .left) }
  locking := [⟨.update, ["l"], .nowait⟩] }

private def output : List OutputColumn :=
  [⟨"selected", ⟨.int32, false⟩⟩, ⟨"id", ⟨.int32, false⟩⟩, ⟨"id", ⟨.int32, true⟩⟩]

/-- A nonvacuous full-query derivation, independent of checker acceptance. -/
private theorem query_derivation :
    QueryValid .basicV11 catalog params query output [.anonymous 1, .anonymous 2] := by
  unfold query
  apply QueryValid.basic (scope := leftScope.append nullableRight)
    (sourceUses := [.anonymous 2]) (selectUses := [.anonymous 1])
    (whereUses := []) (orderUses := []) (limitUses := []) (offsetUses := [])
  · exact joined_valid .left (by decide)
  · exact .expression (expr := anon 1) (alias := some "selected")
      (.parameter (binding := ⟨1, ⟨.int, []⟩, false⟩) (by simp [params]) rfl rfl)
      (by simp) (.all (qualifier := none) (selected := (leftScope.append nullableRight).output)
        rfl (by decide) .nil)
  · decide
  · exact Or.inl rfl
  · exact .absent
  · exact .nil
  · exact .absent
  · exact .absent
  · exact .cons rfl (by decide) .nil
  · rfl
  · rfl
  · rfl

private theorem query_valid : SelectValid .basicV11 catalog params query output :=
  .certified (by decide) (by decide) query_derivation (Or.inr rfl)

example : SelectValid .basicV11 catalog params (translateParameters query) output :=
  translateParameters_valid query_valid

/-- Reversing SELECT/FROM occurrence order cannot satisfy the source notation
rule, even though each occurrence has a declared type individually. -/
example : ¬ ParameterOrder [.anonymous 2, .anonymous 1] := by decide

end SQLean.Tests.JoinPreservation
