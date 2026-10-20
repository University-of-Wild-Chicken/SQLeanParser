import SQLean.RenderContract.ValidityPreservation

/-! Kernel-checked derived-source witnesses, without parser or checker imports.
Child derivations collect their original anonymous ordinals. Only the public
statement judgment checks global order; exposed duplicate labels and positional
prefix aliases preserve exact types and never become fabricated catalog rows.
-/
namespace SQLean.Tests.DerivedPreservation
open Advanced SelectContract RenderContract

private def table : CatalogTable := {
  name := "base_table"
  columns := [{name := "id", type := ⟨.int, []⟩, nullable := some false}] }
private def catalog : Catalog := [table]
private def params : SelectContract.ParameterEnv :=
  [⟨1, ⟨.int, []⟩, false⟩, ⟨2, ⟨.varchar, [5]⟩, true⟩, ⟨3, ⟨.bigInt, []⟩, false⟩]
private def anon (index : Nat) : Advanced.Expr := .parameter (.anonymous index)
private def baseSource : Advanced.From := .table "base_table" (some "inside")
private def baseScope : Scope := .ofTable table.identity (some "inside") [{name := "id", type := ⟨.int32, false⟩}]

private theorem base_valid :
    SourceValid .basicV32 catalog params [] (some baseSource) baseScope [] :=
  .table (table := table) (Or.inr rfl) (by simp [catalog]) rfl (by simp) (.cons rfl .nil)

private def child : Advanced.Query := {
  body := .select {
    items := [.expression (.cast (anon 2) ⟨.varchar, [5]⟩) (some "dup"),
      .expression (.cast .null ⟨.numeric, [8, 2]⟩) (some "dup"),
      .expression (.column (some "inside") "id") (some "tail")]
    source := some baseSource }
  limit := some (anon 3) }
private def childOutput : List OutputColumn :=
  [{name := "dup", type := ⟨.varchar [5], true⟩}, {name := "dup", type := ⟨.numeric [8, 2], true⟩},
    {name := "tail", type := ⟨.int32, false⟩}]

private theorem child_valid :
    QueryValid .basicV32 catalog params [] child childOutput [.anonymous 2, .anonymous 3] := by
  have first : ExprValid params baseScope (.cast (anon 2) ⟨.varchar, [5]⟩)
      (some ⟨.varchar [5], true⟩) [.anonymous 2] :=
    .cast (.parameter (binding := ⟨2, ⟨.varchar, [5]⟩, true⟩)
      (by simp [params]) rfl rfl) rfl (by decide) rfl (by trivial)
  have firstCollation : ExprCollationValid .basicV32 params baseScope
      (.cast (anon 2) ⟨.varchar, [5]⟩) (some ⟨.varchar [5], true⟩)
      (.implicit .databaseDefault) :=
    .cast first (.parameter (binding := ⟨2, ⟨.varchar, [5]⟩, true⟩)
      (by simp [params]) rfl rfl) rfl
  have second : ExprValid params baseScope (.cast .null ⟨.numeric, [8, 2]⟩)
      (some ⟨.numeric [8, 2], true⟩) [] :=
    .cast .null rfl (by decide) rfl (by trivial)
  have secondCollation : ExprCollationValid .basicV32 params baseScope
      (.cast .null ⟨.numeric, [8, 2]⟩) (some ⟨.numeric [8, 2], true⟩) .none :=
    .cast second (.atom .null .null) rfl
  apply QueryValid.basic (cteUses := []) (visible := []) (by decide) .nil (scope := baseScope) (sourceUses := [])
    (selectUses := [.anonymous 2]) (whereUses := []) (orderUses := [])
    (limitUses := [.anonymous 3]) (offsetUses := [])
  · exact base_valid
  · exact .expression (expr := .cast (anon 2) ⟨.varchar, [5]⟩) (alias := some "dup")
      first firstCollation (by simp)
      (.expression (expr := .cast .null ⟨.numeric, [8, 2]⟩) (alias := some "dup")
        second secondCollation (by simp)
        (.expression (expr := .column (some "inside") "id") (alias := some "tail")
          (.column (scope := baseScope) (column := {name := "id", type := ⟨.int32, false⟩}) rfl)
          (.column rfl) (by simp) .nil))
  · exact .expression (expr := .cast (anon 2) ⟨.varchar, [5]⟩) (alias := some "dup")
      first firstCollation (by simp)
      (.expression (expr := .cast .null ⟨.numeric, [8, 2]⟩) (alias := some "dup")
        second secondCollation (by simp)
        (.expression (expr := .column (some "inside") "id") (alias := some "tail")
          (.column (scope := baseScope) (column := {name := "id", type := ⟨.int32, false⟩}) rfl)
          (.column rfl) (by simp) .nil))
  · decide
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact .absent
  · exact .nil
  · exact .nil
  · exact .present (.parameter (binding := ⟨3, ⟨.bigInt, []⟩, false⟩)
      (by simp [params]) rfl rfl)
      (.parameter (binding := ⟨3, ⟨.bigInt, []⟩, false⟩) (by simp [params]) rfl rfl)
      (.int64Identity false)
  · exact .absent
  · exact .nil
  · rfl
  · rfl
  · rfl

/-- This child is typable in a statement whose first occurrence is outside it.
Applying the statement notation test separately to the child would be wrong. -/
example : ¬ ParameterOrder [.anonymous 2, .anonymous 3] := by decide

private def source : Advanced.From := .derived child "d" ["first"] false
private def exposed : Scope := Scope.ofOutput "d" (renameOutput ["first"] childOutput)
private theorem source_valid :
    SourceValid .basicV32 catalog params [] (some source) exposed [.anonymous 2, .anonymous 3] :=
  .derived child_valid (by decide) (by decide) rfl

example : exposed.output =
    [{name := "first", type := ⟨.varchar [5], true⟩}, {name := "dup", type := ⟨.numeric [8, 2], true⟩},
      {name := "tail", type := ⟨.int32, false⟩}] := by decide
example : exposed.columns (some "inside") = [] := by decide
example : exposed.columns (some "base_table") = [] := by decide
example : exposed.columns (some "d") = exposed.output := by decide
example : Resolves exposed (some "d") "dup" {name := "dup", type := ⟨.numeric [8, 2], true⟩} := by decide

/-- Duplicate labels and duplicate prefix aliases remain legal exposed rows. -/
example : SourceValid .basicV32 catalog params [] (some (.derived child "d" [] false))
    (Scope.ofOutput "d" childOutput) [.anonymous 2, .anonymous 3] :=
  .derived child_valid (by decide) (by decide) rfl
example : SourceValid .basicV32 catalog params [] (some (.derived child "d" ["x", "x"] false))
    (Scope.ofOutput "d" (renameOutput ["x", "x"] childOutput)) [.anonymous 2, .anonymous 3] :=
  .derived child_valid (by decide) (by decide) rfl
example : ¬ Resolves (Scope.ofOutput "d" childOutput) (some "d") "dup"
    {name := "dup", type := ⟨.varchar [5], true⟩} := by decide
example : ¬ ColumnAliasesValid ["a", "b", "c", "d"] childOutput := by decide
example : ¬ ColumnAliasesValid [""] childOutput := by decide

private def middle : Advanced.Query := {
  body := .select { items := [.all (some "d")], source := some source } }
private theorem middle_valid :
    QueryValid .basicV32 catalog params [] middle exposed.output [.anonymous 2, .anonymous 3] := by
  apply QueryValid.basic (cteUses := []) (visible := []) (by decide) .nil (scope := exposed) (sourceUses := [.anonymous 2, .anonymous 3])
    (selectUses := []) (whereUses := []) (orderUses := []) (limitUses := []) (offsetUses := [])
  · exact source_valid
  · exact .all (qualifier := some "d") rfl (by decide) .nil
  · exact .all (qualifier := some "d") rfl (by decide) .nil
  · decide
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact .absent
  · exact .nil
  · exact .nil
  · exact .absent
  · exact .absent
  · exact .nil
  · rfl
  · rfl
  · rfl

private def nestedSource : Advanced.From := .derived middle "q" [] false
private def nestedScope : Scope := Scope.ofOutput "q" exposed.output
private theorem nested_valid :
    SourceValid .basicV32 catalog params [] (some nestedSource) nestedScope [.anonymous 2, .anonymous 3] :=
  .derived middle_valid (by decide) (by decide) rfl

example : SourceValid .basicV32 catalog params [] (some (translateSource nestedSource))
    nestedScope [.numbered 2, .numbered 3] :=
  source_valid_translated nested_valid
example : QueryValid .basicV32 catalog params [] (translateParameters child)
    childOutput [.numbered 2, .numbered 3] := query_valid_translated child_valid

private def outer : Advanced.Query := {
  body := .select {
    items := [.expression (anon 1) (some "selected"), .all (some "q")]
    source := some nestedSource } }
private def output : List OutputColumn := {name := "selected", type := ⟨.int32, false⟩} :: exposed.output
private theorem outer_derivation :
    QueryValid .basicV32 catalog params [] outer output [.anonymous 1, .anonymous 2, .anonymous 3] := by
  apply QueryValid.basic (cteUses := []) (visible := []) (by decide) .nil (scope := nestedScope) (sourceUses := [.anonymous 2, .anonymous 3])
    (selectUses := [.anonymous 1]) (whereUses := []) (orderUses := []) (limitUses := []) (offsetUses := [])
  · exact nested_valid
  · exact .expression (expr := anon 1) (alias := some "selected")
      (.parameter (binding := ⟨1, ⟨.int, []⟩, false⟩) (by simp [params]) rfl rfl)
      (.parameter (binding := ⟨1, ⟨.int, []⟩, false⟩) (by simp [params]) rfl rfl) (by simp)
      (.all (qualifier := some "q") rfl (by decide) .nil)
  · exact .expression (expr := anon 1) (alias := some "selected")
      (.parameter (binding := ⟨1, ⟨.int, []⟩, false⟩) (by simp [params]) rfl rfl)
      (.parameter (binding := ⟨1, ⟨.int, []⟩, false⟩) (by simp [params]) rfl rfl) (by simp)
      (.all (qualifier := some "q") rfl (by decide) .nil)
  · decide
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact .absent
  · exact .nil
  · exact .nil
  · exact .absent
  · exact .absent
  · exact .nil
  · rfl
  · rfl
  · rfl

private theorem outer_valid : SelectValid .basicV32 catalog params outer output :=
  .certified (by decide) (by decide) (by decide) outer_derivation (Or.inr rfl)
example : SelectValid .basicV32 catalog params (translateParameters outer) output :=
  translateParameters_valid outer_valid

/-- A derived alias is not silently promoted to a base-table lock target.
A distinct base sibling remains lockable without propagating locks into the
derived query. -/
private def sibling : Advanced.From := .table "base_table" (some "b")
private def combined : Advanced.From := .join .cross nestedSource sibling .none
example : SourceValid .basicV32 catalog params [] (some combined)
    (nestedScope ++ Scope.ofTable table.identity (some "b") [{name := "id", type := ⟨.int32, false⟩}])
    [.anonymous 2, .anonymous 3] :=
  .cross nested_valid
    (.table (table := table) (Or.inr rfl) (by simp [catalog]) rfl (by simp) (.cons rfl .nil))
    (by decide)
example : sourceDerivedNames (some combined) = ["q"] := by decide
example : LockTargets (nestedScope ++ Scope.ofTable table.identity (some "b") [{name := "id", type := ⟨.int32, false⟩}]) ["b"] := by decide
example : ¬ LockTargets (nestedScope ++ Scope.ofTable table.identity (some "b") [{name := "id", type := ⟨.int32, false⟩}]) ["q"] := by decide
example : ¬ LockTargets (nestedScope ++ Scope.ofTable table.identity (some "b") [{name := "id", type := ⟨.int32, false⟩}]) [] := by decide


end SQLean.Tests.DerivedPreservation
