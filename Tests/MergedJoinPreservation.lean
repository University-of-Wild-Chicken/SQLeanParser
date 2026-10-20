import SQLean.RenderContract.ValidityPreservation

/-! Independent constructive USING/NATURAL witnesses, without parser or checker
imports. Exposed rows and qualified namespaces deliberately have different
orders and types. A nested ON predicate resolves the merged INT64 key, and a
full-query derivation preserves SELECT-before-FROM parameter occurrence order.
-/
namespace SQLean.Tests.MergedJoinPreservation
open Advanced SelectContract RenderContract

private def leftTable : CatalogTable := {
  name := "left_table"
  columns := [
    {name := "a", type := ⟨.text, []⟩, nullable := some false},
    {name := "k", type := ⟨.int, []⟩, nullable := some false},
    {name := "v", type := ⟨.varchar, [5]⟩, nullable := some false}] }
private def rightTable : CatalogTable := {
  name := "right_table"
  columns := [
    {name := "v", type := ⟨.varchar, [8]⟩, nullable := some false},
    {name := "k", type := ⟨.bigInt, []⟩, nullable := some true},
    {name := "b", type := ⟨.bool, []⟩, nullable := some false}] }
private def auxTable : CatalogTable := {
  name := "aux_table"
  columns := [{name := "z", type := ⟨.int, []⟩, nullable := some false}] }
private def catalog : Catalog := [leftTable, rightTable, auxTable]
private def params : SelectContract.ParameterEnv :=
  [⟨1, ⟨.int, []⟩, false⟩, ⟨2, ⟨.bigInt, []⟩, false⟩]

private def leftSource : Advanced.From := .table "left_table" (some "l")
private def rightSource : Advanced.From := .table "right_table" (some "r")
private def auxSource : Advanced.From := .table "aux_table" (some "x")
private def leftScope : Scope := .ofBindings [
  ⟨"l", ⟨"a", ⟨.text, false⟩⟩⟩, ⟨"l", ⟨"k", ⟨.int32, false⟩⟩⟩,
  ⟨"l", ⟨"v", ⟨.varchar [5], false⟩⟩⟩]
private def rightScope : Scope := .ofBindings [
  ⟨"r", ⟨"v", ⟨.varchar [8], false⟩⟩⟩, ⟨"r", ⟨"k", ⟨.int64, true⟩⟩⟩,
  ⟨"r", ⟨"b", ⟨.bool, false⟩⟩⟩]
private def auxScope : Scope := .ofBindings [⟨"x", ⟨"z", ⟨.int32, false⟩⟩⟩]

private theorem left_valid : SourceValid .basicV21 catalog params (some leftSource) leftScope [] :=
  .table (table := leftTable) (by simp [catalog]) rfl (by simp)
    (.cons rfl (.cons rfl (.cons rfl .nil)))
private theorem right_valid : SourceValid .basicV21 catalog params (some rightSource) rightScope [] :=
  .table (table := rightTable) (by simp [catalog]) rfl (by simp)
    (.cons rfl (.cons rfl (.cons rfl .nil)))
private theorem aux_valid : SourceValid .basicV21 catalog params (some auxSource) auxScope [] :=
  .table (table := auxTable) (by simp [catalog]) rfl (by simp) (.cons rfl .nil)

private def merged : List OutputColumn :=
  [⟨"v", ⟨.varchar [], false⟩⟩, ⟨"k", ⟨.int64, true⟩⟩]
private def usingSource : Advanced.From :=
  .join .full leftSource rightSource (.using ["v", "k"])
private def usingScope : Scope := mergedJoinScope .full leftScope rightScope ["v", "k"] merged

private theorem using_keys :
    JoinKeysValid .full leftScope.output rightScope.output ["v", "k"] merged :=
  .cons (leftColumn := ⟨"v", ⟨.varchar [5], false⟩⟩)
    (rightColumn := ⟨"v", ⟨.varchar [8], false⟩⟩) (base := .varchar [])
    rfl rfl rfl rfl
    (.cons (leftColumn := ⟨"k", ⟨.int32, false⟩⟩)
      (rightColumn := ⟨"k", ⟨.int64, true⟩⟩) (base := .int64) rfl rfl rfl rfl .nil)

private theorem using_valid : SourceValid .basicV21 catalog params (some usingSource) usingScope [] :=
  .using left_valid right_valid (by decide) (by decide) (by decide) (by decide) using_keys

example : usingScope.output =
    [⟨"v", ⟨.varchar [], false⟩⟩, ⟨"k", ⟨.int64, true⟩⟩,
     ⟨"a", ⟨.text, true⟩⟩, ⟨"b", ⟨.bool, true⟩⟩] := by decide

example : usingScope.columns (some "l") =
    [⟨"a", ⟨.text, true⟩⟩, ⟨"k", ⟨.int32, true⟩⟩,
     ⟨"v", ⟨.varchar [5], true⟩⟩] := by decide

example : usingScope.columns (some "r") =
    [⟨"v", ⟨.varchar [8], true⟩⟩, ⟨"k", ⟨.int64, true⟩⟩,
     ⟨"b", ⟨.bool, true⟩⟩] := by decide

example : Resolves usingScope none "k" ⟨"k", ⟨.int64, true⟩⟩ := by decide
example : Resolves usingScope (some "l") "k" ⟨"k", ⟨.int32, true⟩⟩ := by decide
example : ¬ Resolves usingScope (some "") "k" ⟨"k", ⟨.int64, true⟩⟩ := by decide

example : SourceValid .basicV21 catalog params (some (translateSource usingSource)) usingScope [] :=
  source_valid_translated using_valid

private def naturalMerged : List OutputColumn :=
  [⟨"k", ⟨.int64, true⟩⟩, ⟨"v", ⟨.varchar [], false⟩⟩]
private def naturalSource : Advanced.From := .join .full leftSource rightSource .natural
private def naturalScope : Scope :=
  mergedJoinScope .full leftScope rightScope ["k", "v"] naturalMerged

example : naturalJoinKeys leftScope.output rightScope.output = ["k", "v"] := by decide

private theorem natural_valid :
    SourceValid .basicV21 catalog params (some naturalSource) naturalScope [] :=
  .natural left_valid right_valid (by decide) (by decide) (by decide)
    (.cons (leftColumn := ⟨"k", ⟨.int32, false⟩⟩)
      (rightColumn := ⟨"k", ⟨.int64, true⟩⟩) (base := .int64) rfl rfl rfl rfl
      (.cons (leftColumn := ⟨"v", ⟨.varchar [5], false⟩⟩)
        (rightColumn := ⟨"v", ⟨.varchar [8], false⟩⟩) (base := .varchar [])
        rfl rfl rfl rfl .nil))

example : SourceValid .basicV21 catalog params (some (translateSource naturalSource)) naturalScope [] :=
  source_valid_translated natural_valid

/-- Zero shared names is a legal NATURAL join, including FULL; both exposed
rows remain intact and acquire the ordinary outer-join NULL extension. -/
example : SourceValid .basicV21 catalog params (some (.join .full leftSource auxSource .natural))
    (joinScope .full leftScope auxScope) [] :=
  .natural left_valid aux_valid (by decide) (by decide) (by decide) .nil

example : naturalScope.output =
    [⟨"k", ⟨.int64, true⟩⟩, ⟨"v", ⟨.varchar [], false⟩⟩,
     ⟨"a", ⟨.text, true⟩⟩, ⟨"b", ⟨.bool, true⟩⟩] := by decide

/-- Equal declaration modifiers survive merged output inference. -/
example : JoinKeysValid .inner [⟨"n", ⟨.numeric [8, 2], false⟩⟩]
    [⟨"n", ⟨.numeric [8, 2], false⟩⟩] ["n"]
    [⟨"n", ⟨.numeric [8, 2], false⟩⟩] :=
  .cons (leftColumn := ⟨"n", ⟨.numeric [8, 2], false⟩⟩)
    (rightColumn := ⟨"n", ⟨.numeric [8, 2], false⟩⟩) (base := .numeric [8, 2])
    rfl rfl rfl rfl .nil

/-- NATURAL discovers exposed keys, preserving repeated names so ambiguity
cannot silently disappear through deduplication. -/
example : naturalJoinKeys
    [⟨"k", ⟨.int32, false⟩⟩, ⟨"k", ⟨.int32, false⟩⟩]
    [⟨"k", ⟨.int32, false⟩⟩] = ["k", "k"] := by decide

private def nestedCondition : Advanced.Expr :=
  .binary .eq (.column none "k") (.parameter (.anonymous 2))
private def nestedSource : Advanced.From := .join .inner usingSource auxSource (.on nestedCondition)
private def nestedScope : Scope := usingScope.append auxScope

private theorem nested_valid :
    SourceValid .basicV21 catalog params (some nestedSource) nestedScope [.anonymous 2] :=
  .on using_valid aux_valid (by decide) (by decide)
    (.present (.binary (.column (scope := nestedScope) (qualifier := none) (name := "k")
      (column := ⟨"k", ⟨.int64, true⟩⟩) rfl)
      (.parameter (binding := ⟨2, ⟨.bigInt, []⟩, false⟩) (by simp [params]) rfl rfl) rfl) rfl)

example : SourceValid .basicV21 catalog params (some (translateSource nestedSource))
    nestedScope [.numbered 2] :=
  source_valid_translated nested_valid

private def query : Advanced.Query := {
  body := .select {
    items := [.expression (.parameter (.anonymous 1)) (some "selected"), .all none]
    source := some nestedSource } }
private def output : List OutputColumn := ⟨"selected", ⟨.int32, false⟩⟩ :: nestedScope.output

private theorem query_derivation :
    QueryValid .basicV21 catalog params query output [.anonymous 1, .anonymous 2] := by
  unfold query
  apply QueryValid.basic (scope := nestedScope)
    (sourceUses := [.anonymous 2]) (selectUses := [.anonymous 1])
    (whereUses := []) (orderUses := []) (limitUses := []) (offsetUses := [])
  · exact nested_valid
  · exact .expression (expr := .parameter (.anonymous 1)) (alias := some "selected")
      (.parameter (binding := ⟨1, ⟨.int, []⟩, false⟩) (by simp [params]) rfl rfl)
      (by simp) (.all (qualifier := none) (selected := nestedScope.output) rfl (by decide) .nil)
  · decide
  · exact Or.inl rfl
  · exact .absent
  · exact .nil
  · exact .absent
  · exact .absent
  · exact .nil
  · rfl
  · rfl
  · rfl

private theorem query_valid : SelectValid .basicV21 catalog params query output :=
  .certified (by decide) (by decide) query_derivation (Or.inr rfl)

example : SelectValid .basicV21 catalog params (translateParameters query) output :=
  translateParameters_valid query_valid

end SQLean.Tests.MergedJoinPreservation
