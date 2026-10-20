import SQLean.Assurance
import Tests.Support

/-! Public assurance regressions, including ASTs that a parser normally rejects.
The direct derivation below deliberately does not obtain its proof from a
checker. Runtime checks exercise classification and exact certificate indices.
-/
namespace SQLean.Tests

private def contractCatalog : Advanced.Catalog := [{
  name := "t"
  columns := [
    { name := "id", type := ⟨.int, []⟩, nullable := some false },
    { name := "label", type := ⟨.text, []⟩, nullable := some true },
    { name := "enabled", type := ⟨.bool, []⟩, nullable := some false }]
}]

private def contractParams : SelectContract.ParameterEnv := [
  { index := 1, type := ⟨.int, []⟩ },
  { index := 2, type := ⟨.bool, []⟩, nullable := true }
]

private def literalQuery : Advanced.Query := {
  body := .select { items := [.expression (.literal (.int 7)) (some "seven")] }
}

/-- A kernel-checked rule derivation independent of all checker execution. -/
private theorem literalQuery_valid :
    SelectContract.SelectValid .basicV01 [] [] literalQuery
      [⟨"seven", ⟨.int32, false⟩⟩] := by
  apply SelectContract.SelectValid.basic
    (scope := []) (selectUses := []) (whereUses := []) (orderUses := [])
  · decide
  · decide
  · exact .empty
  · exact .expression (.int (by decide)) (by decide) .nil
  · decide
  · exact .absent
  · exact .nil
  · decide
  · rfl
  · rfl
  · rfl

private def literalCertificate :
    SelectContract.Certificate .basicV01 [] [] literalQuery :=
  ⟨[⟨"seven", ⟨.int32, false⟩⟩], literalQuery_valid⟩

/-- SQL UNKNOWN remains nullable when a Boolean context supplies its type. -/
example : SelectContract.ExprValid [] []
    (.binary .and .null (.literal (.bool true)))
    (some ⟨.bool, true⟩) [] :=
  .binary .null .bool rfl

/-- Contextual NULL never permits arithmetic on a concrete TEXT operand. -/
example : SelectContract.binarySignature .add
    (some ⟨.text, false⟩) none = none := rfl

example : literalCertificate.outputCatalog = [] :=
  literalCertificate.catalog_unchanged

/-- The public certificate retains every input index, including the profile. -/
example (profile : SelectContract.Profile) (catalog : Advanced.Catalog)
    (params : SelectContract.ParameterEnv) (query : Advanced.Query)
    (certificate : SelectContract.Certificate profile catalog params query) :
    SelectContract.SelectValid profile catalog params query certificate.output :=
  certificate.valid

private def outcomeName :
    Assurance.ContractOutcome profile catalog params query → String
  | .valid _ => "valid"
  | .invalid _ => "invalid"
  | .unsupported _ => "unsupported"
  | .inconclusive _ => "inconclusive"

private def checkContractCase (label : String) (expected : String)
    (catalog : Advanced.Catalog) (params : SelectContract.ParameterEnv)
    (query : Advanced.Query) (fuel : Nat := 1024)
    (columns : Option (List SelectContract.OutputColumn) := none) : IO Unit := do
  let outcome := Assurance.checkContract .basicV01 catalog params query fuel
  SQLean.Tests.assert (outcomeName outcome == expected)
    s!"{label}: expected {expected}, got {outcomeName outcome}"
  match outcome with
  | .valid certificate =>
      -- These terms cannot type check if the result is merely checker equality
      -- or if any catalog/parameter/query index was lost.
      have _derivation : SelectContract.SelectValid .basicV01 catalog params query certificate.output :=
        certificate.valid
      have _unchanged : certificate.outputCatalog = catalog :=
        certificate.catalog_unchanged
      SQLean.Tests.assert (certificate.outputCatalog == catalog) s!"{label}: SELECT changed catalog"
      if let some expectedColumns := columns then
        SQLean.Tests.assert (certificate.output == expectedColumns) s!"{label}: incorrect exact output schema"
  | _ => pure ()

private def parameterQuery (parameters : List Advanced.Parameter) : Advanced.Query :=
  { body := .select { items := parameters.map (fun p => .expression (.parameter p)) } }

private def tableQuery (name : Name := "t") (alias : Option Name := none) : Advanced.Query :=
  { body := .select { items := [.all], source := some (.table name alias []) } }

private def columnQuery (qualifier : Option Name) (name : Name)
    (alias : Option Name := none) : Advanced.Query :=
  { body := .select {
    items := [.expression (.column qualifier name)]
    source := some (.table "t" alias []) } }

private structure RawCase where
  label : String
  expected : String
  query : Advanced.Query := literalQuery
  catalog : Advanced.Catalog := contractCatalog
  params : SelectContract.ParameterEnv := []
  fuel : Nat := 1024

def selectContractTests : IO Nat := do
  let raw : List RawCase := [
    { label := "manual empty projection", expected := "invalid",
      query := { body := .select { items := [] } } },
    { label := "manual source-free wildcard", expected := "invalid",
      query := { body := .select { items := [.all] } } },
    { label := "manual absent source", expected := "invalid", query := tableQuery "missing" },
    { label := "manual empty relation alias", expected := "invalid", query := tableQuery "t" (some "") },
    { label := "manual alias hides table name", expected := "invalid",
      query := columnQuery (some "t") "id" (some "x") },
    { label := "manual unknown qualified column", expected := "invalid",
      query := columnQuery (some "t") "absent" },
    { label := "manual empty projection alias", expected := "invalid",
      query := { body := .select { items := [.expression (.literal (.int 1)) (some "")] } } },
    { label := "manual empty IN list", expected := "invalid",
      query := { body := .select { items := [.expression (.inList (.literal (.int 1)) [])] } } },
    { label := "manual mixed placeholder styles", expected := "invalid",
      params := contractParams, query := parameterQuery [.numbered 1, .anonymous 2] },
    { label := "manual anonymous parameter gap", expected := "invalid",
      params := contractParams, query := parameterQuery [.anonymous 2] },
    { label := "manual repeated anonymous parameter", expected := "invalid",
      params := contractParams, query := parameterQuery [.anonymous 1, .anonymous 1] },
    { label := "manual zero parameter", expected := "invalid",
      params := contractParams, query := parameterQuery [.numbered 0] },
    { label := "undeclared parameter identity", expected := "invalid",
      params := contractParams, query := parameterQuery [.numbered 3] },
    { label := "duplicate parameter declarations", expected := "invalid",
      params := [{ index := 1, type := ⟨.int, []⟩ }, { index := 1, type := ⟨.bool, []⟩ }] },
    { label := "zero declared parameter", expected := "invalid",
      params := [{ index := 0, type := ⟨.int, []⟩ }] },
    { label := "malformed parameter datatype", expected := "invalid",
      params := [{ index := 1, type := ⟨.int, [4]⟩ }] },
    { label := "duplicate relation metadata", expected := "invalid",
      catalog := contractCatalog ++ contractCatalog },
    { label := "duplicate column metadata", expected := "invalid",
      catalog := [{ name := "t", columns := [
        { name := "id", type := ⟨.int, []⟩ }, { name := "id", type := ⟨.text, []⟩ }] }] },
    { label := "empty relation metadata", expected := "invalid",
      catalog := [{ name := "t", columns := [] }] },
    { label := "malformed catalog datatype", expected := "invalid",
      catalog := [{ name := "t", columns := [{ name := "id", type := ⟨.int, [4]⟩ }] }] },
    { label := "invalid primary key metadata", expected := "invalid",
      catalog := [{ name := "t", columns := [{ name := "id", type := ⟨.int, []⟩ }], primaryKey := ["absent"] }] },
    { label := "INT64 metadata stays distinct", expected := "unsupported",
      catalog := [{ name := "t", columns := [{ name := "id", type := ⟨.bigInt, []⟩ }] }] },
    { label := "NUMERIC metadata stays distinct", expected := "unsupported",
      catalog := [{ name := "t", columns := [{ name := "amount", type := ⟨.numeric, [8, 2]⟩ }] }] },
    { label := "VARCHAR metadata stays distinct", expected := "unsupported",
      catalog := [{ name := "t", columns := [{ name := "label", type := ⟨.varchar, [20]⟩ }] }] },
    { label := "wide parameter stays distinct", expected := "unsupported",
      params := [{ index := 1, type := ⟨.bigInt, []⟩ }] },
    { label := "literal beyond INT32 is a coverage gap", expected := "unsupported",
      query := { body := .select { items := [.expression (.literal (.int 2147483648))] } } },
    { label := "contract zero budget", expected := "inconclusive", fuel := 0 },
    { label := "contract insufficient nested budget", expected := "inconclusive", fuel := 1 }
  ]
  for test in raw do
    checkContractCase test.label test.expected test.catalog test.params test.query test.fuel

  checkContractCase "independent literal example" "valid" [] [] literalQuery
    (columns := some [⟨"seven", ⟨.int32, false⟩⟩])
  checkContractCase "wildcard preserves ordered nullable schema" "valid" contractCatalog [] (tableQuery)
    (columns := some [⟨"id", ⟨.int32, false⟩⟩, ⟨"label", ⟨.text, true⟩⟩, ⟨"enabled", ⟨.bool, false⟩⟩])
  checkContractCase "manual repeated numbered identity" "valid" [] contractParams
    (parameterQuery [.numbered 2, .numbered 1, .numbered 2])
    (columns := some [
      ⟨"?column?", ⟨.bool, true⟩⟩, ⟨"?column?", ⟨.int32, false⟩⟩, ⟨"?column?", ⟨.bool, true⟩⟩])
  checkContractCase "manual anonymous identities in order" "valid" [] contractParams
    (parameterQuery [.anonymous 1, .anonymous 2])
    (columns := some [⟨"?column?", ⟨.int32, false⟩⟩, ⟨"?column?", ⟨.bool, true⟩⟩])
  checkContractCase "manual alias replaces relation" "valid" contractCatalog []
    (columnQuery (some "x") "id" (some "x"))
    (columns := some [⟨"id", ⟨.int32, false⟩⟩])
  let parsed ← expectOk "contract parsing API"
    (Assurance.parseContract .basicV01 contractCatalog []
      "SELECT label FROM t WHERE label IS NOT NULL")
  checkContractCase "nullable filter does not refine output" "valid" contractCatalog [] parsed.query
    (columns := some [⟨"label", ⟨.text, true⟩⟩])
  SQLean.Tests.assert (outcomeName parsed.outcome == "valid") "parseContract preserves outcome"

  let advanced ← expectOk "expanded syntax remains parseable"
    (Advanced.parseQuery "SELECT COUNT(*) AS n FROM t")
  checkContractCase "aggregate independent rules are pending" "unsupported" contractCatalog [] advanced
  match Assurance.checkExpanded contractCatalog [] advanced with
  | .checked certificate =>
      SQLean.Tests.assert (certificate.output.map ColumnDef.type == [.int])
        "expanded aggregate retains coarse result family"
  | _ => throw (IO.userError "expanded aggregate should retain executable assurance")
  match Assurance.checkExpanded contractCatalog [] literalQuery 0 with
  | .inconclusive _ => pure ()
  | _ => throw (IO.userError "expanded fuel exhaustion must be inconclusive")
  let exactParams ← expectOk "exact parameter API"
    (Assurance.parseContractParameterTypes "bigint,numeric?,text")
  SQLean.Tests.assert (exactParams.map (·.type.name) == [.bigInt, .numeric, .text])
    "exact parameter API collapsed concrete types"
  SQLean.Tests.assert (exactParams.map (·.nullable) == [false, true, false])
    "exact parameter API lost nullability"
  pure (raw.length + 12)

end SQLean.Tests
