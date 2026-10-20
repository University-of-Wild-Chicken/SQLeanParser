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

private def rowCountParams : SelectContract.ParameterEnv := [
  { index := 1, type := ⟨.int, []⟩ },
  { index := 2, type := ⟨.int, []⟩, nullable := true },
  { index := 3, type := ⟨.int, []⟩ }
]

private def literalQuery : Advanced.Query := {
  body := .select { items := [.expression (.literal (.int 7)) (some "seven")] }
}

/-- A kernel-checked rule derivation independent of all checker execution. -/
private theorem literalQuery_valid :
    SelectContract.SelectValid .basicV13 [] [] literalQuery
      [⟨"seven", ⟨.int32, false⟩⟩] := by
  apply SelectContract.SelectValid.certified (uses := [])
  · decide
  · decide
  · apply SelectContract.QueryValid.basic
      (scope := .empty) (selectUses := []) (sourceUses := []) (whereUses := []) (orderUses := [])
      (limitUses := []) (offsetUses := [])
    · exact .empty
    · exact .expression (.int (by decide)) (by decide) .nil
    · decide
    · decide
    · exact .absent
    · exact .nil
    · exact .absent
    · exact .absent
    · exact .nil
    · rfl
    · rfl
    · rfl
  · decide

private def literalCertificate :
    SelectContract.Certificate .basicV13 [] [] literalQuery :=
  ⟨[⟨"seven", ⟨.int32, false⟩⟩], literalQuery_valid⟩

/-- SQL UNKNOWN remains nullable when a Boolean context supplies its type. -/
example : SelectContract.ExprValid [] .empty
    (.binary .and .null (.literal (.bool true)))
    (some ⟨.bool, true⟩) [] :=
  .binary .null .bool rfl

/-- Contextual NULL never permits arithmetic on a concrete TEXT operand. -/
example : SelectContract.binarySignature .add
    (some ⟨.text, false⟩) none = none := rfl

/-- Closed pagination typing and runtime nonnegativity are separate facts. -/
example : SelectContract.PaginationValid []
    (some (.unary .neg (.literal (.int 1)))) [] :=
  .present (.unary (.int (by decide)) rfl (by decide)) (.int32Widen false)

example : ¬ SelectContract.PaginationValueAllowed (some (-1)) := by
  unfold SelectContract.PaginationValueAllowed
  decide

example : SelectContract.PaginationValid [] (some .null) [] :=
  .present .null .unknownNull

example : SelectContract.PaginationValueAllowed none := by
  unfold SelectContract.PaginationValueAllowed
  decide

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
  let outcome := Assurance.checkContract .basicV13 catalog params query fuel
  SQLean.Tests.assert (outcomeName outcome == expected)
    s!"{label}: expected {expected}, got {outcomeName outcome}"
  match outcome with
  | .valid certificate =>
      -- These terms cannot type check if the result is merely checker equality
      -- or if any catalog/parameter/query index was lost.
      have _derivation : SelectContract.SelectValid .basicV13 catalog params query certificate.output :=
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

private def scalarProjection (expr : Advanced.Expr) : Advanced.Query :=
  { body := .select { items := [.expression expr (some "v")] } }

/-- Authored exact declarations exercise preserved catalog/cast modifiers and
PostgreSQL parameter OID semantics, which discard parameter declaration typmods. JSON's missing
comparison operators are tested through each query-level use as well. -/
private def scalarContractTests : IO Nat := do
  let declarations : List (Advanced.DataType × SelectContract.ScalarType) := [
    (⟨.smallInt, []⟩, .smallInt), (⟨.bigInt, []⟩, .int64),
    (⟨.numeric, [8, 2]⟩, .numeric [8, 2]), (⟨.numeric, [6]⟩, .numeric [6]),
    (⟨.real, []⟩, .real), (⟨.doublePrecision, []⟩, .doublePrecision),
    (⟨.varchar, [20]⟩, .varchar [20]), (⟨.char, []⟩, .char [1]),
    (⟨.char, [7]⟩, .char [7]), (⟨.date, []⟩, .date),
    (⟨.time, [3]⟩, .time [3]), (⟨.timeTZ, [6]⟩, .timeTZ [6]),
    (⟨.timestamp, []⟩, .timestamp []), (⟨.timestamp, [0]⟩, .timestamp [0]),
    (⟨.timestampTZ, [4]⟩, .timestampTZ [4]), (⟨.interval, [2]⟩, .interval [2]),
    (⟨.uuid, []⟩, .uuid), (⟨.json, []⟩, .json), (⟨.jsonb, []⟩, .jsonb),
    (⟨.bytea, []⟩, .bytea)
  ]
  for (declaration, exact) in declarations do
    let label := reprStr declaration
    let catalog : Advanced.Catalog := [{
      name := "typed", columns := [{ name := "v", type := declaration, nullable := some false }]
    }]
    let table : Advanced.Query := {
      body := .select { items := [.all], source := some (.table "typed") }
    }
    checkContractCase s!"{label}: exact catalog projection" "valid" catalog [] table
      (columns := some [⟨"v", ⟨exact, false⟩⟩])
    let params : SelectContract.ParameterEnv := [⟨1, declaration, true⟩]
    let parameter := Advanced.Expr.parameter (.numbered 1)
    checkContractCase s!"{label}: exact nullable parameter" "valid" [] params (scalarProjection parameter)
      (columns := some [⟨"v", ⟨exact.unmodified, true⟩⟩])
    checkContractCase s!"{label}: exact NULL cast" "valid" [] [] (scalarProjection (.cast .null declaration))
      (columns := some [⟨"v", ⟨exact, true⟩⟩])
    let compared := scalarProjection (.binary .eq parameter parameter)
    let expected := if exact == .json then "invalid" else "valid"
    checkContractCase s!"{label}: equality availability" expected [] params compared
    checkContractCase s!"{label}: ORDER BY ordinal availability" expected [] params
      { scalarProjection parameter with orderBy := [{ expr := 1 }] }
    checkContractCase s!"{label}: DISTINCT availability" expected [] params
      { body := .select { distinct := true, items := [.expression parameter (some "v")] } }

  let invalidCasts : List (Advanced.DataType × Advanced.DataType) := [
    (⟨.bool, []⟩, ⟨.smallInt, []⟩), (⟨.bool, []⟩, ⟨.bigInt, []⟩),
    (⟨.bool, []⟩, ⟨.numeric, []⟩), (⟨.date, []⟩, ⟨.int, []⟩),
    (⟨.uuid, []⟩, ⟨.bigInt, []⟩), (⟨.json, []⟩, ⟨.int, []⟩),
    (⟨.bytea, []⟩, ⟨.uuid, []⟩), (⟨.interval, []⟩, ⟨.timestamp, []⟩),
    (⟨.timeTZ, []⟩, ⟨.timestamp, []⟩)
  ]
  for (source, target) in invalidCasts do
    checkContractCase s!"explicit cast matrix excludes {reprStr source} -> {reprStr target}"
      "invalid" [] [⟨1, source, false⟩]
      (scalarProjection (.cast (.parameter (.numbered 1)) target))

  let malformed : List Advanced.DataType := [
    ⟨.char, [0]⟩, ⟨.char, [10485761]⟩, ⟨.time, [7]⟩, ⟨.timeTZ, [1, 2]⟩,
    ⟨.timestamp, [7]⟩, ⟨.timestampTZ, [7]⟩, ⟨.interval, [7]⟩,
    ⟨.date, [3]⟩, ⟨.uuid, [1]⟩, ⟨.jsonb, [1]⟩
  ]
  for declaration in malformed do
    checkContractCase s!"malformed exact declaration {reprStr declaration}" "invalid" [] []
      (scalarProjection (.cast .null declaration))

  checkContractCase "JSON ORDER BY output label" "invalid" [] [⟨1, ⟨.json, []⟩, false⟩]
    { scalarProjection (.parameter (.numbered 1)) with orderBy := [{ expr := .column none "v" }] }
  checkContractCase "JSON ORDER BY expression" "invalid" [] [⟨1, ⟨.json, []⟩, false⟩]
    { literalQuery with orderBy := [{ expr := .parameter (.numbered 1) }] }
  checkContractCase "JSONB scalar casts can yield SQL NULL" "valid" [] [⟨1, ⟨.jsonb, []⟩, false⟩]
    (scalarProjection (.cast (.parameter (.numbered 1)) ⟨.numeric, [8, 2]⟩))
    (columns := some [⟨"v", ⟨.numeric [8, 2], true⟩⟩])
  checkContractCase "unknown string temporal comparison remains explicit coverage gap" "unsupported" []
    [⟨1, ⟨.date, []⟩, false⟩]
    (scalarProjection (.binary .eq (.parameter (.numbered 1)) (.literal (.text "2024-01-01"))))
  checkContractCase "concrete TEXT does not implicitly become DATE" "invalid" []
    [⟨1, ⟨.date, []⟩, false⟩, ⟨2, ⟨.text, []⟩, false⟩]
    (scalarProjection (.binary .eq (.parameter (.numbered 1)) (.parameter (.numbered 2))))
  checkContractCase "uncovered interval overload stays unsupported" "unsupported" []
    [⟨1, ⟨.interval, []⟩, false⟩]
    (scalarProjection (.binary .mul (.parameter (.numbered 1)) 2))
  checkContractCase "malformed manual decimal" "invalid" [] [] (scalarProjection (.decimal "1.2.3"))
  checkContractCase "unary plus unknown NULL chooses FLOAT8" "valid" [] []
    (scalarProjection (.unary .pos .null))
    (columns := some [⟨"v", ⟨.doublePrecision, true⟩⟩])
  let timeParams : SelectContract.ParameterEnv := [
    ⟨1, ⟨.time, []⟩, false⟩, ⟨2, ⟨.interval, []⟩, false⟩, ⟨3, ⟨.timeTZ, []⟩, false⟩
  ]
  checkContractCase "IN preserves pairwise temporal comparison alternatives" "valid" [] timeParams
    (scalarProjection (.inList (.parameter (.numbered 1))
      [.parameter (.numbered 2), .parameter (.numbered 3)]))
    (columns := some [⟨"v", ⟨.bool, false⟩⟩])
  pure (declarations.length * 6 + invalidCasts.length + malformed.length + 9)

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
    { label := "INT64 metadata stays distinct", expected := "valid",
      catalog := [{ name := "t", columns := [{ name := "id", type := ⟨.bigInt, []⟩ }] }] },
    { label := "NUMERIC metadata stays distinct", expected := "valid",
      catalog := [{ name := "t", columns := [{ name := "amount", type := ⟨.numeric, [8, 2]⟩ }] }] },
    { label := "VARCHAR metadata stays distinct", expected := "valid",
      catalog := [{ name := "t", columns := [{ name := "label", type := ⟨.varchar, [20]⟩ }] }] },
    { label := "wide parameter stays distinct", expected := "valid",
      params := [{ index := 1, type := ⟨.bigInt, []⟩ }] },
    { label := "literal beyond INT32 retains BIGINT", expected := "valid",
      query := { body := .select { items := [.expression (.literal (.int 2147483648))] } } },
    { label := "literal LIMIT", expected := "valid", query := { literalQuery with limit := some 10 } },
    { label := "zero LIMIT and OFFSET", expected := "valid",
      query := { literalQuery with limit := some 0, offset := some 0 } },
    { label := "closed arithmetic pagination", expected := "valid",
      query := { literalQuery with limit := some (.binary .add 2 3), offset := some (.binary .div 6 2) } },
    { label := "NULL pagination", expected := "valid",
      query := { literalQuery with limit := some .null, offset := some .null } },
    { label := "nullable INT32 pagination", expected := "valid", params := rowCountParams,
      query := { literalQuery with limit := some (.parameter (.numbered 2)) } },
    { label := "negative pagination retains runtime obligation", expected := "valid",
      query := { literalQuery with offset := some (.unary .neg 1) } },
    { label := "division failure remains runtime obligation", expected := "valid",
      query := { literalQuery with limit := some (.binary .div 1 0) } },
    { label := "Boolean pagination", expected := "invalid",
      query := { literalQuery with limit := some (.literal (.bool false)) } },
    { label := "concrete TEXT parameter pagination", expected := "invalid",
      params := [{ index := 1, type := ⟨.text, []⟩ }],
      query := { literalQuery with limit := some (.parameter (.numbered 1)) } },
    { label := "unknown string pagination requires contextual coercion", expected := "unsupported",
      query := { literalQuery with limit := some (.literal (.text "5")) } },
    { label := "wide pagination literal", expected := "valid",
      query := { literalQuery with limit := some (.literal (.int 2147483648)) } },
    { label := "BIGINT pagination cast", expected := "valid",
      query := { literalQuery with limit := some (.cast 1 ⟨.bigInt, []⟩) } },
    { label := "decimal pagination", expected := "valid",
      query := { literalQuery with limit := some (.decimal "2.0") } },
    { label := "LIMIT cannot bind local row column", expected := "invalid",
      query := { tableQuery with limit := some (.column none "id") } },
    { label := "OFFSET cannot bind projected alias", expected := "invalid",
      query := { literalQuery with offset := some (.column none "seven") } },
    { label := "pagination scalar subquery remains unsupported", expected := "unsupported",
      query := { literalQuery with limit := some (.scalarQuery literalQuery) } },
    { label := "anonymous pagination follows projection", expected := "valid", params := rowCountParams,
      query := { parameterQuery [.anonymous 1] with
        limit := some (.parameter (.anonymous 2)), offset := some (.parameter (.anonymous 3)) } },
    { label := "anonymous pagination follows ORDER BY", expected := "valid", params := rowCountParams,
      query := { parameterQuery [.anonymous 1] with
        orderBy := [{ expr := .parameter (.anonymous 2) }],
        limit := some (.parameter (.anonymous 3)) } },
    { label := "anonymous repeated across pagination clauses", expected := "invalid", params := rowCountParams,
      query := { parameterQuery [.anonymous 1] with
        limit := some (.parameter (.anonymous 2)), offset := some (.parameter (.anonymous 2)) } },
    { label := "anonymous pagination gap", expected := "invalid", params := rowCountParams,
      query := { parameterQuery [.anonymous 1] with limit := some (.parameter (.anonymous 3)) } },
    { label := "mixed notation in pagination", expected := "invalid", params := rowCountParams,
      query := { parameterQuery [.numbered 1] with limit := some (.parameter (.anonymous 2)) } },
    { label := "undeclared pagination parameter", expected := "invalid",
      query := { literalQuery with limit := some (.parameter (.numbered 1)) } },
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
    (Assurance.parseContract .basicV13 contractCatalog []
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
  let boundsQuery : Advanced.Query := {
    body := .select { items := [.expression .countAll] }
    limit := some (.parameter (.anonymous 2))
    offset := some (.binary .add (.parameter (.anonymous 3)) 1) }
  let bounds ← expectOk "pagination-only certificate for an unsupported body"
    ((SelectContract.checkPaginationBounds .basicV13 rowCountParams boundsQuery).mapError reprStr)
  have _boundsDerivation : SelectContract.PaginationBoundsValid .basicV13 rowCountParams
      boundsQuery bounds.limitUses bounds.offsetUses := bounds.valid
  SQLean.Tests.assert (bounds.limitUses == [.anonymous 2] && bounds.offsetUses == [.anonymous 3])
    "pagination-only certificate preserves identities without claiming whole-query notation"
  checkContractCase "bounds evidence does not certify aggregate body" "unsupported" [] rowCountParams boundsQuery
  match SelectContract.checkPaginationBounds .basicV13 rowCountParams boundsQuery 0 with
  | .error (.inconclusive _) => pure ()
  | _ => throw (IO.userError "pagination-only zero budget must be inconclusive")
  match SelectContract.checkPaginationBounds .basicV13
      [{ index := 0, type := ⟨.int, []⟩ }] literalQuery with
  | .error (.invalid _) => pure ()
  | _ => throw (IO.userError "pagination-only certificate must validate parameter metadata")
  let scalars ← scalarContractTests
  pure (raw.length + 16 + scalars)

end SQLean.Tests
