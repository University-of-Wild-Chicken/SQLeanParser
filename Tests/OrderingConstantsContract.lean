import SQLean.Assurance
import SQLean.RenderContract.Checker
import SQLean.RenderContract.ValidityPreservation
import Tests.Support

namespace SQLean.Tests
open SelectContract

example : sortSyntax (.unary .neg (.unary .neg (.literal (.int 2)))) = .integer 2 := rfl
example : sortSyntax (.unary .neg (.literal (.int 2147483648))) = .numericConstant := rfl
example : sortSyntax (.unary .pos (.literal (.int 0))) = .expression := rfl
example : sortSyntax (.cast (.literal (.bool true)) ⟨.bool, []⟩) = .expression := rfl
example : ¬ SortExpression .null := by decide
example : ¬ SortExpression (.decimal "1.2") := by decide
example : ¬ SortExpression (.unary .neg (.literal (.int 1))) := by decide
example : SortExpression (.unary .pos (.literal (.int 0))) := by decide

private def orderingColumns : List OutputColumn :=
  [{name := "a", type := ⟨.int32, false⟩}, {name := "b", type := ⟨.int32, false⟩}]

/-- A folded signed ordinal has an independent rule derivation, with no
expression parameter occurrences or ordinary scalar-sort typing premise. -/
private theorem signedOrdinal_valid : SortValid .basicV32 [] .empty [] orderingColumns false
    (.unary .neg (.unary .neg (.literal (.int 2)))) [] :=
  .ordinal rfl (by decide) (by decide) (by decide)

example : SortValid .basicV32 [] .empty [] orderingColumns false
    (RenderContract.translateExpr (.unary .neg (.unary .neg (.literal (.int 2))))) [] :=
  RenderContract.sort_valid_translated signedOrdinal_valid

private def orderingCases : List (String × String) := [
  ("SELECT 10 AS a, 20 AS b ORDER BY 1", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY 2", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY (1)", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY ((2))", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY -(-1)", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY -(-2)", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY - - 1", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY -(-(-(-2)))", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY +0", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY +2", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY +3", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY +(0)", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY +(NULL)", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY -(+1)", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY +(-1)", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY -(1+1)", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY -CAST(1 AS BIGINT)", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY CAST(TRUE AS BOOLEAN)", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY CAST(NULL AS TEXT)", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY CAST('x' AS TEXT)", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY CAST(1.5 AS NUMERIC)", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY 1+1", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY CASE WHEN TRUE THEN 1 ELSE 2 END", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY COALESCE(NULL,1)", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY a", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY b", "valid"),
  ("SELECT 10 AS a, 20 AS b ORDER BY 0", "order_position"),
  ("SELECT 10 AS a, 20 AS b ORDER BY -0", "order_position"),
  ("SELECT 10 AS a, 20 AS b ORDER BY -1", "order_position"),
  ("SELECT 10 AS a, 20 AS b ORDER BY 3", "order_position"),
  ("SELECT 10 AS a, 20 AS b ORDER BY -3", "order_position"),
  ("SELECT 10 AS a, 20 AS b ORDER BY -(-3)", "order_position"),
  ("SELECT 10 AS a, 20 AS b ORDER BY 2147483647", "order_position"),
  ("SELECT 10 AS a, 20 AS b ORDER BY -2147483647", "order_position"),
  ("SELECT 10 AS a, 20 AS b ORDER BY -(-2147483647)", "order_position"),
  ("SELECT 10 AS a, 20 AS b ORDER BY TRUE", "order_constant"),
  ("SELECT 10 AS a, 20 AS b ORDER BY FALSE", "order_constant"),
  ("SELECT 10 AS a, 20 AS b ORDER BY NULL", "order_constant"),
  ("SELECT 10 AS a, 20 AS b ORDER BY 'x'", "order_constant"),
  ("SELECT 10 AS a, 20 AS b ORDER BY ''", "order_constant"),
  ("SELECT 10 AS a, 20 AS b ORDER BY 1.0", "order_constant"),
  ("SELECT 10 AS a, 20 AS b ORDER BY -1.0", "order_constant"),
  ("SELECT 10 AS a, 20 AS b ORDER BY -(-1.0)", "order_constant"),
  ("SELECT 10 AS a, 20 AS b ORDER BY 1e0", "order_constant"),
  ("SELECT 10 AS a, 20 AS b ORDER BY -1e0", "order_constant"),
  ("SELECT 10 AS a, 20 AS b ORDER BY 2147483648", "order_constant"),
  ("SELECT 10 AS a, 20 AS b ORDER BY -2147483648", "order_constant"),
  ("SELECT 10 AS a, 20 AS b ORDER BY -(-2147483648)", "order_constant"),
  ("SELECT 10 AS a, 20 AS b ORDER BY 9223372036854775807", "order_constant"),
  ("SELECT 10 AS a, 20 AS b ORDER BY 9223372036854775808", "order_constant"),
  ("SELECT 10 AS a, 20 AS b ORDER BY -9223372036854775808", "order_constant") ]

def orderingConstantsContractTests : IO Nat := do
  for (sql, expected) in orderingCases do
    let query ← expectOk sql (Advanced.parseQuery sql)
    match SelectContract.checkQuery .basicV32 [] [] query with
    | .ok certificate =>
        SQLean.Tests.assert (expected == "valid" && certificate.output == orderingColumns)
          s!"unexpected ORDER BY constant certificate: {sql}"
        have _preserved := RenderContract.translateParameters_valid certificate.valid
        let identity ← expectOk sql ((RenderContract.check .identityV01 query).mapError reprStr)
        let postgres ← expectOk sql ((RenderContract.check .postgres16V01 query).mapError reprStr)
        have _identity := identity.roundTrip
        have _postgres := postgres.roundTrip
    | .error (.invalid diagnostic) =>
        SQLean.Tests.assert (diagnostic.code == expected)
          s!"wrong SQL92 constant classification: {sql}: {diagnostic.code}"
    | other => throw (IO.userError s!"unexpected ORDER BY outcome: {sql}: {reprStr (other.map (fun _ => ()))}")
  let query ← expectOk "parameter ordering" (Advanced.parseQuery
    "SELECT ? AS a, ? AS b ORDER BY -? + ?")
  let params ← expectOk "parameter types" (Assurance.parseContractParameterTypes "int,int,int,int")
  let certificate ← expectOk "parameter sort" ((SelectContract.checkQuery .basicV32 [] params query).mapError reprStr)
  have _preserved := RenderContract.translateParameters_valid certificate.valid
  SQLean.Tests.assert (Advanced.queryParameters 1024 query ==
    [.anonymous 1,.anonymous 2,.anonymous 3,.anonymous 4])
    "ordinary sort expressions must preserve parameter occurrences"
  pure (orderingCases.length + 1)

end SQLean.Tests
