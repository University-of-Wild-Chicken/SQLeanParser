import SQLean.SelectContract.Profile
import Tests.Support

namespace SQLean.Tests

/-- Older fixtures register names, scalar types and nullability, without
collation identities. Compare exactly those fields. The collation suites
separately require complete `OutputColumn` equality. -/
def sameOutputTypes (actual expected : List SelectContract.OutputColumn) : Bool :=
  actual.map (fun column => (column.name, column.type)) ==
    expected.map (fun column => (column.name, column.type))

end SQLean.Tests
