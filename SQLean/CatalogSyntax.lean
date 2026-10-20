import SQLean.AdvancedSyntax

/-! Immutable catalog representation shared by executable checks and independent
specifications. This module contains no validation or inference procedures. -/
namespace SQLean.Advanced

structure CatalogTable where
  name : Name
  columns : List Column
  uniqueKeys : List (List Name) := []
  primaryKey : List Name := []
  namedKeys : List (Name × List Name) := []
  deriving Repr, BEq, Inhabited

abbrev Catalog := List CatalogTable

end SQLean.Advanced
