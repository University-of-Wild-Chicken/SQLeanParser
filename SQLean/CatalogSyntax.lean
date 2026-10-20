import SQLean.AdvancedSyntax
import SQLean.CollationSyntax

/-! Immutable catalog representation shared by executable checks and independent
specifications. This module contains no validation or inference procedures. -/
namespace SQLean.Advanced

/-- A schema-less key is a legacy, externally resolved relation identity.
It is never silently identified with a schema-qualified object. -/
structure RelationIdentity where
  schema : Option Name := none
  name : Name
  deriving Repr, BEq, DecidableEq, Inhabited

structure CatalogTable where
  name : Name
  columns : List Column
  uniqueKeys : List (List Name) := []
  primaryKey : List Name := []
  namedKeys : List (Name × List Name) := []
  schema : Option Name := none
  exposeUnqualified : Bool := true
  /-- Omission is a caller assertion of the native type-default collation.
  This sidecar does not change the shared DDL column syntax. -/
  columnCollations : List (Name × CollationId) := []
  deriving Repr, BEq, Inhabited

def CatalogTable.identity (table : CatalogTable) : RelationIdentity :=
  ⟨table.schema, table.name⟩

/-- Visibility is caller-supplied resolution metadata, not a search-path
implementation. Explicit schema references ignore unqualified visibility. -/
def CatalogTable.matchesReference (table : CatalogTable) (name : Name)
    (schema : Option Name := none) : Bool :=
  table.name == name && match schema with
    | none => table.exposeUnqualified
    | some schema => table.schema == some schema

abbrev Catalog := List CatalogTable

def Catalog.schemaAware (catalog : Catalog) : Bool :=
  catalog.any (fun table =>
    table.schema.isSome || !table.exposeUnqualified || !table.columnCollations.isEmpty)

end SQLean.Advanced
