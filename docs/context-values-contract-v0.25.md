# Context values and the exact NAME type: v0.25

The closed profile `sqlean-basic-select-v0.25` adds the seven bare PostgreSQL
context forms `CURRENT_SCHEMA`, `CURRENT_CATALOG`, `CURRENT_USER`, `USER`,
`CURRENT_ROLE`, `SESSION_USER`, and `SYSTEM_USER`. It also admits the six fixed
catalog functions `current_schema()`, `current_database()`,
`current_schemas(BOOLEAN)`, `current_user()`, `session_user()`, and `system_user()`.
Reserved function names require their native quoted or qualified call spelling
where PostgreSQL requires it. Bare forms and calls remain different AST nodes;
for example, `CURRENT_CATALOG` and `current_database()` have different output
labels. No context value is reinterpreted as an ordinary column.

This is a further bounded SELECT contract, not complete PostgreSQL validity.
Temporal SQL value forms such as `CURRENT_TIMESTAMP`, named function arguments,
user-defined functions, and other unmodeled query dependencies retain their
existing explicit boundaries. There is no release claim.

## Exact type and normative environment

`Advanced.TypeName.name` and `SelectContract.ScalarType.name` denote PostgreSQL
`NAME`, independently of `TEXT`. `NAME` has no declaration modifiers. Scalar
casts, parameters, catalog columns, ordered projections, and arrays preserve
this exact identity. Repeated declared array dimensions normalize to one
concrete array type, as for the previously supported scalar types.

The six native string casts are directional: `NAME` converts implicitly to
`TEXT`, but its casts to `CHAR` and `VARCHAR` require assignment or explicit
context. `TEXT`, `CHAR`, and `VARCHAR` all convert implicitly to `NAME`. Explicit
casts retain PostgreSQL's existing string I/O conversion rules. Value conversion,
encoding, and the native 63-byte identifier storage/truncation boundary are
execution obligations, not static nonfailure claims.

The normative scalar operator inventory now includes three additional exact
input pairs, `NAME/NAME`, `NAME/TEXT`, and `TEXT/NAME`, for each of the six
comparison operators. The selected declarations also support the existing
quantified-array and direct-row comparison rules. `NAME[]` equality and array
predicates require matching array element identities; they do not silently
promote a `NAME[]/TEXT[]` pair. Common-type contexts such as `CASE`, `COALESCE`,
array constructors, and array concatenation use their separate directional
coercion rules: a first `NAME` and subsequent `TEXT` can keep `NAME`, whereas a
first `TEXT` remains `TEXT`.

The eight native NAME-left LIKE/ILIKE/regular-expression declarations preserve
the NAME-specific operator family. Existing CHAR and TEXT pattern families
remain distinct. Concatenation and ordinary string calls may convert NAME to
TEXT through their own selected signatures. The previously covered function name
`length` gains its native `length(BYTEA, NAME) -> INTEGER` overload. The fixed
ordinary-function inventory therefore grows from 84 to 91 declarations.

The contract assumes the fixed PostgreSQL 16 built-in function/operator/type
environment. It does not model shadowing by application-defined routines or a
custom collation calculus. NAME has native C collation; conversions and mixed
expressions may retain it. The certificate proves the displayed type and
conservative SQL nullability, not collation-independent comparison values.

## Context and nullability rules

`CURRENT_SCHEMA` and `current_schema()` produce nullable NAME: a search path
without an existing accessible schema can produce SQL NULL. `SYSTEM_USER` and
its catalog function produce nullable TEXT: authentication methods without an
external identity can produce SQL NULL. The other five bare forms, and
`current_database()`, `current_user()`, and `session_user()`, produce nonnullable
NAME. `current_schemas(BOOLEAN)` produces NAME[] and propagates the Boolean
argument's SQL NULL; a successful non-NULL argument may produce an empty array.

The exact value depends on the native session. `CURRENT_USER`, `USER`, and
`CURRENT_ROLE` follow the effective user; `SESSION_USER` follows the session
identity. The independent rule does not infer any of these values from the
relation catalog's pre-resolved unqualified visibility metadata. It also does
not manufacture a `search_path` implementation from that metadata. Native
session settings and authentication are separate assumptions for execution.

The new `ExprValid.contextValue` constructor has no parameter occurrences and
returns the closed `contextValueType`. `outputLabel` assigns the native strong
label for each distinct form, including `user`, `current_role`, and
`current_catalog`. Casts and CASE's existing label inheritance preserve those
strong labels. Ordinary calls use their existing declaration judgment, with an
explicit nullable result policy for the two nullable zero-argument functions.

## Proof and rendering guarantees

The checker constructs an independent `ExprValid` derivation for each admitted
context expression. The public query certificate remains indexed by the exact
profile, catalog, parameter declarations, and original AST. Type compatibility
and SQL NULL flags are checked without executing the query. Unknown catalog or
session helper calls remain Unsupported; invalid admitted signatures remain
Invalid; exhausted resources remain Inconclusive.

Bare forms introduce no placeholder occurrences. All existing compound
expression traversal and query-wide parameter-order rules remain in force.
The general parameter-translation validity theorem is extended to the new
constructor. Identity rendering certifies parsing back to the exact AST;
PostgreSQL rendering certifies parsing back to the parameter-translated AST.
The unconditional translation-idempotence and PostgreSQL serialization
relations remain proved over the finite AST. SQLite rendering explicitly
refuses the new context nodes and NAME declarations; no cross-dialect session
semantics are asserted.

## Registered evidence

`Tests.ContextValuesContract` currently passes 384 focused checks, 50 authored
full-query certificates, and 13 fixed original-source full-query certificates.
The original-source registry contains 15 ordered output columns. All 50 authentic
statements receive identity and PostgreSQL rendering certificates. The other
nine structurally source-free queries call unmodeled helpers, and 28 queries
depend on external catalogs; they receive rendering evidence only. Eligibility
and exact expected outputs are fixed before checking, not selected by success.
No original-source SQL is executed and no application catalog or parameter types
are invented for that population.

The authored corpus and the six-function, 26-operator, and six-cast inventories
live under `fixtures/context_values/`. Lean checks link the complete registered
inventories to the normative selected signatures, including NAME array equality.
The preexisting 192-comparison and 19-array-element fixtures remain explicit
baseline subsets; the new inventory supplies the added NAME cases. The combined
ordinary-function fixture contains exactly the 91 normative declarations.
Native catalog checks and authored session/value/descriptor probes are separate
external evidence, not axioms used by the Lean derivations.

The renderer adds 185 focused checks; the dispatcher suite passes 49. Affected
regression suites pass 100 scalar-form cases, 457 quantified cases, 274 row
comparison cases, 1,576 array-predicate cases, and 333 pattern cases. These counts
record the targeted run; the project-wide build, native integration, and compiled
trust audit are registered separately by the integration workflow.

The native harness observes 100 values/types, 100 SQL NULL flags, 136 exact
result descriptors, eight expected runtime errors, 58 catalog/B-tree facts
and fifteen analysis outcomes. Its separate session-state checks execute ten
source/canonical SELECTs with 110 value fields across explicit and empty
search paths, SET ROLE, SET SESSION AUTHORIZATION and restored identity.
Two private roles exist only inside a rolled-back transaction; restoration
and their absence are checked. These state checks require the authenticated
superuser for a caller-supplied DSN; the local private cluster supplies that
test environment. They do not change existing roles.

All fifty authored SQLite attempts have registered outcomes: 29 context-value
exclusions, nine scalar-function exclusions, one NAME type exclusion, one
ILIKE exclusion and ten earlier input-parser boundaries. No cross-dialect
context translation is claimed.

The [industrial replay](corpus/context-values-v0.25/README.md) accepts 253 of
276 source statements. Its general SQL-value watchlist still flags River's
`columnExists` by feature presence; a supplementary PostgreSQL raw-AST
observation confirms CURRENT_SCHEMA remains a SQLValueFunction, rather than
a column reference, through canonical rendering.

## Primary references

- [PostgreSQL 16 session information functions](https://www.postgresql.org/docs/16/functions-info.html)
- [PostgreSQL 16 identifier syntax](https://www.postgresql.org/docs/16/sql-syntax-lexical.html)
- [PostgreSQL 16 type resolution for CASE and related constructs](https://www.postgresql.org/docs/16/typeconv-union-case.html)
- Pinned PostgreSQL 16 `pg_type.dat`, `pg_cast.dat`, `pg_operator.dat`, and
  `pg_proc.dat`, with the native catalog identity checks in this factor's harness.
