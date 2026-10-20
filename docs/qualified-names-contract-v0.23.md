# Schema-qualified relation names: v0.23

`sqlean-basic-select-v0.23` adds exact two-component relation names and
three-component column or wildcard references. `From.table`, `Expr.column`,
and `SelectItem.all` retain their existing arguments and append an optional
schema component. The existing unqualified constructor applications remain
usable. Names are decoded identifier components: `"schema.with.dot".t`,
`schema."table.with.dot"`, and `"schema.table"` are different identities.
The lexer retains PostgreSQL's existing unquoted case normalization; the
renderer quotes each component separately.

Catalog records append `schema : Option Name` and `exposeUnqualified : Bool`.
The full relation identity is the pair of schema and table components.
Qualified lookup selects that exact identity regardless of exposure.
Unqualified lookup selects the uniquely exposed entry with that basename.
Both spellings therefore reach the same relation identity and exact column
metadata. This is caller-supplied, pre-resolved visibility metadata; it is
not an implementation of PostgreSQL's `search_path` algorithm. The caller
must supply a faithful snapshot of the connection's resolution context.
Uniqueness checks alone do not establish that an actual session search path,
role, privileges, temporary namespace, or concurrent catalog state induces
the supplied mapping.

For JSON, an omitted schema preserves legacy behavior and defaults
`exposeUnqualified` to true. A schema-bearing entry defaults it to false
unless the caller explicitly sets it. Direct Lean catalog records retain
the true default for compatibility; callers constructing schema-aware
metadata must select exposure deliberately. Catalog well-formedness checks
full-key uniqueness and exposed-basename uniqueness separately. It also
forbids an incomplete legacy schema-less entry from sharing its basename
with a schema-qualified entry. Such metadata could double-register the
same object and cannot establish distinct identities.

Each `Scope` now contains an ordered list of relation namespaces, separately
from the exposed row used by unqualified columns and `*`. A namespace
records its visible name, base identity or derived origin, explicit-alias
status, ordered columns, and outer-join null extension. Qualified lookup
selects a unique namespace before looking for its column. Thus two
unaliased tables `s1.t` and `s2.t` can coexist, but `t.only_left` is ambiguous
even if only the first table contains that column. Schema-qualified
references can select either table. An explicit alias hides the original
schema path even when the alias repeats the original basename.
An optional base-table column alias list renames a positional prefix and
preserves the remaining labels, exact types, physical origin, and column
order. Duplicate output labels are allowed; a reference that matches more
than one renamed column is ambiguous. Excess or empty aliases are rejected.

Join compatibility follows the corresponding PostgreSQL distinction:
equal visible names are permitted for distinct unaliased base identities,
but explicit aliases and derived aliases must not collide. USING and
NATURAL continue to merge only the exposed row, preserving the separate
relation namespaces and each original qualified wildcard order and type.
Outer joins extend both column nullability and the relation's locking
metadata. Derived aliases expose only their certified output, with no
invented schema identity.

Explicit row-lock OF targets use a different rule from column references.
PostgreSQL selects the first matching visible relation name in range-table
order. The contract models that order exactly, including same-basename
tables from different schemas. It then checks that the selected relation
is a non-null-extended base relation. An omitted OF list selects every
visible relation. Propagation through a selected derived relation remains
Unsupported. Schema-qualified OF targets remain rejected by the typed
parser, matching PostgreSQL's requirement for unqualified OF names.
The pinned parser implementations describe
[namespace matching and conflicts](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/backend/parser/parse_relation.c)
and [ordered locking-target selection](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/backend/parser/analyze.c).

An absent qualified scalar column is not automatically a native SQL error:
PostgreSQL may interpret it as a function applied to the relation's whole
row. That notation, and bare relation-name whole-row projection, remain
Unsupported because this profile has no composite-row typing environment.
An unqualified `ctid`, `tableoid`, `xmin`, `xmax`, `cmin`, or `cmax` is also
Unsupported when a visible base namespace would supply an implicit system
column. Such a column can make a same-named derived output ambiguous;
ordinary output metadata alone cannot settle the reference. Qualified
declared columns, derived-only outputs, and table-column aliases that
replace a system-column name within their namespace remain available.
Undefined or ambiguous relation namespaces and duplicate actual column
matches remain Invalid. A qualified reference requiring schema provenance
that a legacy entry does not contain is Unsupported rather than guessed.
The `pg_temp` schema alias is also explicitly Unsupported; physical schema
identities and schema-alias resolution must not be conflated.

Database-qualified relation paths are deferred until the environment
records the current database explicitly. The broader PostgreSQL grammar
interface retains its separate coverage. Schema creation, dynamic search
paths, role expansion, namespace privileges, system-column lookup,
inheritance, and concurrent catalog changes are not proved by this
increment. Qualified catalog-dependent authentic queries do not acquire
invented metadata merely because they parse.

The independent source and query judgments carry exact namespace identity
and resolution evidence. Parameter traversal is unchanged: schema parts
are names, not parameter-bearing expressions. General translation preserves
the exact namespace scope, merged output, row-lock selections, types,
nullability, and complete lexical parameter order. The checked renderer
retains each normalized component and its boundary. The older coarse
schema checker fails closed on schema-aware metadata instead of flattening
names into dotted strings or erasing their identity.

Fifty authored queries receive full query certificates with explicit
catalog and binding assumptions. Fifty unchanged authentic queries from
PostgreSQL, sqlc, and Hatchet receive syntax and rendering certificates
only; every source is catalog-dependent. The 140 focused checks additionally cover
quoted dots and case, reserved suffix identifiers, alias hiding, exposed
and hidden entries, duplicate basenames, namespace-before-column errors,
qualified merged joins, ordered OF targets, incomplete legacy metadata,
whole-row coverage boundaries, and malformed hand-built references.
The native harness checks 200 bound source/canonical row observations across
empty and populated tables, 166 ordered column descriptors, 25 analysis and
planning SQLSTATE boundaries, seven `pg_table_is_visible` premises, and eight
two-session observations of the first matching OF target. Its system-name
boundaries include PostgreSQL's difference between comma FROM and explicit
CROSS JOIN; the static checker conservatively excludes implicit system-name
resolution in either form because the typed parser normalizes comma sources.
The 50 SQLite checks use matching `?NNN` parameter identities: 43 report the
explicit schema-qualification coverage boundary, while seven encounter earlier
input restrictions (two unquoted KEY alias lists, one SQL-standard SUBSTRING,
and four row-locking clauses). None receives a SQLite certificate.
Native observations supplement these structural and static guarantees;
they do not establish full PostgreSQL evaluation or cross-dialect
equivalence.

The complete Lean build and test suites pass, including 153 focused parser and
renderer checks. All 832 Python tests pass. The affected prior JOIN, USING/NATURAL, derived-source and
locking native harnesses also pass on PostgreSQL 16.15 and SQLite 3.45.1.
The original industrial replay accepts 248 of 276 statements; the remaining
28 are retained in the [milestone audit](corpus/qualified-names-v0.23/README.md).

The trust audit checks 210 Lean source files and the compiled declaration
closures, rejecting custom axioms, proof placeholders and native proof
shortcuts. Its main closure contains 24,123 project declarations, including
12,933 theorems. The admitted foundations remain `propext`, `Classical.choice`
and `Quot.sound`; there is no claim of an axiom-free foundational system.
The verified input digest is
`e3728181c7a46efb17a3856bd1d4ab86af4257b4046d0530c37c883db887ffd3`
at parent checkpoint `81ffa44e2b95c108f26f8a552853c2eef1adff7e`.
This is an incremental development milestone. The full PostgreSQL release
gate remains unmet.
