# Unchanged schema-qualified source queries

The corpus contains 50 distinct complete queries: 37 PostgreSQL regressions,
12 sqlc PostgreSQL integration-test queries, and one shipping Hatchet Go SQL
constant. Every query contains a two-component schema-qualified relation
reference. SQL is preserved exactly; no namespace prefix, identifier, alias,
parameter, or expression is removed or rewritten.

The existing upstream pins and licenses are retained:

- [PostgreSQL](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256):
  `f0595c3d839debdb140903621c1b44a4f4d86256`,
  [PostgreSQL license](../extended_types/licenses/postgres-COPYRIGHT.txt).
- [sqlc](https://github.com/sqlc-dev/sqlc/tree/0f1602fe1a4b780336e3e878dde720892fd8578d):
  `0f1602fe1a4b780336e3e878dde720892fd8578d`, MIT.
- [Hatchet](https://github.com/hatchet-dev/hatchet/blob/392e7c472221cdab235cca674640e98f904e1ea0/pkg/repository/sqlcv1/tasks.sql.go):
  `392e7c472221cdab235cca674640e98f904e1ea0`, MIT. The selected
  `ensureTablePartitionsExist` constant is decoded without running Go code.

The manifest binds 26 complete source files, their licenses, exact statement or
constant selectors, and SQL hashes. Existing source snapshots are reused where
available. Statement extraction retains comments inside queries; the application
constant retains its original comment and whitespace.

There are 58 schema-qualified relation references. Nine queries contain explicit
aliases on qualified relations, and four contain quoted components, including
`"S 1"."T 1"` and `"computed_tables"."something"`. Qualified column references
comprise 36 two-component paths and four three-component paths such as
`astoria.slack_feedback.workspace_id`. Seven queries contain parameters; the
corpus records their slot identities but does not invent their types or values.

The finite observer stores `parts`, `quoted`, and `spelling` separately. It checks
decoded raw-parser names against the actual source at UTF-8 byte offsets. Quoted
names containing dots remain single components, and escaped quotes remain part
of the identifier. Comments and whitespace around separator dots are preserved
in the spelling. Relation alias names are recorded without resolving references.
Database-qualified FROM references and column paths longer than three components
are outside this factor. The observer does not model catalog lookup, search_path,
binding, privileges, or output types.

No literal-dot quoted identifier or database-qualified relation occurs in these
50 authentic queries. That source-coverage gap is explicit: separate authored
fixtures test quoted-dot distinctions and the database-qualification boundary.
The discovered DuckDB examples of cross-database references were not substituted
for PostgreSQL namespace evidence.

All 50 queries depend on a real catalog, including `information_schema` and
`pg_catalog` relations. `source_free` is therefore false. They receive
identity/PostgreSQL checked rendering and exact AST round-trip checks. They do
not receive fabricated full static certificates, and source SQL is never
executed. Separate authored `synthetic.json` cases use an explicit catalog and
namespace configuration for independent contract and native PostgreSQL checks.

```sh
python3 scripts/extract_factor_corpus.py --factor qualified_names --check
python3 -m unittest discover -s scripts -p 'test_qualified_name_extraction.py'
```

Optional `--oracle` reproduces syntax metadata with pinned pglast 7.21
(PostgreSQL 17.7). The project's broad grammar replay uses its pinned
PostgreSQL 16 grammar. Temporary discovery probes that removed namespace
prefixes were kept outside the repository; their rewritten SQL is not part of
this corpus or its correctness evidence.
