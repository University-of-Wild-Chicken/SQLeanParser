# Non-LATERAL derived-table source corpus

`concrete.jsonl` contains 50 distinct, unchanged, whole SELECT statements:
47 PostgreSQL engine regressions and three sqlc compiler regressions. They
contain 91 derived sources: 75 at depth one, 12 at depth two, and four at depth
three. Four statements use explicit derived-column alias lists.

The selected FROM subqueries have table aliases and do not use LATERAL.
They exercise source-free projections, base tables, qualified and wildcard
projections, computed columns, aliases, nested joins, ON/USING/NATURAL,
filtering, sorting, limits, and COALESCE. They exclude CTEs, grouping,
aggregates, general function calls, expression subqueries, set operations,
table functions, and row-locking clauses.

Pinned sources and licenses:

- [PostgreSQL REL_16_STABLE](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256):
  commit `f0595c3d839debdb140903621c1b44a4f4d86256`, PostgreSQL License.
- [sqlc](https://github.com/sqlc-dev/sqlc/tree/0f1602fe1a4b780336e3e878dde720892fd8578d):
  commit `0f1602fe1a4b780336e3e878dde720892fd8578d`, MIT.

`concrete_sources.json` pins 10 source files and both license files by SHA-256.
Every selection is one complete SQL statement span. Existing snapshots are
reused; additional files reside under `fixtures/factor_sources/sources`.
Records retain the source SQL, exact line/link, source kind, parameter slots,
and each derived source's alias, ordered column aliases, nesting depth,
and explicit `lateral: false`. No identifiers, literals, parameters, or clauses
are rewritten, and normalized duplicates cannot increase the count.

Four deliberate non-LATERAL correlation errors in the upstream `join.sql`
population were excluded. Whole-row/composite projection examples were also
excluded. The optional raw-parser observation checks each SELECT independently:
qualified column references must name a relation visible in that SELECT,
and a source-free SELECT must contain no column references. A child cannot
borrow its parent's or a sibling's relation name during this screen.

This is a conservative finite syntax screen, **not** catalog-dependent name
resolution or a validity certificate. Unqualified column existence and
ambiguity, relation kinds, output schemas, alias arities, scalar types, and
successful execution still require the actual catalog and environment.
Analyzer-negative inputs are not relabeled as valid by parsing alone.
These concrete queries receive syntax and checked-rendering checks only;
**they are never executed**, and application catalogs or parameter types
are not invented.

Reproduce from local pinned inputs:

```sh
python3 scripts/extract_factor_corpus.py --factor derived_contract --check
python3 -m unittest discover -s scripts -p test_derived_extraction.py
python3 -m unittest discover -s scripts -p test_factor_extraction.py
```

Optional `--oracle` requires `pglast==7.21` and verifies one whole SELECT,
parameter slots, the dependency/scope screen, and exact derived-source
observations. Its raw parser uses PostgreSQL 17.7. The separate PostgreSQL 16
grammar replay also checks all 50 statements. Neither oracle executes SQL.
