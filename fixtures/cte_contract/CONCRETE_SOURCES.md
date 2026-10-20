# Unchanged nonrecursive SELECT CTE sources

This fixed population contains 50 complete, unchanged queries: seven PostgreSQL
regression statements, eight SQLC compiler tests, 14 Materialize engine tests,
12 DuckDB engine tests, seven SQLite engine tests, and two shipping Hatchet
application constants. The exact source files, selectors, commits, licenses,
SQL hashes, and source links are recorded in `concrete_sources.json`.

The population exercises ordinary SELECT-only CTE definitions, sequential
visibility, repeated references, joins, nested WITH scopes, shadowing, explicit
CTE column names, partial relation column aliases, qualified external
relations, ordering and pagination, and an unused definition. It includes
78 definitions and 130 relation occurrences: 75 resolve lexically to those
definitions and 55 are external relation occurrences. Five definitions shadow
a visible outer name; 14 declare column aliases. No selected statement needs
recursive or materialized CTEs, modifying CTE bodies, VALUES, set operations,
grouping, aggregates, scalar subqueries, table functions, or windows.

The existing repository pins and licenses are reused:

- [PostgreSQL](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256),
  PostgreSQL license.
- [SQLC](https://github.com/sqlc-dev/sqlc/tree/0f1602fe1a4b780336e3e878dde720892fd8578d),
  MIT.
- [Materialize](https://github.com/MaterializeInc/materialize/tree/726570dba1d2e4d839c707a84a986fb3b3acc5c3),
  Business Source License 1.1, change date 2030-10-20 and change license
  Apache-2.0. These original source-available terms remain intact.
- [DuckDB](https://github.com/duckdb/duckdb/tree/917243df252f114d9c448b1d23f8618f0d683769),
  MIT.
- [SQLite](https://github.com/sqlite/sqlite/tree/5484850c7a2cd90f2a06b8d4f3453b259aefc1e1),
  public domain.
- [Hatchet](https://github.com/hatchet-dev/hatchet/tree/392e7c472221cdab235cca674640e98f904e1ea0),
  MIT. Its generated SQLC constants `ReadDAGByExternalID` and `LookUpTraceId`
  are real application queries. Their unspecified parameter types and catalog
  bindings remain unspecified here.

SQL statement spans, SQLite literal Tcl blocks, and complete Go constants
reuse the existing readers. DuckDB uses an explicit selected-prefix bound:
all records through the selected query must be recognized, while later test
directives are outside the selection scope. The strict whole-file reader
remains the default for previous factors. Materialize's CTE-specific prefix
reader admits the recorded I/II/BB headers and unselected `statement count N`
records. Four selected inputs retain literal `onlyif cockroach` metadata.
These conditions and counts are provenance, never instructions to run a test
or claims about PostgreSQL values. Expected-result sections remain opaque.

The finite raw-AST observer records definition names, declared column aliases,
UTF-8 byte positions, nesting depth and shadowing. It binds each relation
occurrence to the byte position of a visible CTE definition, or explicitly
marks it external. Definitions become visible sequentially after their bodies;
a qualified relation remains external even if its final name matches a CTE.
This observer does not resolve columns, infer data types, consult a catalog,
or establish semantic validity.

Exactly 13 closed queries were selected for full certificates before running
the checker. `source_contracts.json` preregisters their 21 ordered output
positions: 15 INT32, two TEXT, and four BOOL, all nonnullable. Names include
duplicate `x`/`y` and `v` projections, explicit aliases, and `?column?`.
The JSON registry is checked against a separately declared Lean registry.
The other 37 queries receive checked identity/PostgreSQL rendering without
invented application catalogs or bindings. `source_free` describes lexical
relation/parameter dependencies; it is not used to discover successful
certificate cases.

Source SQL, SQLC code, Tcl programs, and test control directives are never
executed. Native PostgreSQL and SQLite observations use separately authored
fixtures. Upstream expected values are not PostgreSQL oracles. In particular,
the source collection excludes SQLite forward-reference examples, DuckDB
SELECT-alias reuse, an overlong PostgreSQL CTE column list, and a DuckDB
NULL-text/temporal comparison rather than silently claiming cross-dialect
validity for those cases.

```sh
python3 scripts/extract_factor_corpus.py --factor cte_contract --check
python3 -m unittest discover -s scripts -p 'test_cte_extraction.py'
```

Optional `--oracle` recomputes the observations using pinned pglast 7.21.
Offline reproduction uses the retained sources, standard-library readers,
selectors and hashes, without network access or source execution.
