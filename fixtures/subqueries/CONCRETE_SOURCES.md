# Uncorrelated expression-subquery source corpus

This population contains **150 unchanged authentic input statements**, split into
50 `EXISTS`, 50 scalar-subquery and 50 scalar `IN`/`NOT IN` witnesses. There are
57, 53 and 51 occurrences respectively of the selected factor in those groups.
The 150 complete SQL inputs are globally distinct after removing token-level
whitespace/comments; no renamed or synthesized variants fill the source counts.
The separate `synthetic.json` contains authored experiments, not scraped SQL.

`extract_subquery_corpus.py --check` reproduces the exact SQL bytes from 44 pinned
source files and checks source/license hashes, complete-input selectors,
declaration context and the preregistered certificate registry. All default
checks use the Python standard library. `--oracle` additionally requires the
existing pinned pglast 7.21 environment (PostgreSQL 17.7 raw grammar) and reproduces
the syntax observations; this is not a PostgreSQL 16 semantic or execution oracle.
Neither mode executes downloaded SQL, source declarations, program code, control
directives, or upstream expected results.

## Fixed populations and certificate scope

- `exists_concrete.jsonl`: DuckDB 18, PostgreSQL 9, Hatchet 5, RisingWave 4,
  Concourse 4, sqlc 3, Materialize 3, SQLite 2 and River 2. The fixed certificate
  population is 22 queries / 23 ordered columns: one closed query and 21 queries
  under explicit declaration-backed catalogs.
- `scalar_concrete.jsonl`: DuckDB 19, SQLite 12, PostgreSQL 7, Materialize 7,
  RisingWave 4 and Hatchet 1. The fixed certificate population is 32 queries /
  37 columns: 24 closed queries and eight declaration-backed queries.
- `in_concrete.jsonl`: DuckDB 15, PostgreSQL 11, Materialize 10, Calcite 8,
  SQLite 4 and RisingWave 2. The fixed certificate population is 24 queries /
  24 columns: 12 closed queries and 12 declaration-backed queries.

The **78 queries / 84 columns** in `source_contracts.json` were registered by
inspection of the original SQL and written field declarations, and independently
reviewed before checker replay. Each entry fixes the exact ID, catalog path,
ordered output names, scalar types, nullability, and collation identity. The
registry is not derived by selecting queries that happen to pass a checker.
Every one of the 150 sources receives checked identity/PostgreSQL rendering;
only registered entries receive the complete static certificate claim.

The other **72** remain explicit rendering-only witnesses. Their original
application/catalog or parameter declarations are not invented. A small number
also use legacy aggregate/custom-call/DISTINCT dependencies. In particular, the
three closed inputs `SELECT 1=(SELECT NULL)`, its CTE variant, and
`SELECT 1 IN (SELECT NULL)` do not receive Valid certificates: a SELECT resolves
its unknown output to TEXT before the outer INTEGER comparison. These exact
upstream inputs are retained as syntax evidence, not called PostgreSQL-valid
expressions. Structurally source-free counts are 1 / 26 / 13, which are deliberately
separate from certificate eligibility.

All selected subqueries are noncorrelated under the finite conservative lexical
screen. The observer records local relation/column names, sequential CTE scope,
external dependencies, and explicit parameter slots. It refuses unresolved or
possibly outer-bound references. Actual source declarations supply column names
where otherwise the screen cannot distinguish local from outer lookup. The
screen is not a general SQL binder or the project's independent typing relation.
Lateral/correlated expressions and other SubLink families are not substituted
for the required three factors.

## Conditional source catalogs

`concrete_sources.json` retains **26 exact CREATE TABLE input declarations**, with
source offsets, SQL hashes, and their written INT/INTEGER or BOOL/BOOLEAN fields.
Eighteen files in `catalogs/` give the caller-asserted snapshots used by the
41 registered table-dependent queries. These snapshots contain only original
field names/types and explicit nullable constraints; setup has not run and no
claim is made that the source deployment currently exposes that catalog.

`sourceProvenance` links each catalog to the retained declarations. The caller's
assumption is that these named relations have precisely those fields, types and
nullability. No table data, effective constraint enforcement, installed locale,
provider, collation OID, or application parameter environment is invented.
The retained Materialize composite PRIMARY KEY is provenance-only: the finite
field reader does not treat an ignored table constraint as evidence of effective
catalog nullability. Its two field-level NOT NULL declarations are recorded
separately; that context serves the conservative scope screen, not a registered
full certificate. PostgreSQL TEMP-table declarations similarly serve only scope
screening for their two selected queries.

Scalar-subquery certificates do not assert at-most-one-row cardinality. Their
outputs remain nullable even when their selected expression is nonnullable;
empty input can return NULL and multiple rows can fail at execution. Several
DuckDB source contexts explicitly change that engine's multirow-subquery setting;
the setting and expected answers remain inert source context and are not adopted
as PostgreSQL behavior. `EXISTS` projection evaluation, SQL NULL versus empty-IN
behavior, and actual source data are also not execution claims of this corpus.

## Input boundaries and origin

The selectors retain complete SQL statements, literal SQLLogicTest input blocks,
literal Tcl SQL statements, whole Go SQL constants/call arguments, and complete
Quidem input statements. Nine RisingWave planner inputs come from literal YAML
`sql: |` blocks; each selected SELECT is an unchanged complete statement within
that block and its preceding table declarations are preserved. Quidem table
results, SQLLogicTest expected results/plans, and YAML expected-output names stay
opaque. A previously considered SELECT tail inside a WITH statement was rejected
and replaced with a complete upstream input before freezing this corpus.

Six PostgreSQL inputs are exact SELECT bodies of actual CREATE VIEW source
statements. Their entire CREATE VIEW container, exact body offset, and prefix
(including one `security_barrier = true` declaration) are retained. These are
embedded input statements, not generated EXPLAIN plans, and the wrapper is never
executed. Four Concourse examples are whole plain/raw query argument tokens at
`QueryRow`/`QueryRowContext` call sites; assembly with runtime variables is excluded.
River template comments remain literal original comments, with no replacement.

The complete repository commits, file SHA256 values, line links, selectors and
license paths are in `concrete_sources.json` and the JSONL records. Pins include:

- [PostgreSQL 16 source](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256), PostgreSQL license.
- [DuckDB source](https://github.com/duckdb/duckdb/tree/917243df252f114d9c448b1d23f8618f0d683769), MIT.
- [Materialize source](https://github.com/MaterializeInc/materialize/tree/726570dba1d2e4d839c707a84a986fb3b3acc5c3), Business Source License 1.1, change date 2030-10-20 and change license Apache-2.0. This source-available material is retained under its own terms, not relicensed. Copied files retain their original Cockroach/PostgreSQL-derived notices.
- [RisingWave source](https://github.com/risingwavelabs/risingwave/tree/7c5bb80f065b52e3eeaab0e0739684772d48aafc), Apache-2.0.
- [SQLite source](https://github.com/sqlite/sqlite/tree/5484850c7a2cd90f2a06b8d4f3453b259aefc1e1), public domain.
- [Calcite source](https://github.com/apache/calcite/tree/83a36ba09be41ce447773feb231716b2b4e71198), Apache-2.0 with retained NOTICE.
- [Hatchet source](https://github.com/hatchet-dev/hatchet/tree/392e7c472221cdab235cca674640e98f904e1ea0) and [sqlc source](https://github.com/sqlc-dev/sqlc/tree/0f1602fe1a4b780336e3e878dde720892fd8578d), MIT.
- [Concourse source](https://github.com/concourse/concourse/tree/98c85dd83cdf8b8c06b57aaa168dc5efd3cbda50), Apache-2.0.
- [River source](https://github.com/riverqueue/river/tree/1354a059d7cbe5790acc7a755a2ab7ac6d2f1ed8), MPL-2.0.

Application-shipping inputs are labelled separately from engine/compiler
regressions. Cross-engine regression origins do not make their expected values
PostgreSQL oracles. Authored native experiments are implemented by the separate
`check_subqueries_cli.py` harness; downloaded statements never enter its native
SQL builders.
