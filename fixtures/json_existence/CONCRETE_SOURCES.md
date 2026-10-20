# Unchanged JSONB existence queries

This population contains 50 distinct complete SELECT statements: 27 PostgreSQL
regressions, 14 CockroachDB regressions, eight Materialize regressions, and the
shipping River `jobGetCancelRequested` Go constant. All original SQL bytes are
retained, including the River template comment and numbered parameter. Nothing
is substituted, renamed, or synthesized to reach the count.

The sources reuse these existing pins and license copies:

- [PostgreSQL](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256),
  `f0595c3d839debdb140903621c1b44a4f4d86256`,
  [PostgreSQL license](../extended_types/licenses/postgres-COPYRIGHT.txt).
  The selected files are `src/test/regress/sql/jsonb.sql` and
  `contrib/pg_stat_statements/sql/select.sql`.
- [CockroachDB v22.1.0](https://github.com/cockroachdb/cockroach/blob/5b78463ed2e7106a8477b63fa837564ad02bb510/pkg/sql/logictest/testdata/logic_test/json),
  `5b78463ed2e7106a8477b63fa837564ad02bb510`.
  The original [BSL terms](../factor_sources/licenses/cockroach-v22.1-BSL.txt)
  specify a change date of April 1, 2025 and the
  [Apache 2.0 change license](../factor_sources/licenses/cockroach-v22.1-APACHE.txt).
  The original [license notice](../factor_sources/licenses/cockroach-v22.1-LICENSE)
  remains included.
- [Materialize](https://github.com/MaterializeInc/materialize/blob/726570dba1d2e4d839c707a84a986fb3b3acc5c3/test/sqllogictest/jsonb.slt),
  `726570dba1d2e4d839c707a84a986fb3b3acc5c3`,
  [BSL 1.1](../factor_sources/licenses/materialize-20261020-LICENSE),
  change date October 20, 2030, change license Apache 2.0. This source remains
  source-available under its original terms; it is not relicensed here.
- [River](https://github.com/riverqueue/river/blob/1354a059d7cbe5790acc7a755a2ab7ac6d2f1ed8/riverdriver/riverpgxv5/internal/dbsqlc/river_job.sql.go#L598),
  `1354a059d7cbe5790acc7a755a2ab7ac6d2f1ed8`,
  [MPL 2.0](../external_postgresql/licenses/river-LICENSE.txt).
  The constant is decoded from committed SQLC output without running Go.
  Its `/* TEMPLATE: schema */` comment is retained, with no schema expansion.

The manifest binds five complete input files, their license hashes, complete
statement/constant/query-block selectors, and exact selected-SQL hashes. Existing
PostgreSQL and River snapshots are reused. The two new SQLLogicTest snapshots
retain their comments and notices in full.

There are 56 existence-operator occurrences: 33 `?`, 11 `?|`, and 12 `?&`.
Six queries project two predicates. Forty-four queries have no source tables,
columns, or parameters and explicitly cast their JSONB documents. Two of these
use SQL `NULL::jsonb`, one beneath `NOT`; JSON `null` and NULL array members are
different syntactic observations. The remaining six queries comprise five
PostgreSQL `testjsonb` queries and the River query. Their actual catalog and
binding types are not supplied or inferred.

The finite observer records `source_free` and `json_existence` entries containing
`operator`, `left_form`, `left_cast`, `left_literal_null`, `right_form`, and
`right_cast`. Cast fields describe only casts actually written in the source.
Column and nested-expression types remain unspecified. Operator locations are
checked against the original source using PostgreSQL UTF-8 byte positions.
Malformed literal JSON is screened with Python's JSON decoder, without claiming
PostgreSQL conversion semantics. Source results, output types, and validity are
not inferred by this extraction metadata; any full-certificate registry is a
separate independently reviewed artifact.

The existing finite Cockroach-format reader still selects only `query T` by
default. This factor alone opts into complete `query B` and `query BB` blocks.
Known prefixes are recognized without running test commands; unknown directives
and conditional guards before a selected block are rejected. Expected-result
sections are opaque and are never used as PostgreSQL result oracles. The chosen
Cockroach and Materialize blocks need no conditional guards.

All 50 unchanged statements passed the project's PostgreSQL 16 grammar checker
and identity/PostgreSQL checked rendering. A separate fixed-ID registry in
`Tests.JsonExistenceContract` certifies the 44 literal-only queries with an empty
catalog and binding environment, including their exact 50 Boolean output
positions, six duplicate-label pairs, and two nullable results. The six
catalog-dependent queries retain rendering evidence without fabricated bindings.
The optional pglast observation uses the existing pinned 7.21 / PostgreSQL 17.7
raw parser. These checks do not execute SQL. No downloaded query, test program,
or expected result is executed.

```sh
python3 scripts/extract_factor_corpus.py --factor json_existence --check
python3 -m unittest discover -s scripts -p 'test_json_existence_extraction.py'
```
