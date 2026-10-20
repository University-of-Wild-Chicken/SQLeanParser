# Unchanged SQL context-name queries

The population contains 50 complete original SELECT statements: 32 PostgreSQL
regressions, seven pgweb shipping queries, four River shipping queries, four
DuckDB regressions, two Materialize regressions, and one RisingWave regression.
All SQL bytes are retained. The source counts do not include case, whitespace,
or trailing-semicolon-only variants.

The source revisions and retained license copies are:

- [PostgreSQL](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256),
  `f0595c3d839debdb140903621c1b44a4f4d86256`,
  [PostgreSQL license](../extended_types/licenses/postgres-COPYRIGHT.txt).
- [pgweb](https://github.com/sosedoff/pgweb/tree/e4858a16d8e032730055289596ea9059a91bca64),
  `e4858a16d8e032730055289596ea9059a91bca64`,
  [MIT license](../factor_sources/licenses/pgweb-LICENSE).
  Two embedded `.sql` files are selected in full. Five complete plain Go strings
  come from the activity-query map and `QueryRowContext` call. The activity map
  includes explicitly versioned PostgreSQL 9.1, 9.2, and 9.6 branches; their
  current PostgreSQL 16 catalog compatibility is not asserted.
- [River](https://github.com/riverqueue/river/tree/1354a059d7cbe5790acc7a755a2ab7ac6d2f1ed8),
  `1354a059d7cbe5790acc7a755a2ab7ac6d2f1ed8`,
  [MPL 2.0](../external_postgresql/licenses/river-LICENSE.txt).
  Three committed SQLC constants retain their original placeholders and template
  comments. One complete inline `QueryRow` literal is selected unchanged.
- [DuckDB](https://github.com/duckdb/duckdb/tree/917243df252f114d9c448b1d23f8618f0d683769),
  `917243df252f114d9c448b1d23f8618f0d683769`,
  [MIT license](../factor_sources/licenses/duckdb-LICENSE).
- [Materialize](https://github.com/MaterializeInc/materialize/tree/726570dba1d2e4d839c707a84a986fb3b3acc5c3),
  `726570dba1d2e4d839c707a84a986fb3b3acc5c3`,
  [BSL 1.1](../factor_sources/licenses/materialize-20261020-LICENSE).
  The original source-available terms remain intact: change date October 20,
  2030, change license Apache 2.0. These excerpts are not relicensed here.
- [RisingWave](https://github.com/risingwavelabs/risingwave/tree/7c5bb80f065b52e3eeaab0e0739684772d48aafc),
  `7c5bb80f065b52e3eeaab0e0739684772d48aafc`,
  [Apache 2.0 license](../factor_sources/licenses/risingwave-LICENSE).

The manifest binds each full source file, license, selector and selected query
to a content hash. The finite Go reader checks a complete unescaped string token
in the pinned map-value or `QueryRow`/`QueryRowContext(ctx, query)` positions. It
rejects concatenated expressions and does not evaluate Go. The whole-file reader
retains the full embedded SQL file. Existing SQLLogicTest readers retain complete
literal query blocks without running setup commands or conditional directives.
Upstream expected-result sections remain opaque and supply no PostgreSQL oracle.

There are 63 context-name occurrences: 32 `CURRENT_USER`, seven `SESSION_USER`,
two each of `USER`, `CURRENT_ROLE`, `CURRENT_CATALOG`, and bare `CURRENT_SCHEMA`,
11 `current_database()` calls, and five `current_schema()` calls. This authentic
population has no `SYSTEM_USER` occurrence; authored tests cover that form.
Unrelated temporal value keywords are outside this factor.

The observer records the written name, keyword-versus-call form, and PostgreSQL
UTF-8 byte location. It validates the spelling against unquoted source code,
keeping string literals, quoted identifiers and comments separate. PostgreSQL's
special `SYSTEM_USER` representation is recognized as a SQL-syntax
`pg_catalog.system_user` call, not a `SQLValueFunction`. No context value,
search path, current user, catalog, output type or binding type is inferred by
the source observer.

Twenty-two queries are structurally source-free. A separate fixed-ID registry in
`Tests.ContextValuesContract` certifies 13 selected queries with 15 exact ordered
output positions. The other nine source-free queries use additional helpers
outside that registry; 28 queries depend on an external catalog or bindings.
Those 37 retain checked rendering evidence without fabricated environments.
All 50 original queries pass PostgreSQL 16 grammar and identity/PostgreSQL
checked rendering. The optional pglast observation uses the separately pinned
7.21 / PostgreSQL 17.7 raw parser.

No downloaded query or source program is executed. Native context-state
observations use separate authored fixtures.

```sh
python3 scripts/extract_factor_corpus.py --factor context_values --check
python3 -m unittest discover -s scripts -p 'test_context_values_extraction.py'
```
