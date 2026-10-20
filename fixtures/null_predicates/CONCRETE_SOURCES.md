# Unchanged postfix and row null-predicate sources

This fixed population contains 50 unchanged SELECT inputs exercising
`ISNULL`, `NOTNULL`, or a direct row's `IS NULL` / `IS NOT NULL`. An existing
ordinary scalar `IS NULL` expression alone is not a factor witness. The
60 observed predicates comprise 18 `ISNULL`, 11 `NOTNULL`, 19 row `IS NULL`,
and 12 row `IS NOT NULL`. They include an empty row, two-, three-, and
four-field rows, nested postfix predicates, Boolean precedence, filters,
outer joins, and casts around postfix predicates.

The population is 22 H2, 10 SQLite, three Materialize, three DuckDB, two
PostgreSQL, two Turso, five SQLGlot, one sqlparser-rs, one JSqlParser, and one
Calcite input. Engine regressions and parser regressions are labeled
separately. Neither a source project's dialect nor its expected result is a
claim about PostgreSQL behavior.

`concrete_sources.json` pins every complete source file, source selector,
original SQL hash, source URL, license, and notice:

- [PostgreSQL](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256),
  PostgreSQL license.
- [SQLite](https://github.com/sqlite/sqlite/tree/5484850c7a2cd90f2a06b8d4f3453b259aefc1e1),
  public domain. The existing finite Tcl reader selects literal SQL inputs.
- [Materialize](https://github.com/MaterializeInc/materialize/tree/726570dba1d2e4d839c707a84a986fb3b3acc5c3),
  Business Source License 1.1, change date 2030-10-20 and change license
  Apache-2.0. Original source-available terms remain intact.
- [DuckDB](https://github.com/duckdb/duckdb/tree/917243df252f114d9c448b1d23f8618f0d683769), MIT.
- [H2](https://github.com/h2database/h2database/tree/03bdf4d8b68d4de13a163830821f66ab11acfc1f),
  MPL-2.0 or EPL-1.0; both alternatives are retained in its license file.
- [Turso](https://github.com/tursodatabase/turso/tree/9a80037f68973871b16fc228f66b92679f9bc9ac),
  MIT; LICENSE and NOTICE retained.
- [SQLGlot](https://github.com/tobymao/sqlglot/tree/68cd4a2d8f766132e338721df8676e0b42d6b7ca), MIT.
- [sqlparser-rs](https://github.com/apache/datafusion-sqlparser-rs/tree/3330dc9e7ca73930a32d069d4c0338dea470b40f),
  Apache-2.0; LICENSE and NOTICE retained.
- [JSqlParser](https://github.com/JSQLParser/JSqlParser/tree/f6ac2571e6e9777d6a5ee942a4ea53cd91153e4d),
  Apache-2.0 or LGPL-2.1; both license alternatives retained.
- [Calcite](https://github.com/apache/calcite/tree/83a36ba09be41ce447773feb231716b2b4e71198),
  Apache-2.0; LICENSE and NOTICE retained.

The new finite reader selects six kinds of input without executing their host
formats. H2 selections are complete input lines; six records select the exact
complete `SELECT ...;` body of an actual `EXPLAIN SELECT ...;` input. Both
wrapper bytes and body offsets are preserved as provenance. Expected plan
output lines beginning `>` never supply SQL. Other H2 inputs retain the
whole SELECT line. Turso selections retain complete literal `test isnull` or
`test notnull` bodies. Python selections are complete plain string tokens in
the first argument of `validate_identity`; Rust selections are the first
plain literal of `verified_only_select_with_canonical`; Java selections are
the exact `String sqlStr = "...";` input assignment. The Calcite input is
bounded by its registered issue comment and following result-table delimiter.
Escaped/concatenated strings, descriptions, expected-result arguments,
fragments, and unsupported source controls fail selection.

The Materialize opt-in additionally recognizes literal `subtest` labels and
`onlyif cockroach` before unselected records. Conditions are never evaluated,
and a conditional selected record is rejected. The chosen tuple input is
unconditional. Other factors retain their previous reader behavior.

`observed_syntax.null_predicates` records source spelling and UTF-8 byte
location, raw argument form, row arity, and nested-row presence. The structural
`source_free` flag is true for 23 inputs. It is not a certificate selector:
22 predeclared inputs receive full static certificates with 25 ordered
positions (23 nonnullable BOOL and two nonnullable, unmodified VARCHAR).
The VARCHAR positions are the DuckDB query's explicit casts, both labeled
`varchar`; the Materialize tuple alias is `r`; other eligible outputs are
`?column?`. The fixed JSON registry is checked against separately declared
Lean metadata.

The closed Calcite query has nested row values and remains explicitly
Unsupported by the independent static profile, while its exact PostgreSQL
rendering succeeds. The other 27 inputs depend on upstream table catalogs.
All 50 receive identity/PostgreSQL checked rendering. No source catalog,
parameter declarations, runtime inputs, or expected values are invented.
Source SQL and source programs are never executed. Native observations use
separately authored queries; upstream output sections remain opaque.

```sh
python3 scripts/extract_factor_corpus.py --factor null_predicates --check
python3 -m unittest discover -s scripts -p 'test_null_predicate_extraction.py'
```

Optional `--oracle` recomputes syntax observations with pinned pglast 7.21.
Offline reproduction requires no network, pglast, database, or source
execution. These 50 examples establish a finite source population, not
universal PostgreSQL/SQLite row semantics.
