# Unchanged array-overlap source statements

`concrete.jsonl` contains 50 distinct whole SELECT statements, each containing
`&&`. Two also contain `@>`. Exact queries, complete-file hashes, source offsets,
license hashes, commit pins, and syntax observations are frozen in
`concrete_sources.json`. Case/whitespace duplicate queries cannot increase the
population. No source SQL or upstream program is executed.

The sources are:

- 21 PostgreSQL engine regressions in `src/test/regress/sql/arrays.sql` and
  `src/test/regress/sql/create_index.sql`, at
  [`f0595c3d839debdb140903621c1b44a4f4d86256`](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256),
  under the [PostgreSQL license](../extended_types/licenses/postgres-COPYRIGHT.txt).
- 12 RUM engine regressions in
  [`sql/array.sql`](https://github.com/postgrespro/rum/blob/b8a31e85d59805db2e91bbf088e279729b41ca32/sql/array.sql),
  at `b8a31e85d59805db2e91bbf088e279729b41ca32`, under the
  [PostgreSQL license](../factor_sources/licenses/rum-LICENSE).
  The separately hashed `rum_init.sql` records use of the existing
  `&&(anyarray, anyarray)` operator; custom RUM operators and distance ordering are
  excluded. Selected table references occur in the `test_array.i int2[]` context.
- Four RisingWave regressions in
  [`e2e_test/batch/functions/array_predicates.slt.part`](https://github.com/risingwavelabs/risingwave/blob/7c5bb80f065b52e3eeaab0e0739684772d48aafc/e2e_test/batch/functions/array_predicates.slt.part),
  at `7c5bb80f065b52e3eeaab0e0739684772d48aafc`, under
  [Apache-2.0](../factor_sources/licenses/risingwave-LICENSE).
- 11 ReadySet PostgreSQL-oriented tests: seven complete SQLLogicTest queries in
  [`logictests/sqlparser/psql/array_overlap.test`](https://github.com/readysettech/readyset/blob/a8ca5319d26690303f27d92963fee4c6240445bd/logictests/sqlparser/psql/array_overlap.test)
  and four complete literal query strings in
  [`readyset-e2e-tests/tests/array_operators.rs`](https://github.com/readysettech/readyset/blob/a8ca5319d26690303f27d92963fee4c6240445bd/readyset-e2e-tests/tests/array_operators.rs),
  at `a8ca5319d26690303f27d92963fee4c6240445bd`. **These excerpts and snapshots
  remain under [Business Source License 1.1](../factor_sources/sources/readyset/LICENSE),
  copyright ReadySet, Inc.; they are source-available, not Open Source, and are
  not relicensed under this project's license.** The retained license permits
  redistribution and non-production use, specifies its production restrictions,
  and names a four-year Change Date and Apache-2.0 Change License. This fixture
  does not claim that the pinned version has already converted. Its copies and
  excerpts remain subject to the complete retained license.
- One sqlc application example in
  [`examples/booktest/postgresql/query.sql`](https://github.com/sqlc-dev/sqlc/blob/0f1602fe1a4b780336e3e878dde720892fd8578d/examples/booktest/postgresql/query.sql),
  at `0f1602fe1a4b780336e3e878dde720892fd8578d`, under
  [MIT](../extended_types/licenses/sqlc-LICENSE.txt). Its original `$1::varchar[]`
  stays intact; no application parameter type or value is invented.
- One Yugabyte PostgreSQL-fork regression in
  [`src/postgres/src/test/regress/sql/yb.orig.ybgin_misc.sql`](https://github.com/yugabyte/yugabyte-db/blob/368344314c469f272e699e2a8bd8f5ecb517892e/src/postgres/src/test/regress/sql/yb.orig.ybgin_misc.sql),
  at `368344314c469f272e699e2a8bd8f5ecb517892e`. The root
  [licensing scope](../factor_sources/licenses/yugabyte-LICENSE.md) assigns
  `src/postgres/` to [Apache-2.0](../factor_sources/licenses/yugabyte-LICENSE);
  its [NOTICE](../factor_sources/licenses/yugabyte-NOTICE.txt) and inherited
  [PostgreSQL notice](../factor_sources/licenses/yugabyte-src-postgres-COPYRIGHT)
  are also retained and hash-checked. Only the first unchanged occurrence of the
  `altercoltab.a int[]` overlap query is selected; repeated source occurrences do
  not count as distinct examples.

Five fixed source-free queries—the four RisingWave queries and RUM's
`NULL::int[]` query—receive full independent static certificates with empty
catalog/environment. `Tests.ArrayPredicateContract` fixes their IDs, Boolean type,
`?column?` output label, and nullability: the RUM outer-NULL query is nullable;
NULL elements inside nonnull arrays do not make the other four nullable. All
50 receive exact identity/PostgreSQL renderer certificates. The other 45 retain
rendering-only evidence because their external catalogs/bindings are not supplied.
Every source query remains unexecuted.

The Rust recognizer selects an entire unescaped ordinary string token from an
exact `let queries: Vec<(&str, &str)> = vec![...]` declaration whose entries are
literal query/description pairs. Comments and strings cannot supply fake token
boundaries. Raw/escaped strings, formatting calls, concatenation, substitutions,
substrings, and descriptions are not eligible. The SQL bytes inside the quotes
are retained exactly. SQLLogicTest results are opaque and are not PostgreSQL
expectations. These are finite source-format recognizers, not Rust or test-runner
interpreters.

Syntax observations record operand forms and explicit immediate casts only;
they never infer array types for columns or choose overloads. Complete file
context establishes that selected table columns are arrays rather than geometric,
range, or custom-extension uses of the same spelling. This provenance observation
is separate from full static validity. All 50 are replayed against the pinned
PostgreSQL grammar; optional `--oracle` checks their syntax metadata with
pglast 7.21 (PostgreSQL 17.7).

```sh
python3 scripts/extract_factor_corpus.py --factor array_overlap --check
python3 -m unittest discover -s scripts -p 'test_rust_query_extraction.py'
python3 -m unittest discover -s scripts -p 'test_array_predicate_extraction.py'
```

The 50 authored synthetic queries and their native runtime expectations are
maintained separately.
