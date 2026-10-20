# Unchanged array-containment source statements

`concrete.jsonl` contains 50 distinct whole SELECT statements, with 30 `@>` and
20 `<@` occurrences. No query has been renamed, repaired, substituted, or generated
to reach that count. `concrete_sources.json` pins revisions, complete input files,
licenses, source offsets, SQL hashes, and finite syntax observations. Extraction
does not execute source SQL or upstream programs.

The population is:

- 26 PostgreSQL engine regressions from `src/test/regress/sql/arrays.sql` and
  `src/test/regress/sql/create_index.sql`, at
  [`f0595c3d839debdb140903621c1b44a4f4d86256`](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256).
  The original [PostgreSQL license](../extended_types/licenses/postgres-COPYRIGHT.txt)
  and existing file snapshots are reused.
- 20 RUM extension regressions from
  [`sql/array.sql`](https://github.com/postgrespro/rum/blob/b8a31e85d59805db2e91bbf088e279729b41ca32/sql/array.sql),
  pinned to `b8a31e85d59805db2e91bbf088e279729b41ca32`, under the
  [PostgreSQL license](../factor_sources/licenses/rum-LICENSE). These are ordinary
  array containment operators. The separately hashed `rum_init.sql` context
  shows the RUM array operator class referencing the existing `anyarray` operators;
  custom `%` and `<=>` operator queries are excluded. The table queries refer to
  the source's declared `test_array.i int2[]`.
- Four RisingWave engine regressions from
  [`e2e_test/batch/functions/array_predicates.slt.part`](https://github.com/risingwavelabs/risingwave/blob/7c5bb80f065b52e3eeaab0e0739684772d48aafc/e2e_test/batch/functions/array_predicates.slt.part),
  at `7c5bb80f065b52e3eeaab0e0739684772d48aafc`, under
  [Apache-2.0](../factor_sources/licenses/risingwave-LICENSE).
  Complete SQLLogicTest query blocks, including their final newline, are retained.
  Upstream expected results are opaque source content and are never PostgreSQL
  value oracles.

Six preselected source-free queries—the four RisingWave queries and the two RUM
`NULL::int[]` queries—receive independent full static certificates with empty
catalog and parameter environment. Their fixed IDs, output label `?column?`,
Boolean type, and nullability expectations are registered in
`Tests.ArrayPredicateContract`; only the two outer-NULL queries are nullable.
All 50 receive exact identity/PostgreSQL rendering round-trip checks. The remaining
44 depend on upstream tables and receive rendering evidence only; source DDL
documents their origin but is not invented or silently imported as an application
validity environment. None of these 50 source queries is executed.

`observed_syntax` records written operand forms, immediate casts, written array
suffix rank, and the absence or presence of a FROM source. It does not infer
column types, choose overloads, establish runtime dimensions, validate literal
conversion, or assert application correctness. Calls, scalar subqueries, row
constructors, subscripts, and custom operators are outside this finite population.
All 50 parse under the separate pinned PostgreSQL grammar replay; optional
`--oracle` checks the frozen observations with pglast 7.21 (PostgreSQL 17.7).

Reproduce without network access:

```sh
python3 scripts/extract_factor_corpus.py --factor array_containment --check
python3 -m unittest discover -s scripts -p 'test_array_predicate_extraction.py'
```

The authored 50-query `synthetic.json` population and its native PostgreSQL
expectations are separate from this authentic source population.
