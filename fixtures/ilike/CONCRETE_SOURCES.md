# ILIKE source corpus

`concrete.jsonl` contains 50 distinct, unchanged, whole SELECT statements:
40 DuckDB engine regressions, seven PostgreSQL engine regressions, two River
application constants, and one Hatchet application constant. None occurs in
the existing `fixtures/statement_families/concrete.jsonl` population. The
application constants are shipping code, not captured production traffic.

There are 43 `ILIKE` and seven `NOT ILIKE` nodes. Sources cover constant and
column patterns, prefix/suffix/interior wildcards, `_`, repeated `%`, Unicode
text, empty patterns, a NULL pattern, ordering, and application pagination.
The River constants retain concatenation and existing typed-array exclusions.
The Hatchet constant retains conditional ordering and an ordinary `concat`
call. These additional expressions are not rewritten to simplify a query.

Pinned sources and licenses:

- [DuckDB](https://github.com/duckdb/duckdb/tree/917243df252f114d9c448b1d23f8618f0d683769):
  `917243df252f114d9c448b1d23f8618f0d683769`, MIT.
- [PostgreSQL REL_16_STABLE](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256):
  `f0595c3d839debdb140903621c1b44a4f4d86256`, PostgreSQL License.
- [River](https://github.com/riverqueue/river/tree/1354a059d7cbe5790acc7a755a2ab7ac6d2f1ed8):
  `1354a059d7cbe5790acc7a755a2ab7ac6d2f1ed8`, MPL-2.0.
- [Hatchet](https://github.com/hatchet-dev/hatchet/tree/392e7c472221cdab235cca674640e98f904e1ea0):
  `392e7c472221cdab235cca674640e98f904e1ea0`, MIT.

`concrete_sources.json` pins eight source files and four license inputs by
SHA-256. PostgreSQL selections are complete SQL statements; the three
application selections are exact Go string constants. The River
`/* TEMPLATE: schema */` comments remain unchanged; no schema substitution or
template expansion occurs. All original parameter numbers are preserved.
Only these three application statements contain parameters, and their
types and values are not invented.

The 40 DuckDB selections are complete literal SQLLogicTest query blocks from
`test_ilike.test` and `test_ilike_constant_pattern.test`, including their
original final newlines. The finite reader neither runs directives nor
evaluates substitutions. Result sections are opaque and never become
PostgreSQL expectations. Unicode case folding, collations, and NULL behavior
may differ between engines; this population makes no cross-engine
equivalence claim. Embedded-NUL cases, explicit `ESCAPE`, and explicit
`COLLATE` dependencies were not selected.

Each record observes only keyword polarity and the raw-parser node form on
each side. It does not infer operand types, operator signatures, collation,
pattern validity, or runtime results. Existing array casts and quantified
array comparisons in River queries remain syntax dependencies. SQL array
constructors/access, row constructors, array/quantified subqueries, other
extended operators, and schema-qualified pattern operators are excluded by
the finite source screen. Concatenation is an admitted existing operator.

All 50 concrete queries receive syntax and checked-rendering checks only.
They are never executed. Application catalog validity, function typing, and
successful execution are not claimed. Separate authored fixtures supply
catalogs and native expectations for the independent ILIKE contracts.
No query was synthesized, renamed, shortened, or otherwise rewritten.
Exact and case/whitespace duplicates cannot increase the population.

Reproduce from local pinned inputs:

```sh
python3 scripts/extract_factor_corpus.py --factor ilike --check
python3 -m unittest discover -s scripts -p test_pattern_extraction.py
```

Optional `--oracle` requires `pglast==7.21` and verifies one whole SELECT,
parameter slots, exact pattern observations, and the stated syntax
exclusions. Its raw parser uses PostgreSQL 17.7. The separate PostgreSQL 16
grammar replay checks all 50 originals. Neither oracle executes SQL.
