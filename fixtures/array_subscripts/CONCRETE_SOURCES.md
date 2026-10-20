# Array subscript and slice source corpus

`concrete.jsonl` contains 50 distinct, unchanged, whole SELECT statements:
24 PostgreSQL engine regressions and 26 DuckDB engine regressions. None
occurs in the existing `fixtures/statement_families/concrete.jsonl`
population. These are public regression inputs, not application traffic.

The statements contain 76 subscript groups with 117 dimensions: 71 element
indices and 46 slices. There are 28 slice-bearing statements and 28
element-index statements, with overlap for mixed groups. Source syntax
includes omitted bounds, SQL NULL bounds, zero and negative bounds,
arithmetic and column bounds, casts, chained dimensions, and explicit
parentheses. Three statements have nested access groups. Grouping is
retained: `a[1][2]` is one group, whereas `(a[1])[2]` contains two groups.
The selected groups have at most three dimensions. These counts describe
syntax, not an inferred or enforced PostgreSQL array rank.

Pinned sources and licenses:

- [PostgreSQL REL_16_STABLE](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256):
  `f0595c3d839debdb140903621c1b44a4f4d86256`, PostgreSQL License.
- [DuckDB](https://github.com/duckdb/duckdb/tree/917243df252f114d9c448b1d23f8618f0d683769):
  `917243df252f114d9c448b1d23f8618f0d683769`, MIT.

`concrete_sources.json` pins five source files and both license files by
SHA-256. PostgreSQL statements are complete original semicolon-terminated
SQL spans. DuckDB statements are complete original SQLLogicTest query
blocks, including their final newline; no semicolon is appended. The two
DuckDB snapshots and their license reside under `fixtures/factor_sources`.
Each record retains exact SQL, source lines and links, source dialect,
parameter-slot observations, and ordered subscript groups with bound
presence. The small SQLLogicTest reader recognizes only the record forms
present in these pinned files. It never interprets directives or executes
SQL. Expected-result blocks are skipped as opaque text.

DuckDB's list semantics differ from PostgreSQL's arrays, including nested
lists and negative indices. DuckDB expected results are **not** imported
as PostgreSQL oracles, and no equivalence between the engines is claimed.
The selected text is separately checked against PostgreSQL's grammar.

Six PostgreSQL statements come from `domain.sql`. Their upstream setup uses
domains over arrays or arrays of such domains. That context explains why
parenthesized nested accesses can be meaningful; it is not synthesized as
an SQLean schema. Three statements from `subselect.sql` access arrays
returned by scalar subqueries. These nine statements remain syntax and
rendering evidence, with no independent domain or scalar-subquery validity
claim. Ordinary calls such as `pg_typeof` likewise do not imply that the
independent function-signature profile covers them.

The population excludes quantified subqueries, ARRAY subqueries, row
constructors, record-field access, JSON/hstore/geometric subscripting, and
known scalar-base failures. The proposed seven-dimension PostgreSQL source
was omitted because PostgreSQL's analyzer rejects it even though its raw
grammar accepts it. The native dimension-limit failure is tested separately;
it does not count toward these 50 positive source examples.

Discovery probes temporarily removed subscript groups to identify unrelated
parser dependencies. Those probes are not corpus inputs or coverage evidence.
No committed statement is rewritten, renamed, or shortened. Exact and
case/whitespace duplicates cannot increase the population.

These concrete statements receive syntax and checked-rendering checks only.
They are never executed. No catalogs, parameter types, runtime values, or
expected result types are invented. In-range access, non-NULL output, shape
compatibility, domain behavior, and successful execution are not established
by the source screen or raw parser. Synthetic contract fixtures separately
provide explicit environments and authored PostgreSQL expectations.

Reproduce from local pinned inputs:

```sh
python3 scripts/extract_factor_corpus.py --factor array_subscripts --check
python3 -m unittest discover -s scripts -p test_array_subscript_extraction.py
python3 -m unittest discover -s scripts -p test_sqllogic_sql_extraction.py
```

Optional `--oracle` requires `pglast==7.21` and checks one whole SELECT,
parameter slots, exact subscript-group observations, and the stated syntax
exclusions. Its raw parser uses PostgreSQL 17.7. The separate PostgreSQL 16
grammar replay checks all 50 originals. Neither oracle executes SQL.
