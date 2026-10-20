# Row-constructor comparison source corpus

`concrete.jsonl` contains 50 distinct, unchanged, whole SELECT statements:
16 Hatchet and six Temporal application query constants, eight PostgreSQL
engine regressions, and 20 SQLite engine regressions. None occurs in the
existing `fixtures/statement_families/concrete.jsonl` population. Application
constants are shipping source code, not captured production traffic.

The statements contain 72 direct row-constructor comparisons: 40 `=`,
ten `>`, nine `>=`, seven `<=`, and six `<`. The selected sources do not
contain a `<>` comparison. One comparison uses explicit `ROW(...)`
constructors; the other 71 use implicit parenthesized tuples. Field counts
range from two to five. These are observed syntax counts, not inferred
field types or operator-overload selections. Separate synthetic fixtures
cover all six operators and both constructor forms; missing source variants
are not fabricated.

The six Temporal SELECT constants are preserved from the original application
audit: `getHistoryNodesQuery`, `getHistoryNodeMetadataQuery`,
`paginateBranchesQuery`, `getTimerTasksQuery`, `getTaskV2Qry`, and
`getTaskV2QryWithLimit`. Their original Go strings and parameter numbers are
unchanged. The original audit also contains a DELETE with a row comparison;
it is outside this SELECT population and is tracked separately.

Pinned sources and licenses:

- [Hatchet](https://github.com/hatchet-dev/hatchet/tree/392e7c472221cdab235cca674640e98f904e1ea0):
  `392e7c472221cdab235cca674640e98f904e1ea0`, MIT.
- [Temporal](https://github.com/temporalio/temporal/tree/b7bc978d1040afe2dcbc68ecfe8b228ae198e0b6):
  `b7bc978d1040afe2dcbc68ecfe8b228ae198e0b6`, MIT.
- [PostgreSQL REL_16_STABLE](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256):
  `f0595c3d839debdb140903621c1b44a4f4d86256`, PostgreSQL License.
- [SQLite](https://github.com/sqlite/sqlite/tree/5484850c7a2cd90f2a06b8d4f3453b259aefc1e1):
  `5484850c7a2cd90f2a06b8d4f3453b259aefc1e1`, public-domain dedication.

`concrete_sources.json` pins 13 source files and all four license inputs by
SHA-256. Each selection is one complete original SQL statement, original Go
string constant, or complete semicolon-terminated statement inside a literal
Tcl SQL block. The existing finite Tcl reader performs no evaluation or
substitution. Each record retains exact SQL, source lines and links, source
kind, parameter slots, and ordered observations of comparison operator,
field count, and explicit/implicit spelling on both sides.

The population requires nonempty constructors with equal field counts on
both sides of a relational comparison. Standalone rows, nested composite
rows, row-valued IN, row/array/quantified subqueries, custom row operators,
and comparisons against nonconstructor row values are excluded. Existing
CTEs, joins, aggregates, ordinary calls, array casts, quantified array
comparisons, and pagination remain where present. Their presence does not
claim independent validity for application catalogs or unknown functions.

Ten additional simple PostgreSQL ROW regressions use unquoted output aliases
`TRUE`, `FALSE`, or `NULL`, which the current typed parser excludes. They
were not rewritten to increase this population. Other omitted source
candidates require unsupported collation, binary-string, table-function,
custom-type, or composite-value syntax.

Discovery probes temporarily replaced row-constructor syntax to identify
unrelated parser dependencies. Those probes are not corpus inputs or coverage
evidence. No committed query is rewritten, renamed, or shortened. Exact and
case/whitespace duplicates cannot increase the population.

All 50 concrete queries receive syntax and checked-rendering checks only.
They are never executed. SQLite expected results are not PostgreSQL oracles;
no cross-engine equivalence is claimed. Application schemas, parameter types,
runtime values, and operator resolution are not invented. Field compatibility,
NULL behavior, collation effects, and successful execution are not established
by the source screen or raw parser.

Reproduce from local pinned inputs:

```sh
python3 scripts/extract_factor_corpus.py --factor row_comparisons --check
python3 -m unittest discover -s scripts -p test_row_comparison_extraction.py
```

Optional `--oracle` requires `pglast==7.21` and verifies one whole SELECT,
parameter slots, exact row-comparison observations, and the stated syntax
exclusions. Its raw parser uses PostgreSQL 17.7. The separate PostgreSQL 16
grammar replay checks all 50 originals. Neither oracle executes SQL.
