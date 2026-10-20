# Concatenation source corpus

`concrete.jsonl` contains 50 distinct, unchanged, whole SELECT statements:
one Hatchet application query constant and 49 PostgreSQL engine regressions.
None occurs in the existing `fixtures/statement_families/concrete.jsonl`
population. The application constant is shipping source code, not captured
production traffic.

The statements contain 86 `||` nodes. Twenty-eight statements come from the
JSONB regressions, including object merges, scalar and array-shaped JSONB
values, empty objects, and an unknown literal on either side of a JSONB cast.
Fourteen string regressions cover nested concatenation, literal text,
CHAR/VARCHAR casts, and concatenation inside ordinary function arguments.
Two text regressions retain `text || 2+2` and `unknown-literal || 2+2`.
Two JSON regressions concatenate text before a JSON cast. The remaining
statements exercise `pg_typeof`, a recursive CTE, a Hatchet catalog query,
and a genuine BYTEA concatenation in a pgcrypto regression.

These are syntax observations, not selected operator signatures. The metadata
retains each operand's raw-parser node form and, only for an immediate cast,
its declared type name. Across the 86 nodes there are 42 JSONB, four TEXT,
two BPCHAR, one VARCHAR, and one BYTEA immediate cast declarations. Function
return types, column types, and unknown literal types remain unassigned.
For example, the pgcrypto statement has a BYTEA cast on one side and an
ordinary function call on the other; this observer does not infer the
function's result type. No application catalog or binding environment is
invented. All 50 statements happen to be parameter-free.

Pinned sources and licenses:

- [Hatchet](https://github.com/hatchet-dev/hatchet/tree/392e7c472221cdab235cca674640e98f904e1ea0):
  `392e7c472221cdab235cca674640e98f904e1ea0`, MIT.
- [PostgreSQL REL_16_STABLE](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256):
  `f0595c3d839debdb140903621c1b44a4f4d86256`, PostgreSQL License.

`concrete_sources.json` pins eight source files and both license inputs by
SHA-256. Each selection is a complete original SQL statement or an original
Go string constant. The records retain exact SQL bytes, source lines and
links, source kind, parameter slots, and ordered operand observations.
The extractor does not evaluate source programs or execute these queries.

The source population excludes explicit array concatenation, array access,
row constructors, quantified/array subqueries, schema-qualified operators,
and other extended operators. JSONB values with JSON array syntax remain
JSONB literal contents, not SQL array constructors. The intentional PostgreSQL
operator-resolution failure `select 3 || 4.0;` was not selected. HSTORE,
BIT, and TSQUERY concatenation candidates were also omitted. Qualified
`sqlc.arg(...)` macro calls were not rewritten to enlarge the population.

Discovery probes temporarily replaced the operator token to find unrelated
parser dependencies. Such probes are not corpus inputs or coverage evidence.
No committed query is rewritten, renamed, or shortened. Exact and
case/whitespace duplicates cannot increase the population.

All 50 concrete queries receive syntax and checked-rendering checks only.
They are never executed. The source screen and raw grammar do not establish
overload resolution, result types, collation behavior, runtime success, or
application validity. Separate authored fixtures supply catalogs and native
expectations for the independent concatenation contracts.

Reproduce from local pinned inputs:

```sh
python3 scripts/extract_factor_corpus.py --factor concatenation --check
python3 -m unittest discover -s scripts -p test_concatenation_extraction.py
```

Optional `--oracle` requires `pglast==7.21` and verifies one whole SELECT,
parameter slots, exact concatenation observations, and the stated syntax
exclusions. Its raw parser uses PostgreSQL 17.7. The separate PostgreSQL 16
grammar replay checks all 50 originals. Neither oracle executes SQL.
