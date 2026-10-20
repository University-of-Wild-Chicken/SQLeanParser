# JSONB containment source corpus

`concrete.jsonl` contains 50 distinct, unchanged, whole SELECT statements
from PostgreSQL's `src/test/regress/sql/jsonb.sql`: 41 use `@>` and nine use
`<@`. These are engine regressions, not application queries or captured
production traffic. None duplicates the existing
`fixtures/statement_families/concrete.jsonl` population.

The first 42 statements contain one containment expression over literal
documents, with an explicit left JSONB cast and either an unknown string
literal or an explicit JSONB cast on the right. They cover objects, missing
keys, JSON null, scalars, arrays, repeated array values, nested structures,
and both containment directions. The other eight are five `COUNT(*)`
predicates over `testjsonb` and three `SELECT *` predicates over `nestjsonb`,
retained from their original indexing regressions. All 50 are parameter-free.

The source is pinned to
[PostgreSQL REL_16_STABLE](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256),
commit `f0595c3d839debdb140903621c1b44a4f4d86256`, under the PostgreSQL
License. `concrete_sources.json` reuses the existing pristine file and license
snapshots, pinning both by SHA-256. Each selection retains complete original
SQL bytes, source lines, links, and string contents. No SQL is rewritten,
renamed, or shortened; exact and case/whitespace duplicates cannot increase
the population.

Metadata records only operator spelling, operand forms, immediate cast
declarations, and the source-free structural observation. There are 42
explicit left JSONB casts and eight column operands; nine right operands
have explicit JSONB casts and 41 are untyped string literals. Column types,
overloads, output schemas, values, and nullability are not inferred by this
extractor. The table-dependent statements do not gain an invented catalog.

The finite source screen excludes parameters, custom/array type casts,
array constructors, subscripting, row expressions, subqueries, CTEs, set
operations, qualified/derived/multiple table sources, other operators, and
calls other than the table-dependent `COUNT(*)` cases. It checks both
operand document strings with Python's JSON decoder and rejects non-JSON
numeric constants. This malformed-literal screen is not PostgreSQL
conversion validation and does not establish PostgreSQL Unicode, numeric,
catalog, indexing, or execution semantics.

All 50 receive syntax and exact checked-rendering checks. The fixed first
42 source-free records additionally receive independent static certificates
under an empty catalog and parameter environment, with one unnamed,
nonnullable Boolean output. Their IDs are explicitly registered in the
public Lean corpus test; successful validation is not used to choose the
population. The remaining eight retain rendering-only coverage. Five need
aggregate validity and all eight depend on upstream table contexts; this
corpus does not claim those additional contracts.

No concrete source query is executed, and upstream expected-output files
are not imported as native expectations. Separate authored fixtures provide
native values, result descriptors, operator catalog observations, and
runtime error cases. Discovery substitutions used to screen unrelated
parser dependencies are not retained or counted as examples.

Reproduce from local pinned inputs:

```sh
python3 scripts/extract_factor_corpus.py --factor json_containment --check
python3 -m unittest discover -s scripts -p test_json_containment_extraction.py
```

Optional `--oracle` requires `pglast==7.21` and verifies one whole SELECT,
the exact observed syntax, and the finite source boundaries. Its raw parser
uses PostgreSQL 17.7; the separate PostgreSQL 16 grammar replay also checks
all 50 originals. Neither oracle executes SQL.
