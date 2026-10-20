# JSON extraction source corpus

`concrete.jsonl` contains 50 distinct, unchanged, whole SELECT statements:
25 from PostgreSQL's `json.sql` regressions and 25 from `jsonb.sql`.
They are engine regressions, not application queries or captured production
traffic. None occurs in the existing
`fixtures/statement_families/concrete.jsonl` population.

There are 52 extraction nodes: 15 `->`, 11 `->>`, 12 `#>`, and 14 `#>>`.
Two statements contain nested extraction. The sources exercise object keys,
array indexes, negative indexes, missing values, JSON null, typed SQL NULL
keys, empty path literals, array-constructed paths, and paths with NULL
elements. All statements are source-free and parameter-free; no application
schema or binding environment is invented.

The source is pinned to
[PostgreSQL REL_16_STABLE](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256),
commit `f0595c3d839debdb140903621c1b44a4f4d86256`, under the PostgreSQL
License. `concrete_sources.json` pins both existing source files and the
license input by SHA-256. Each selection is one complete original statement,
retaining exact SQL bytes, source lines, links, and string contents.

Metadata records operator spelling, operand node forms, and only immediate
cast declarations. There are 25 explicit JSON and 25 explicit JSONB document
casts. The two nested operands have no inferred type in this metadata.
Right operands include 27 constants, 17 array constructors, and eight
explicit casts: four TEXT and four INTEGER typed NULLs. These observations
do not select overloads or compute results or nullability.

The finite source screen excludes table references, parameters, calls,
subqueries, rows, array subscripting, other JSON operators, and
schema-qualified operator names. It also checks that the selected document
strings are well-formed ordinary JSON using Python's JSON decoder, rejecting
non-JSON numeric constants. This limited malformed-literal screen is not
PostgreSQL conversion validation: it does not establish PostgreSQL's
Unicode, numeric, path, catalog, or execution semantics. The selected
upstream sections are extraction corner cases, not intentionally malformed
JSON input tests.

Discovery probes temporarily substituted existing operators to identify
unrelated parser dependencies. Those probes are not corpus inputs or
coverage evidence. No committed query is rewritten, renamed, or shortened.
Exact and case/whitespace duplicates cannot increase the population.

All 50 concrete queries receive syntax, checked-rendering, and independent
static-contract checks under an empty catalog and parameter environment.
The public Lean corpus test has a separate, explicit source-ID-to-output
schema mapping; the provenance extractor does not infer those output types.
This fixed source-free population needs no invented application catalog.
The concrete queries are never executed. PostgreSQL expected-output files
are not imported as native expectations. Separate authored fixtures provide
input types, native values, result descriptors, and runtime error boundaries
for the independent extraction contracts.

Reproduce from local pinned inputs:

```sh
python3 scripts/extract_factor_corpus.py --factor json_extraction --check
python3 -m unittest discover -s scripts -p test_json_operator_extraction.py
```

Optional `--oracle` requires `pglast==7.21` and verifies one whole SELECT,
parameter slots, exact extraction observations, and the stated source
boundaries. Its raw parser uses PostgreSQL 17.7. The separate PostgreSQL 16
grammar replay checks all 50 originals. Neither oracle executes SQL.
