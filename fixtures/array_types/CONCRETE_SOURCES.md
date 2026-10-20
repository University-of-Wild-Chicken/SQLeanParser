# Array type source corpus

`concrete.jsonl` contains 50 distinct, unchanged, whole SELECT statements:
42 PostgreSQL engine regressions, seven Hatchet application constants, and
one sqlc compiler regression. None occurs in the existing
`fixtures/statement_families/concrete.jsonl` population.

This increment covers array type suffixes in casts and declared parameter
types. The source population contains 65 type occurrences across seven
element families: integer, bigint, text, double precision, interval,
timestamp with time zone, and UUID. Eight queries have numbered parameters.
All selected suffixes are `[]`; array values in string literals include
empty arrays, NULL elements, multiple dimensions, and explicit lower bounds.
Syntax bounds describe declarations, not runtime size or rank guarantees.

The queries do not contain ARRAY constructors, subscripting or slices,
ANY/SOME/ALL comparisons, array subqueries, or row constructors. Those are
separate factors. Existing ordinary function calls, joins, SELECT CTEs,
grouping, locking, and conditional expressions remain in the sources.
Unknown or extension function signatures receive no independent validity
claim. The synthetic contract fixtures separately supply explicit catalogs
and parameter declarations for the promoted fragment.

Pinned sources and licenses:

- [PostgreSQL REL_16_STABLE](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256):
  `f0595c3d839debdb140903621c1b44a4f4d86256`, PostgreSQL License.
- [Hatchet](https://github.com/hatchet-dev/hatchet/tree/392e7c472221cdab235cca674640e98f904e1ea0):
  `392e7c472221cdab235cca674640e98f904e1ea0`, MIT.
- [sqlc](https://github.com/sqlc-dev/sqlc/tree/0f1602fe1a4b780336e3e878dde720892fd8578d):
  `0f1602fe1a4b780336e3e878dde720892fd8578d`, MIT.

`concrete_sources.json` pins nine source files and three license files by
SHA-256. Every selection is an entire SQL statement or a decoded upstream
Go string constant. Existing snapshots are reused; additional files reside
under `fixtures/factor_sources/sources`. Each record retains its complete
SQL, original source line/link, source kind, parameter slots, and ordered
array type observations. No query is renamed, shortened, or rewritten.
The extraction rejects exact and case/whitespace duplicates.

Discovery used temporary copies with suffixes removed to identify unrelated
parser dependencies. Those copies are **not** corpus inputs or coverage
evidence: every committed statement retains every original suffix.
Deliberate malformed array-input tests and known invalid function-call tests
were omitted from this selection. Source origin and parsing still do not
establish catalog-dependent validity or successful execution.

These concrete queries receive syntax and checked-rendering checks only.
They are never executed, and application catalogs, parameter types, and
values are not invented. Casting text to an array can fail when PostgreSQL
interprets its contents; a syntactic or static typing certificate does not
prove that runtime conversion succeeds.

Reproduce from local pinned inputs:

```sh
python3 scripts/extract_factor_corpus.py --factor array_types --check
python3 -m unittest discover -s scripts -p test_array_type_extraction.py
```

Optional `--oracle` requires `pglast==7.21` and verifies one whole SELECT,
parameter slots, array type observations, and exclusion of the later array
expression forms. Its raw parser uses PostgreSQL 17.7. The separate
PostgreSQL 16 grammar replay checks all 50 original statements. Neither
oracle executes SQL.
