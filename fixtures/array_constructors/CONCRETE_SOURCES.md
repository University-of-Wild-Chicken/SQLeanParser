# Array constructor source corpus

`concrete.jsonl` contains 50 distinct, unchanged, whole SELECT statements:
49 PostgreSQL engine regressions and one sqlc compiler regression. None
occurs in the existing `fixtures/statement_families/concrete.jsonl`
population. These are public regression inputs, not production traffic.

The statements contain 94 constructor nodes. Twelve statements have nested
constructors, reaching depth six, with both `ARRAY[ARRAY[...]]` and
`ARRAY[[...]]` notation. The population includes NULL elements, strings,
integer and decimal elements, repeated values, scalar and array casts,
multiple constructors in one expression, and `ARRAY[]::text[]`.
Constructor depth describes expression nesting; it is not a declared or
enforced PostgreSQL type rank.

All selected statements are source-free SELECTs. ARRAY subqueries,
ANY/SOME/ALL comparisons, subscripts, slices, row constructors, and
user-defined type casts are excluded. Existing ordinary calls such as
`array_cat`, `array_fill`, `array_position`, and `cardinality` remain
unchanged. Function names in a source query do not imply that their
signatures belong to SQLean's independent validity profile.

Pinned sources and licenses:

- [PostgreSQL REL_16_STABLE](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256):
  `f0595c3d839debdb140903621c1b44a4f4d86256`, PostgreSQL License.
- [sqlc](https://github.com/sqlc-dev/sqlc/tree/0f1602fe1a4b780336e3e878dde720892fd8578d):
  `0f1602fe1a4b780336e3e878dde720892fd8578d`, MIT.

`concrete_sources.json` pins four source files and both license files by
SHA-256. Each selection is one complete original SQL statement.
Existing snapshots are reused; additional files reside under
`fixtures/factor_sources/sources`. Each record retains its exact SQL,
source line/link, source kind, parameter slots, and ordered constructor
observations: depth, element count, and whether an enclosing array cast
supplies type context through constructor nodes. A cast around a function
call does not supply that context to the function's arguments.

Discovery probes temporarily replaced constructor syntax to identify
unrelated parser dependencies. Those probes are not corpus inputs or
coverage evidence. No committed query is rewritten, renamed, or shortened.
Exact and case/whitespace duplicates cannot increase the population.
The untyped empty constructor and known deliberate invalid function-call
tests were omitted from this selection.

These concrete queries receive syntax and checked-rendering checks only.
They are never executed. Catalogs, parameter types, runtime values, and
function signatures are not invented. Shape compatibility, function
availability, successful casts, and successful execution are not established
by the source screen or raw parser. Synthetic contract fixtures separately
supply the explicit environment and expected typing for the promoted fragment.

Reproduce from local pinned inputs:

```sh
python3 scripts/extract_factor_corpus.py --factor array_constructors --check
python3 -m unittest discover -s scripts -p test_array_constructor_extraction.py
```

Optional `--oracle` requires `pglast==7.21` and checks one whole SELECT,
parameter slots, ordinary-call syntax, exact constructor observations, and
the exclusions above. Its raw parser uses PostgreSQL 17.7. The separate
PostgreSQL 16 grammar replay checks all 50 original statements. Neither
oracle executes SQL.
