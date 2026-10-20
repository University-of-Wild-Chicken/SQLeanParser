# Quantified array comparison source corpus

`concrete.jsonl` contains 50 distinct, unchanged, whole SELECT statements:
29 Hatchet application query constants, 18 PostgreSQL engine regressions,
and three sqlc compiler regressions. None occurs in the existing
`fixtures/statement_families/concrete.jsonl` population. Application
constants are shipping source code, not captured production traffic.

The statements contain 51 quantified comparisons: 41 `ANY` and ten `ALL`.
Source operator spellings are 45 `=`, four `>=`, one `!=`, and one `>`.
PostgreSQL normalizes the `!=` spelling to `<>`; the fixture records both.
Right operands comprise 34 casts, 13 unknown string literals, two parameter
references, and two ARRAY constructors. Thirty-two statements have parameter
slots. Original table names, comments, casts, parameter numbers, and complete
query text are preserved.

The inspected pinned source pool contained no authentic `SOME(array)`
statement among its 199 array-quantifier candidates. The selected population
also lacks `<`, `<=`, and the literal `<>` spelling. Those gaps are explicit:
the separately authored synthetic fixture exercises all six comparison
operators with `ANY`, `SOME`, and `ALL`, plus `!=`. Renamed or fabricated
source variants do not count toward the concrete population.

This factor covers scalar comparisons against array expressions. The
selection excludes quantified subqueries, all other expression subqueries,
subscripts, slices, row constructors, custom operators, and user-defined
types. Existing CTE, ordinary call, cast, and pagination syntax remains
unchanged where present. Recognizing a function or table name does not imply
that its catalog-dependent validity is established.

Pinned sources and licenses:

- [Hatchet](https://github.com/hatchet-dev/hatchet/tree/392e7c472221cdab235cca674640e98f904e1ea0):
  `392e7c472221cdab235cca674640e98f904e1ea0`, MIT.
- [PostgreSQL REL_16_STABLE](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256):
  `f0595c3d839debdb140903621c1b44a4f4d86256`, PostgreSQL License.
- [sqlc](https://github.com/sqlc-dev/sqlc/tree/0f1602fe1a4b780336e3e878dde720892fd8578d):
  `0f1602fe1a4b780336e3e878dde720892fd8578d`, MIT.

`concrete_sources.json` pins 14 source files and all three license files by
SHA-256. Each selection is one complete SQL statement or one original Go
string constant. Existing snapshots are reused; three additional sqlc files
reside under `fixtures/factor_sources/sources`. Records retain exact SQL,
source lines and links, source kind, parameter slots, and ordered
observations of operator spelling, quantifier spelling, and right-operand
syntax. UTF-8 byte offsets from PostgreSQL's raw parser are converted before
checking the source spelling; quoted text and comments cannot supply it.

Discovery probes temporarily removed quantifier keywords to identify
unrelated parser dependencies. Those probes are not corpus inputs or
coverage evidence. No committed statement is rewritten, renamed, or shortened.
Exact and case/whitespace duplicates cannot increase the population.

These concrete statements receive syntax and checked-rendering checks only.
They are never executed. Application schemas, parameter types, runtime
values, and operator resolution are not invented. The source screen and
raw parser establish neither successful casts nor successful execution.
Synthetic contract fixtures separately provide explicit types, bindings,
and authored expected Boolean or SQL NULL results.

Reproduce from local pinned inputs:

```sh
python3 scripts/extract_factor_corpus.py --factor array_quantified --check
python3 scripts/generate_array_quantified_examples.py --check
python3 -m unittest discover -s scripts -p test_array_quantified_extraction.py
```

Optional `--oracle` requires `pglast==7.21` and checks one whole SELECT,
parameter slots, exact quantified observations, and the exclusions above.
Its raw parser uses PostgreSQL 17.7. The separate PostgreSQL 16 grammar
replay checks all 50 originals. Neither oracle executes SQL.

`operator_signatures.json` is a separate authored expectation fixture:
six operators times 32 scalar input pairs. It is not extracted source SQL.
The pairs are all integer-width pairs, all real/double pairs, all
date/timestamp/timestamptz pairs, and ten same-type pairs. Its `char` spelling
denotes the PostgreSQL `bpchar` operator input for this catalog check.
Native checks independently verify signature existence, Boolean result,
and strictness; Lean tests compare the declared pairs with the independent
overload specification.
