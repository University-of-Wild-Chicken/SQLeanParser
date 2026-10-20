# Array concatenation source corpus

`concrete.jsonl` contains 50 distinct, unchanged, whole SELECT statements:
eight PostgreSQL regression queries and 42 RisingWave SQLLogicTest query
blocks. These are public engine tests, not application queries or captured
production traffic. None duplicates the existing whole-grammar concrete
population.

The PostgreSQL examples retain concatenation, append, prepend, nested
constructors, three-dimensional arrays, concatenation chains, explicit
output aliases, and integer/numeric widening. The RisingWave examples
retain all three operand shapes across the SMALLINT/INTEGER/BIGINT
cross-product, NUMERIC and REAL diagonal and cross-type pairs, VARCHAR
with a text constructor, and a timestamp-array/date combination.
There are 52 `||` nodes because two PostgreSQL statements contain chains.
All 50 queries are source-free and parameter-free.

The two sources are pinned:

- [PostgreSQL REL_16_STABLE](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/test/regress/sql/arrays.sql),
  commit `f0595c3d839debdb140903621c1b44a4f4d86256`, PostgreSQL License.
  The existing pristine `arrays.sql` and license snapshots are reused.
- [RisingWave array concatenation tests](https://github.com/risingwavelabs/risingwave/blob/7c5bb80f065b52e3eeaab0e0739684772d48aafc/e2e_test/batch/functions/array_concat.slt.part),
  commit `7c5bb80f065b52e3eeaab0e0739684772d48aafc`, Apache License 2.0.
  The complete original source file and license are retained in
  `fixtures/factor_sources`. No root NOTICE file exists at this pin.

`concrete_sources.json` pins source and license SHA-256 hashes. Every
selection preserves complete original SQL bytes, line numbers, links, and
literal contents. SQLLogicTest selectors cover exactly one literal query
block; headers and result bodies remain provenance context. The finite
reader treats expected results as opaque text and does not execute test
directives. The selected file has no loops, substitutions, or conditional
directives. RisingWave's result strings are never imported as PostgreSQL
expectations.

Metadata records operand node forms, immediate cast names, and the number
of written array suffixes on those casts. The `array_rank` observation is
the count of type suffixes, not a claim about a runtime array's dimensions.
Array constructors and nested concatenations have no inferred element
type or rank in this metadata. The screen excludes catalog references,
parameters, calls, subqueries, row forms, subscripting, other operators,
custom types, and sized array declarations. Each selected concatenation
contains explicit array syntax in at least one operand subtree. This
structural condition does not resolve PostgreSQL polymorphic overloads.

The fixed population receives PostgreSQL 16 grammar and exact
identity/PostgreSQL renderer checks. Independent static certificates use a
separate explicit source-ID/output-schema registration under an empty
catalog and parameter environment; the provenance extractor does not infer
the expected schemas. Concrete source SQL is never executed. Separate
authored fixtures provide PostgreSQL native value, descriptor, overload,
and runtime-error observations.

Reproduce from pinned local inputs:

```sh
python3 scripts/extract_factor_corpus.py --factor array_concatenation --check
python3 -m unittest discover -s scripts -p test_array_concatenation_extraction.py
```

Optional `--oracle` requires `pglast==7.21` (PostgreSQL 17.7 raw parser) and
checks the exact syntax observations. The independent PostgreSQL 16 grammar
replay checks all 50 original queries. Neither parser oracle executes SQL.
