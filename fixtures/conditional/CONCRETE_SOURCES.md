# Conditional-expression source corpus

`concrete.jsonl` contains 50 distinct, unchanged, whole SELECT statements:
11 shipping Hatchet application constants, 13 sqlc compiler regression inputs,
and 26 PostgreSQL engine regression inputs. The corpus includes searched CASE,
simple CASE, COALESCE, NULLIF, GREATEST and LEAST. It covers omitted ELSE,
multiple WHEN branches, nested conditional expressions, predicates, joins,
subqueries and common table expressions.

The three repository commits, licenses, extraction rules and interpretation
limits are shared with [the function corpus](../functions/CONCRETE_SOURCES.md).
`concrete_sources.json` records the exact selected source files, SHA-256 hashes,
constant names or complete-statement offsets, and the expected conditional
forms. Shared snapshots and license texts are referenced directly.

Every JSONL record preserves the original statement and its source link.
Function calls such as `date_bin`, `exp`, `now`, `random`, `unnest` and the
regression fixture's `vol` are previous-factor syntax dependencies. The corpus
does not supply fabricated production schemas, parameter types or values,
and it is not executed. Compiler and engine tests are labeled separately
from application queries. Some regression statements intentionally exercise
runtime errors or evaluation order; raw syntax acceptance is the claim here.

Reproduce from local inputs:

```sh
python3 scripts/extract_factor_corpus.py --factor conditional --check
python3 -m unittest discover -s scripts -p 'test_factor_extraction.py'
```

Add `--oracle` with pinned `pglast==7.21` to verify the complete SELECT,
all factor observations, lack of later-factor syntax dependencies and
placeholder slots. The required six conditional forms and the exact 50-case
source population are checked even without the optional oracle.
