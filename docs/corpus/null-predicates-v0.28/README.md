# Industrial PostgreSQL corpus after null-predicate contracts

The expanded typed parser accepts 257 of the original 276 pinned BenchBase,
River and Temporal statements and rejects 19. Among the 260 distinct SQL
texts, 241 are accepted and 19 rejected. This increment changes none of those
acceptance outcomes; it adds independently certified null-predicate syntax
and strengthens native SQLite precedence handling.

The two new factors separately retain fifty authored and fifty unchanged
source statements each. Their fixed complete-certificate population contains
47 authentic queries and 59 ordered output positions. Catalog-dependent and
nested-row examples remain rendering evidence with explicit typing gaps.
No application catalog or parameter declarations are invented.

No original source SQL was executed. `results.jsonl` retains exact audited SQL
and outcomes; `audit.json` records source, runner and binary hashes. The
Markdown failure display trims trailing whitespace only. The generic
interpretation watchlist still flags River's `columnExists`; its supplementary
raw-AST observation remains in the context-value increment.

The optional pglast 7.21 / PostgreSQL 17.7 raw parser accepts all 276 statements.
The separate proof-carrying grammar API targets PostgreSQL 16.15. Neither
interface proves equivalence to PostgreSQL C semantic actions or successful
runtime evaluation.

Reproduce with `scripts/requirements-corpus.txt` installed:

```sh
lake build
python scripts/audit_postgresql_corpus.py --output .lake/industrial-audit
```

Full PostgreSQL contracts and entire-grammar source populations remain
unfinished. Publication of `0.0.1-alpha` remains held.
