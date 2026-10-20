# Industrial PostgreSQL corpus after set-operation contracts

The expanded typed parser accepts 257 of the 276 pinned BenchBase, River and
Temporal statements. Among 260 distinct SQL texts, it accepts 241 and rejects
19. This increment strengthens validity for existing set-operation syntax;
it changes none of those syntax outcomes.

Separate UNION, INTERSECT and EXCEPT populations each retain fifty authored
and fifty unchanged source queries. The authentic full-contract registry has
62 statements and 83 independently specified output positions. The other 88
queries retain checked rendering with their catalog or input dependencies
explicit. No application catalog or parameter types are invented.

Original source SQL is never executed. `results.jsonl` retains exact SQL and
outcomes; `audit.json` identifies the runner, source and binary hashes.
The Markdown failure display only trims trailing whitespace. The existing
River `columnExists` interpretation watchlist remains unchanged.

The optional pglast 7.21 / PostgreSQL 17.7 raw parser accepts all 276 statements.
The independent grammar interface targets pinned PostgreSQL 16.15; neither
interface establishes equivalence to PostgreSQL's C semantic actions.

Reproduce with `scripts/requirements-corpus.txt` installed:

```sh
lake build
python scripts/audit_postgresql_corpus.py --output .lake/industrial-audit
```

Full PostgreSQL typed contracts and the requested entire-grammar authentic
source populations remain unfinished. Publication of `0.0.1-alpha` remains held.
