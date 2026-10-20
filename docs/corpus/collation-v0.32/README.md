# Industrial PostgreSQL corpus after collation contracts

The expanded typed parser accepts 257 of the 276 pinned BenchBase, River and
Temporal statements. Among 260 distinct SQL texts, it accepts 241 and rejects
19. Explicit COLLATE and its independent provenance contract change none of
these application-corpus syntax outcomes.

The separate collation population contains fifty authored queries and fifty
unchanged PostgreSQL source statements. All fifty source statements receive
full static certificates and checked rendering under explicit catalog
assumptions, with 71 independently registered output positions. Eighteen use
source-declaration contexts; thirty-two use an observed isolated fixture
catalog that supplies metadata absent from the source deployment evidence.
Those two provenance categories remain distinct.

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
