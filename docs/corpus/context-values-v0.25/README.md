# Industrial PostgreSQL corpus after context values

The expanded typed parser accepts 253 of the original 276 pinned BenchBase,
River and Temporal statements and rejects 23. Among the 260 distinct SQL
texts, 237 are accepted and 23 rejected. This increment newly accepts River's
`pGNotifyMany`, `columnExists`, `indexExists` and `indexesExist`.

The general interpretation watchlist flags `columnExists` because it contains
a SQL-value keyword. The supplementary `context-interpretation.json` checks
that both original and canonical PostgreSQL raw ASTs contain
`SVFOP_CURRENT_SCHEMA`, no column reference named `current_schema`, and the
same ordered parameter uses `[1, 2]`. Its recorded structural flags are empty.
This is a finite parsing observation, not an execution-equivalence theorem.

These are syntax observations. The replay does not invent application
catalogs, parameter declarations or independent full-query certificates.
No source SQL was executed. `results.jsonl` retains every input and outcome,
and `audit.json` binds the observation to input, runner, binary and source
hashes. Candidate feature tags describe syntax present, not necessarily the
first cause of rejection. The Markdown failure display trims trailing
whitespace; exact SQL remains in `results.jsonl`.

The optional pglast 7.21 / PostgreSQL 17.7 raw-parser oracle accepts all 276
statements. The separate proof-carrying whole-grammar interface targets
PostgreSQL 16.15. Grammar acceptance does not establish typed validity or
execution equivalence.

Reproduce with `scripts/requirements-corpus.txt` installed:

```sh
lake build
python scripts/audit_postgresql_corpus.py --output .lake/industrial-audit
```

Full PostgreSQL contracts and the entire-grammar source populations remain
unfinished. Publication of `0.0.1-alpha` remains held.
