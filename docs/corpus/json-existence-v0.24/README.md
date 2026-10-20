# Industrial PostgreSQL corpus after JSONB existence

The expanded typed parser accepts 249 of the original 276 pinned BenchBase,
River and Temporal statements and rejects 27. Among the 260 distinct SQL
texts, 233 are accepted and 27 rejected. This increment newly accepts River's
`JobGetCancelRequested`, whose JSONB existence operator now parses while its
actual numbered binding is preserved.

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
