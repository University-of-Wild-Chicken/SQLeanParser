# Industrial PostgreSQL corpus after schema-qualified names

The expanded typed parser accepts 248 of the original 276 pinned BenchBase,
River and Temporal statements and rejects 28. Among the 260 distinct SQL
texts, 232 are accepted and 28 rejected. This increment newly accepts River's
`schemaGetExpired` and Temporal's `listTablesQuery`.

Four other River schema queries now parse their qualified relations but still
stop at `current_schema`. The full remaining statements and diagnostics are
preserved in `failures.md`; removing one blocking construct does not count as
accepting the whole query.

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
