# Industrial PostgreSQL corpus after named function arguments

The expanded typed parser accepts 256 of the original 276 pinned BenchBase,
River and Temporal statements and rejects 20. Among the 260 distinct SQL texts,
240 are accepted and 20 rejected.

This increment newly accepts River's `leaderAttemptElect`,
`leaderAttemptReelect` and `leaderInsert`, whose `make_interval(secs => ...)`
calls previously stopped at the named separator. These statements are DML.
Their syntax acceptance does not establish independent whole-DML validity,
execution equivalence or transaction guarantees. The new independent
`make_interval` binding rules are tested separately in SELECT certificates.

No source statement was executed. No application relation catalog, parameter
declarations or source-query validity evidence was invented for this replay.
`results.jsonl` retains every input and outcome; `audit.json` binds the
observation to source, runner and binary hashes. Candidate feature tags describe
syntax present, rather than necessarily identifying the first rejection cause.
The Markdown failure display trims trailing whitespace; exact SQL remains in
the JSONL artifact.

The generic interpretation watchlist still flags River's `columnExists`
because of its SQL-value keyword. The prior context-value increment contains
a separate raw-AST observation for that expression; named-call support does
not change its implementation.

The optional pglast 7.21 / PostgreSQL 17.7 raw-parser oracle accepts all 276
statements. The separate proof-carrying grammar interface targets PostgreSQL
16.15. Grammar recognition does not establish typed validity or equivalence
to PostgreSQL's C semantic actions.

Reproduce with `scripts/requirements-corpus.txt` installed:

```sh
lake build
python scripts/audit_postgresql_corpus.py --output .lake/industrial-audit
```

Full PostgreSQL contracts and the entire-grammar source populations remain
unfinished. Publication of `0.0.1-alpha` remains held.
