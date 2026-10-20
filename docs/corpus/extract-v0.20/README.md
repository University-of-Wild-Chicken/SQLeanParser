# Industrial PostgreSQL corpus after EXTRACT

The expanded typed parser accepts 238 of the original 276 pinned BenchBase,
River and Temporal statements and rejects 38. Among the 260 distinct SQL
texts, 222 are accepted and 38 rejected. This increment closes the three
EXTRACT syntax failures in BenchBase TPC-H Q7, Q8 and Q9.

These are syntax-acceptance counts. The industrial queries do not receive
independent validity certificates from this replay: their complete catalogs,
parameter declarations and broader query contracts are separate obligations.
No source SQL was executed.

`results.jsonl` preserves all inputs and outcomes; `failures.md` documents
every remaining rejection. Candidate feature tags describe syntax present
in a failed query, not necessarily its blocking token. `audit.json` records
the corpus, runner, binary and source hashes and the local worktree at the
time of the observation.

The optional pglast 7.21 / PostgreSQL 17.7 raw-parser oracle accepts all
276 statements. The separate proof-carrying whole-grammar interface targets
PostgreSQL 16.15. Its grammar coverage does not promote these statements to
typed-validity or execution-equivalence proofs.

Reproduce with `scripts/requirements-corpus.txt` installed:

```sh
lake build
python scripts/audit_postgresql_corpus.py --output .lake/industrial-audit
```

Full PostgreSQL contracts and the required entire-grammar source populations
remain unfinished. Publication of `0.0.1-alpha` remains held.
