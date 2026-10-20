# Industrial PostgreSQL corpus after SUBSTRING

The expanded typed parser accepts 246 of the original 276 pinned BenchBase,
River and Temporal statements and rejects 30. Among the 260 distinct SQL
texts, 230 are accepted and 30 rejected. SQL-standard SUBSTRING closes the
remaining expression-syntax failure in BenchBase TPC-H Q22.

These counts concern syntax acceptance. The replay does not supply the
application catalogs, parameter declarations or broader query contracts
needed for independent validity certificates. No source SQL was executed.

`results.jsonl` preserves every input and outcome. `failures.md` records all
remaining rejections, while `audit.json` binds the observation to its input,
runner, binary and source hashes. Candidate feature tags identify syntax
present in a query; they do not establish its blocking token.

The optional pglast 7.21 / PostgreSQL 17.7 raw-parser oracle accepts all 276
statements. The separate proof-carrying whole-grammar API targets PostgreSQL
16.15. Its grammar coverage does not confer typed validity or execution
equivalence.

Reproduce with `scripts/requirements-corpus.txt` installed:

```sh
lake build
python scripts/audit_postgresql_corpus.py --output .lake/industrial-audit
```

Full PostgreSQL contracts and the entire-grammar source populations remain
unfinished. Publication of `0.0.1-alpha` remains held.
