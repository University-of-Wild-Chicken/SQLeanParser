# Industrial PostgreSQL corpus after interval qualifiers

The expanded typed parser accepts 245 of the original 276 pinned BenchBase,
River and Temporal statements and rejects 31. Among the 260 distinct SQL
texts, 229 are accepted and 31 rejected. Interval field qualifiers close the
syntax failures in BenchBase TPC-H Q4, Q5, Q6, Q10, Q12, Q14 and Q20.

These counts concern syntax acceptance. This replay does not supply the
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
