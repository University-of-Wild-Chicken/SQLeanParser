# Industrial PostgreSQL corpus after row comparisons

This replay uses the original 276 pinned BenchBase, River and Temporal
records (260 distinct SQL texts). SQLean's expanded typed parser now accepts
233 records and rejects 43. Among distinct texts the counts are 217 and 43.
All seven original row-constructor failures now parse: six Temporal SELECTs
and a Temporal DELETE containing a row-comparison SELECT.

These counts measure syntax acceptance only. They do not promote the source
queries to independent validity certificates or supply their missing catalogs
and parameter types. No source SQL was executed.

`results.jsonl` retains all statements and outcomes; `failures.md` records
each remaining rejection and its candidate syntax factors. The candidate
tags describe features present in a rejected query. A tag can refer to
already-supported syntax and does not by itself identify its blocking token.
`audit.json` pins corpus, runner, binary and Lean-source hashes together with
the local checkpoint and worktree changes at observation time.

The optional raw-parser oracle is pglast 7.21 / PostgreSQL 17.7 and accepts
all 276 source records. The separate whole-grammar Lean API is pinned to
PostgreSQL 16.15; its broader coverage is not conflated with the typed-parser
counts here.

Reproduce in an environment with `scripts/requirements-corpus.txt` installed:

```sh
lake build
python scripts/audit_postgresql_corpus.py --output .lake/industrial-audit
```

Full PostgreSQL typed validity, renderer contracts and the required
entire-grammar source populations remain unfinished. Release `0.0.1-alpha`
is still held until those obligations are complete.
