# Industrial PostgreSQL corpus after uncorrelated expression-subquery contracts

The expanded typed parser accepts 257 of the 276 pinned BenchBase, River and
Temporal statements. Among 260 distinct SQL texts, it accepts 241 and rejects
19. Uncorrelated expression-subquery contracts change none of these existing
application-corpus syntax outcomes. The audit uses the final production binary
with SHA256 `2c00c6692f3acf23d027849b18d8efc3036f033339e5a87dfd6e165a7d60824a`.

`results.jsonl` retains exact original SQL and outcomes; `audit.json` records
measured counts and input, runner and binary hashes. `failures.md` lists the
remaining rejections, trimming trailing whitespace only for display. The River
`columnExists` interpretation watchlist remains unchanged.

The separate expression-subquery population contains 150 authored queries and
150 unchanged upstream statements: fifty each for scalar subqueries, EXISTS,
and scalar IN/NOT IN subqueries. The fixed authentic certificate registry has
78 statements and 84 ordered output positions. Thirty-seven use empty catalogs;
forty-one use conditional field catalogs derived from exact original CREATE
TABLE inputs. The remaining 72 are explicit rendering-only source evidence,
including three INTEGER/TEXT comparison conflicts after subquery target typing.
All source statements are noncorrelated under the finite conservative scope
screen; full source certificates are registered independently of checker results.

Original source SQL and setup are never executed. The optional pglast 7.21 /
PostgreSQL 17.7 raw parser supplies syntax observations only. The independent
grammar interface targets pinned PostgreSQL 16.15; neither establishes equivalence
to PostgreSQL's C semantic actions. Authored experiments separately observe
cardinality errors, NULL behavior, prepared descriptions and output collations.

Reproduce the original application-corpus audit with a built executable and the
pinned dependencies in `scripts/requirements-corpus.txt`:

```sh
python scripts/audit_postgresql_corpus.py --output .lake/industrial-audit
```

See [the source provenance and eligibility inventory](../../../fixtures/subqueries/CONCRETE_SOURCES.md)
for exact source counts and caller catalog assumptions. Full PostgreSQL typed
contracts and the requested entire-grammar authentic populations remain unfinished;
publication of `0.0.1-alpha` remains held.
