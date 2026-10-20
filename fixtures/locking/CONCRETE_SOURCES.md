# Row-locking source corpus

`concrete.jsonl` contains 50 distinct, unchanged, whole SELECT statements:
15 Temporal and 8 Hatchet shipping application constants, 2 sqlc compiler
regression inputs, and 25 PostgreSQL regression statements. It covers
`FOR UPDATE`, `FOR NO KEY UPDATE`, `FOR SHARE`, `FOR KEY SHARE`,
ordered `OF` target lists, default waiting, `NOWAIT` and `SKIP LOCKED`.
The original statements retain pagination before and after locking clauses,
joins, subqueries and common table expressions.

Exact observed clause counts are 39 UPDATE, 9 SHARE, 1 NO KEY UPDATE and
1 KEY SHARE; wait policies are 42 default, 7 SKIP LOCKED and 1 NOWAIT.
These counts describe the selected finite sources, not a frequency estimate
for production workloads.

Source revisions and licenses:

- [Temporal](https://github.com/temporalio/temporal/tree/b7bc978d1040afe2dcbc68ecfe8b228ae198e0b6),
  commit `b7bc978d1040afe2dcbc68ecfe8b228ae198e0b6`, MIT.
- [Hatchet](https://github.com/hatchet-dev/hatchet/tree/392e7c472221cdab235cca674640e98f904e1ea0),
  commit `392e7c472221cdab235cca674640e98f904e1ea0`, MIT.
- [sqlc](https://github.com/sqlc-dev/sqlc/tree/0f1602fe1a4b780336e3e878dde720892fd8578d),
  commit `0f1602fe1a4b780336e3e878dde720892fd8578d`, MIT.
- [PostgreSQL 16.15](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256),
  commit `f0595c3d839debdb140903621c1b44a4f4d86256`, PostgreSQL License.

`concrete_sources.json` pins source files, license bytes, selected constant names
or complete-statement boundaries, exact SQL hashes and observed locking clauses.
Existing snapshots are reused; newly needed sources are under `sources`.
Every JSONL record includes its source line/link, original SQL, placeholder slots,
locking strength, wait policy and ordered target list. The extractor does not
rename tables, replace parameter values, rearrange clauses or generate variants.
The SQL statement scanner preserves complete `BEGIN ATOMIC` routine bodies
when locating source-file boundaries.

The corpus is not executed. No production schema or parameter types are supplied,
and syntax acceptance does not prove that a relation permits row locking,
that every selected query is statically valid, or that a particular lock
will be acquired at runtime. Compiler and engine tests are labeled distinctly
from application queries. Native execution of separately authored synthetic
fixtures is a different test population.

Reproduce:

```sh
python3 scripts/extract_factor_corpus.py --factor locking --check
python3 -m unittest discover -s scripts -p 'test_factor_extraction.py'
```

Add `--oracle` with pinned `pglast==7.21` to recheck the complete SELECT,
locking clauses, parameter slots and feature dependencies. Its raw parser uses
PostgreSQL 17.7 grammar; that is separate from the pinned PostgreSQL 16 source
and the target parser's own grammar evidence.
