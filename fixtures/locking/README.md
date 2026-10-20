# Row-locking verification fixtures

`synthetic.json` contains 50 authored SELECTs and exact catalog, parameter, output
type, nullability, and result-row expectations. Run
`python3 scripts/generate_locking_examples.py --check` to reproduce it.

The first 48 cases cover four strengths (`UPDATE`, `NO KEY UPDATE`, `SHARE`,
`KEY SHARE`) and three wait policies (default, `NOWAIT`, `SKIP LOCKED`) in four
shapes: a filtered base table, an alias with a text parameter, reordered numbered
pagination parameters, and anonymous parameters with locking before pagination.
The final two cases contain multiple locking clauses. Both parameter order and
`OFFSET` before `LIMIT` are intentional regression witnesses.

`concrete.jsonl` contains 50 unchanged public source statements. Their pinned
origins, source kinds, licenses, extraction boundaries, and observed locking
clauses are documented in [CONCRETE_SOURCES.md](CONCRETE_SOURCES.md). The harness
checks their identity and PostgreSQL rendering certificates; it does not invent
catalogs or parameter values for them or execute them.

Run the native harness against PostgreSQL 16 binaries as a non-root user:

```sh
python3 scripts/check_locking_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 -m unittest discover -s scripts -p test_locking_cli.py
```

The harness uses a disposable cluster and performs:

- 50 full-contract checks with the authored catalog and parameter types.
- Identity and PostgreSQL checked rendering plus canonical rechecks for all
  100 sources.
- 50 explicit SQLite input rejections: 38 reach its row-locking diagnostic;
  the other 12 reach its earlier `OFFSET`-before-`LIMIT` diagnostic. These are
  parser rejections, not successful SQLite rendering certificates.
- 200 PostgreSQL `PREPARE`/`EXECUTE` observations: the synthetic source and its
  canonical rendering, each on empty and populated tables. Declared return
  types and exact ordered rows must match. Each case rolls back its savepoint
  to release acquired locks.
- Eight synchronized two-session observations. A persistent owner first
  confirms it locked row 1. Both source and canonical `NOWAIT` queries must
  return SQLSTATE `55P03`; both `SKIP LOCKED` queries must omit that row.
  After an acknowledged owner rollback, all four queries must return every
  row. Every wait is bounded. Statement timeout remains distinct from the
  expected lock error, so accidentally removing `NOWAIT` cannot pass by
  timing out.

These are finite native observations. They do not prove concurrency semantics,
lock-acquisition timing, general semantic equivalence, or validity of arbitrary
application schemas. PostgreSQL describes the tested syntax and lock-release
behavior in its [SELECT documentation](https://www.postgresql.org/docs/16/sql-select.html)
and [explicit locking documentation](https://www.postgresql.org/docs/16/explicit-locking.html).
