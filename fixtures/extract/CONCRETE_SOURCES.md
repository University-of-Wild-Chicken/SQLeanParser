# Unchanged temporal EXTRACT source statements

`concrete.jsonl` contains 50 distinct whole SELECT statements copied unchanged
from PostgreSQL's own engine regression tests, at commit
[`f0595c3d839debdb140903621c1b44a4f4d86256`](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256)
on the pinned PostgreSQL 16 branch. These are engine tests, not application
traffic or generated variants. The existing
[PostgreSQL license copy](../extended_types/licenses/postgres-COPYRIGHT.txt)
and six existing source snapshots are reused; no new upstream license is needed.

The source distribution is:

- 22 statements from [`date.sql`](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/test/regress/sql/date.sql).
- Six from [`time.sql`](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/test/regress/sql/time.sql).
- Nine from [`timetz.sql`](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/test/regress/sql/timetz.sql).
- Two from [`timestamp.sql`](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/test/regress/sql/timestamp.sql).
- Two from [`timestamptz.sql`](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/test/regress/sql/timestamptz.sql).
- Nine from [`interval.sql`](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/test/regress/sql/interval.sql).

Every selected query is a single source-free, unaliased EXTRACT projection over
an explicit temporal string literal/cast, without parameters or an external
catalog. There are 22 distinct field spellings, including date calendar fields,
fractional-second fields, and time-zone fields. Two statements retain
`DATE 'infinity'`: one extracts DAY and one EPOCH. Their differing NULL/Infinity
behavior is deliberate. Boundary-year statements include BC dates and negative
intervals; source text and whitespace are never rewritten.

The finite discovery pass found 109 EXTRACT-bearing statements in these files.
It retained 85 distinct direct source-free temporal-literal candidates before
selecting these 50. It excluded 16 upstream unsupported field/type examples,
three table-dependent projections, two CURRENT_DATE expressions, one interval
arithmetic/power expression, and two case/whitespace duplicate queries. None of
the selected 50 needs interval field qualifiers such as `YEAR TO MONTH`, interval
arithmetic, aliases, or another new syntax factor. These discovery categories do
not turn the source-format observer into a PostgreSQL semantic analyzer.

`concrete_sources.json` binds complete source-file and license hashes, exact
statement indices and offsets, each SQL hash, and the syntax observations.
`observed_syntax.temporal_extractions` records the normalized unit token,
explicit declared temporal type, and literal text. It does not evaluate that
text or borrow upstream expected results. `parameter_types` remains null and
application schema validity remains unclaimed; the separately registered full
static certificates use the actual empty catalog and environment for this fixed
source-free population. Their output types, labels, and nullability belong to
the independent contract tests, not this extraction metadata.

All 50 original queries are checked by the PostgreSQL grammar replay and the
identity/PostgreSQL rendering boundary. Source queries and upstream programs
are never executed. Native PostgreSQL execution expectations use the separate
authored `synthetic.json` population. Optional extraction `--oracle` checks
the finite syntax observations with pglast 7.21 (PostgreSQL 17.7); the project's
independent pinned grammar replay targets PostgreSQL 16.

```sh
python3 scripts/extract_factor_corpus.py --factor extract --check
python3 -m unittest discover -s scripts -p 'test_extract_extraction.py'
```
