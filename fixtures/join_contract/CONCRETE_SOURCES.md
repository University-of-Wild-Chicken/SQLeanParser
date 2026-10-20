# Base-table JOIN source corpus

`concrete.jsonl` contains 50 distinct, unchanged, whole SELECT statements:
one shipping Hatchet application constant, 19 sqlc compiler regression inputs,
and 30 PostgreSQL engine regression inputs. The nested join trees contain
6 CROSS, 21 INNER, 30 LEFT, 5 RIGHT, and 6 FULL join nodes. Several statements
contain more than one node.

The selections use named relations, optional table aliases, `ON` conditions
(or no condition for CROSS), nested join chains, qualified and unqualified
columns, wildcard projections, filtering, sorting, and previously supported
COALESCE expressions. The selected sources contain no USING, NATURAL, derived
table, table-function, CTE, aggregate, or subquery dependency. Named relations
are syntax observations; whether an application name resolves to a table,
view, or foreign table requires its real catalog.

Pinned sources and licenses:

- [Hatchet](https://github.com/hatchet-dev/hatchet/tree/392e7c472221cdab235cca674640e98f904e1ea0):
  commit `392e7c472221cdab235cca674640e98f904e1ea0`, MIT.
- [sqlc](https://github.com/sqlc-dev/sqlc/tree/0f1602fe1a4b780336e3e878dde720892fd8578d):
  commit `0f1602fe1a4b780336e3e878dde720892fd8578d`, MIT.
- [PostgreSQL REL_16_STABLE](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256):
  commit `f0595c3d839debdb140903621c1b44a4f4d86256`, PostgreSQL License.

`concrete_sources.json` pins 15 source files and all three license files by
SHA-256. Existing vendored snapshots are reused where available; additional
sqlc inputs reside under `sources`. Every selection is one whole Go constant
or a complete SQL statement span. Each JSONL record retains the source text,
line/link, source kind, placeholder slots, and an ordered join tree with
original relation names and aliases. No identifier, literal, parameter, or
SQL clause is rewritten. Normalized duplicates cannot increase the count.

These sources are checked for parsing and exact checked rendering only.
They are **never executed** by corpus verification. Application catalogs
and parameter types are not invented. Presence in this corpus does not
establish name resolution, static validity, query planning, or execution
success in an application's real environment.

Reproduce from local pinned inputs:

```sh
python3 scripts/extract_factor_corpus.py --factor join_contract --check
python3 -m unittest discover -s scripts -p test_factor_extraction.py
```

With optional `pglast==7.21`, add `--oracle` to verify one whole SELECT,
parameter slots, dependency observations, and the exact nested join tree.
That raw-parser oracle uses PostgreSQL 17.7; PostgreSQL source files are pinned
to version 16. The independent PostgreSQL 16 grammar replay also includes all
50 statements. Neither grammar oracle executes source SQL.
