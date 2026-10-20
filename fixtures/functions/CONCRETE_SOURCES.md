# Ordinary function-call source corpus

`concrete.jsonl` contains 50 distinct, unchanged, whole SELECT statements:
20 shipping Hatchet application constants, 10 sqlc compiler regression inputs,
and 20 PostgreSQL engine regression inputs. There are 40 distinct ordinary
function names. This is a finite syntax and rendering population; its presence
does not assert that every function has an independent validity specification.

The selections exercise unqualified function names with positional arguments,
including zero arguments, nested calls, arguments containing casts, and calls
in SELECT, WHERE, GROUP BY, HAVING and ORDER BY. Qualified names, named and
variadic arguments, window clauses, ordered aggregate arguments, and table
functions belong to later factors. COUNT/SUM/AVG/MIN/MAX can also appear as
previously supported aggregate syntax.

Pinned sources and licenses:

- [Hatchet](https://github.com/hatchet-dev/hatchet/tree/392e7c472221cdab235cca674640e98f904e1ea0):
  commit `392e7c472221cdab235cca674640e98f904e1ea0`, MIT.
- [sqlc](https://github.com/sqlc-dev/sqlc/tree/0f1602fe1a4b780336e3e878dde720892fd8578d):
  commit `0f1602fe1a4b780336e3e878dde720892fd8578d`, MIT.
- [PostgreSQL REL_16_STABLE](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256):
  commit `f0595c3d839debdb140903621c1b44a4f4d86256`, PostgreSQL License.

`concrete_sources.json` pins every source file and license by SHA-256 and
selects either a complete Go constant or an exact complete SQL statement span.
Shared snapshots are reused from `extended_types` or `factor_sources`;
the license texts reside in `extended_types/licenses`. JSONL records include
the original SQL, exact source line/link, source kind, function observations
and placeholder slots. No SQL identifiers, literals or parameters are rewritten.
Case/whitespace-equivalent duplicates cannot increase the count.

Some SELECT calls invoke application partition maintenance or advisory locks.
These statements are **never executed** by this corpus check. Application
schemas and parameter types are not invented. PostgreSQL raw parsing establishes
syntax acceptance only; it does not establish function existence, overload
resolution, absence of side effects or successful execution.

Reproduce from local hash-pinned inputs:

```sh
python3 scripts/extract_factor_corpus.py --factor functions --check
python3 -m unittest discover -s scripts -p 'test_factor_extraction.py'
```

With the pinned optional `pglast==7.21` dependency, add `--oracle` to recheck
one whole SELECT, function/dependency observations and parameter slots.
That raw-parser oracle uses PostgreSQL 17.7 grammar; the source snapshot itself
is PostgreSQL 16. These are separate provenance and oracle facts.
