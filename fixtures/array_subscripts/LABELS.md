# Authored output-label descriptor observations

`labels.json` contains 87 authored SELECT probes, separate from the 50
external source statements and the 50 synthetic value/type cases. Its fields
are exactly `sql`, `name`, and `type`. SQL text and captured descriptors are
preserved without rewriting.

The descriptors were captured on PostgreSQL
`16.15 (Ubuntu 16.15-0ubuntu0.24.04.1)` and independently reproduced on the
same version on 2026-10-20. Each source query was used in a temporary view
definition. The observation reads the first output column's `attname` and
`format_type(atttypid, atttypmod)` from `pg_attribute`. Defining and describing
the view invokes PostgreSQL's analyzer; the SELECT is not evaluated.

The captured file SHA-256 is
`d219e4a8fd06e779bd0f1fb1edc15b093e3ffa4ccb04841fda27a67d4c512a83`.
There are 35 pairs of scalar-cast and subscripted-array-cast probes, followed
by 17 expressions combining casts, columns, CASE, COALESCE, arrays, and
nested subscript groups. The observations include distinctions such as
`int4` versus `integer`, `bpchar` versus `char`, labels inherited from named
columns, and labels selected from CASE's ELSE expression. Type descriptors
retain numeric, character, and temporal modifiers.

The subscript CLI checker compares source and rendered native descriptors
for 85 supported probes with these observations, and separately compares
the CLI's reported output name. The two bare `FLOAT` / `FLOAT[]` spellings
are preserved in the 87-query capture but currently receive explicit typed
parser rejection checks. Their native descriptors remain recorded without
claiming typed-parser support. Dropping, reordering, renaming, or changing a
checked descriptor must fail. Full static type and nullability contract
checks belong to the other synthetic fixtures; this label population does
not replace them.
These are finite observations for the recorded PostgreSQL version, not a
claim about all output labels or execution semantics.

Reproduce the integrated check with the built CLI and a private local
PostgreSQL 16 cluster:

```sh
python3 scripts/check_array_subscripts_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 -m unittest discover -s scripts -p test_array_subscript_labels.py
```
