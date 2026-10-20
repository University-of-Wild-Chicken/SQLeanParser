# Concrete extended-type statements

`concrete.jsonl` contains 50 unchanged complete SELECT statements: 20 shipping
Hatchet application constants, one sqlc compiler regression, and 29 PostgreSQL
engine regression statements. Each record labels its source kind; regression
statements are not presented as application traffic.

The new type families represented are SMALLINT/INT2, fixed-length CHAR, DATE,
TIME, TIMETZ, TIMESTAMP, TIMESTAMPTZ, INTERVAL, UUID, JSON, JSONB, and BYTEA.
Existing integer, real, text, boolean, and numeric types also appear in context.
Forms include postfix casts, `CAST`, typed string literals, `CHAR(n)`,
`TIMESTAMP(2) WITHOUT TIME ZONE`, and `TIMESTAMP WITH TIME ZONE`. The selection
excludes arrays, user-defined types, interval field qualifiers, and dependencies
on new general functions or operators.

Pinned upstream sources:

- [Hatchet application query constants](https://github.com/hatchet-dev/hatchet/tree/392e7c472221cdab235cca674640e98f904e1ea0/pkg/repository/sqlcv1),
  commit `392e7c472221cdab235cca674640e98f904e1ea0`, MIT.
- [sqlc nullable-cast regression](https://github.com/sqlc-dev/sqlc/blob/0f1602fe1a4b780336e3e878dde720892fd8578d/internal/endtoend/testdata/cast_null/pgx/v5/query.sql),
  commit `0f1602fe1a4b780336e3e878dde720892fd8578d`, MIT.
- [PostgreSQL 16 regression sources](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256/src/test/regress/sql),
  commit `f0595c3d839debdb140903621c1b44a4f4d86256`, resolved from
  `REL_16_STABLE`, PostgreSQL License.

The selected upstream files are copied unchanged, including their original
headers. License texts are retained in `licenses/`. `concrete_sources.json`
pins every source-file hash, license hash, Go constant selector or complete
SQL statement span, and selected SQL hash. Individual records provide the
original file, line, commit URL, source kind, SQL text, and observed type
families. No renamed, repaired, or parameter-substituted query is counted.
Hatchet uses its shipped sqlc-generated constants, so upstream parameter
numbering is preserved rather than reconstructed from sqlc macros.

`observed_parameter_slots` records only the slot identities occurring in source.
`parameter_types` is explicitly null; application catalog/type validity is not
claimed. There are no invented production parameter bindings or schemas.
These source queries are not executed by the extractor, and surrounding
upstream test setup, timezone, DateStyle, tables, or session settings are not
silently imported.

Reproduce and verify the exact population offline:

```sh
python3 scripts/extract_extended_type_corpus.py --check
```

Also verify each statement with the pinned raw PostgreSQL grammar oracle:

```sh
python3 scripts/extract_extended_type_corpus.py --check --oracle
```

The optional oracle is pglast 7.21 / PostgreSQL 17.7 raw grammar. It checks one
SELECT, the observed type families, absence of arrays/user-defined type
dependencies, and parameter slots. It does not certify application schemas,
runtime literal conversion, result semantics, or the entire PostgreSQL 16
grammar. PostgreSQL 16 is the pinned engine-source and native-CI target; native
execution evidence belongs to the separate integration tests.
