# Unchanged named-argument source corpus

This population contains 50 distinct, unchanged whole SELECT statements:
42 PostgreSQL regression statements and 8 sqlc compiler regression statements.
They are public test sources, not production traffic. Source programs and SQL
are never executed by extraction or by the native verification harness.

The PostgreSQL revision is
[`f0595c3d839debdb140903621c1b44a4f4d86256`](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256);
the sqlc revision is
[`0f1602fe1a4b780336e3e878dde720892fd8578d`](https://github.com/sqlc-dev/sqlc/tree/0f1602fe1a4b780336e3e878dde720892fd8578d).
The PostgreSQL and MIT license copies, source files, whole-statement offsets,
line numbers, and SHA256 hashes are recorded in `concrete_sources.json`.
Existing pinned snapshots and licenses are reused; the sqlc query files and
generated interface are retained as additional unchanged source evidence.

The corpus exercises 87 named arguments: 51 `=>` and 36 `:=` occurrences.
Twenty calls mix a positional prefix with named arguments. Written order is
preserved, including `plus(b => $2, a => $1)`, reordered named/default arguments,
adjacent unary signs, block comments, and a line comment immediately after `=>`.
The 11 routines are `make_interval`, `dfunc`, `concat_lower_or_upper`, `plus`,
`table_args`, `parse_ident`, `jsonb_set_lax`, `jsonb_path_match`,
`jsonb_path_query_first`, `jsonb_path_query_array`, and `jsonb_path_exists`.
The selected `dfunc` cases have the corresponding polymorphic function
declaration in the original PostgreSQL file; no application catalog is inferred
from it. Known error cases, sqlc macro calls, FROM functions, window calls, and
other later syntax dependencies were excluded before fixing the population.

`observed_syntax.named_calls` records function spelling and byte location,
ordered argument names (`null` denotes a positional argument), and the ordinal,
name, source notation, and byte location of each named argument. These are
syntactic observations. They do not resolve overloads, associate defaults,
reorder arguments, infer result types, or evaluate string contents. UTF-8 byte
locations and the source spelling are checked independently. The observer is a
finite recognizer for these unqualified, unmodified call sources; it is not a
general PostgreSQL lexer or static validator.

Forty-six statements are structurally source-free; four contain numbered
parameters. This flag does not imply full static validity. The independently
registered full-certificate population consists of seven `make_interval`
statements:

- PostgreSQL `src/test/regress/sql/interval.sql`, statement indices 320–324:
  five closed queries using literal arguments and omitted defaults.
- sqlc `internal/endtoend/testdata/func_args/pgx/v5/query.sql`, statement 1:
  `SELECT make_interval(secs => $1);`, with declared input `double precision`.
- The same sqlc file, statement 2:
  `SELECT make_interval(days => $1::int);`, with declared input `integer`.

The two input declarations are backed by the pinned generated
[`MakeIntervalSecs` and `MakeIntervalDays` methods](https://github.com/sqlc-dev/sqlc/blob/0f1602fe1a4b780336e3e878dde720892fd8578d/internal/endtoend/testdata/func_args/pgx/v5/go/query.sql.go).
Their actual parameter types are `float64` and `int32`, respectively. Extraction
checks the generated constant against the selected SQL, the complete method
signature prefix, and the `QueryRow` forwarding call. It records the interface
file hash, source link, method, and parameter spelling. Only these two records
receive `parameter_types`; no parameter values or relation catalog are invented.
The certificate is conditional on those declared input types. Forty-three other
records receive checked identity/PostgreSQL rendering, with no full validity
claim for their unregistered routines or unspecified inputs.

The original audit's three River `make_interval` failures are DML statements.
This SELECT corpus does not turn their whole-statement validity into a verified
claim. Source values and source function results are not native execution
oracles; native tests use separately authored fixtures.

Reproduce the fixed sources without network access:

```sh
python3 scripts/extract_factor_corpus.py --factor named_arguments --check
python3 -m unittest discover -s scripts -p 'test_named_arguments_extraction.py'
```

With the separately installed, pinned pglast 7.21 dependency, add `--oracle` to
check the original statements and their syntactic observations again.
