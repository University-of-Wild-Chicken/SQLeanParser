# Pinned application SQL sources

These fixtures contain **172 distinct SQL constants from application code**:
56 from River's PostgreSQL driver and 116 from Temporal's PostgreSQL persistence
plugin. They are not synthesized variations or database regression-test inputs.
The population includes SELECT and mutation/administration statements.

## Provenance and licensing

- **River**: [`riverqueue/river` at `1354a059d7cbe5790acc7a755a2ab7ac6d2f1ed8`](https://github.com/riverqueue/river/tree/1354a059d7cbe5790acc7a755a2ab7ac6d2f1ed8/riverdriver/riverpgxv5/internal/dbsqlc).
  Sources are the PostgreSQL driver's committed `*.sql.go` files, with the
  corresponding `*.sql` files retained for provenance. The generated files
  identify SQLC **v1.31.1**. River source and the extracted River records retain
  **MPL-2.0** attribution; the upstream license is copied verbatim to
  [licenses/river-LICENSE.txt](licenses/river-LICENSE.txt).
- **Temporal**: [`temporalio/temporal` at `b7bc978d1040afe2dcbc68ecfe8b228ae198e0b6`](https://github.com/temporalio/temporal/tree/b7bc978d1040afe2dcbc68ecfe8b228ae198e0b6/common/persistence/sql/sqlplugin/postgresql).
  Sources are non-test Go files in the PostgreSQL persistence plugin, including
  its driver/session subdirectories. The code carries the **MIT** license;
  upstream copyright and license text are copied verbatim to
  [licenses/temporal-LICENSE.txt](licenses/temporal-LICENSE.txt).

[application_sources.json](application_sources.json) pins commits, every
vendored source-file SHA256, both license-file hashes, and expected extraction
counts. Each JSONL record identifies its upstream file, constant, source line,
commit URL, license, decoded SQL, and original Go constant expression.

## Extraction and exclusions

The extractor lexes Go comments and string literals without executing Go.
It decodes string constants, literal concatenation, and references to string
constants in the same file. Concatenation matters because SQLC represents
backticks in SQL comments as separate quoted Go literals. The resulting SQL
bytes, comments, whitespace, and placeholders are preserved; no parameter
substitution or SQL rewrite is performed.

River's parameter mapping comes from its committed SQLC output. The extractor
does not guess a mapping for source `@name` or `sqlc.arg` expressions. Template
comments and their upstream fallback bodies are retained and listed in each
record's `template_markers`. These are unexpanded source constants, not the
exact SQL sent after runtime schema/WHERE/ORDER BY substitution. In particular,
template markers inside quoted string data remain string data. River's
vendored `rivershared/sqlctemplate/sqlc_template.go` documents and implements
that separate runtime expansion, which this syntax-only corpus does not run.

River contributes 31 SELECT, 10 INSERT, 8 UPDATE, and 7 DELETE statements.
Its remaining named SQLC command, `JobInsertFastManyCopyFrom`, uses the binary
copy API and has no submitted query-string constant; its raw source and
exclusion reason appear in [river_extraction.json](river_extraction.json).

Temporal contributes 65 SELECT, 9 INSERT, 7 UPDATE, 33 DELETE, and 2 CREATE TABLE
statements. [temporal_extraction.json](temporal_extraction.json) accounts for all
196 inspected constants: 116 included and 80 excluded. Exclusions retain
raw decoded SQL or the undecoded source expression and a reason. They include
non-statement constants, base/part fragments, actual `fmt.Sprintf` templates,
named sqlx bindings, unsupported constant expressions, and raw-parser
rejections. No values are invented to complete these fragments.

Every included statement passes **pglast 7.21's PostgreSQL 17 raw grammar**
as exactly one statement. This is syntax evidence only: queries are not
executed, application schemas are not loaded, and type resolution, effects,
semantics, runtime template variants, and PostgreSQL 16 compatibility are not
established by this extraction.

## Reproduction

With the pinned pglast environment:

```sh
python scripts/extract_application_corpus.py --check
```

The command verifies all vendored hashes and reproduces both JSONL populations
and both extraction ledgers byte for byte. Add `--fetch` to download the same
commit-pinned upstream bytes and verify their hashes before extraction. Omitting
`--check` writes the deterministic output files. The extractor never executes
downloaded source or SQL.
