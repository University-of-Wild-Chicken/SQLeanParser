# External PostgreSQL corpus audit — 2026-10-20

SQLean parsed **161 of 276 source statements** and rejected **115**. PostgreSQL
17.7's raw parser accepted all 276. There were no timeouts, process failures, or
multi-statement extraction errors. After exact SQL deduplication, the result is
**145 accepted / 115 rejected out of 260 distinct statements**.

Start with the [complete rejection catalog](failures.md). It contains every
rejected statement, the exact SQL submitted to SQLean, its diagnostic, candidate
feature tags, and a link to its pinned upstream source. The
[machine-readable results](results.jsonl) also include accepted queries.
[Audit metadata](audit.json) records versions and input, executable, source, and
result hashes.

This is a source-query corpus from real software plus established benchmark
workloads. It is **not production traffic**, and query counts do not represent
execution frequency. No SQL was executed. Acceptance means the syntax API
returned an AST; it does not certify schema/type validity, execution behavior,
or faithful interpretation of every PostgreSQL construct.

## Sources and selection

- [River](https://github.com/riverqueue/river/tree/1354a059d7cbe5790acc7a755a2ab7ac6d2f1ed8),
  a background job queue: **56 queries, 8 accepted / 48 rejected**.
  Uses the committed PostgreSQL SQLC output, preserving the application's `$n`
  parameter mapping. These are **unexpanded upstream constants**: template
  markers, including markers inside string data, remain intact. Runtime schema,
  predicate, ordering, and string substitutions are not enumerated. A binary
  `:copyfrom` command is recorded separately because it has no submitted SQL string.
- [Temporal](https://github.com/temporalio/temporal/tree/b7bc978d1040afe2dcbc68ecfe8b228ae198e0b6),
  its PostgreSQL persistence implementation: **116 queries, 68 accepted /
  48 rejected**. Extracts complete Go string constants, including same-file
  constant concatenation. Eighty other constants are listed with dispositions:
  fragments, format templates, named bindings, unsupported constant expressions,
  and PostgreSQL parser rejections. These are not counted as SQLean syntax gaps.
- [BenchBase](https://github.com/cmu-db/benchbase/tree/33c00473807ebd49304d114a6d769d2d2b2bbb34),
  six workload families: **104 templates, 85 accepted / 19 rejected**.
  These are benchmark workloads, not captured application traffic. All 18
  applicable PostgreSQL overrides are applied. JDBC `?` markers outside quoted
  regions/comments become `$1`, `$2`, etc.; original SQL and transformations are
  retained. Two Twitter limits use documented upstream defaults. The TPC-H Q15
  CREATE VIEW entry is a bind template; raw-parser acceptance does not mean
  PostgreSQL would allow its parameters at execution.

BenchBase breakdown:

- SmallBank: 21 accepted / 0 rejected.
- TATP: 12 / 0.
- TPC-C: 31 / 2.
- TPC-H: 9 / 15, including Q15's CREATE VIEW and DROP VIEW statements.
- Twitter: 6 / 1.
- YCSB: 6 / 1.

The application portion alone is **76 accepted / 96 rejected out of 172**.
Across the whole corpus there are 167 SELECT, 36 UPDATE, 43 DELETE, 26 INSERT,
and 4 DDL statements. Sixteen exact duplicates are retained as distinct
BenchBase procedure statements, explicitly marked `duplicate_of` in the
results. All 115 rejections are distinct SQL strings.

The [fixture directory](../../../fixtures/external_postgresql/) contains
provenance, extraction ledgers, and upstream license copies. River SQL remains
under MPL-2.0, Temporal under MIT, and BenchBase under Apache-2.0. Extracted SQL
and reproduced excerpts retain their upstream licensing; they are not
relicensed as SQLean implementation code.

## Syntax work suggested by the evidence

These counts are **overlapping feature occurrences in rejected queries**,
identified using PostgreSQL AST nodes (and lexer tokens for special spellings).
They are not exclusive first-cause classifications or predicted improvement
counts. A query can require several changes. Supported constructs such as
comma-FROM also receive contextual tags; a tag alone is not a claim of missing
support.

1. **Expression-valued LIMIT/OFFSET — 38 rejected queries.**
   [Temporal endpoint pagination](failures.md#q-b7b648ddea76) is a small,
   direct example:

   ```sql
   SELECT id, data, data_encoding, version
   FROM nexus_endpoints WHERE id > $1 ORDER BY id LIMIT $2
   ```

   SQLean reports `expected nonnegative integer`. The current AST stores
   pagination as natural-number literals; adding parameter/expression forms
   needs an AST change as well as grammar support.

2. **General functions, conditional expressions, and types.**
   General function calls occur in 35 rejected queries, CASE/COALESCE-like
   expressions in 31, and extended types in 38. Examples include
   [River advisory locks](failures.md#q-9c7008643f14),
   [CASE for table existence](failures.md#q-836c557ac02a), and casts to
   `timestamptz`, `jsonb`, arrays, and application enum types. TPC-H also
   exposes date/interval literals and date/string functions. Supporting generic
   calls must preserve function names and argument syntax without treating
   arbitrary functions as statically verified.

3. **Concurrency clauses — 26 rejected queries.**
   [YCSB read-modify-write](failures.md#q-186db28a7da3) isolates `FOR UPDATE`.
   River needs `FOR UPDATE SKIP LOCKED`; Temporal also uses row locking.
   Preserve lock strength, target relations, and wait policy explicitly.

4. **Arrays, quantified comparisons, and row comparisons.**
   Array/subscript constructs appear in 22 rejected queries, quantified
   comparisons in 11, and row constructors in 7.
   [River migration deletion](failures.md#q-d3c883158632) uses
   `version = any($1::bigint[])`.
   [Temporal task pagination](failures.md#q-2980e901565a) uses
   `(pass, task_id) >= ($3, $4)`. Extended operators, including JSON and bitwise
   operations, appear in 8 rejected queries.

5. **CTEs around mutations and joined mutations.**
   Six rejected queries contain data-modifying CTEs, five place WITH before
   top-level DML, seven contain UPDATE FROM, and two contain DELETE USING.
   [River job cancellation](failures.md#q-dda613cadd82) combines several of
   these with functions, CASE, types, and locks. Existing SELECT-only CTE
   support is insufficient for this transactional pattern.

6. **Qualified relations and remaining forms.**
   Six rejected queries use schema-qualified relations, including
   [Temporal catalog lookup](failures.md#q-e8b604cc4e3f).
   [River scheduling](failures.md#q-9ff0847c5642) supplies a real window-function
   example. [Twitter insertion](failures.md#q-94ebd18a8752) needs DEFAULT in
   VALUES. TPC-H Q15 supplies CREATE/DROP VIEW. This corpus is too small in
   windows and DDL to claim comprehensive coverage of either family.

Before expanding grammar, address the accepted-but-misinterpreted forms below.
Then pagination and locking are focused additions; functions, conditional
expressions, and richer types are shared dependencies for larger River and
TPC-H queries. Keep newly accepted syntax in the syntax tier until the
corresponding checking/rendering contracts cover it.

## Acceptance can hide interpretation defects

[Eight supplementary synthetic probes](interpretation-probes.json) are
separate from the 276 corpus statements. All eight parse, but seven expose
changes to PostgreSQL special forms after SQLean serialization:

- `SELECT CURRENT_DATE;` becomes `SELECT "current_date";`: a value function
  becomes a column reference. The same issue affects the tested session/time
  value keywords.
- `SELECT 1 ISNULL;` becomes `SELECT 1 AS "isnull";`, and
  `SELECT NULL NOTNULL;` becomes `SELECT NULL AS "notnull";`.
- `SELECT * FROM ONLY users;` becomes a query of table `"only"` with alias
  `"users"`. UPDATE ONLY and DELETE FROM ONLY similarly change the target
  relation and lose the inheritance restriction.
- The comma-FROM control preserves its relation references when SQLean renders
  an explicit CROSS JOIN.

These are focused raw-AST observations, not a general SQL equivalence test.
They nevertheless expose concrete distinctions that the AST must preserve.
The SELECT checked renderer certifies reconstruction of SQLean's parsed AST;
it does not prove that the initial parse faithfully interpreted PostgreSQL.
The DML probes use the ordinary, unchecked `--postgres` renderer and are
identified separately in the evidence. None of the 161 accepted external
queries triggered this limited special-form watchlist; that does not establish
their semantic equivalence.

## Reproduce

From the repository root:

```sh
lake build --wfail sqlean
python3 -m venv .lake/corpus-venv
.lake/corpus-venv/bin/pip install -r scripts/requirements-corpus.txt
.lake/corpus-venv/bin/python scripts/extract_application_corpus.py --check
python3 scripts/extract_benchbase_corpus.py --check
.lake/corpus-venv/bin/python scripts/audit_postgresql_corpus.py
.lake/corpus-venv/bin/python scripts/probe_postgresql_interpretation.py \
  --output .lake/external-postgresql-audit/interpretation-probes.json
python3 -m unittest discover -s scripts -p 'test_*.py'
```

The replay writes to `.lake/external-postgresql-audit/`, preserving this
baseline. Compare its `results.jsonl` with the checked-in results to see which
specific queries changed. It uses `sqlean --assurance syntax` once per
statement, a five-second timeout, and four independent child processes.
Expected syntax rejections are measured outcomes; timeouts, unexpected
process/protocol failures, and multi-statement extraction errors return
nonzero. PostgreSQL-rejected inputs are reported outside the valid-SQL
denominator.

The optional oracle is pinned to **pglast 7.21 / PostgreSQL 17.7**. It uses the
PostgreSQL raw parser without a server, schemas, bound values, or execution.
This is separate from the project's PostgreSQL 16 execution tests and Lean
proof tiers. Extraction/harness unit tests run in existing offline CI;
the external syntax replay is an explicit developer audit, not a new network
dependency for normal builds.
