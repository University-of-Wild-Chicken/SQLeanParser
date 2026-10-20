# SQLean

The planned **0.0.1-alpha** release is held until full PostgreSQL contract
coverage is complete. APIs and proof profiles remain experimental; the
[coverage and release checklist](docs/releases/0.0.1-alpha.md) records the
current assurance levels and outstanding obligations.

A Lean 4 SQL parser with public AST interfaces, canonical SQL rendering, and proof-carrying static validation. It supports SELECT with joins, grouping, aggregates, derived tables, ordinary and recursive CTEs, UNION/UNION ALL, and queries without FROM, plus single-table INSERT, UPDATE, and DELETE. PostgreSQL extensions include DISTINCT ON, aggregate FILTER, casts, LIKE/ILIKE, IN/BETWEEN, NULLS ordering, and mutation RETURNING. The advanced statement interface also supports correlated IN/EXISTS and scalar subqueries, LATERAL, USING/NATURAL joins, INTERSECT/EXCEPT, ON CONFLICT, INSERT SELECT, NULL, exact decimal/exponent literals, typed parameters, and table DDL. The project uses Lean **4.34.0**, with no external Lean package dependencies.

The [SELECT validity contract draft](docs/SELECT_validity_contract.md) now has a
first implementation with explicit assurance tiers. The independent proof tier
currently covers source-free SELECTs, base tables and nested non-LATERAL
derived tables joined with CROSS or INNER/LEFT/RIGHT/FULL JOIN using ON,
USING or NATURAL matching. The broader SELECT
family and mutation/DDL syntax remain available through the existing APIs and
the expanded executable-check tier. This is an initial contract milestone,
not a claim that the complete draft has been implemented.

The full PostgreSQL target is pinned to **16.15**, commit
`f0595c3d839debdb140903621c1b44a4f4d86256`. A separate
[grammar API](fixtures/postgresql_grammar/README.md) imports every upstream
context-free production and returns a concrete syntax tree with an independent
Lean derivation. Its UTF-8 lexer retains exact source spelling and byte offsets,
and its source renderer carries an exact reconstruction proof. This API is
available as `SQLean.PostgresGrammar.parse`, `sqlean --postgres-grammar`, and
`sqlean_pg_grammar` (including JSONL batch input). The report explicitly keeps
PostgreSQL's C semantic actions and static SQL validity unchecked. Full grammar
data does not expand the typed AST or certify every PostgreSQL statement.

The [v0.27 keyword-function increment](docs/keyword-functions-contract-v0.27.md)
admits PostgreSQL keyword names in ordinary function calls, including `LEFT`
and `RIGHT`, while retaining their restrictions as bare identifiers.
Two exact TEXT/INTEGER signatures preserve nullability and output labels.
Fifty authored queries and 49 unchanged source queries receive full
certificates; the catalog-dependent River example receives rendering
certificates. The [industrial replay](docs/corpus/keyword-functions-v0.27/README.md)
accepts 257 of 276 statements. A recorded source/native-binary discrepancy
for `RIGHT` at the minimum INTEGER count is excluded from portable value
expectations.

The [v0.26 named-argument increment](docs/named-arguments-contract-v0.26.md)
adds `=>` and `:=` function arguments while retaining their lexical order.
Independent binding rules check positional prefixes, exact names, unique
slots and declared defaults. `make_interval` has a complete seven-slot
declaration; unregistered named routines retain rendering-only assurance.
The factor includes fifty authored queries and fifty unchanged PostgreSQL/sqlc
queries. Seven source certificates include two parameterized queries whose
input declarations come from pinned generated sqlc interfaces.
The [industrial replay](docs/corpus/named-arguments-v0.26/README.md) accepts
256 of 276 statements; the three newly accepted River statements remain in
the broader DML assurance tier.

The [v0.25 context-value increment](docs/context-values-contract-v0.25.md)
adds seven SQL context forms, six session functions and PostgreSQL's exact
`NAME` type. Directional casts, NAME comparisons and arrays retain native
type identities; context values retain their distinct output labels and
session-dependent nullability. Fifty authored queries and 13 unchanged source
queries receive full certificates, while all 50 sources receive rendering
certificates. Native checks also exercise role changes, session authorization
and empty search paths. The [industrial replay](docs/corpus/context-values-v0.25/README.md)
accepts 253 of 276 statements.

The [v0.24 JSONB existence increment](docs/json-existence-contract-v0.24.md)
adds `?`, `?|` and `?&` with exact native signatures, outer-NULL propagation,
and the geometric-overload ambiguity of two unknown `?|` operands.
Fifty authored queries and 44 unchanged source queries receive full static
and rendering certificates; six catalog-dependent sources retain rendering
certificates. Anonymous placeholders are distinguished from question operators
by their syntactic role, preserving compact templates and numbered bindings.
The [industrial replay](docs/corpus/json-existence-v0.24/README.md) accepts
249 of 276 statements, including River's `JobGetCancelRequested`.

The [v0.23 schema-qualified name increment](docs/qualified-names-contract-v0.23.md)
adds separate schema, table and column components, exact relation identities,
and explicit unqualified visibility metadata. Relation lookup precedes column
lookup, aliases hide original paths, and row-lock targets retain PostgreSQL's
ordered selection rule. Fifty authored queries receive full static and
rendering certificates. Fifty unchanged PostgreSQL, sqlc and Hatchet queries
receive rendering certificates; their application catalogs are not invented.
Database-qualified paths, dynamic search-path resolution, `pg_temp` alias
resolution and composite whole-row typing remain explicit coverage gaps.
The [industrial replay](docs/corpus/qualified-names-v0.23/README.md) accepts
248 of 276 statements and records the remaining 28 syntax rejections.

The [v0.22 SUBSTRING increment](docs/substring-contract-v0.22.md)
adds all five SQL-standard keyword forms and six concrete TEXT/BYTEA
declarations, including regex extraction. The contract distinguishes
FOR-only's explicit INTEGER conversion from positional overload resolution,
preserves lexical parameter order in reversed FOR/FROM forms, and marks
regex results nullable even for non-NULL inputs. BIT/VARBIT declarations
remain separate type coverage work.
Fifty synthetic queries and 50 unchanged source queries receive full
certificates. Its [industrial replay](docs/corpus/substring-v0.22/README.md)
accepted 246 of 276 statements, including TPC-H Q22.

The [v0.21 interval qualifier increment](docs/interval-fields-contract-v0.21.md)
adds all 13 field/range forms, including `YEAR TO MONTH` and
`DAY TO SECOND(p)`, to literals, casts, array types and catalog declarations.
Fifty synthetic queries and 50 unchanged source queries receive full static
and rendering certificates. Exact field masks and precision survive output
metadata; PostgreSQL parameter declarations erase them until an explicit cast.
Rendering preserves the different interpretations of unknown strings, typed
TEXT and interval arrays. Precision above six remains an explicit coverage
gap because PostgreSQL warns and clamps it.
The [industrial replay](docs/corpus/interval-fields-v0.21/README.md) now accepts
245 of 276 statements, closing seven further TPC-H syntax failures.

The [v0.20 EXTRACT increment](docs/extract-contract-v0.20.md)
adds temporal field extraction with all six PostgreSQL declarations and exact
NUMERIC results. Fifty synthetic queries and 50 unchanged PostgreSQL source
queries receive full static and rendering certificates. Nullable results
account for infinite dates/timestamps; unsupported field units and literal
conversion remain runtime obligations. Decoded field strings retain their
contents through canonical rendering.
Native checks cover 112 value/type observations, 112 SQL NULL observations,
130 exact result descriptors and 18 expected errors. The updated
[industrial corpus replay](docs/corpus/extract-v0.20/README.md) accepts
238 of 276 statements, closing all three original EXTRACT syntax failures.

The [v0.19 array-predicate increment](docs/array-predicates-contract-v0.19.md)
adds array containment (`@>`, `<@`) and overlap (`&&`) with matching element
types and strict outer-NULL propagation. Separate inventories retain the three
generic operators and nineteen supported element-equality mappings. Each
factor has 50 synthetic queries with full static and rendering certificates,
plus 50 unchanged source queries. Eleven of the source queries also receive
full static certificates; 89 table-dependent queries retain rendering-only
assurance. Native checks cover 200 value/type observations, 218 descriptors,
and 18 expected errors.
JSON arrays remain Unsupported because they lack element equality; JSONB
arrays are covered. Ranges and geometric overloads remain separate work.

The [v0.18 array-concatenation increment](docs/array-concatenation-contract-v0.18.md)
adds array concatenation, append and prepend with exact common-element types
and separate NULL rules for their three native declarations. All 50 synthetic
queries and 50 unchanged source queries receive full static and rendering
certificates. Native checks cover 100 value/type observations, 100 SQL NULL
observations, 112 prepared result descriptors and 14 expected runtime errors.
Array dimensions and input conversion remain runtime obligations.

The [v0.17 JSONB containment increment](docs/json-containment-contract-v0.17.md)
adds `@>` and `<@` with exact JSONB signatures, unknown-input disambiguation
and strict NULL propagation. Fifty synthetic queries and 42 of the 50
unchanged source queries receive full static certificates; all 50 sources
receive rendering certificates. Native checks cover 100 value/type observations,
112 result descriptors, two operator declarations and eight expected errors.
Array containment is covered by v0.19; range and geometric containment remain
separate typed-contract work.

The [v0.16 JSON extraction increment](docs/json-extraction-contract-v0.16.md)
adds `->`, `->>`, `#>` and `#>>` with all twelve JSON/JSONB signatures.
Both the 50 synthetic queries and 50 unchanged source queries receive full
static and rendering certificates. Native checks cover 100 value/type
observations, 100 separate SQL NULL observations, 118 result descriptors,
12 operator declarations and ten expected errors. Missing values, JSON null,
SQL NULL and text extraction remain distinct. SQLite JSON translation is
explicitly outside this increment's rendering contract.

The [v0.15 pattern-matching increment](docs/pattern-matching-contract-v0.15.md)
adds independent ILIKE and regex (`~`, `~*`, `!~`, `!~*`) contracts, retaining
CHAR-subject overloads and nullable results. Each factor has 50 synthetic
certificates and 50 unchanged source examples. Native PostgreSQL checks cover
200 value/type observations, 216 descriptors, 12 expected errors and 12
operator declarations. SQLite explicitly excludes these PostgreSQL operations.
The PostgreSQL lexer also rejects unsupported maximal operator tokens such as
`||-`, preserving native token boundaries instead of silently splitting them.

The [v0.14 concatenation increment](docs/concatenation-contract-v0.14.md)
adds exact scalar `||` signatures for text conversion, JSONB and BYTEA.
It preserves operator selection, nullable metadata and dialect-specific
precedence. Fifty synthetic certificates and 50 unchanged sources accompany
100 PostgreSQL value/type observations, 110 descriptors, five native
overload checks, ten expected errors and 40 separate SQLite observations.
Array concatenation has a separate contract in v0.18.

The [v0.13 row-comparison increment](docs/row-comparisons-contract-v0.13.md)
adds all six comparison operators between explicit `ROW(...)` or implicit
tuple constructors. Independent derivations retain each field's selected
operator and lexical parameter order. Fifty synthetic certificates and 50
unchanged sources accompany 100 PostgreSQL value/type observations, 112
descriptors, 198 B-tree operator checks, 10 expected errors, and 66 separate
SQLite observations. The [row-milestone industrial audit](docs/corpus/row-comparisons-v0.13/README.md)
accepts 233 of the original 276 statements; all seven row-comparison failures
are now parsed. Standalone and nested record typing remain separate obligations.

The [v0.12 subscript increment](docs/array-subscripts-contract-v0.12.md)
adds array element extraction, slices with omitted bounds, and mixed
multidimensional groups. Independent derivations retain element modifiers and
check assignment conversions for each bound. Fifty synthetic certificates and
50 unchanged source examples accompany 100 native value/type observations,
270 exact descriptors and 10 expected execution errors. It also corrects
inferred cast, CASE and subscript labels, checked against 85 native examples.
SQLite explicitly rejects PostgreSQL array subscripts.

The [v0.11 quantified-comparison increment](docs/array-quantified-contract-v0.11.md)
adds the six scalar comparison operators with `ANY`, `SOME` and `ALL` arrays.
Independent derivations retain the selected scalar operator and conservatively
nullable Boolean result. Fifty synthetic certificates and 50 unchanged
source examples accompany 100 native value/type observations, 106 exact
descriptors, 10 expected execution errors and 192 native operator checks.
The source corpus contains authentic ANY/ALL examples; no SOME spelling was
found in that pinned population. Synthetic examples cover all three spellings.

The [v0.10 constructor increment](docs/array-constructors-contract-v0.10.md)
adds `ARRAY[...]`, nested bracket shorthand, common element-type inference and
contextual direct casts, including typed empty arrays. Independent judgments
and parameter-translation proofs cover the new syntax. Fifty synthetic
certificates and 50 unchanged source examples accompany 112 native value/type
observations, 120 exact result descriptors and 14 expected runtime errors.
SQLite explicitly rejects these constructors. Array subqueries remain a
separate increment; indexing and slicing are covered by v0.12.

The [v0.9 array-type increment](docs/array-types-contract-v0.9.md)
adds built-in array types, repeated unsized suffixes, casts, catalog columns and
typed parameters. Exact element types remain distinct while declared dimension
counts normalize. It also corrects parameter modifier inference: PostgreSQL
ignores modifiers on prepared parameter declarations, while explicit casts
preserve them. Fifty synthetic certificates and 50 unchanged source examples
are checked, with 126 native value/type observations and 126 exact prepared
result descriptors.

The [v0.8 derived-source increment](docs/derived-contract-v0.8.md)
adds recursively nested non-LATERAL SELECT sources and positional column
renaming. Independent derivations retain exact output types, modifiers,
nullability and duplicate labels, and check parameter notation once over the
complete query. It includes 50 synthetic full-query certificates and 50
unchanged source rendering examples. Correlation, expression subqueries and
outer locking of derived sources remain separate obligations.

The [v0.7 merged-join increment](docs/merged-joins-contract-v0.7.md) adds
USING and NATURAL joins with independent rules for merged columns, qualified
original columns, common types and modifiers, output order and nullability.
Each factor has 50 synthetic complete-query certificates and 50 unchanged
source rendering examples. SQLite has separate native expectations because
its wildcard order and RIGHT/FULL merged-key values can differ from PostgreSQL.

The [v0.6 join increment](docs/joins-contract-v0.6.md) promotes base-table
CROSS and INNER/LEFT/RIGHT/FULL JOIN ON queries to independent static validity.
Its rules derive exact scopes, unique relation aliases, Boolean ON predicates,
outer-join nullability, lock eligibility and parameter order. It includes 50
synthetic full-query certificates and 50 unchanged source rendering examples.

The [v0.5 locking increment](docs/locking-contract-v0.5.md) adds PostgreSQL row
locking, target aliases, wait policies and both LIMIT/OFFSET orders. Basic
SELECT certificates include lock-target validity; identity/PostgreSQL renderer
certificates retain the exact locking AST and parameter order. Joins and nested
queries retain their existing, separate assurance levels.

The [v0.4 scalar forms increment](docs/scalar-forms-contract-v0.4.md) adds
ordinary function calls, CASE, COALESCE, NULLIF, GREATEST and LEAST. Independent
static validity uses a closed inventory of 44 built-in names with explicit
overload rules. Each of the function and conditional factors has 50 synthetic
full-query certificates and 50 unchanged source rendering examples.

The [v0.3 scalar increment](docs/extended-types-contract-v0.3.md) adds concrete
numeric, temporal, UUID, JSON/JSONB, BYTEA and character types, preserving their
supported modifiers. It includes 50 synthetic full SELECT certificates, 50
unchanged source statements with rendering checks, and 100 separately bound
PostgreSQL source/rendered value-and-type observations.

The [v0.2 pagination contract](docs/pagination-contract-v0.2.md) adds expression-valued
LIMIT/OFFSET, including parameters, to this basic proof profile and the checked
renderers. It separates full-query validity from bounds-only evidence for
broader application queries, and leaves value-dependent execution obligations
explicit. Its 50 synthetic and 50 concrete source statements have separate
assurance scopes. The pagination suite passed 204 SQLite executions and 212
PostgreSQL PREPARE/EXECUTE cases, including expected runtime errors.

The [SELECT renderer contract](docs/SELECT_render_contract.md) also has an
initial implementation. It adds a separate checked serialization boundary for
the expanded SELECT AST, exact reconstruction certificates, and explicit
parameter transport. A second iteration proves general parameter-translation
and serialization laws, then adds a SQLite rendering profile alongside
PostgreSQL. Independent database semantic preservation remains an open
obligation; static validity and rendering assurance are separate APIs.

The [name/scope contract](docs/SELECT_scope_contract.md) adds an independent
fragment for source tables, aliases, CROSS JOIN, and nested correlated EXISTS.
Its resolver has kernel-checked soundness, completeness, uniqueness, and
failure/refutation theorems. It checks names only; the bridge to the production
checker is currently tested on finite cases, not proved generally. Its
PostgreSQL-oriented alias visibility rules are separate from SQLite rendering
and do not expand the public validity tier. Import
`SQLean.ScopeContract.Embedding` to use the fragment API.

Build and test from the repository root:

```sh
lake build
lake exe sqlean_tests
lake exe sqlean_scope_tests
python3 scripts/check_assurance_cli.py
python3 scripts/check_render_cli.py
python3 scripts/check_renderer_corpus.py
python3 scripts/check_lean_trust.py
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/generate_crud_examples.py --check
python3 scripts/check_crud_cli.py
python3 scripts/generate_relational_examples.py --check
python3 scripts/check_relational_cli.py
python3 scripts/generate_industrial_examples.py --check
python3 scripts/check_industrial_cli.py
python3 scripts/generate_postgresql_examples.py --check
python3 scripts/test_postgresql_results.py
python3 scripts/generate_advanced_examples.py --check
python3 scripts/generate_dialect_examples.py --check
python3 scripts/check_dialect_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/generate_pagination_examples.py --check
python3 scripts/extract_pagination_corpus.py --check
python3 scripts/check_pagination_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/check_extended_types_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/check_scalar_forms_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/check_locking_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/check_join_contract_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/check_merged_join_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/check_derived_contract_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/check_array_types_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/check_array_constructors_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/check_array_quantified_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/check_array_subscripts_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/check_row_comparisons_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/check_concatenation_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/check_pattern_matching_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/check_json_extraction_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/check_json_containment_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/check_interval_fields_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/check_substring_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/check_qualified_names_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/check_json_existence_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/check_context_values_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/check_named_arguments_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/check_keyword_functions_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/inventory_postgresql_grammar.py --check
python3 scripts/generate_postgresql_grammar.py --check
python3 scripts/check_postgresql_grammar_cli.py
```

[GitHub Actions CI](.github/workflows/ci.yml) runs on pushes, pull requests, and
manual dispatch. A Python job runs all offline regression tests and checks all
the generated corpora. A second job builds the library, CLI, and test executable
from scratch using `lean-toolchain`, runs the Lean and SQLite suites, then runs
both PostgreSQL corpora and the actual parameter-execution check against
PostgreSQL 16, including the rendering and dialect checks. Both jobs use Ubuntu
24.04 and Python 3.12. PostgreSQL checks use
temporary private clusters; no database secrets are required. New runs cancel
superseded runs for the same branch or pull request.

The renderer CI replay sends **1,237 SELECT queries from the compatibility
corpora** through `--render-assurance identity` and `postgres`, then checks
canonical rerendering and parameter maps. The inventory includes the original SELECTs, CRUD reads,
joins, grouping, derived tables, ordinary/recursive CTEs, set operations, and
the SELECT portions of the PostgreSQL and advanced corpora. Non-SELECT
statements remain in their existing mutation/DDL suites. Missing fixtures or
unexpected renderer rejections fail the replay.
The 200 dialect fixtures retain their separate checked-rendering suite.

The same replay checks **400 portable SELECTs** with the SQLite renderer and
executes source/rendered pairs on empty and seeded databases. It compares
column counts, duplicate-preserving rows, and ordered results where specified.
SQLite-generated expression labels differ in
[54 explicitly recorded cases](fixtures/renderer_label_expectations.json);
the remaining cases also require equal labels. These exceptions do not disable
row or column-count checks, and new label differences fail CI.
Separate native witnesses cover DISTINCT ON, richer aggregates and FILTER,
USING/NATURAL joins, set multiplicities, nested CTE scope, and correlated
subqueries. SQLite and PostgreSQL use their own expected results. These are
finite observations alongside Lean reconstruction proofs, not a universal
database-semantic equivalence claim.

An [external PostgreSQL corpus audit](docs/corpus/postgresql-2026-10-20/README.md)
covers 276 statements from River, Temporal, and six BenchBase workload
families. At the recorded baseline, 161 parsed and 115 were rejected. The report preserves every failure,
pinned upstream sources, extraction rules, and a prioritized syntax backlog.
Separate probes document accepted PostgreSQL special forms that SQLean
currently interprets incorrectly. These syntax observations do not extend
the validity or rendering assurance tiers.

The project-wide trust audit rejects proof placeholders, project-defined axioms,
native proof shortcuts, user-authored unsafe/partial declarations, and kernel-check bypasses.
It inventories every Lean source module, including private declarations, and
checks transitive axiom dependencies. The only allowed foundational axioms are
Lean's `propext`, `Classical.choice`, and `Quot.sound`; this is explicitly **not**
a claim that Lean uses no logical foundations. Negative probes test that the
audit actually rejects forbidden declarations. Lean-generated executable
recursion helpers are permitted only when attached to a safe kernel definition
or safe opaque declaration,
and their axiom dependencies are still audited. Offline tests
guard the specification's import boundary: it may depend on its normative
profile, immutable syntax/catalog definitions, and `Std`, but not on executable
validators. Rendering admissibility similarly cannot import the parser,
renderer, or static checker. The assurance, rendering, and dialect CLI suites
run in the integration job.

To run the PostgreSQL oracle, supply a directory containing `initdb`, `pg_ctl`,
and `psql` (for example, the output of `pg_config --bindir`):

```sh
python3 scripts/check_postgresql_cli.py --local-bin /usr/lib/postgresql/16/bin
```

The checker starts a temporary PostgreSQL cluster with Unix sockets only, tests
original and rendered statements on empty and seeded tables, and removes the
cluster afterward. RETURNING checks compare both result rows and table contents
after each mutation, with savepoint rollbacks between runs. PostgreSQL 16 was
used for this corpus. Alternatively, `--dsn` uses a fresh random schema inside a
rolled-back transaction on a supplied test database; `--psql` selects its client.

The PostgreSQL transport uses `COPY ... CSV FORCE_QUOTE *`: quoted fields are
text (including the literal NULL marker), and only an unquoted marker is SQL
NULL. Offline decoder regressions require neither PostgreSQL nor Lean. Result
arity, row ordering, and RETURNING state comparisons retain their existing
representation. These finite database checks are not a proof of execution
equivalence for arbitrary database states. Run `--local-bin` as a non-root user
(as required by `initdb`).

The Lean test executable checks syntax, expression precedence, schema and type errors, certificates, and SQL round trips. The Python checks use only the standard library. The generators check that example files match their deterministic source; the CRUD, relational, and industrial CLI checks independently compile each example and its rendered SQL using SQLite `EXPLAIN`, without executing mutations. The relational and industrial checks also compare SELECT results on empty and seeded SQLite databases. Recursive examples use finite data or explicit bounds, and the industrial checker caps SQLite execution work. The PostgreSQL checker performs 600 source/canonical result comparisons, 100 RETURNING mutation-state comparisons, and 36 independently specified result checks.

The compatibility corpora contain **50 examples per added query category**, 50 per CRUD category, and the original 100 SELECT examples. The 750 advanced examples are listed later in this README. The latest [dialect corpus](fixtures/dialects) adds 200 examples: 50 each for SQLite numbered parameters, SQLite compound queries, SQLite comma-style LIMIT, and PostgreSQL NUMERIC scales above precision. Its JSON metadata supplies independent expected rows, labels, and bound values.

| Category | Examples | New functionality |
| --- | --- | --- |
| DISTINCT ON | [50 examples](fixtures/postgresql/distinct_on.sql) | First row per key, expressions, aliases, ordinals, and grouping. |
| Aggregate FILTER | [50 examples](fixtures/postgresql/aggregate_filter.sql) | Conditional COUNT/SUM/AVG/MIN/MAX in projections, HAVING, and sorting. |
| Casts | [50 examples](fixtures/postgresql/casts.sql) | PostgreSQL `::` and standard CAST, with explicit scalar targets. |
| Predicates | [50 examples](fixtures/postgresql/predicates.sql) | LIKE/ILIKE, IN lists, BETWEEN, and their NOT forms. |
| NULLS ordering | [50 examples](fixtures/postgresql/null_ordering.sql) | FIRST/LAST with ascending/descending, outer joins, aggregates, and compounds. |
| RETURNING | [50 examples](fixtures/postgresql/returning.sql) | INSERT/UPDATE/DELETE result projections, wildcards, aliases, and scalar expressions. |
| Recursive CTEs | [50 examples](fixtures/industrial/recursive_ctes.sql) | Bounded sequences, employee hierarchies, graph reachability, and bills of materials. |
| Unions | [50 examples](fixtures/industrial/unions.sql) | UNION/UNION ALL, multiple arms, global ordering/pagination, unions inside CTEs and derived tables. |
| SELECT without FROM | [50 examples](fixtures/industrial/source_free.sql) | Constant projections, arithmetic, predicates, aggregate results, and constant seed relations. |
| Joins | [50 examples](fixtures/relational/joins.sql) | INNER, LEFT, RIGHT, FULL, CROSS, aliases, qualified columns, wildcards, null checks. |
| Grouping and aggregates | [50 examples](fixtures/relational/grouping.sql) | GROUP BY, HAVING, COUNT/SUM/AVG/MIN/MAX, DISTINCT aggregates, aliases and ordinals. |
| Derived-table subqueries | [50 examples](fixtures/relational/subqueries.sql) | SELECT in FROM or JOIN, nested queries, named outputs, aggregate results. |
| Nonrecursive CTEs | [50 examples](fixtures/relational/ctes.sql) | WITH, multiple bindings, column lists, nested WITH, references to earlier bindings. |
| Read / SELECT | [50 examples](fixtures/crud/select.sql) | `*`, `DISTINCT`, sorting, pagination, boolean literals and unary expressions. |
| Create / INSERT | [50 examples](fixtures/crud/insert.sql) | Implicit/explicit target columns, reordered columns, multiple rows, constant expressions. |
| Update / UPDATE | [50 examples](fixtures/crud/update.sql) | One or several assignments, column-based expressions, optional filters. |
| Delete / DELETE | [50 examples](fixtures/crud/delete.sql) | Optional filters, comparisons, boolean combinations. |
| Original SELECT MVP | [100 examples](fixtures/queries.sql) | Regression coverage for the original expression grammar and API. |

The original and compatibility corpus statements are parsed, certified against their schemas, rendered, and reparsed with equal ASTs using the corresponding APIs. The new dialect corpus instead checks exact rendering certificates and native database results; it does not claim stronger static-validity coverage. The original PostgreSQL SELECT corpus uses the uniform `parseRelQuery` interface, since normalized BETWEEN expressions can also fit the legacy grammar. The advanced corpus uses `Advanced.parse` and `Advanced.render` to keep its AST interface stable. Each line is a separate input; passing an entire corpus file to the single-statement CLI is an error. Regenerate fixtures with the corresponding `scripts/generate_*_examples.py` script.

Use the CLI with one SQL argument, a file containing one statement, or standard input:

```sh
lake exe sqlean 'SELECT * FROM users ORDER BY age DESC LIMIT 10 OFFSET 20'
lake exe sqlean --ast 'UPDATE users SET age = age + 1 WHERE id = 7'
lake exe sqlean --schema fixtures/crud/schema.json \
  "INSERT INTO users (id, age, name, city) VALUES (1, 30, 'Ada', 'London'), (2, 25, 'Grace', 'Paris')"
lake exe sqlean --schema fixtures/crud/schema.json 'DELETE FROM users WHERE age < 18'
lake exe sqlean --schema fixtures/relational/schema.json \
  'SELECT u.name, o.amount FROM users u LEFT JOIN orders o ON u.id = o.user_id'
lake exe sqlean --file statement.sql
printf '%s\n' 'SELECT id FROM users' | lake exe sqlean
```

The CLI prints canonical SQL; `--ast` selects AST output. `--schema` additionally validates the statement and reports selected/RETURNING output types (or the mutation category when no rows are returned). Syntax/validation failures exit with status 1; invalid CLI arguments exit with status 2. Parsing or certifying SQL does not execute it. DDL validation reports an in-memory catalog transition without changing a database.

SELECT assurance is opt-in, so existing CLI output and all earlier parser APIs
keep their behavior. Choose one tier before checking:

- `--assurance contract` uses the fixed `sqlean-basic-select-v0.27` profile.
  `valid` carries an independent declarative derivation in the Lean API.
  `invalid` reports a violated profile condition, `unsupported` reports a
  missing rule or excluded feature, and `inconclusive` reports budget exhaustion.
- `--assurance checked` uses the existing expanded static checks. Success is
  named `checked`, with `checker-acceptance` evidence and coarse type families.
  A rejection is named `rejected`, not a refutation of the independent contract.
  This tier retains joins, grouping, subqueries, CTEs, set operations, dialect
  extensions, and mutation/DDL checking.
- `--assurance syntax` reports `parsed` without checking catalog bindings or
  types. It does not read a supplied schema or infer parameter types.

Assurance mode emits exactly one JSON report, without canonical SQL. The
`assurance` field identifies the requested tier; `evidence` is `none` on every
failure. Successful SELECT reports include ordered `outputColumns` with names,
types, and nullability. A contract report uses `typePrecision: "exact"`; the
expanded tier uses `"family"`. The JSON is a report, not a serialized Lean proof.
Contract certificates are indexed by the exact profile, catalog, parameter
environment, and advanced query AST, and expose a catalog-preservation theorem.
There is no automatic fallback from a failed contract check to weaker evidence.

```sh
lake exe sqlean --assurance contract --schema fixtures/crud/schema.json \
  'SELECT name, id FROM users WHERE age >= 18 ORDER BY id'
lake exe sqlean --assurance contract --param-types 'int?' \
  'SELECT $1 AS value WHERE $1 IS NOT NULL'
lake exe sqlean --assurance checked --schema fixtures/advanced/schema.json \
  'SELECT COUNT(*) AS total FROM users'
lake exe sqlean --assurance syntax 'SELECT unknown FROM absent'
```

Exit status is 0 for `valid`/`checked`/`parsed`, 1 for
`invalid`/`rejected` or a parse error, 2 for invalid CLI options, 3 for
`unsupported`, and 4 for `inconclusive`. Parse errors remain separate from
AST-validity outcomes and are printed on stderr. `--max-depth N` changes the
SELECT checking budget (default 1,024); zero is inconclusive, not invalid SQL.
It cannot be used with syntax mode, and custom budgets for mutations/DDL are
unsupported. Assurance mode cannot be combined with `--ast` or `--postgres`.

The current independent profile has the following explicit boundary:

- Source-free SELECT, base tables or nested non-LATERAL derived sources
  with CROSS/INNER/LEFT/RIGHT/FULL JOIN,
  using ON, USING or NATURAL matching,
  optional table aliases, nonempty projection,
  expression aliases, `*` and qualified wildcards, WHERE, ordinary DISTINCT,
  ORDER BY, and expression-valued LIMIT/OFFSET. Top-level duplicate labels
  retain their positions; sorting by an ambiguous label is invalid. Table
  aliases hide the original name. Projection aliases are unavailable to WHERE
  and sibling projection expressions.
- Each JOIN ON sees its two child scopes before that join's NULL extension.
  Outer joins make the appropriate result columns conservatively nullable.
  Relation aliases must be unique. USING keys appear first in their listed
  order, followed by left and right nonkeys; NATURAL keys follow left-output
  order. Qualified wildcards retain each relation's original columns and types.
  Missing or ambiguous keys are invalid, and merged keys use explicit
  equality/common-type rules with conservative nullability.
  SELECT parameter occurrences precede FROM/ON, WHERE, ORDER BY and pagination.
- Derived sources expose only their certified output under the declared alias.
  Column-alias lists rename a positional prefix; remaining labels are retained.
  Duplicate labels remain legal but ambiguous when referenced by name.
  A derived child cannot see a parent or sibling source. Parameter identities
  continue across query boundaries. Explicit outer row locks targeting derived
  sources remain unsupported; locking a nonnullable base sibling is covered.
- Concrete SMALLINT, INTEGER, BIGINT, NUMERIC, REAL, DOUBLE PRECISION, TEXT,
  VARCHAR, CHAR, BOOLEAN, temporal types, UUID, JSON/JSONB and BYTEA, including
  supported modifiers. Integer magnitudes choose INTEGER, BIGINT or NUMERIC;
  decimal/exponent literals have exact NUMERIC type. All supplied metadata
  must be supported, including unused declarations.
- Arrays of the concrete built-in types support unsized `[]` suffixes,
  casts, projections, typed bindings, NULL tests and covered comparison or
  conditional signatures. Element modifiers are preserved for columns and
  casts. A parameter expression has the unmodified OID type, for scalar and
  array declarations alike. Array NULL elements do not make the outer value
  nullable. SQLite rejects array types.
- `ARRAY[...]` constructors infer a common element type and preserve lexical
  parameter order through nested brackets. A direct array cast supplies
  element coercions and permits empty constructors. This context reaches raw
  nested constructors only. Constructors produce nonnullable arrays even when
  elements are NULL; incompatible runtime dimensions remain execution errors.
- `=`, `<>`, `<`, `<=`, `>` and `>=` with `ANY`/`SOME`/`ALL` arrays resolve a
  scalar operator against the array element type. Unknown string/NULL inputs
  can receive contextual array types. Result nullability is conservative
  because array types do not track member nullability or cardinality.
- Explicit PostgreSQL scalar tables govern arithmetic, casts, comparisons,
  LIKE, IN and BETWEEN. JSON lacks comparison operators while JSONB admits
  them. Successful conversion and evaluation of actual values remain runtime
  obligations. The closed function inventory and CASE/COALESCE/NULLIF/
  GREATEST/LEAST rules are documented in the v0.4 increment.
- A bare NULL has unknown type until context supplies one. A matching concrete
  operand can supply that context; NULL cannot reconcile two incompatible types.
  All-NULL comparisons use TEXT, and a projected unconstrained NULL becomes
  nullable TEXT. NULL Boolean operands are contextual BOOLEAN. Unknown arithmetic
  and unary signs without a concrete numeric type are rejected. Null tests return
  non-null BOOLEAN. Other expressions conservatively propagate nullable inputs;
  WHERE does not refine output nullability.
- Numbered parameters denote positive declared identities and may repeat.
  Anonymous parameters must occur as 1,2,... in source order; mixing styles is
  invalid even for manually constructed ASTs. Contract parameter declarations
  retain concrete `Advanced.DataType` values, rather than `SqlType` families.
- Ordinary sorting permits input expressions, unique bare output names, and
  one-based output positions. Output names take precedence over input names;
  aliases are not substituted inside larger expressions. DISTINCT sorting is
  currently certified only by output names or positions. Other DISTINCT sort
  expressions return Unsupported pending a projected-expression identity rule.
- Pagination expressions are typed in an empty local scope: input columns and
  output aliases are unavailable. Supported numeric types use explicit
  assignment conversion to PostgreSQL's `int8` row-count target; an untyped NULL
  acquires that context. Negative results, overflow, division by zero and failed
  casts remain execution obligations. Both LIMIT/OFFSET orders retain parameter
  occurrence order.
  The separate `checkPaginationBounds` API certifies only the outer bounds of
  a query and cannot establish full-query validity or parameter notation.

Independent rules for grouping/aggregates, correlation, LATERAL,
CTEs/recursion, set operations, and base-table column-renaming remain future
milestones. DISTINCT ON and ILIKE require separate dialect rules. These forms
remain supported by the expanded parser/checker. The contract draft remains the
target for the general SELECT family; the first implementation does not claim
complete coverage or completeness of its checker.

The implementation separates [normative profile tables](SQLean/SelectContract/Profile.lean),
[inductive validity judgments](SQLean/SelectContract/Spec.lean), and a
[proof-producing checker](SQLean/SelectContract/Checker.lean).
`SelectContract.checkQuery_sound` connects success to `SelectContract.SelectValid`;
the latter does not call an executable validator or inference procedure.
[Assurance APIs](SQLean/Assurance.lean) wrap the four contract outcomes and expose
the expanded check as a separate tier. For example:

```lean
import SQLean.Assurance
open SQLean

def contractQuery : Advanced.Query := {
  body := .select { items := [.expression (.literal (.int 1)) (some "one")] } }

#eval (SelectContract.checkQuery .basicV02 [] [] contractQuery).map
  (fun certificate => certificate.output)

example (certificate : SelectContract.Certificate profile catalog params query) :
    SelectContract.SelectValid profile catalog params query certificate.output :=
  certificate.valid

example (certificate : SelectContract.Certificate profile catalog params query) :
    certificate.outputCatalog = catalog := certificate.catalog_unchanged
```

The earlier declarative certificates retain their original profiles. They are
not automatically certificates for this new contract. None of these tiers
establishes parser/renderer correctness, runtime cast or arithmetic safety,
subquery cardinality, recursive termination, authorization, or transaction
execution. Database comparisons remain finite test evidence.

Checked SELECT rendering uses the uniform `Advanced.Query` AST. It requires no
schema: `SELECT missing FROM absent` can serialize faithfully while failing a
separate validity check. Existing `render`, `renderPostgres`, and legacy APIs
retain their signatures and syntax coverage; arbitrary ASTs passed to those
unchecked APIs do not receive a rendering certificate.

```sh
lake exe sqlean --render-assurance identity 'SELECT missing FROM absent'
lake exe sqlean --render-assurance postgres \
  'WITH c(x) AS (SELECT ?) SELECT ?, (SELECT ?), x FROM c'
lake exe sqlean --render-assurance sqlite \
  'SELECT ?2 AS second, ?1 AS first UNION ALL SELECT ?1, ?2 LIMIT 0, 2'
python3 scripts/check_render_cli.py --local-bin /usr/lib/postgresql/16/bin
python3 scripts/check_dialect_cli.py --local-bin /usr/lib/postgresql/16/bin
```

`--render-assurance identity` selects `sqlean-select-render-v0.1`, preserving
numbered markers and anonymous `?` markers. This identity profile is a SQLean
parameter dialect, not a claim that PostgreSQL accepts `?` directly.
`--render-assurance postgres` selects `postgresql-16-select-render-v0.1` and
translates anonymous ordinal `i` to `$i`. These two profiles fix UTF-8 client/server
encoding, `standard_conforming_strings=on`, a 63-byte identifier limit, and the
same catalog/search path/namespace interpretation. These are required target
assumptions, not settings the renderer silently changes. See PostgreSQL 16's
[lexical rules](https://www.postgresql.org/docs/16/sql-syntax-lexical.html).

`--render-assurance sqlite` selects `sqlite-3.39-select-render-v0.1`.
It emits explicit `?NNN` markers, preserving slot indices and repeated references.
SQLite `$name` markers are named bindings allocated in encounter order, so this
profile rejects them rather than treating `$2` as slot 2. Bare `?` input uses
global occurrence order; mixing bare and numbered markers is excluded.
The profile assumes SQLite 3.39 or later, UTF-8 input, a variable limit of at
least 32766, and unchanged database/namespace/collation settings. It retains
the common 63-byte identifier restriction as a conservative profile boundary.
See SQLite's [parameter rules](https://www.sqlite.org/lang_expr.html#parameters)
and [SELECT syntax](https://www.sqlite.org/lang_select.html).

`Advanced.parseSQLiteQuery` and `Advanced.parseSQLite` select SQLite's
left-associative, equal-precedence set operations and recognize `LIMIT offset,
count`. They also associate comma joins and explicit JOINs from left to right,
preserve unquoted identifier spelling, and use non-nesting block comments.
Default parsing retains PostgreSQL's INTERSECT/JOIN precedence, unquoted-name
folding, and nested block comments.
The SQLite-oriented parser shares other expression syntax with the expanded
parser: for example, it accepts `::` input and renders standard CAST. It is a
conversion interface, not an exact recognizer of native SQLite source syntax.
`Advanced.renderSQLite` is the total unchecked query printer; use
`RenderContract.check .sqliteV01` to obtain a certificate.

Successful JSON reports have `status: "rendered"`, `assurance:
"checked-roundtrip"`, SQL, a binding map, the profile/mode, and named theorem
obligations. `semanticPreservation` is explicitly false: full SQL semantics have
not been established. Each map entry identifies the original parameter style
and index and its target slot. Repeated numbered references share one entry;
anonymous references must occur exactly as 1..N across CTEs, DISTINCT ON,
projection, sources/joins, predicates, grouping, ordering, LIMIT, and OFFSET. Mixed styles
return `unsupported`. PostgreSQL mode limits slots to 1..65535, matching the
[PostgreSQL 16 parameter limit](https://www.postgresql.org/docs/16/limits.html);
SQLite mode limits them to 1..32766. Supply parameter
values and concrete declared types separately, using the same returned map.
`translateParameters_idempotent` proves, for every finite advanced query, that
applying this parameter-only AST translation a second time makes no further change.

The [independent admissibility specification](SQLean/RenderContract/Admissibility.lean)
checks every represented field before rendering. It rejects empty/NUL/overlong
identifiers, NUL text, malformed decimal tokens, contradictory DISTINCT flags,
a recursion marker with no CTE, empty projections/IN/USING lists, invalid join
condition combinations, and FILTER on a nonaggregate. Decimal and exponent
spelling is retained without floating-point conversion. Identifiers remain
quoted exact names; text retains quotes, backslashes, newlines, and Unicode.
The supported cast modifier subset is `VARCHAR(1..10485760)`,
`NUMERIC(1..1000)`, and `NUMERIC(p,s)` with `1 <= p <= 1000` and
`0 <= s <= 1000`. This includes scales above precision supported by
[PostgreSQL 16](https://www.postgresql.org/docs/16/datatype-numeric.html).
Negative scales remain outside the natural-number modifier AST. A singleton
IN-list whose only element is a scalar
subquery is also `unsupported`: its serialization is ambiguous with the distinct
IN-subquery constructor. The renderer does not insert an artificial cast or
arithmetic expression to disambiguate it.

The separate [SQLite coverage rules](SQLean/RenderContract/SQLiteAdmissibility.lean)
exclude ILIKE, DISTINCT ON, LATERAL, relation-alias column lists, INTERSECT ALL,
EXCEPT ALL, and OFFSET without LIMIT. Compound queries must associate to the
left, with no operand-local WITH, ORDER BY, LIMIT, or OFFSET. Global clauses
remain available. These restrictions preserve the AST without inserting wrapper
SELECTs to emulate parentheses that SQLite does not accept.
SQLite's native typing, casts, NULL behavior, and identifier resolution still
apply: numeric type modifiers do not acquire PostgreSQL precision semantics,
division by zero can yield NULL, and visible columns named TRUE/FALSE can shadow
those literals. The execution tests record these differences explicitly.

The [checked boundary](SQLean/RenderContract/Checker.lean) returns either an
indexed `Certificate profile query` or a structured failure:
`invalid` means an inadmissible representation; `unsupported` means a stated
profile gap; `inconclusive` means the requested depth budget was exceeded;
`mismatch` means a renderer/parser reconstruction disagreement.
Failures publish no SQL. Exit codes are respectively 1, 3, 4, and 1; successful
rendering exits 0 and argument errors exit 2. `--max-depth` defaults to 1024 and
checks inspected AST depth before serialization/reparsing. Inspection itself is
total and is not an operating-system memory/time bound. Process failure or
external resource exhaustion must still be handled by the caller.

```lean
import SQLean.RenderContract
open SQLean

def renderedQuery : Advanced.Query := {
  body := .select {items := [.expression (.parameter (.anonymous 1)) (some "value")]} }

#eval (RenderContract.check .postgres16V01 renderedQuery).map
  (fun certificate => (certificate.sql, certificate.parameterMap))

example (certificate : RenderContract.Certificate profile query) :
    RenderContract.parseRendered profile certificate.sql =
      .ok (RenderContract.expectedQuery profile query) :=
  certificate.roundTrip

example (profile : RenderContract.Profile) (query : Advanced.Query) :
    RenderContract.renderSql profile (RenderContract.expectedQuery profile query) =
      RenderContract.renderSql profile query :=
  RenderContract.render_expected_stable profile query
```

The certificate proves exact full reparsing with Lean equality over **every AST
field**, canonical rerendered bytes, and the independently specified
admissibility conditions. Parameter-map completeness, injectivity on referenced
bindings, and transport of separately supplied values/types have separate
theorems. `identity_validity_preserved` transfers an existing independent
validity derivation, including its ordered output schema, to the reconstructed
identity-mode AST. This is not a schema theorem about PostgreSQL execution.
The mathematical renderer now uses total structural recursion over finite ASTs;
there is no fuel or replacement-SQL fallback.

The second proof iteration adds universal structural results in
[SerializationProofs](SQLean/RenderContract/SerializationProofs.lean),
[SQLiteSerializationProofs](SQLean/RenderContract/SQLiteSerializationProofs.lean),
and [ValidityPreservation](SQLean/RenderContract/ValidityPreservation.lean).
For every finite query AST, parameter translation leaves PostgreSQL and SQLite
rendered bytes unchanged; `render_expected_stable` supplies canonical stability
directly to certificates. `translateParameters_valid` preserves any existing
basic-SELECT validity derivation and its exact ordered output schema under the
same index-keyed parameter environment. `translated_validity_preserved` transfers
that derivation to the reconstructed target AST. These are AST theorems, not
claims that the two databases execute the query identically.

Full reconstruction remains certified per successful checked instance. A theorem that **every**
admissible query passes the round-trip boundary remains open, as do independent
target-grammar fidelity, name-resolution preservation under target semantics,
and the contract's complete behavioral equivalence (bags, ordering ties,
permitted LIMIT outcomes, errors, and divergence). Source-to-rendered semantics
also requires a separate parser theorem. Hand-built AST regressions and fixed
SQLite/PostgreSQL observations supply finite evidence, including hostile lexical data,
deep nesting, actual parameter execution, duplicates/NULLs, and modeled errors;
they do not close those universal obligations.
For reproducible trust evidence, run
`python3 scripts/check_lean_trust.py --evidence-json .lake/trust-audit.json`.
The manifest records the Git revision, dirty state, hashes of the exact
source/configuration inventory and compiled artifacts, and the Lean version.
CLI rendering JSON names its profile and renderer version; associate deployment
reports with this build manifest to identify the exact code. The manifest
attests the trust audit, not independent SQL semantics.

Schemas are supplied externally as JSON:

```json
{"tables":[{"name":"flags","columns":[{"name":"id","type":"int"},{"name":"enabled","type":"bool"},{"name":"label","type":"text"}]}]}
```

The original `parseSchemaJson` interface accepts JSON types `int`, `text`, `bool`, and `real`; columns may specify `"nullable": true` and otherwise default to non-null. Table/column names must be nonempty and unique in their scope, and tables must have columns. Schema names are exact; ordinary unquoted SQL identifiers normalize to lowercase. [The CRUD schema](fixtures/crud/schema.json) contains `users`, `inventory`, and `flags`; [the relational schema](fixtures/relational/schema.json) contains users, orders, departments, employees, and flags. These compatibility fixtures contain only required, non-null columns without defaults, so their INSERT statements must supply every column. `parseSchemaJson` returns the original `Schema` interface; `Advanced.parseCatalogJson` additionally preserves defaults and key metadata, as described with the advanced catalog API below. The CLI uses that catalog decoder and selects advanced validation when the schema needs its richer metadata.

For example, join orders before grouping customers and filter by their number of matching orders:

```sql
SELECT u.id, u.name, COUNT(o.id) AS order_count, SUM(o.amount) AS total
FROM users AS u
LEFT JOIN orders AS o ON u.id = o.user_id
GROUP BY u.id, u.name
HAVING COUNT(o.id) >= 1
ORDER BY total DESC;
```

A derived table names the result of a nested SELECT. Its alias is required:

```sql
SELECT totals.user_id, totals.total
FROM (
  SELECT user_id, SUM(amount) AS total
  FROM orders
  GROUP BY user_id
) AS totals
WHERE totals.total > 100;
```

WITH gives a query result a name usable by later bindings and the main SELECT:

```sql
WITH totals (customer_id, total) AS (
  SELECT user_id, SUM(amount) FROM orders GROUP BY user_id
), large_orders AS (
  SELECT customer_id, total FROM totals WHERE total > 100
)
SELECT u.name, large_orders.total
FROM users u
JOIN large_orders ON u.id = large_orders.customer_id;
```

In the original relational API, CTEs are checked sequentially: each can use earlier bindings and the outer schema. A binding shadows an outer relation with the same name; duplicate names in one WITH list are rejected. Derived tables and CTEs may nest. They expose the natural names of selected columns and explicit result aliases. Computed outputs at these boundaries require `AS name` (or a bare alias); a CTE's explicit column list can instead supply all output names. The column list must match the result arity. Duplicate output names are rejected at a derived-table/CTE boundary, so alias columns when a joined projection would otherwise repeat a name. This original API does not allow references to enclosing FROM aliases; the advanced API adds correlated subqueries and LATERAL sources.

Recursive CTEs support an anchor followed by one recursive step. For example, a bounded integer sequence works with an empty schema:

```sql
WITH RECURSIVE sequence(n) AS (
  SELECT 1
  UNION ALL
  SELECT n + 1 FROM sequence WHERE n < 10
)
SELECT n FROM sequence ORDER BY n;
```

The same pattern follows a hierarchy using a join in the step:

```sql
WITH RECURSIVE team(id, manager_id, name, depth) AS (
  SELECT id, manager_id, name, 0 FROM employees WHERE id = 1
  UNION ALL
  SELECT e.id, e.manager_id, e.name, t.depth + 1
  FROM employees e JOIN team t ON e.manager_id = t.id
  WHERE t.depth < 20
)
SELECT name, depth FROM team ORDER BY depth, name;
```

The supported recursive shape is `anchor UNION [ALL] step`. The anchor cannot refer to its own CTE. The recursive body cannot carry a top-level WITH, ORDER BY, LIMIT, or OFFSET; place final sorting and pagination on the outer SELECT. The step must reference the CTE exactly once directly in FROM or JOIN; it may use INNER/CROSS joins and filters. Recursive steps cannot contain aggregates, GROUP BY, HAVING, DISTINCT, nested sources/CTEs, or further unions. Anchor and step outputs must have identical type vectors, including nullability, and the CTE's output names come from its explicit column list or the anchor. Earlier CTEs are visible; forward and mutual recursion are rejected. Under WITH RECURSIVE, names of current and later bindings are reserved rather than resolved to equally named physical tables. Ordinary CTEs are also allowed in a WITH RECURSIVE list.

`UNION` removes duplicate rows, while `UNION ALL` preserves them when executed by a database. Any number of nonrecursive arms can be combined. The original relational validator requires equal arity and identical output types, including nullability. The advanced validator also computes supported common numeric/nullable types for set operations; it does not model every PostgreSQL coercion. Output names come from the first SELECT. A compound query's final ORDER BY accepts an unambiguous output name or a positive integer literal denoting a one-based output position; arbitrary expressions and source-qualified names are rejected. Final ORDER BY, LIMIT, and OFFSET apply to the whole compound. The original API requires an aliased derived table to sort or limit an individual input. Advanced set operations also accept parenthesized operands with their own sorting and pagination.

SELECT without FROM uses an empty column scope. Constants, expressions, filters, and supported aggregate expressions can be checked; unbound columns and wildcards are rejected. This supplies constant anchors and seed relations without requiring a physical table.

This portable recursive shape follows the shared anchor/step structure documented by [PostgreSQL](https://www.postgresql.org/docs/current/queries-with.html) and [SQLite](https://www.sqlite.org/lang_with.html). Static certification does not establish termination or detect data cycles. A recursive query can be well typed and run indefinitely; callers must choose appropriate predicates or a suitable deduplicating UNION for their data.

PostgreSQL's DISTINCT ON keeps the first row for each key. For deterministic choices, provide enough ORDER BY keys to break ties:

```sql
SELECT DISTINCT ON (user_id) user_id, id, amount
FROM orders
ORDER BY user_id, amount DESC, id;
```

DISTINCT ON keys are resolved like ORDER BY keys, including aliases and output positions. The initial ORDER BY keys must come from DISTINCT ON; all DISTINCT ON keys must have appeared before an unrelated sort key. Permutations, repeated keys, and shorter all-matching initial orders are accepted. Omitting ORDER BY is permitted but does not select a predictable representative. DISTINCT ON keys also obey expression typing and grouping rules; ordinary DISTINCT and DISTINCT ON cannot coexist in a hand-built AST. See PostgreSQL's [SELECT documentation](https://www.postgresql.org/docs/current/sql-select.html).

FILTER selects the input rows for one aggregate:

```sql
SELECT user_id,
       COUNT(*) FILTER (WHERE status = 'paid') AS paid_orders,
       SUM(amount) FILTER (WHERE status = 'paid') AS paid_total
FROM orders
GROUP BY user_id
ORDER BY paid_total DESC NULLS LAST, user_id;
```

FILTER attaches directly to COUNT(*) or COUNT/SUM/AVG/MIN/MAX, including DISTINCT arguments. Its predicate must be boolean and cannot contain aggregates. It does not change the aggregate's output type or make a nullable aggregate non-null. NULLS FIRST/LAST is stored independently of ASC/DESC and works on ordinary and compound query ordering. FILTER follows PostgreSQL's [aggregate-expression syntax](https://www.postgresql.org/docs/current/sql-expressions.html#SYNTAX-AGGREGATES).

In the original relational API, `expr::type` and `CAST(expr AS type)` accept INT/INTEGER, TEXT, BOOL/BOOLEAN, REAL, and DOUBLE PRECISION. `CastType` preserves REAL versus DOUBLE PRECISION so rendering preserves the requested precision; both belong to the static `SqlType.real` family. Supported conversions are identity, conversions to/from text, integer/real conversions, and integer/boolean conversions. Casts preserve nullability. Certification checks that a conversion is supported, not that textual values parse or numeric values fit at execution time. The advanced API adds BIGINT, VARCHAR, NUMERIC, and supported length/precision/scale modifiers through `Advanced.DataType`. Arrays and user-defined cast targets remain unsupported.

Both expression APIs and RETURNING projections accept LIKE/ILIKE, nonempty IN expression lists, BETWEEN bounds, and their NOT variants. LIKE/ILIKE require text operands and propagate nullability. IN remains a dedicated AST node and renders as IN, preserving PostgreSQL's common-type coercion across its operands. The original `RelExpr` normalizes BETWEEN into two inclusive comparisons joined by AND. `Advanced.Expr` keeps a dedicated BETWEEN node, preserving parameter identity and nested expressions during rendering. Advanced expressions also support IN subqueries. BETWEEN SYMMETRIC, explicit ESCAPE clauses, and volatile functions remain unsupported. PostgreSQL documents LIKE/ILIKE in [pattern matching](https://www.postgresql.org/docs/current/functions-matching.html).

Mutation RETURNING exposes the affected row through the same rich projection syntax:

```sql
UPDATE users SET age = age + 1 WHERE id = 7
RETURNING id, age, name ILIKE 'a%' AS starts_with_a;

DELETE FROM orders WHERE status = 'cancelled'
RETURNING orders.*, CAST(amount AS TEXT) AS amount_text;
```

The statement certificate validates the complete mutation before checking RETURNING. Projection names resolve against the target table; wildcards, qualified columns, aliases, and scalar expressions are supported. Aggregates are forbidden, and the projection must be nonempty. Bare mutations still return an empty output-type list; RETURNING statements report their projection types. The legacy mutation constructors retain their existing expression grammar. The advanced statement constructors add target aliases, ON CONFLICT, rich mutation expressions, and RETURNING subqueries. UPDATE FROM, DELETE USING, and old/new row aliases remain unsupported. The library does not execute mutations or model trigger effects. See PostgreSQL's [RETURNING documentation](https://www.postgresql.org/docs/current/dml-returning.html).

The original relational and CRUD grammar remains available through the compatibility APIs. Its grammar is:

```ebnf
statement = (select | insert | update | delete) [";"] ;
select    = [WITH [RECURSIVE] cte {"," cte}]
            selectCore {UNION [ALL] selectCore}
            [ORDER BY orderItem {"," orderItem}]
            [LIMIT integer [OFFSET integer]] ;
selectCore = SELECT [DISTINCT [ON "(" exprList ")"]] selectItem {"," selectItem}
             [FROM source {join}]
             [WHERE expr] [GROUP BY exprList] [HAVING expr] ;
cte       = identifier ["(" identifier {"," identifier} ")"] AS "(" select ")" ;
source    = identifier [[AS] identifier] | "(" select ")" [AS] identifier ;
join      = [INNER] JOIN source ON expr
          | (LEFT | RIGHT | FULL) [OUTER] JOIN source ON expr
          | CROSS JOIN source ;
selectItem = "*" | identifier "." "*" | expr [[AS] identifier] ;
insert    = INSERT INTO identifier ["(" identifier {"," identifier} ")"]
            VALUES row {"," row} [returning] ;
row       = "(" exprList ")" ;
update    = UPDATE identifier SET assignment {"," assignment} [WHERE expr] [returning] ;
assignment = identifier "=" expr ;
delete    = DELETE FROM identifier [WHERE expr] [returning] ;
returning = RETURNING selectItem {"," selectItem} ;
orderItem = expr [ASC | DESC] [NULLS (FIRST | LAST)] ;
exprList  = expr {"," expr} ;
expr      = orExpr ;
orExpr    = andExpr {OR andExpr} ;
andExpr   = notExpr {AND notExpr} ;
notExpr   = {NOT} cmpExpr ;
cmpExpr   = addExpr [("=" | "<>" | "!=" | "<" | "<=" | ">" | ">=") addExpr
                    | IS [NOT] NULL | [NOT] (LIKE | ILIKE) addExpr
                    | [NOT] IN "(" exprList ")" | [NOT] BETWEEN addExpr AND addExpr] ;
addExpr   = mulExpr {("+" | "-") mulExpr} ;
mulExpr   = unaryExpr {("*" | "/") unaryExpr} ;
unaryExpr = {"+" | "-"} primary ;
primary   = atom {"::" castType} ;
atom      = identifier ["." identifier] | integer | string | TRUE | FALSE
          | "(" expr ")" | CAST "(" expr AS castType ")"
          | aggregate [FILTER "(" WHERE expr ")"] ;
aggregate = COUNT "(" "*" ")"
          | (COUNT | SUM | AVG | MIN | MAX) "(" [DISTINCT] expr ")" ;
castType  = INT | INTEGER | TEXT | BOOL | BOOLEAN | REAL | DOUBLE PRECISION ;
```

In this compatibility grammar, qualification, PostgreSQL scalar expressions, IS NULL, and aggregates extend SELECT; RETURNING supports the scalar subset. Legacy INSERT values and UPDATE/DELETE clauses retain their original unqualified expression grammar. Advanced mutations use `Advanced.Expr`, including NULL, decimals, parameters, and subqueries. Aggregates take one expression, except COUNT(*). COUNT(DISTINCT *) is rejected. Ordinary columns named `count`, `sum`, `avg`, `min`, or `max` remain usable without parentheses. Nested SELECTs cannot contain semicolons.

Postfix casts bind before unary signs, followed by multiplication/division, addition/subtraction, the predicate/comparison tier, NOT, AND, and OR. Binary chains associate left. This subset uses a single nonchainable tier for comparison operators, LIKE/ILIKE, IN, BETWEEN, and IS NULL; use parentheses for mixed forms such as `(name LIKE 'a%') = TRUE`. It does not implement PostgreSQL's complete operator precedence table. Comparison chains such as `a < b < c` are rejected. Integers are arbitrary-precision decimal numerals; a leading sign is a separate unary AST node. The original compatibility grammar takes unsigned integer LIMIT/OFFSET literals. The advanced grammar accepts expression bounds, including parameters and casts, with either LIMIT/OFFSET order or OFFSET alone. SQLite comma-style LIMIT remains literal-only and requires LIMIT before OFFSET; LIMIT ALL remains deferred in the typed AST. See the [pagination contract](docs/pagination-contract-v0.2.md) for static and runtime obligations.

GROUP BY and ORDER BY accept expressions, whole-key result aliases, or one-based selected-column positions. Zero, negative, and out-of-range positions are rejected by validation. GROUP BY prefers an input column when its name conflicts with a result alias; ORDER BY prefers the output name. Output-name lookup includes natural bare-column names and explicit aliases; repeated names must denote identical expressions after column resolution. Aliases inside larger expressions and aliases in HAVING are not substituted. With DISTINCT, sort expressions must occur in the selected projection after alias/ordinal expansion. Wildcards expand in FROM/JOIN column order.

An aggregate query's SELECT, HAVING, and ORDER BY expressions must use grouping keys, constants, aggregates, or expressions built from them. GROUP BY expressions are compared structurally after resolving column names, so an unqualified column and its uniquely resolved qualified form agree. Functional dependencies, such as assuming another column is determined by a grouped primary key, are not inferred. Aggregates are forbidden in WHERE, ON, GROUP BY, and arguments to other aggregates. HAVING also creates an aggregate query when GROUP BY is absent.

The typed AST remains a SQL subset, separate from the complete grammar interface. Remaining unsupported typed forms include recursive SEARCH/CYCLE, window functions, named/variadic call notation, additional JSON/array operators, database-qualified relation names, DML CTEs, UPDATE FROM, DELETE USING, row-valued IN, per-value DEFAULT, and transaction commands. DDL is limited to the table forms described below; foreign keys, CHECK constraints, views, indexes, sequences, permissions, and schema DDL are not modeled. Exactly one statement and at most one trailing semicolon are accepted.

Keywords are case-insensitive. Unquoted identifiers begin with ASCII letters or `_`, followed by ASCII letters, digits, or `_`; the advanced lexer also permits `$` after the first character. Double-quoted identifiers preserve spelling and allow reserved words. The original reserved-word policies are in `Parser.crudReservedWords` and `Parser.relationalReservedWords`; advanced syntax has its own reserved-word set. Escape quotes by doubling them: `'O''Brien'` and `"a""b"`. Empty quoted identifiers are rejected. Strings and quoted identifiers support Unicode. Both lexers accept `--` line comments and `/* ... */` comments; the advanced lexer additionally supports nested block comments. Parse errors carry a zero-based character offset and one-based line/column positions.

Import `SQLean` to use the library:

```lean
import SQLean
open SQLean

def users : Schema := [
  { name := "users", columns := [⟨"id", .int⟩, ⟨"age", .int⟩] }
]

#eval (parseStatement "SELECT * FROM users ORDER BY age DESC LIMIT 10").map toSql
#eval (parseAndValidateStatement users "UPDATE users SET age = age + 1 WHERE id = 7").map
  (fun checked => checked.certificate.outputTypes)  -- Except.ok []
#eval (parseAndValidateStatement users
  "SELECT age, COUNT(*) AS n FROM users GROUP BY age ORDER BY n DESC").map
  (fun checked => checked.certificate.outputTypes)  -- Except.ok [SqlType.int, SqlType.int]
#eval (parseAndValidateStatement users
  "UPDATE users SET age = age + 1 WHERE id = 7 RETURNING id, age::TEXT").map
  (fun checked => checked.certificate.outputTypes)  -- Except.ok [SqlType.int, SqlType.text]
#eval (parseAndValidateRelQuery users
  "SELECT COUNT(*) FILTER (WHERE age >= 18) AS adults FROM users").map
  (fun checked => checked.certificate.outputTypes)  -- Except.ok [SqlType.int]

-- Request the relational AST even for a simple SELECT.
#eval (parseRelQuery "SELECT id FROM users").map toSql
#eval do
  let query ← (parseRelQuery "SELECT AVG(age) AS mean_age FROM users").mapError toString
  (checkRelQuery users query).mapError toString  -- Except.ok [SqlType.nullable SqlType.real]

-- A uniform relational AST and its certificate, including recursive CTEs.
#eval (parseAndValidateRelQuery []
  "WITH RECURSIVE s(n) AS (SELECT 1 UNION ALL SELECT n + 1 FROM s WHERE n < 5) SELECT n FROM s").map
  (fun checked => checked.certificate.outputTypes)  -- Except.ok [SqlType.int]

-- The original API still accepts the original, strict SELECT MVP grammar.
#eval (parseQuery "SELECT id FROM users").map toSql
#eval (parseAndValidate users "SELECT id FROM users WHERE age >= 18").map
  (fun checked => checked.certificate.outputTypes)  -- Except.ok [SqlType.int]
```

| Interface | Purpose |
| --- | --- |
| `Statement`, `Mutation`, `SelectQuery`, `InsertQuery`, `UpdateQuery`, `DeleteQuery` | Public CRUD and RETURNING syntax constructors. |
| `Projection`, `OrderBy`, `Assignment`, `Expr`, `BinOp`, `UnOp`, `Value` | Public syntax components. |
| `RelQuery`, `RelExpr`, `CastType`, `TableRef`, `Join`, `JoinKind`, `SelectItem`, `RelOrderBy`, `AggregateFn`, `CTE`, `UnionBranch` | Public syntax for relational SELECTs, PostgreSQL expressions, nested sources, and compounds. |
| `Schema`, `TableDef`, `ColumnDef`, `SqlType` | External table and column definitions. |
| `parseStatement` | `String → Except ParseError Statement`; consumes the complete input. |
| `parseRelQuery` | `String → Except ParseError RelQuery`; always returns the relational AST. |
| `ToSql` / `toSql` | SQL rendering with escaped identifiers/strings and explicit parentheses. |
| `certifyStatement schema statement` | `CertifiedStatement schema statement`, containing `outputTypes` and a validity proof. |
| `checkStatement schema statement` | Output types or a validation error; mutations without RETURNING have no output columns. |
| `parseAndValidateStatement schema source` | A parsed AST and its certificate packaged as `CheckedStatement schema`. |
| `parseAndValidateRelQuery schema source` | A uniform relational AST and its certificate packaged as `CheckedRelQuery schema`. |
| `certifyRelQuery schema query` | `CertifiedRelQuery schema query`, with output types, names, and proofs for the query and its nested sources. |
| `checkRelQuery schema query` | Relational result types or a validation error. |
| `Query`, `parseQuery` / `parse`, `certifyQuery`, `checkQuery`, `parseAndValidate` | The original SELECT API, retained for compatibility. |

The original `parseQuery` source parser retains its strict MVP grammar and reserved-name policy, including mandatory FROM. `parseStatement` tries the legacy SELECT grammar first, returning `.select` there and `.relational` for richer SELECT syntax, then falls back to `.extended` for the advanced syntax. RETURNING is reserved in the statement grammar; quote existing identifiers with that name. INSERT/UPDATE/DELETE constructors remain available, and `Statement.returning` wraps a `Mutation` and its output items. Use `parseRelQuery` or `parseAndValidateRelQuery` for the original consistent relational AST, or `Advanced.parse` for the uniform advanced AST. The low-level legacy token APIs retain their original grammar and expect lexer-produced tokens with exactly one final EOF. Shared original syntax types now live in `SyntaxBase.lean`, re-exported by `AST.lean`. The compatibility `certifyStatement schema statement` API checks `.extended` statements with an empty parameter environment and a catalog converted from the original schema. Use `parseAndValidateAdvanced` when parameters, defaults, key metadata, or resulting catalog transitions are needed.

The advanced corpus adds **750 examples, 50 per class**: [IN subqueries](fixtures/advanced/in_subqueries.sql), [EXISTS](fixtures/advanced/exists.sql), [LATERAL](fixtures/advanced/lateral.sql), [USING](fixtures/advanced/using_joins.sql), [NATURAL](fixtures/advanced/natural_joins.sql), [INTERSECT](fixtures/advanced/intersect.sql), [EXCEPT](fixtures/advanced/except.sql), [UPSERT](fixtures/advanced/upsert.sql), [INSERT SELECT](fixtures/advanced/insert_select.sql), [NULL](fixtures/advanced/nulls.sql), [decimal/exponent numbers](fixtures/advanced/floating.sql), [parameters](fixtures/advanced/placeholders.sql), [CREATE TABLE](fixtures/advanced/create_table.sql), [ALTER TABLE](fixtures/advanced/alter_table.sql), and [DROP TABLE](fixtures/advanced/drop_table.sql). Each has independent output-type expectations; parameterized cases also declare parameter types and test values.

Run their database comparisons with PostgreSQL binaries available locally:

```sh
python3 scripts/check_advanced_cli.py --local-bin /usr/lib/postgresql/16/bin
```

The checker performs 1,500 source/canonical result/status comparisons (including 1,180 row-result comparisons), 526 mutation/DDL state comparisons, and 61 independent result/catalog oracles on empty and populated databases. DDL state checks include table/column names, types, defaults, nullability, constraints, and rows. Parameter cases use PostgreSQL PREPARE/EXECUTE as well as COPY result capture; question marks inside quoted text remain text. The script uses temporary databases and the NULL-preserving COPY decoder.

For parameterized statements, `check_advanced_cli.py` currently discards the
PREPARE/EXECUTE output and captures results from typed literal substitution.
Its parameter result oracles therefore directly cover the literal path only.
The separate bounded check below captures actual SQL EXECUTE rows through a
typed PL/pgSQL set-returning bridge and the same NULL-preserving COPY protocol:

```sh
python3 scripts/test_parameter_execution.py  # offline wiring/oracle tests only
python3 scripts/check_parameter_execution.py --local-bin /usr/lib/postgresql/16/bin
# Or: python3 scripts/check_parameter_execution.py --dsn "$TEST_DATABASE_URL"
```

It selects 12 historical placeholder fixtures (2, 17, 22–25, 27, 42, 47–50)
and adds one fixed NULL/marker-text/empty-string case without changing the
historical corpus. On empty and seeded tables, each execution path must match
handwritten expected rows and arity; RETURNING cases also compare database
snapshots after each path. Each path starts from the same savepoint state.
Repeated/out-of-order `$n`, quoted `?`, anonymous parameters, INSERT, UPDATE,
DELETE and UPSERT RETURNING are included. The bridge issues the actual SQL
`EXECUTE sqlean_parameters (...)`; it does not interpolate the prepared query.
Offline tests do not establish PostgreSQL execution success. A successful database
run would establish only these finite source-SQL checks, not CLI canonicalization,
wire-protocol binding, arbitrary SQL adapter correctness, or general semantic
equivalence. Use the local-cluster command as a non-root user.

Advanced queries support correlated IN, NOT IN, EXISTS, NOT EXISTS, and scalar subqueries. IN and scalar subqueries require one output column; scalar subquery results are conservatively nullable, and the checker does not prove at-most-one-row cardinality. Inner scopes shadow outer names. A LATERAL derived table can see preceding sources; ordinary derived tables cannot see sibling sources. LEFT LATERAL joins propagate nullability. USING and NATURAL joins merge unqualified shared columns and wildcard outputs while retaining both qualified original columns. INTERSECT binds more tightly than UNION/EXCEPT; UNION and EXCEPT associate left. ALL variants preserve bag-operation syntax. Parenthesized operands retain their own sorting and pagination.

```sql
SELECT u.id FROM users u
WHERE EXISTS (SELECT 1 FROM orders o WHERE o.user_id = u.id);

SELECT u.id, recent.amount FROM users u
LEFT JOIN LATERAL (
  SELECT amount FROM orders o WHERE o.user_id = u.id ORDER BY id DESC LIMIT 1
) recent ON TRUE;

SELECT id FROM users INTERSECT SELECT user_id FROM orders
EXCEPT SELECT id FROM users WHERE age < 18;

INSERT INTO users (id, age, name, city)
SELECT id + 100, age, name, city FROM users
ON CONFLICT (id) DO UPDATE SET name = excluded.name
RETURNING id, name;
```

NULL is represented independently of text and waits for expression context; a bare selected NULL resolves to nullable text. Decimal and exponent literals retain their exact lexemes, including `.5`, `1.`, and `1.2e-3`; parsing never rounds through a machine float. Decimal/exponent literals and noninteger numeric cast targets use the coarse `SqlType.real` family; integer literals and INT/BIGINT targets use `SqlType.int`. The advanced AST preserves distinctions between NUMERIC, REAL, and DOUBLE PRECISION and retains supported modifiers. Type-name synonyms normalize to canonical SQL names. Numeric range, rounding, overflow, and successful text conversion are runtime concerns.

Both PostgreSQL `$1` parameters and client-style `?` parameters are supported. Anonymous parameters are numbered in source order, starting at one; mixed styles are rejected. Default rendering preserves their style, and `Advanced.renderPostgres` / CLI `--postgres` converts `?` to the corresponding `$n`. A dedicated advanced BETWEEN node prevents parameter duplication during rendering. Validation requires an explicit parameter-type environment; it does not silently guess types for missing bindings.

```sh
lake exe sqlean --param-types int,int,int --postgres 'SELECT ? BETWEEN ? AND ?'
lake exe sqlean --schema fixtures/advanced/schema.json --param-types int \
  'SELECT id FROM users WHERE id = $1'
```

Compatibility parameter types are `int,text,bool,real`; a suffix `?` permits NULL values, for example `int,text?`. Contract parameter input additionally recognizes concrete `bigint`, `double`, `numeric`, and `varchar` declarations so unsupported exact types can be reported without collapsing them. Advanced schema JSON retains concrete `int`, `bigint`, `text`, `bool`, `real`, `double precision`, `numeric`, and `varchar` declarations and an optional `modifiers` array of nonnegative integers. It also accepts a `nullable` Boolean (default false), a `default` SQL-expression string, table `uniqueKeys` arrays, a `primaryKey` column array, and a `namedKeys` object mapping constraint names to column arrays. `Advanced.parseCatalogJson` validates this metadata with the expanded checker; `Advanced.decodeCatalogJson` only decodes its structure, allowing the contract checker to validate the environment independently. ON CONFLICT targets must match a declared unique key or named constraint. DO UPDATE requires a target; its expressions can qualify the target table or `excluded`. Unqualified names shared by both scopes are ambiguous. Omitted INSERT columns require a default or nullable type; INSERT SELECT checks arity and assignment compatibility.

Table DDL supports CREATE TABLE / IF NOT EXISTS, column NULL/NOT NULL and constant DEFAULT expressions, and column/table PRIMARY KEY and UNIQUE constraints. Types include INT/INTEGER, BIGINT, TEXT, VARCHAR with optional length, BOOLEAN, REAL, DOUBLE PRECISION, and NUMERIC with optional precision/scale. ALTER TABLE supports ADD/DROP COLUMN with existence guards, RENAME COLUMN/TO, compatible ALTER COLUMN TYPE, SET/DROP NOT NULL, and SET/DROP DEFAULT. Multiple actions must affect distinct columns; RENAME is standalone. This conservatively avoids PostgreSQL's phase-dependent combinations. DROP TABLE supports IF EXISTS and RESTRICT/CASCADE. The catalog models only tables and local unique/primary constraints, not external dependency graphs or row data.

Use the catalog API to check a DDL sequence and feed each resulting catalog into the next statement:

```lean
import SQLean
open SQLean

def exampleCatalog : Advanced.Catalog := [{
  name := "users"
  columns := [{ name := "id", type := ⟨.int, []⟩, nullable := some false }]
  uniqueKeys := [["id"]] }]

#eval (parseAndValidateAdvanced exampleCatalog [(1, .int)]
  "SELECT EXISTS (SELECT 1 FROM users WHERE id = $1)").map
  (fun checked => checked.result.outputTypes)

#eval do
  let statements ← (["CREATE TABLE items (id INT PRIMARY KEY, label TEXT)",
    "ALTER TABLE items ADD COLUMN price REAL DEFAULT 0.0"].mapM Advanced.parse).mapError toString
  (Advanced.checkStatements [] [] statements).mapError toString
```

Public advanced interfaces include `Advanced.Statement`, `Query`, `Expr`, `From`, `DataType`, `Column`, `Catalog`, `ParameterEnv`, `parse`, `parseQuery`, `parseExpression`, `render`, `renderPostgres`, `checkQuery`, `inferExpr`, `checkStatementDetailed`, `certifyStatement`, and `checkStatements`. `parseAndValidateAdvanced catalog params source` returns the AST, output types, resulting catalog, and a Lean proof that the bounded static checker accepted that result. The advanced certificates attest this algorithmic contract; they are not independent declarative SQL-semantics proofs. The existing declarative proofs remain available for the original constructors.

Advanced validation limits recursive CTEs to the documented portable anchor/step shape and rejects forward references, including physical-table homonyms under WITH RECURSIVE. It conservatively rejects aggregates whose arguments/FILTER refer to an outer query level and some PostgreSQL implicit coercions; explicit casts and local aggregate inputs avoid these cases. Query validation has a depth budget of 1,024 and reports exhaustion as an error. Additional modifiers directly around an already-modified parenthesized query require a derived table. DDL certificates describe schema transitions only: they do not establish that existing rows satisfy a new NOT NULL/unique constraint, that casts succeed, or that a database operation will execute successfully.

In the relational AST, `recursive` records the WITH RECURSIVE modifier, and `unions` holds the subsequent `UnionBranch` arms in order (`all = true` for UNION ALL). The root query owns global sorting and pagination. A source with an empty name, no alias, and no derived query denotes absent FROM. Validation rejects malformed hand-built AST combinations as well as invalid parsed queries.

`RelQuery.distinctOn` holds DISTINCT ON keys and is mutually exclusive with `distinct = true`. `RelOrderBy.nullsFirst` distinguishes the default (`none`), FIRST (`some true`), and LAST (`some false`). `RelExpr.cast`, `pattern`, `filteredAggregate`, and `inList` preserve the corresponding PostgreSQL syntax. `RelExpr.between` supplies the normalized comparison AST; `RelExpr.inValues` builds an IN node whose list must be nonempty for certification.

Contract catalog JSON additionally accepts a table `schema` component and
`exposeUnqualified` Boolean. Schema-bearing entries default to hidden from
unqualified lookup; legacy entries default to exposed. An explicitly exposed
entry represents the caller's resolved connection visibility, not a search-path
algorithm. Full `(schema, name)` identities and exposed basenames must each be
unique. Qualified names preserve component boundaries, including quoted dots.
The older expanded checker rejects schema-aware catalogs rather than erasing
their identity. See the [v0.23 contract](docs/qualified-names-contract-v0.23.md).

Static validity requires a well-formed schema, existing relations, and uniquely resolved, correctly typed expressions. A table alias hides that table's original qualifier and schema path. Unqualified column names must identify exactly one visible column; duplicate relation aliases are rejected. Distinct unaliased tables with the same basename can coexist across schemas, but a reference by that basename is ambiguous even when only one table has the requested column. ON cannot reference a later JOIN. In the original relational API, ON sees preceding relations and the current JOIN source; CROSS JOIN forbids ON and the other join kinds require it. `Advanced.From` preserves join trees and separately represents ON, USING, and NATURAL joins.

Relational arithmetic accepts integer/real operands; ordered comparisons accept numeric pairs or two text operands. Equality accepts matching base types or a numeric pair. Logical operators and predicates require boolean base types. The original CRUD expression checker retains its integer arithmetic/comparison rules. The original INSERT checker requires complete target coverage and checks every row's arity/types in an empty column environment. Advanced INSERT additionally uses catalog defaults/nullability and validates SELECT sources and conflict actions. UPDATE checks unique assignment targets and matching value types against the original table environment, so swaps such as `SET id = age, age = id` typecheck. UPDATE and DELETE without WHERE are valid.

Outer joins make the unmatched side's result types nullable: right for LEFT, left for RIGHT, both for FULL. Arithmetic, comparisons, and logical operators propagate nullable inputs; IS NULL and IS NOT NULL return non-null booleans. Predicates accept nullable booleans. COUNT returns a non-null integer. SUM returns a nullable numeric type, AVG a nullable real, and MIN/MAX a nullable numeric or text type. These are static type annotations; the parser and checker do not evaluate SQL values or use WHERE clauses to narrow nullability.

For the original expression, CRUD, and relational constructors, the declarative typing and validity relations are separate from their executable checkers. Lean checks soundness and completeness equivalences for the original query checker, the relational core, and complete nested queries, including:

```text
inferType_iff:
  inferType columns expr = .ok type ↔ HasType columns expr type
checkQuery_iff:
  checkQuery schema query = .ok types ↔ ValidQuery schema query types
inferRelType_iff:
  inferRelType scope aggregates expr = .ok type ↔ RelHasType scope aggregates expr type
checkRelQueryCore_iff:
  checkRelQueryCore schema query = .ok types ↔ ValidRelQueryCore schema query types
checkRelQuery_iff:
  checkRelQuery schema query = .ok types ↔ ValidRelQuery schema query types
checkStatement_iff:
  checkStatement schema statement = .ok types ↔ ValidStatement schema statement types
```

The full relational certificate composes child query proofs, CTE scope extensions, recursive anchor/step checks, compound output compatibility, output naming checks, and the flat core derivation. `checkRelQuery_iff` establishes that the full checker accepts exactly the queries satisfying `ValidRelQuery` for the supplied schema and AST. The statement certificate API and its equivalence theorem also cover relational SELECTs. The `.extended` constructor embeds the explicitly algorithmic advanced static-check contract described above; it does not add an independent declarative typing derivation for the advanced syntax. These proofs use standard Lean axioms; there are no `sorry` placeholders or custom axioms.

These are static guarantees. The checked SELECT renderer additionally carries
exact instance reconstruction proofs described above; general
grammar-correctness and universal round-trip proofs remain open. The library
does not execute queries or prove row-level constraints, division safety,
recursive termination/cycle safety, write effects, transaction behavior, or
ACID properties. For example, `1 / 0` remains well typed. SQLite and PostgreSQL
checks provide additional test evidence, not a formal semantic equivalence claim.
