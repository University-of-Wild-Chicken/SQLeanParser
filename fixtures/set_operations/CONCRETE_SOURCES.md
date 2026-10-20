# Unchanged UNION, INTERSECT, and EXCEPT sources

This population contains 150 distinct original SELECT statements: 50 assigned
to UNION, 50 to INTERSECT, and 50 to EXCEPT. The assignments are disjoint even
when a statement contains multiple kinds of set operation. Comparison after
case/whitespace normalization also preserves all 150 identities. No source SQL,
Tcl program, SQLLogicTest directive, or condition is executed by extraction.

The source statements are engine or compiler regression inputs, not production
traffic: 148 engine inputs and two sqlc compiler inputs. Each JSONL row retains
the original SQL, source commit, source URL and line, complete-input selector,
SQL hash, license, and dialect where applicable. `raw_sql == sql`, and
`transformations` is empty. The full pinned files and license hashes are listed
in `concrete_sources.json`; 34 source files are retained or reused.

## Sources and licenses

- PostgreSQL, commit
  [`f0595c3d839debdb140903621c1b44a4f4d86256`](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256),
  supplies 20 UNION, 17 INTERSECT, and 30 EXCEPT inputs. The PostgreSQL license
  is retained at `../extended_types/licenses/postgres-COPYRIGHT.txt`.
- DuckDB, commit
  [`917243df252f114d9c448b1d23f8618f0d683769`](https://github.com/duckdb/duckdb/tree/917243df252f114d9c448b1d23f8618f0d683769),
  supplies 23 UNION, seven INTERSECT, and four EXCEPT inputs. Its MIT license is
  retained at `../factor_sources/licenses/duckdb-LICENSE`.
- SQLite, commit
  [`5484850c7a2cd90f2a06b8d4f3453b259aefc1e1`](https://github.com/sqlite/sqlite/tree/5484850c7a2cd90f2a06b8d4f3453b259aefc1e1),
  supplies seven UNION and 14 INTERSECT inputs. Its public-domain declaration
  is retained at `../factor_sources/licenses/sqlite-LICENSE.md`.
- Materialize, commit
  [`726570dba1d2e4d839c707a84a986fb3b3acc5c3`](https://github.com/MaterializeInc/materialize/tree/726570dba1d2e4d839c707a84a986fb3b3acc5c3),
  supplies 11 INTERSECT and 15 EXCEPT inputs. This source-available snapshot
  retains Business Source License 1.1, with change date 2030-10-20 and change
  license Apache-2.0, at
  `../factor_sources/licenses/materialize-20261020-LICENSE`. The copied files'
  attribution and Cockroach derivation notices remain intact; these inputs
  are not relicensed by this project.
- sqlc, commit
  [`0f1602fe1a4b780336e3e878dde720892fd8578d`](https://github.com/sqlc-dev/sqlc/tree/0f1602fe1a4b780336e3e878dde720892fd8578d),
  supplies one INTERSECT and one EXCEPT compiler input. Its MIT license is
  retained at `../extended_types/licenses/sqlc-LICENSE.txt`.

## Selection and observation boundaries

SQL files use complete statement spans. SQLite inputs use the existing finite
Tcl literal-block reader, which never evaluates substitutions or executes host
commands. SQLLogicTest selections bind complete ordinary query input blocks
with their exact delimiter and offsets, including their final newline.

The set-operation reader recognizes a bounded prefix through the selected
input. Unselected statements, expected errors, and expected result bodies are
opaque. Materialize's unselected `query T multiline` plan results end at a
literal `EOF` line; query-looking text inside those results cannot become a
source selection. The exact unselected
`simple conn=mz_system,user=mz_system` record is skipped without connecting to
anything. One older unselected Cockroach query omits its empty-result
separator; selected records still require the separator. Unknown directives
before the selected input fail extraction.

Sixteen selected Materialize inputs retain `onlyif cockroach` as provenance
(seven INTERSECT and nine EXCEPT inputs). No condition is evaluated, and their
presence is not a claim that Materialize supports the statement. Upstream
expected values, plans, row counts, and errors are never used as PostgreSQL
value or type oracles.

The optional pinned pglast 7.21 observer records each raw set-operation node,
its operator and ALL flag, structural path, and local ORDER BY/LIMIT/OFFSET
presence. Both raw `larg`/`rarg` SELECT children and similarly named JOIN
children are traversed correctly. Relation spellings and byte positions are
checked independently, and sequential nonrecursive CTE visibility distinguishes
references from external tables. This observer does not infer output types or
consult any application catalog.

There are 210 observed set-operation nodes: 101 UNION (53 ALL), 51 INTERSECT
(seven ALL), and 58 EXCEPT (14 ALL). Within its assigned factor, 28 UNION inputs,
seven INTERSECT inputs, and 12 EXCEPT inputs exercise ALL. Nested operands,
mixed operations, derived sources, current nonrecursive CTEs, type resolution,
NULLs, output aliases, and operand-local modifiers are retained unchanged.

Known PostgreSQL collation-error inputs, invalid literal conversions, illegal
set-operation locking or qualified ORDER BY references, recursive-error tests,
and unsupported VALUES inputs were excluded during selection. Four selected
catalog-dependent INTERSECT statements still need existing independent-contract
prerequisites: one COUNT query, one DISTINCT query, and two scalar-subquery
queries. These are explicit rendering-only cases.

## Fixed certificate registry

`source_contracts.json` preregisters 62 closed queries and 83 ordered output
columns: 50 UNION queries/63 columns, six INTERSECT queries/10 columns, and six
EXCEPT queries/10 columns. Its columns were inspected before running the new
checker and are separately registered in the Lean corpus tests. They comprise
54 INT32, 13 TEXT, 11 NUMERIC, three DOUBLE PRECISION, and two TIMESTAMP positions;
eight positions are nullable. The explicit `t3(z)` CTE alias produces `x, z`,
overriding the inner projection's `y` label.

The canonical JSON SHA256 of that registry is
`cdcb59a9619748976cb6103fc02eacb9e855403ad4eb23c14e632db980579ec1`.
Offline extraction binds the fixed registry to exactly those 62 source-free
inputs. The remaining 88 originals receive checked rendering, with no invented
catalog, search path, column types, or parameter declarations. All 150 have an
empty observed parameter inventory. A raw-parser observation or checked
rendering certificate does not itself establish native execution results,
catalog validity, or semantic equivalence between database dialects.

Reproduce the bytes and optional raw-tree observations with:

```sh
python3 scripts/extract_set_operation_corpus.py --check
# In an environment containing exactly pglast 7.21:
python3 scripts/extract_set_operation_corpus.py --check --oracle
```

Authored native fixtures in `synthetic.json` are a separate population. The
native harness executes those authored inputs; it does not execute the 150
public originals.
