# Unchanged recursive SELECT CTE sources

This fixed population contains 50 complete original queries: 14 PostgreSQL
engine regressions, 31 DuckDB engine regressions, four SQLC compiler tests,
and one shipping Hatchet application constant. All 50 contain an actual
recursive reference; a `WITH RECURSIVE` keyword alone is not counted as a
factor witness. The statements are distinct both exactly and after the
repository's case/whitespace comparison, and none repeats an earlier
factor's concrete query.

`concrete_sources.json` binds every input to its complete pinned source file,
source selector, SQL hash, license, and commit. Twelve complete source files
and four license files are retained or reused. The existing pins are:

- [PostgreSQL](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256),
  PostgreSQL license.
- [DuckDB](https://github.com/duckdb/duckdb/tree/917243df252f114d9c448b1d23f8618f0d683769),
  MIT.
- [SQLC](https://github.com/sqlc-dev/sqlc/tree/0f1602fe1a4b780336e3e878dde720892fd8578d),
  MIT.
- [Hatchet](https://github.com/hatchet-dev/hatchet/tree/392e7c472221cdab235cca674640e98f904e1ea0),
  MIT. `getRunsListRecursive` is a real task/DAG hierarchy query. Its catalog
  and parameter types remain unspecified rather than being invented.

The population has 58 CTE definitions, including 55 actually recursive
definitions, and 157 relation occurrences. Thirty-three queries use
`UNION ALL` in an actual recursive definition; the others use duplicate
eliminating `UNION`. It includes explicit column lists, table aliases and
alias column lists, multiple sequential definitions, ordinary CTEs inside
recursive terms, joins, arrays and slices, string concatenation, Unicode
quoted column names, and outer sorting/pagination. Every selected recursive
definition has a root UNION, no anchor self-reference, and one recursive-arm
self-reference. This is observed source structure, not a proof that every
statement meets all PostgreSQL recursive-analysis rules.

The source observer resolves relation names against lexical CTE definitions.
It records definition and reference UTF-8 byte positions, the containing
anchor/step contexts, and actual self-reference counts. WITH RECURSIVE names
are visible throughout their sibling group; ordinary WITH names become
visible sequentially. Nested shadowing is resolved by definition identity,
not by counting matching identifier text. Qualified relations remain
external. The observer distinguishes raw SELECT set operands from JOIN
operands and follows nested subqueries. It does not resolve columns, infer
types or collations, consult catalogs, or infer successful execution.

Thirty-one queries are syntactically source-free. Ten of those have existing
prerequisite gaps recorded separately from the recursion factor. Across the
entire population, five queries contain scalar subqueries, five aggregates,
three ordinary helper calls, and two DISTINCT clauses; these groups may
overlap. Nineteen queries depend on external relations or parameters.
Hatchet's parameter inventory is first-occurrence order `[2, 1, 3, 4]`, and
one SQLC query uses `[1]`; no parameter values or types are fabricated.
`source_free` is a lexical dependency observation, not a certificate-success
filter.

Exactly 21 closed queries were preregistered for full static certificates by
inspecting their SQL and the independent recursive/collation rules before
running the checker. `source_contracts.json` fixes 24 ordered positions:
20 INT32, two TEXT, one INTEGER array, and one BIGINT. Every position is
nullable because the outer projections reference actual recursive CTE
bindings. Names preserve explicit `zz`, `arr`, and Unicode `fibₙ` aliases.
The two string-concatenation recursions use closed default-collation literals
and recursive references, with no NAME or external collatable source.
The JSON registry is checked against a separately declared Lean ID/output
registry. The other 29 statements receive rendering evidence without
invented catalog, parameter, function, or subquery assumptions.

Whole SQL statement spans and the complete Go constant reuse existing
readers. The dedicated DuckDB SQLLogicTest reader recognizes every record
through the selected header and preserves the complete query input,
including its final newline. It recognizes only the additional literal
control `require no_alternative_verify`, which precedes three selected
inputs and is retained in their provenance. Setup statements, PRAGMAs,
controls, conditions, and expected-result bodies are never executed.
Unknown prefix controls fail closed, while content after the selected
query is outside that selection's reader boundary.

The concrete queries receive checked identity/PostgreSQL rendering. Downloaded
SQL and source programs are never executed. Native database observations use
separately authored fixtures, and DuckDB/PostgreSQL regression expected values
are not imported as runtime oracles. This corpus does not claim recursion
termination: an unbounded recursive query with an outer LIMIT can be a
legitimate static input.

```sh
python3 scripts/extract_recursive_contract_corpus.py --check
python3 -m unittest discover -s scripts -p 'test_recursive_extraction.py'
```

Optional `--oracle` requires pinned pglast 7.21 and recomputes raw-tree syntax
observations. Its PostgreSQL 17 parser is an observation tool, not the
PostgreSQL 16 static-validity specification. The separate pinned PostgreSQL
16 grammar replay also includes all 50 inputs. Offline reproduction needs
only retained sources, standard-library readers, selectors, and hashes.
