# Unchanged interval field/range source statements

Every query in `concrete.jsonl` contains a newly covered explicit interval field
or range qualifier. Plain `INTERVAL(p)` precision-only syntax is excluded. There
are 50 distinct complete statements: 49 PostgreSQL regressions and one DuckDB
regression, all source-free unaliased interval typed literals. No query is
rewritten, renamed, generated, or executed.

The PostgreSQL statements reuse the existing
[`interval.sql`](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/test/regress/sql/interval.sql)
snapshot at `f0595c3d839debdb140903621c1b44a4f4d86256`, under the
[PostgreSQL license](../extended_types/licenses/postgres-COPYRIGHT.txt).
The source includes 52 simple literal projections with interval modifiers.
Removing two unrestricted precision-only examples and the explicitly marked
conversion-error example `INTERVAL '123 11' DAY` leaves 49 positive candidates
that exercise the new qualifier syntax.

The fiftieth whole query is `SELECT INTERVAL '90' DAY;`, from
[`test/sql/types/interval/test_interval.test`](https://github.com/duckdb/duckdb/blob/917243df252f114d9c448b1d23f8618f0d683769/test/sql/types/interval/test_interval.test#L159)
at the existing DuckDB pin `917243df252f114d9c448b1d23f8618f0d683769`, under
[MIT](../factor_sources/licenses/duckdb-LICENSE). The complete SQLLogicTest
query block is selected by the existing finite reader. Its original whitespace
is retained, and its expected-result section remains opaque. DuckDB execution
behavior is not used as a PostgreSQL oracle.

All 13 explicit field/range forms are represented: YEAR, MONTH, DAY, HOUR,
MINUTE, SECOND, YEAR TO MONTH, DAY TO HOUR, DAY TO MINUTE, DAY TO SECOND,
HOUR TO MINUTE, HOUR TO SECOND, and MINUTE TO SECOND. Precision is absent in
38 statements and explicitly 2 in 12. The metadata preserves this distinction;
it never substitutes the maximum precision for an omitted precision.

`concrete_sources.json` fixes complete-file/license hashes, commit revisions,
statement/query-block boundaries, SQL hashes, and syntax metadata.
`observed_syntax.interval_fields` records the raw parser field mask, its SQL
range name, optional precision, and literal text. This is a syntax observation;
it neither evaluates the literal nor borrows upstream expected values. The
observer rejects the unrestricted mask 32767, unknown masks, arrays, parameters,
hidden expressions, catalogs, aliases, and other projection shapes.

All 50 have actual empty catalog/parameter environments. Their independent
fixed-ID contract tests verify the exact interval range/precision, output label
`interval`, and nonnullable output. Identity/PostgreSQL renderers check exact AST
round trips. Downloaded source SQL is never executed: separate authored
`synthetic.json` queries supply native PostgreSQL runtime expectations.
Grammar replay uses the project's pinned PostgreSQL 16 grammar; optional
`--oracle` checks the frozen syntax observations with pglast 7.21 (PostgreSQL 17.7).

```sh
python3 scripts/extract_factor_corpus.py --factor interval_fields --check
python3 -m unittest discover -s scripts -p 'test_interval_field_extraction.py'
```

Discovery against the original 276-query corpus identified seven SELECTs blocked
by interval field qualifiers: TPC-H Q4, Q5, Q6, Q10, Q12, Q14, and Q20. The
CREATE VIEW statement in Q15 also contains a qualifier but has a separate
statement-grammar dependency. Only replay of the unchanged original corpus
establishes the final acceptance count; temporary discovery edits are not fixtures.
