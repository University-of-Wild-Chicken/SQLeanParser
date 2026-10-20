# NULL-aware comparison and row null tests: v0.28

The profile `sqlean-basic-select-v0.28` adds independent validity rules for
`IS DISTINCT FROM`, `IS NOT DISTINCT FROM`, and null tests on direct flat row
constructors. The typed parser also accepts the PostgreSQL `ISNULL` and
`NOTNULL` spellings. Earlier syntax and lower assurance tiers remain available.
This increment does not complete the PostgreSQL validity contract.

## Separate native analysis paths

`Expr.distinctFrom left right negated` retains both original operands and the
polarity. It is not lowered to an ordinary comparison or a null test. The
independent specification distinguishes these PostgreSQL analysis paths:

- An ordinary scalar pair selects an exact admitted Boolean equality
  declaration using the existing overload resolver. The declaration's input
  types and implicit coercions are recorded by the derivation. This path
  explicitly excludes raw NULL and direct row operands.
- A top-level undecorated NULL operand bypasses equality resolution. The other
  operand must still be independently well typed. This admits JSON and JSON
  array operands without claiming an equality implementation for them.
- Two direct flat rows require equal lengths and one exact equality selection
  per pair of fields. Empty row pairs are admitted. Each field has already been
  typed: a NULL field does not invoke the top-level shortcut.
- A direct flat row opposite raw NULL has a separate rule. Its fields must be
  independently valid, but it does not require field equality declarations.

All admitted DISTINCT predicates have nonnullable Boolean output, regardless
of operand nullable flags. The inventory contains fixed built-in Boolean
equality declarations; this conclusion is not generalized to arbitrary
user-defined operators. Unlike the earlier six ordinary row comparisons,
DISTINCT row pairs do not require a common B-tree strategy.

Cast decoration matters. `value::JSON IS DISTINCT FROM NULL` has the raw-NULL
path, while `value::JSON IS DISTINCT FROM NULL::JSON` requires a missing JSON
equality declaration and is Invalid. Compatible JSON-array equality remains
Unsupported because native analysis accepts it while element comparison can
fail at execution. The raw-NULL path supports that same array type without
using equality. Unknown strings retain contextual coercion, so a statically
admitted string-to-integer conversion can still fail on its value.

## Row null tests are field sensitive

`ISNULL` and `NOTNULL` normalize to the existing `.isNull` AST, retaining its
negated flag. A new independent flat-row rule validates every field and gives
nonnullable Boolean output. No equality operator is required, so JSON fields
are permitted.

For a direct row, PostgreSQL `IS NULL` tests whether all fields are NULL, while
`IS NOT NULL` tests whether all are non-NULL. A mixed row satisfies neither
predicate. Both predicates hold for the zero-field row. Accordingly, the
negative form is not represented as Boolean negation of the positive form.

The raw-NULL DISTINCT shortcut tests a row value differently from a row null
test: `ROW(NULL,NULL) IS NOT DISTINCT FROM NULL` is false, whereas
`ROW(NULL,NULL) IS NULL` is true. Keeping the two AST and derivation paths
separate prevents a renderer or checker normalization from erasing this
distinction.

Standalone record values, nested row fields, custom composites, and scalar
subqueries remain Unsupported where their prerequisite contracts are absent.
Unequal direct-row lengths and known incompatible equality operands are
Invalid. Every parameter still needs a declaration; the NULL shortcut does
not invent a parameter type.

## Proof and rendering boundaries

The independent `ExprValid` rules are separate from executable checking.
`checkQuery_sound` continues to produce a derivation indexed by the exact
profile, catalog, declarations, query and ordered output. New kernel-checked
witnesses construct scalar, raw-NULL, zero-row and field-sensitive row
derivations without invoking the checker.

The universal translation-validity theorem covers each new rule. Parameter
occurrences retain lexical order: all left row fields precede all right row
fields. Pairwise operator selection never reorders anonymous placeholders.
Identity and PostgreSQL renderer certificates still assert exact AST
round-trips, and the general parameter-translation and serialization theorems
remain applicable.

The renderer emits canonical long-form DISTINCT and NULL predicates.
Postfix chaining follows PostgreSQL grammar: repeated null tests and a postfix
null test followed by DISTINCT are supported, but an unparenthesized DISTINCT
expression followed by a postfix test is not silently re-associated.

SQLite has a separate structural rendering boundary. It excludes direct row
DISTINCT comparisons and direct row null tests. Scalar source/canonical
observations use independently authored SQLite expectations; PostgreSQL and
SQLite need not agree on coercion, such as text versus numeric operands.
Neither checked rendering nor this static contract asserts cross-dialect
value equivalence.

## Registered verification

The focused Lean replay passes 8,401 cases. Its independently authored
28-by-28 declared-type registry covers both DISTINCT polarities, all four
operand-nullability combinations and flat-row pairs. Additional cases cover
raw NULL over every declared type, all four null-test spellings, zero/mixed
rows, labels, lexical parameters, missing declarations, Invalid versus
Unsupported boundaries and fuel exhaustion. The earlier 274 row-comparison
checks and 54 scalar boundaries pass after promoting their newly supported
null-test cases to exact positive assertions; the 100 earlier scalar corpus
certificates also pass. The renderer suite passes 261 checks, including
PostgreSQL and SQLite precedence differences and explicit row boundaries.

Each new factor has fifty authored queries. All 100 require complete SELECT
certificates, exact ordered nonnullable Boolean metadata, both checked
renderings and translation preservation. Native execution checks run authored
SQL only and distinguish expected runtime conversion errors from static
typing.

The authentic source registry has fifty unchanged statements per factor and
requires both checked renderings for all 100. Its fixed complete-query
population passes 47 certificates: 25 DISTINCT queries with 34 ordered outputs,
and 22 null-test queries with 25 ordered outputs. These expectations were
registered from original input syntax before checking. All outputs are
nonnullable; two DuckDB-source postfix/cast projections return unmodified
VARCHAR, and the other 57 positions return Boolean. Exact names, ordering and
nullable flags are checked against the independent Lean registry and the
separately authored metadata fixture.

The remaining 53 sources receive rendering certificates only. Fifty-two have
catalog dependencies; the source-free Calcite query contains nested rows and
explicitly remains Unsupported for complete static validity. Source-free
metadata alone therefore never determines certification. No source SQL is
executed, and no catalog or parameter assumptions are invented. Original
source dialect and provenance remain attached to each record; parser
normalization does not claim agreement among those engines' value semantics.

The contract proves the stated static derivations and conservative metadata.
Native result checks remain finite observations, not a proof of complete SQL
execution semantics or the absence of runtime exceptions.

The PostgreSQL 16.15 helper passes 3,506 exact static/parser boundaries,
including 3,488 independently registered native analysis outcomes. Authored
source and canonical SQL pass 200 value/type-OID observations, 200 SQL-NULL
observations, 224 output-descriptor observations and 16 expected runtime-error
observations. SQLite 3.45.1 passes 108 authored source/canonical observations;
46 other authored statements have exact recorded SQLite exclusions.

The separate precedence guard passes 680 SQLite source/canonical pairs,
72 IS-alias pairs and 19 fixed value expectations. An optional pinned pglast
7.21 / PostgreSQL 17.7 comparison passes 252 parse-tree or rejection checks.
These guards cover chained equality, IS, DISTINCT, LIKE, BETWEEN and IN
operators without imposing PostgreSQL's precedence on SQLite.

The complete Python regression suite passes 1,005 tests. The raw PostgreSQL
grammar replay covers 11,959 records and 2,393 reduction productions, plus
44 protocol checks. All 100 newly retained source statements pass their
pinned-parser observation and byte-exact extraction checks.

The 441-job warning-free Lean build and complete Lean/scope suites pass.
The broad renderer replay passes 1,237 SELECTs and 2,474 identity/PostgreSQL
renderings; SQLite passes 400 renderings and 800 bounded execution comparisons.
The existing PostgreSQL CRUD integration passes 300 certified examples,
600 source/canonical comparisons, 100 RETURNING state comparisons and
36 independent result expectations. The industrial corpus remains at
257 accepted statements out of 276, with all 19 rejections documented.

The compiled trust audit checks 26,954 project declarations, including 15,068
theorems and 577 generated recursion helpers, and rejects all five proof-bypass
witnesses. Its frozen input inventory SHA-256 is
`133858a6cb743715d4d0a6036c72e660dae9f092deadfec7857dc5dd35bc723e`,
based on commit `4c66110ac19e4b1be919f8beee7a3396e5a47777`. The disclosed
Lean foundations remain `propext`, `Classical.choice` and `Quot.sound`; there
are no custom axioms, proof placeholders or native proof-evaluation shortcuts.
The release remains held for the unfinished PostgreSQL contracts.

## Primary references

- [PostgreSQL 16 comparison predicates](https://www.postgresql.org/docs/16/functions-comparison.html)
- [SQLite expression precedence and IS operators](https://www.sqlite.org/lang_expr.html)
- [Pinned PostgreSQL expression transformation](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/backend/parser/parse_expr.c):
  `transformAExprDistinct`, `make_distinct_op` and `make_row_distinct_op`
- [Pinned PostgreSQL grammar](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/backend/parser/gram.y):
  comparison and postfix null-test productions
