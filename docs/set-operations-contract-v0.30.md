# Set-operation validity, profile v0.30

`sqlean-basic-select-v0.30` extends the independent SELECT contract to `UNION`,
`INTERSECT` and `EXCEPT`, with default duplicate elimination or `ALL`. Operands
can use the existing covered SELECT, join, derived-table and ordinary CTE rules,
including parenthesized operands with their own WITH, sorting or pagination.
The expanded syntax API retains its other features at their existing assurance
levels. This increment does not complete PostgreSQL contracts or authorize the
held alpha release.

## Independent rules

`PendingColumn` and `ItemsInputValid` retain raw NULL/string projection inputs
until the containing binary set operation selects a common type. `SetOperandValid`
distinguishes those contextual inputs from completed query outputs. A CTE,
derived table or completed inner set operation exposes concrete output types;
it cannot propagate an unresolved literal through that boundary.

`SetColumnsValid` requires equal widths and positional common-type selection,
records both operand coercions, retains matching supported type modifiers,
and selects output labels from the left operand. Selection remains directional:
for example, CHAR followed by TEXT can produce unmodified `bpchar`. The output
nullable flag is the disjunction of both input flags for all six variants. This
is a conservative bound, not a claim that every result actually contains NULL.
All variants except `UNION ALL` require an admitted grouping equality capability.
JSON and arrays of JSON lack that capability and are rejected at this boundary.

Each binary operation resolves its own inputs. Consequently,
`SELECT NULL UNION SELECT NULL UNION SELECT 1` first produces a TEXT result
from the inner operation and then fails the outer TEXT/INTEGER match. The
implementation does not flatten the tree or gather all leaf types together.

Branch-local DISTINCT resolves every unknown output to TEXT. Branch-local
ORDER BY resolves only referenced result positions, using the SQL92 ordinal
or output-label rules. An unrelated ordering expression, parentheses or
pagination alone does not finalize an unknown output.

The ordinary sorting contract now admits repeated output labels when all
matching projection expressions are syntactically identical. It selects the
first matching target, as PostgreSQL does. Other possible transformed-expression
equivalences remain Unsupported. At a compound result, repeated output labels
remain ambiguous even when their input expressions are identical.

Sort items are checked in sequence. Resolving just one of two identical unknown
targets changes its type before the next item is analyzed: `ORDER BY 1,x` and
`ORDER BY x,x` can therefore make the repeated label `x` ambiguous. Resolving both
targets first, as in `ORDER BY 1,2,x`, keeps them compatible. A separate native
regression population records unknown NULL/string cases and known-type controls.

`SetOrdersValid` permits only unambiguous left-result labels or positive,
in-range INTEGER ordinals, with an orderable result type. There is no input
relation namespace or arbitrary expression sorting at this level. Root or
direct operand row locking is invalid; locks inside a nested derived query or
CTE definition remain governed by their existing independent rules.

## Parameters and preservation

The statement collects enclosing CTE parameters, left and right operand
parameters, and outer pagination parameters in written order. Definition
references do not duplicate occurrences. Numbered references retain their
identity and repeated uses; anonymous references retain their consecutive
lexical positions. Branch-local modifiers keep their own occurrences.

Four mutually recursive preservation theorems transport `QueryValid`,
`SourceValid`, `CTEsValid` and `SetOperandValid` through parameter translation.
Separate projection, pending-input resolution, column-merging and sorting
lemmas preserve output names, concrete types and nullable flags. The public
`Certificate`, complete-query interface and unchanged-catalog theorem retain
their existing roles. A successful checker branch must construct the independent
derivation; checker success is not the definition of validity.

## Exact scope of the claims

These are static type/coercion, namespace and parameter contracts. They do not
prove row-value semantics, native query-planner equivalence, privileges,
resource bounds or successful evaluation of literal values.

Literal input functions are a separate obligation even when PostgreSQL invokes
them during analysis. For example, `SELECT 'bad' UNION SELECT 1` has an admissible
unknown-to-INTEGER coercion in the static contract, while PostgreSQL PREPARE
rejects the value with `22P02`. The native harness records both facts separately.
This is the same boundary already present for explicit casts and contextual
CASE/COALESCE inputs; it is not a newly claimed analysis-success guarantee.

Recursive CTE rules, grouping/aggregation, expression subqueries and LATERAL
correlation still require further independent contract increments. The typed
parser also retains the separate restriction on additional modifiers around an
already modified parenthesized query. Four PostgreSQL 16-valid wrapper cases
are explicitly recorded as gaps. A PostgreSQL 17 parser oracle is not treated
as authority for PostgreSQL 16 acceptance at those version boundaries.

## Verification populations

Each of the three factors has 50 authored examples and 50 globally distinct,
unchanged authentic statements. The authored examples independently specify
162 ordered output positions, parameter values, multiset results and four
table populations: empty, items only, labels only and both. They exercise
duplicate counts, NULL membership, directional coercions and type modifiers,
nested operations, CTE scope, sorting, pagination and nested row locks.

The [authentic source registry](../fixtures/set_operations/source_contracts.json)
declares full-query metadata for 62 statements and 83 output positions:
50 UNION statements and six each for INTERSECT and EXCEPT. Eligibility comes
from source inspection, not checker acceptance. The other 88 statements retain
checked rendering without invented catalog or parameter assumptions. Original
source SQL is never executed.

PostgreSQL native observations compare authored source/canonical queries,
typed rows, exact descriptor labels and modifiers, and separate PREPARE and
execution SQLSTATEs. Ordered cases compare sequence as well as bag multiplicity.
SQLite observations use independent expectations: its compound precedence,
affinity, duplicate comparison and native syntax differ. `INTERSECT ALL`,
`EXCEPT ALL`, right-nested compounds, operand-local clauses and other excluded
forms retain explicit rendering or input diagnostics. A printable flattened
SQLite compound can have a PostgreSQL-style parenthesized source that SQLite
itself rejects; that original-source error is recorded separately.

The structural renderer guard compares 126 normalized PostgreSQL raw-AST
source/canonical pairs and separately covers SQLite compound precedence.
These finite external observations supplement the kernel-checked validity and
renderer contracts; they do not establish universal PostgreSQL execution
equivalence.

## Integration results

The focused Lean suite passes 84 type/scope/ordering checks, 150 authored
full-query certificates, all 62 registered authentic certificates and 290
renderer checks. Every one of the 150 authentic statements also receives
checked identity/PostgreSQL rendering.

The main native harness passes 92 static boundaries, 1,200 PostgreSQL 16.15
typed-row observations, 324 exact descriptor positions and 360 separate
source/canonical analysis/execution observations. SQLite 3.45.1 passes 620
row/label observations and four expected original-source syntax errors;
72 statements have explicit input or rendering exclusions.

The ordering-sequence guard passes 80 static classifications, including 60
exact positive schemas and 20 ambiguities, plus 160 PostgreSQL PREPARE outcomes
and 120 descriptor positions. The structural guard passes 126 PostgreSQL
roundtrips/raw-AST comparisons, 32 SQLite observations, five SQLite exclusions,
four PostgreSQL 16 wrapper-gap observations and four source/canonical native
precedence anchors. Its PostgreSQL 17 oracle observations are version-labelled
separately.

The warning-free build completes 451 jobs. The full Lean and scope executables,
1,092 Python tests and offline generators pass. Existing CTE, ordering-constant
and assurance CLI regressions also pass. The raw grammar replay passes 12,159
records, 44 protocol cases, 125 outer statement families and 2,395 observed
reduction productions. The [industrial corpus](corpus/set-operations-v0.30/README.md)
retains 257 typed-parser acceptances and 19 rejections.

The broad renderer replay passes 1,237 SELECTs, 2,474 identity/PostgreSQL
renderings, 400 SQLite renderings and 800 bounded SQLite comparisons. The
compiled trust audit checks 27,523 declarations, including 15,224 theorems and
586 generated recursion helpers, and rejects all five deliberate bypass
witnesses. Its frozen input inventory SHA-256 is
`762d8f0168698951b3e1aede00c6b08f207a986705c76e414f1e54d9c87216a9`,
based on commit `7f3cbbb3c121632a2b698a245387166baef66a01`.
The disclosed Lean foundations remain `propext`, `Classical.choice` and
`Quot.sound`; no project-defined axioms, proof placeholders or native proof
shortcuts are introduced.

## Primary references

- [PostgreSQL 16 common-type resolution](https://www.postgresql.org/docs/16/typeconv-union-case.html)
- [PostgreSQL 16 combining queries](https://www.postgresql.org/docs/16/queries-union.html)
- [PostgreSQL 16 sorting compound results](https://www.postgresql.org/docs/16/queries-order.html)
- [SQLite compound SELECT rules](https://www.sqlite.org/lang_select.html#compound_select_statements)
