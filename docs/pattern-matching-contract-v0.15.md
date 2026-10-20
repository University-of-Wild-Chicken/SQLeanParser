# ILIKE and regex matching: v0.15

`sqlean-basic-select-v0.15` promotes ILIKE into the independent SELECT
contract and adds the PostgreSQL regex operators `~`, `~*`, `!~` and `!~*`.
This continues the original external-corpus audit's extended-operator
priority. The two factors have separate synthetic and unchanged-source
populations, with 50 queries in each population.

ILIKE retains the existing `Expr.pattern arg pattern true` representation.
NOT ILIKE normalizes to unary NOT around that expression. Regex uses
`Expr.regex arg pattern insensitive negated`; its two flags preserve all
four operator spellings. LIKE's existing rule, including its BYTEA
overload, remains separate.

The independent `ExprValid.ilike` and `ExprValid.regex` rules require two
operand derivations and an explicit selected `FunctionOverload` from
`stringMatchSignature`. Both operands must have string-family types or be
unknown constants. The selected left type is PostgreSQL `bpchar` for a
concrete CHAR operand and TEXT otherwise. The selected right type is always
TEXT. VARCHAR and unknown operands therefore receive TEXT context; a
known CHAR pattern is converted to TEXT.

This asymmetric selection matters for values. CHAR on the left retains its
padding through the bpchar-specific matching operator. CHAR on the right
loses trailing padding when converted to TEXT. For example,
`CAST('abc' AS CHAR(5)) ILIKE 'abc'` is false in PostgreSQL, whereas
`'abc' ILIKE CAST('abc' AS CHAR(5))` is true. An explicit left-side TEXT cast
also changes the first result. The contract records the native overload
instead of collapsing both operands to TEXT.

The selected inventory has ten declarations: ILIKE and each of the four
regex spellings, each with TEXT/TEXT and bpchar/TEXT inputs. Their result
is Boolean. Successful matching produces a non-NULL Boolean for non-NULL
inputs, and SQL NULL propagates from either operand; output nullability is
their disjunction. Numeric, Boolean, temporal, UUID, JSON, JSONB, BYTEA and
array inputs are Invalid for these operators unless explicitly converted
to a supported string type. In particular, BYTEA's LIKE support does not
extend to ILIKE or regex.

PostgreSQL ILIKE matches case-insensitively according to the active locale.
Regex matching can find a substring unless the pattern is anchored;
ILIKE follows LIKE's whole-string wildcard behavior. The
[PostgreSQL pattern-matching documentation](https://www.postgresql.org/docs/16/functions-matching.html)
describes these distinct languages and their collation restrictions.
The certificate proves operator/type admissibility, not pattern-language
evaluation. Invalid regex syntax can raise an execution error; SQL NULL
can suppress evaluation of a malformed pattern through the strict operator.
These cases do not justify rejecting the static operand types.

The current catalog abstraction records types and nullability, not
collation identifiers or providers. This increment does not prove
collation compatibility, locale-dependent truth values, or successful
execution under a nondeterministic collation. PostgreSQL 16 rejects
nondeterministic collations for these matching operations. Explicit COLLATE
syntax and a collation-aware validity environment remain separate work.
Native examples use a controlled deterministic environment.

Regex operators have PostgreSQL's general-operator precedence, equal to
concatenation and below arithmetic. Their left association is retained:
`'abc' ~ 'a' || 'bc'` produces TEXT `truebc`, while
`'abc' ILIKE 'a' || 'bc'` produces Boolean true because ILIKE binds less
tightly than concatenation. Canonical rendering parenthesizes the
expressions and preserves the normalized AST and operator flags.

Parameter occurrences are ordered as the complete argument expression
followed by the complete pattern expression. The checker still enforces
one global anonymous numbering sequence at the outer query boundary.
The general translation theorems preserve the selected signature, flags,
nullability and whole-query validity. Both matching forms use the default
`?column?` label unless explicitly aliased.

SQLite checked rendering rejects ILIKE and these PostgreSQL regex
operators. It does not substitute LIKE, a user-defined REGEXP function,
or a different pattern language. Ordinary LIKE remains unchanged.
This is an explicit dialect boundary, not a failed PostgreSQL validity
claim.

Verification includes 333 focused Lean checks, exact operator-inventory linkage, direct kernel
derivations, full query certificates, both PostgreSQL rendering profiles,
and general validity transport. Focused cases exercise all operand
directions, CHAR/VARCHAR modifiers, unknown and NULL inputs, every spelling,
composition and precedence, parameter ordering, and failure classifications.
The synthetic fixture tests require all 100 queries to succeed with exact
ordered output names, types and nullability; no failed query is skipped.

The ten-entry catalog fixture is checked against the complete selected
inventory. NOT ILIKE's native `!~~*` spellings can be audited separately as
normalization evidence: the core derivation uses a positive ILIKE operator
followed by Boolean NOT. These catalog checks and native observations
supplement the independent typing rules without establishing a general
evaluation theorem.

The unchanged concrete queries receive rendering evidence only. The ILIKE
population contains 40 DuckDB, seven PostgreSQL, two River and one Hatchet
query; the regex population contains 50 PostgreSQL queries. Their source
dialect and provenance remain attached, and no catalog or parameter
binding is invented for them. NAME, CITEXT and other external source types
remain outside the profile's concrete scalar inventory. Full PostgreSQL
collation, regex evaluation and arbitrary operator environments are not
completed by this increment.

The native CLI regression checks 200 source/canonical value-and-type observations,
216 real prepared result descriptors, 12 expected execution errors, and 12 native
operator declarations (ten selected signatures plus two NOT ILIKE signatures).
It checks 41 failure boundaries and 100 explicit SQLite exclusions. Malformed
patterns are supplied as bound values in execution-error cases. The corpus source
statements are parsed and rendered without execution.

The PostgreSQL lexer now scans maximal operator runs before checking its finite
vocabulary, including PostgreSQL's trailing-sign and comment rules. Thus `||-`
and `~-` are unsupported operators, not silently split concatenation/matching
and unary minus. Space or comment delimiters retain their meaning; SQLite keeps
its separate tokenization. The anonymous `?` placeholder remains a documented
SQLean extension. Thirty additional renderer/lexer checks bring the focused
rendering suite to 174 cases.
