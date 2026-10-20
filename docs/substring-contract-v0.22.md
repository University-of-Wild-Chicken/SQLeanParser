# SUBSTRING: v0.22

`sqlean-basic-select-v0.22` admits PostgreSQL's five special SUBSTRING
forms and the ordinary comma-separated function call. It retains the
previous four positional SUBSTR declarations. The normative
`substringCatalog` contains six declarations: TEXT or BYTEA with an
INTEGER start and optional INTEGER length, TEXT with a regular-expression
pattern, and TEXT with a SQL regular-expression pattern and escape string.
The ordinary supported function inventory consequently contains 84
declarations. BIT and VARBIT remain outside this profile's type inventory;
their two native SUBSTRING declarations are not claimed here.

`Advanced.Expr.substring` stores a `SubstringForm` and arguments in source
order. `FROM start FOR length`, `FOR length FROM start`, `FROM start`,
`FOR length`, and `SIMILAR pattern ESCAPE escape` have distinct form tags.
The ordinary comma-separated spelling remains an ordinary function call.
The independent `SubstringArguments` judgment maps those lexical inputs
to the selected native call's argument order. In particular, FOR/FROM
permutes typed arguments without permuting parameter occurrences.

FOR-only requires a separate rule. PostgreSQL inserts the INTEGER
constant 1 and explicitly casts the length to INTEGER before resolving
the function. `SubstringLengthValid` records that conversion independently
of normal positional implicit coercion. It therefore permits supported
BIGINT, numeric, floating-point, character, Boolean, and JSONB lengths
that ordinary FROM/FOR positions do not accept implicitly. A bare unknown
literal receives the INTEGER context. The conversion's nullable metadata
is preserved, including the existing conservative JSONB cast flag.
The [pinned PostgreSQL grammar](https://github.com/postgres/postgres/blob/f0595c3d839debdb140903621c1b44a4f4d86256/src/backend/parser/gram.y)
defines this insertion and the reversed argument order.

Overload selection remains type-sensitive. A bare unknown string in a
TEXT subject's FROM position prefers the TEXT regular-expression
declaration, even when its contents look numeric. BYTEA has only
positional declarations in this profile. SIMILAR/ESCAPE does not force
a regular-expression overload: INTEGER arguments select the positional
declaration, including with a BYTEA subject. Character modifiers do not
survive the TEXT result; native implicit CHAR-to-TEXT conversion also
has its normal trailing-space behavior.

Positional results have the disjunction of the input nullable flags.
Both regular-expression declarations always have a nullable TEXT result:
failure to find a match can return SQL NULL with entirely non-null inputs.
This distinction applies equally to ordinary calls and every special
form. The selected declaration, exact result type, nullability, lexical
parameter uses, and strong `substring` default label are part of the
independent validity derivation.
The PostgreSQL 16 documentation describes
[text substring forms](https://www.postgresql.org/docs/16/functions-string.html),
[binary substring forms](https://www.postgresql.org/docs/16/functions-binarystring.html),
and [regular-expression extraction](https://www.postgresql.org/docs/16/functions-matching.html).

The certificate concerns static typing and metadata. Negative lengths,
integer conversion failures or overflow, invalid regular expressions or
escape strings, evaluated child-expression errors, collation behavior,
and resource limits remain execution obligations. For example, a
JSONB numeric length can convert successfully while JSONB `null` raises
an error; the conservative nullable flag does not promise successful
conversion of JSON null. Likewise, a NULL subject does not prove that
another argument's failing cast will never be evaluated.

General parameter translation preserves the independent derivation and
source-order occurrences, including the reversed form. Both checked
PostgreSQL renderer profiles retain the exact normalized AST and form.
The SQLite rendering profile rejects the special PostgreSQL forms and
generic function calls under its existing coverage boundary. No
cross-dialect execution-equivalence claim is made.

The focused suite has 510 checks, including a linked six-declaration
fixture, twenty scalar families and their array forms, nullable inputs,
implicit versus explicit conversions, unknown literals, malformed
hand-built arity, unsupported child expressions, strong labels, lexical
parameter order, and exhausted fuel. Direct kernel examples construct
form-conversion and Boolean-length-cast evidence; renderer witnesses
also construct complete independent expression derivations.

Fifty authored queries and fifty unchanged authentic queries receive
full query certificates, exact output metadata, identity and PostgreSQL
rendering certificates, and general validity transport. The authentic
registry is fixed before checking: 27 PostgreSQL, 11 CockroachDB, and
12 Materialize examples, all source-free and parameter-free. It contains
37 TEXT, 6 BYTEA, and 7 Boolean projections. These examples are analyzed
under the PostgreSQL profile regardless of their source project; their
origin does not establish cross-engine semantics. Failed cases cannot
be silently reassigned to a weaker assurance tier. Native declaration,
value, descriptor, NULL, and expected-error observations supplement the
proofs; they do not establish a complete evaluator or a contract for all
PostgreSQL syntax.

Native execution checks cover 108 value/type observations, 108 independent
SQL NULL observations, 124 exact prepared-result descriptors, sixteen
expected runtime errors and six function declarations. Another 214 authored
native-analysis cases agree with contract classification and result metadata.
Conversion failures during native literal analysis remain conversion
obligations, not a static rejection inferred from the literal's contents.
The renderer suite adds 168 focused checks. Downloaded source statements
are never executed.
