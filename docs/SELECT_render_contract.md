# SQLean SELECT renderer correctness contract — v0.1

**The renderer shall serialize a query without changing what that query denotes. It shall not repair, simplify, optimize, or reinterpret the query.**

This is a proposed natural-language contract for the SELECT family covered by the preceding validity specification. It distinguishes **faithful AST serialization**, **parameter-binding preservation**, and **semantic preservation**. Establishing one does not automatically establish the others.

SQLeanParser already exposes two relevant operations: `render`, which retains the parameter style, and `renderPostgres`, which converts anonymous parameters to numbered PostgreSQL parameters. They require different round-trip statements. 

---

## R-01. Scope and central obligation

The contract covers SELECT queries, including their expressions, sources, joins, grouping, subqueries, CTEs, set operations, ordering, and pagination.

It applies to every finite composition of the constructs admitted by the selected language profile—not merely queries in a generated corpus.

For every admissible query AST, successful rendering shall produce:

> A complete SQL representation of the same query structure, with the same bindings, literal contents, expression grouping, clause scopes, and parameter identities, under the declared target profile.

For a statically valid query, the rendered representation shall also preserve its independently specified meaning and output schema.

**Serialization does not require proving that a query is statically valid.** For example, a query referencing an unknown table can still have a faithful textual representation. Whether that table exists belongs to validation.

Conversely, static validity does not establish renderability. An otherwise well-typed AST might contain an identifier or literal that the target cannot represent faithfully.

The contract shall therefore distinguish:

| Property | Meaning |
|---|---|
| **Structurally admissible** | The AST satisfies the syntax and representation conditions needed for faithful serialization |
| **Statically valid** | The query satisfies the separate name-resolution and typing specification |
| **Semantically preserved** | The generated SQL denotes the same computation under the specified interpretation |

---

## R-02. Fixed target profile

Each rendering operation shall use an explicit, versioned target profile.

The profile shall specify the SQL dialect and version, supported syntax, identifier rules, literal encoding, parameter convention, and relevant environmental assumptions.

For an initial PostgreSQL profile, these assumptions shall include the server and client encoding, string-literal interpretation, identifier-length limit, and the catalog and namespace interpretation used for unqualified names.

The renderer shall not silently depend on the current machine’s locale, an unspecified server setting, or whichever database happens to accept its output.

For example, PostgreSQL string interpretation depends on `standard_conforming_strings`, and identifiers exceeding the server’s configured length limit are truncated. Quoting alone does not eliminate those dependencies. [PostgreSQL](https://www.postgresql.org/docs/16/sql-syntax-lexical.html)

**A change of target profile is a change of contract.** Successful rendering for one profile shall not imply compatibility with another.

---

## R-03. Admissible inputs

The admissible AST domain shall be defined independently of the renderer.

It shall not be defined as:

> Whatever reparses successfully after rendering.

Its conditions shall include syntactically meaningful constructor combinations, representable names and literals, valid parameter identities, and the absence of unsupported constructs.

Examples of inadmissible representations include a zero-indexed numbered parameter, an empty required identifier, malformed numeric-token content, or contradictory flags that the target syntax cannot express.

An AST field shall not be silently ignored merely because other fields determine which printing branch executes. Every meaningful field must either affect the output or be excluded by an explicit admissibility condition.

Likewise, representation details that cannot survive serialization must be addressed explicitly. For example, a “recursive” flag on a query with no CTE bindings cannot simply disappear under an exact round-trip claim.

The specification shall state whether each such case is rejected or belongs to a separately specified normalization operation.

**The admissible domain must include constructive examples of every claimed feature.** Defining it so narrowly that the theorem becomes vacuous is not acceptable.

---

## R-04. Complete statement and lexical containment

Successful statement rendering shall produce exactly one complete SELECT statement.

The entire output shall belong to that statement. Correctness shall not depend on a parser accepting a prefix and ignoring trailing material.

The statement-level API shall append one statement terminator. Query and expression renderers used inside larger constructs shall not append terminators.

This is a syntactic requirement, not a character-count requirement: semicolons inside a string or quoted identifier are data.

Every identifier and literal shall remain confined to its intended grammatical role. Its contents shall not introduce a new clause, comment, operator, or statement.

For example, a text value containing:

```text
'; SELECT 99; --
```

shall remain one text value. It shall not change the surrounding query’s syntax.

Whitespace and punctuation shall prevent unintended token merging. Rendering adjacent unary operators must not accidentally create comment syntax.

This guarantee concerns **faithful serialization of AST data**, not authorization. A correctly serialized query may still request information that an application should not permit.

---

## R-05. Identifier preservation

Every rendered identifier shall decode to the exact identifier represented by the AST under the target profile.

The renderer shall preserve case, character sequence, qualification boundaries, and binding role. It shall not apply Unicode normalization, transliteration, case folding, truncation, or replacement unless that transformation is explicitly part of the AST’s already-established identifier interpretation.

The renderer shall distinguish an identifier containing a period from a qualified reference:

```sql
"a.b"
```

and:

```sql
"a"."b"
```

shall not be interchanged.

Reserved words used as names shall remain identifiers. Embedded delimiter characters shall be escaped rather than removed.

For PostgreSQL, quoted identifiers preserve case and embedded double quotes are doubled. The identifier-length limit still applies, and a zero character is not permitted. An input that cannot satisfy these constraints shall be rejected, not silently changed. [PostgreSQL](https://www.postgresql.org/docs/16/sql-syntax-lexical.html)

The renderer shall not rename aliases or CTEs in v0.1. Capture-avoiding renaming would require its own transformation contract.

---

## R-06. Literal and type preservation

### Text and Boolean literals

A text literal shall preserve its exact character sequence, including empty content, quotation marks, backslashes, whitespace, newlines, and supported non-ASCII characters.

Escaping shall be correct for the selected target profile. It shall not merely make the output acceptable to SQLeanParser’s lexer.

Characters that cannot be represented by the target shall produce a structured failure. They shall not be deleted or replaced.

Boolean and NULL literals shall retain their distinct meanings. SQL NULL shall not be serialized as the text value `'NULL'`.

Parameter values supplied separately to a database shall remain separate from SQL text; literal substitution is not an equivalent parameter-rendering implementation. PostgreSQL provides separate parameter transport precisely as a distinct execution interface. [PostgreSQL](https://www.postgresql.org/docs/16/libpq-exec.html)

### Numeric literals

Numeric rendering shall preserve the literal’s specified value **and any lexical distinctions relevant to its type interpretation**.

It shall not pass exact decimal or exponent notation through an inexact floating-point conversion.

For an AST node retaining a numeric lexeme, that lexeme shall first satisfy an independently defined numeric-token grammar appropriate to the node. An arbitrary string shall not acquire permission to appear as SQL merely because it occupies a field named `decimal`.

The initial exact-serialization profile shall retain valid decimal lexemes rather than normalize their spelling. Integer values represented structurally may use a fixed canonical decimal spelling.

### Casts and type modifiers

A cast shall retain its source expression, target type, and all specified modifiers.

The renderer shall not collapse `REAL`, `DOUBLE PRECISION`, and `NUMERIC` into one spelling because a static checker groups them into one numeric family. PostgreSQL distinguishes exact numeric types from inexact floating-point types. [PostgreSQL](https://www.postgresql.org/docs/16/datatype-numeric.html)

Similarly, a specified length, precision, or scale shall not disappear.

---

## R-07. Expression structure and precedence

The generated text shall preserve the expression tree.

Parentheses shall be emitted wherever required to prevent a different grouping under the target grammar. Additional parentheses are permitted only where they do not change the grammatical role.

For example:

```sql
a - (b - c)
```

shall not become:

```sql
a - b - c
```

Likewise, a negation over a conjunction shall not become a conjunction containing one negated operand.

Operator identity, operand order, unary signs, and cast placement shall be preserved. The renderer shall not assume associativity, commutativity, distributivity, or two-valued Boolean identities.

The renderer shall not perform constant folding, reassociation, predicate simplification, or duplicate elimination.

A transformation that happens to preserve a mathematical value may still affect SQL types, NULL behavior, or errors. Such transformations belong to a separately verified normalization or optimization pass.

For v0.1, **rendering is syntax-directed serialization, not rewriting**.

---

## R-08. Query structure and clause ownership

Every clause shall remain attached to the same query node or expression node.

The following information shall be preserved:

| Construct | Required preservation |
|---|---|
| SELECT list | Item order, repeated items, aliases, and wildcard qualifiers |
| FROM | Source identity, source order, aliases, and nesting |
| Joins | Join kind, left/right operands, association, and condition form |
| Predicates | Their placement in `ON`, `WHERE`, `HAVING`, or aggregate `FILTER` |
| Grouping | Grouping-expression order and structure |
| Aggregates | Function, argument, `DISTINCT`, and attached filter |
| Subqueries | Scalar, `EXISTS`, or `IN` role and nesting |
| CTEs | Binding order, names, column lists, bodies, and recursion marker |
| Set operations | Operator, `ALL` flag, operand order, and tree association |
| Ordering/pagination | Sort keys, directions, null placement, limits, offsets, and owning query |

In particular, the renderer shall not move a predicate between an outer join’s `ON` clause and the surrounding `WHERE` clause. Those positions do not generally have the same meaning. [PostgreSQL](https://www.postgresql.org/docs/16/queries-table-expressions.html)

It shall not expand `*`, rewrite `USING` into `ON`, or replace `NATURAL` joins using catalog information. Those are schema-dependent transformations, not ordinary serialization.

A source-free SELECT shall remain source-free. The renderer shall not introduce a dummy table.

---

## R-09. Set-operation and nested-query boundaries

The renderer shall preserve the complete set-operation tree, not merely the textual sequence of operators.

For example:

```sql
q1 EXCEPT (q2 EXCEPT q3)
```

shall not become an expression interpreted as:

```sql
(q1 EXCEPT q2) EXCEPT q3
```

Parentheses shall also preserve whether a CTE, ordering clause, limit, or offset belongs to an operand or to the compound query.

PostgreSQL gives `INTERSECT` a different precedence from `UNION` and `EXCEPT`; parentheses also determine whether a trailing `LIMIT` belongs to an operand or the combined result. These distinctions must therefore be represented explicitly. [PostgreSQL](https://www.postgresql.org/docs/16/queries-union.html)

A recursive CTE’s anchor and recursive branch shall retain their roles. The renderer shall not change `UNION ALL` to `UNION`, remove a recursion marker, or rearrange bindings.

**An AST is finite even when the query it represents may execute indefinitely.** Rendering termination and recursive-query execution termination are separate properties.

---

## R-10. Binding and correlation preservation

Under the same catalog and scope interpretation, each rendered reference shall denote the same binding as its AST counterpart.

This applies to table references, column references, aliases, CTE references, correlated references, and lateral dependencies.

The renderer shall not change scope boundaries or move a reference between query levels.

It shall preserve the distinction between a local alias and an equally spelled outer alias. Merely preserving the name’s characters is insufficient if the surrounding scope changes.

`LATERAL` shall remain attached to the same derived source. Source reordering that changes which bindings are available is prohibited.

Output aliases shall remain attached to their original expressions. A sort or grouping reference shall retain its intended role as an output-name reference, input-column reference, expression, or ordinal.

In particular, the renderer shall not replace an ordinal with an arbitrary expression that happens to evaluate to the same integer.

Binding preservation shall be justified through the independent name-resolution rules—not inferred from successful execution on one schema.

---

## R-11. Parameter identity and translation

Parameter preservation shall be specified separately from ordinary identifier preservation.

### Identity-preserving mode

Numbered parameter references shall retain their indices. Repeated occurrences of one parameter shall remain references to one binding.

For anonymous parameters, the AST shall carry an unambiguous statement-wide occurrence identity. In v0.1, anonymous occurrences must have distinct ordinals matching the order in which their markers occur in the rendered statement.

This order includes CTE bodies and nested queries. Numbering shall not restart inside a subquery.

A hand-built AST whose anonymous ordinals conflict with this ordering shall be rejected by the admissibility boundary rather than silently rebound.

### PostgreSQL translation mode

Translation shall establish a binding map from logical input parameters to target parameter slots.

That map shall be injective over distinct referenced bindings, consistent across repeated references, and complete for every emitted parameter marker.

The accompanying parameter values and declared types shall be transported using the same map. PostgreSQL’s native prepared-query interface uses numbered markers such as `$1` and `$2`. [PostgreSQL](https://www.postgresql.org/docs/16/sql-prepare.html)

For v0.1, the supported cases are:

| Input style | Target mapping |
|---|---|
| Numbered only | Preserve each positive index |
| Anonymous only | Map occurrence ordinal `i` to `$i` |
| Mixed styles | Unsupported unless a separate collision-free mapping contract is supplied |

Thus, converting both logical `Anonymous(1)` and logical `Numbered(1)` into `$1` is prohibited when they represent different bindings.

The map may be an explicit returned value or a fixed mapping derivable from the documented mode. It shall not be an undocumented caller responsibility.

**Replacing placeholders with typed literals does not establish this obligation.** It bypasses the binding interface being verified.

---

## R-12. Structural round-trip correctness

For every admissible AST, parsing the complete rendered text with the corresponding SQLeanParser interface shall reconstruct the expected AST.

In identity-preserving mode:

\[
\operatorname{ParseFull}(\operatorname{Render}(q))
=
\operatorname{Success}(q).
\]

In parameter-translation mode:

\[
\operatorname{ParseFull}(\operatorname{RenderPG}(q))
=
\operatorname{Success}(T_\mu(q)),
\]

where \(T_\mu\) changes parameter representations according to the declared binding map and leaves all other fields unchanged.

Neither theorem shall use a comparison that ignores arbitrary AST fields.

If exact equality is impossible because a representation contains information that SQL cannot retain, the specification must either restrict admissibility or define a separate, narrowly enumerated normalization.

Such normalization shall be specified before the proof. It shall not mean “whatever the parser reconstructs.”

For this initial contract, normalization is the identity except for the explicitly declared parameter translation.

**This round-trip theorem establishes agreement between the renderer and parser. It does not independently establish that either implements the target SQL language correctly.**

---

## R-13. Output-schema preservation

For a query satisfying the independent validity contract, rendering shall preserve the ordered output schema under that same specification.

This includes output width, column positions, concrete types, specified type modifiers, and justified nullability annotations. Repeated output columns shall remain repeated.

Explicit aliases and inherited simple-column names shall be preserved.

For v0.1, labels of unaliased computed outputs may remain unspecified where the validity contract leaves them unspecified. A stronger claim about every database-reported label requires an explicit target-labeling specification.

This distinction matters because SQL systems derive labels for unaliased expressions; those labels are not necessarily recorded as explicit AST aliases. [PostgreSQL](https://www.postgresql.org/docs/16/queries-select-lists.html)

An unspecified label shall not be confused with permission to change a specified one.

The renderer shall not add casts, rename outputs, or expand wildcards merely to make a schema comparison pass.

---

## R-14. Semantic preservation

Structural round trips shall be supplemented by an independent semantic obligation.

For every supported, statically valid query, every database state consistent with its catalog, and every compatible parameter assignment:

> The AST interpretation and the interpretation of its rendered SQL shall have the same observable behavior under the fixed profile and parameter mapping.

The SQL interpretation shall not be defined by invoking the renderer and then SQLeanParser’s own parser. That would make the semantic claim circular.

### Observable results

The observation model shall include output positions, specified labels, typed values, NULL values, and row multiplicities.

An unordered result shall be compared as a **bag**, not as a set. Removing duplicates is a semantic change unless the query requests it.

For ordered results, the model shall preserve ordering requirements. When those requirements leave ties unresolved, correctness shall not demand identical incidental tie order from two executions.

Similarly, an under-specified `LIMIT` may permit different selected rows. PostgreSQL explicitly warns that pagination without a sufficiently determining order can return unpredictable subsets. [PostgreSQL](https://www.postgresql.org/docs/16/queries-limit.html)

The contract shall therefore compare the **sets of permitted observable outcomes**, rather than assume that every query denotes one deterministic result sequence.

### Errors and divergence

The observation model shall also include supported language-level errors and divergence where applicable.

A renderer shall not suppress or introduce a modeled division error, invalid conversion, scalar-subquery cardinality error, or nontermination through a structural change.

Scalar subqueries illustrate why row equality alone is insufficient: a multirow scalar result is an error, while a zero-row scalar result supplies NULL. [PostgreSQL](https://www.postgresql.org/docs/16/sql-expressions.html)

Operational details such as execution time, query plans, memory consumption, network failures, and exact diagnostic wording are outside v0.1 unless separately specified.

A theorem covering only successful terminating evaluations must be named accordingly. It shall not be advertised as full behavioral preservation.

---

## R-15. Determinism and canonical stability

Given the same AST, rendering mode, profile, and renderer version, successful rendering shall produce identical output bytes and the same parameter map.

The output shall not depend on hash-table iteration order, ambient locale, time, random choices, or mutable global state.

The formatting policy shall fix keyword spelling, spacing, quotation, parenthesization, and terminator handling sufficiently to make this reproducible.

Canonical output shall be stable under parsing and rerendering:

\[
\operatorname{Render}(
  \operatorname{ParseFull}(\operatorname{Render}(q))
)
=
\operatorname{Render}(q),
\]

with the corresponding mode and translated AST where necessary.

“Canonical” here means a stable representation of an AST. It does **not** mean that every semantically equivalent query receives the same text.

Source comments, original whitespace, keyword capitalization, and redundant source parentheses need not be reproduced unless they are explicitly represented and covered by a separate lossless-printing contract.

---

## R-16. Termination, resources, and failure behavior

The mathematical renderer shall terminate on every finite admissible AST.

A fuel-based implementation shall prove that the fuel supplied by its public entry point is sufficient for every recursive rendering call.

It shall not return replacement SQL when fuel is exhausted.

In particular, returning `NULL`, `SELECT NULL`, an empty source, or a truncated query is not a successful rendering of the original AST.

The inspected `AdvancedPretty.lean` uses computed fuel and contains such fallback branches in its private helpers. The required obligation is that those branches are unreachable through the covered public entry points. Their presence alone does not establish a reachable defect. 

For executable deployments, resource exhaustion shall produce a failure distinguishable from unsupported syntax or invalid representation.

A failed operation shall not publish partial SQL as a valid result.

A low-level function returning only `String` may remain internal, but a public correctness claim must either require an admissibility witness or be enforced by a checked boundary. Arbitrary constructible AST values shall not silently inherit the theorem.

---

## R-17. Source-to-rendered correctness requires a parser theorem

This renderer contract begins with an AST.

It does not, by itself, establish that an original SQL source string and the generated SQL mean the same thing.

That stronger claim requires both:

\[
\text{original source}
\;\xrightarrow{\text{correct parsing}}\;
\text{AST}
\;\xrightarrow{\text{correct rendering}}\;
\text{generated source}.
\]

A parser that assigns the wrong meaning to the original text cannot be repaired by a renderer that faithfully prints the resulting AST.

Therefore, source-to-rendered semantic preservation shall cite the parser’s source-interpretation theorem as a separate dependency.

A source/canonical differential test is useful evidence, but it does not replace either theorem.

---

## R-18. Required adversarial witnesses and evidence

The verification package shall include concrete witnesses for the following obligations:

| Witness | Required result |
|---|---|
| Name containing a quote, period, reserved word, or non-ASCII character | Preserve one intended identifier and its binding |
| Text containing quotes, backslashes, newlines, and SQL-looking content | Preserve one text value |
| Malformed content in a numeric-lexeme field | Reject before successful rendering |
| Nested subtraction, division, negation, and casts | Preserve the expression tree |
| Nested set operations with operand-local limits | Preserve association and clause ownership |
| Outer join with both `ON` and `WHERE` predicates | Preserve their distinct locations |
| Repeated numbered parameters and nested anonymous parameters | Preserve identity and statement-wide ordering |
| Mixed parameter styles | Reject under v0.1 or establish a separate collision-free mapping |
| Deeply nested admissible AST | Complete rendering without fallback substitution |
| Duplicate rows, NULL-bearing predicates, and ordering ties | Use the declared semantic comparison, not an unsuitable equality test |

Testing shall include hand-constructed admissible ASTs, not only parser-produced ASTs. Parser-generated inputs can otherwise conceal unsupported constructor states.

Every reported assurance result shall identify the exact theorem or test, supported fragment, rendering mode, profile, code revision, and remaining trusted dependencies.

Passing tests establish those tested instances. A checked round trip establishes reconstruction of that instance. A general proof establishes only its stated theorem and assumptions.

---

## Core theorem obligations

The initial formalization should expose these claims separately:

| Obligation | Required statement |
|---|---|
| **Lexical integrity** | Names and literals remain in their intended grammatical roles |
| **Target-syntax fidelity** | The output has the intended structure under an independently specified target grammar |
| **AST round trip** | Full reparsing reconstructs the original or explicitly translated AST |
| **Binding preservation** | References and parameters retain their meanings |
| **Schema preservation** | The independently derived output schema is preserved |
| **Semantic preservation** | AST and SQL interpretations have equal permitted observations |
| **Fuel adequacy and determinism** | Rendering completes without substitution and has stable output |

The principal semantic statement is:

\[
\boxed{
\operatorname{Behaviors}_{AST}(q,C,D,\rho,\Pi)
=
\operatorname{Behaviors}_{SQL}(s,C,D,\rho_\mu,\Pi)
}
\]

whenever \(q\) is admissible and valid, rendering produces \(s\) with parameter map \(\mu\), and the database state and environments satisfy the declared assumptions.

Here, the two interpretations are independently defined, and `Behaviors` includes the result, ordering, multiplicity, NULL, error, and divergence distinctions specified above.

**The governing rule is: change the representation, not the query. Any operation that changes bindings, structure, values, or permitted behavior is a transformation requiring a separate correctness argument—not an implementation detail of the renderer.**
