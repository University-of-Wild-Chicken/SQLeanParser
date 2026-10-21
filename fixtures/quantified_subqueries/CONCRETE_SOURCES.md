# Unchanged quantified-subquery inputs

The active population has **101 distinct whole SELECT inputs: 50 scalar and
51 row quantified comparisons**. It meets both fifty-input class minima.
There are 92 DuckDB, four Materialize, three PostgreSQL and two Calcite inputs,
covering ANY (54), SOME (13), ALL (34), and all six comparison operators.
Classification uses the left operand of the raw quantified SubLink; inputs
contain no mixed scalar/row comparisons and are never counted twice.

The VALUES/anonymous-derived increment activates seventeen original inputs
which were deferred at v0.35. Their SQL, IDs, immutable source selectors and
hashes are unchanged. `deferred_values_v0.35.jsonl` retains the exact historical
records, including their then-open coverage annotations. It is an archive, not
an extra covered population. `deferred_values.jsonl` is now empty. The manifest's
`values_activation` binds the archive hash, all seventeen activated IDs and the
prior manifest, selector and registry hashes. The original 84 active selections
and eighty static oracle entries remain unchanged prefixes.

`concrete_sources.json` pins complete files, immutable commits, licenses and
notices, exact whole-input selectors, SQL hashes and comment-free token hashes.
SQLLogicTest statements are bounded by query headers and expected-result
delimiters; Quidem and PostgreSQL inputs retain complete statement boundaries.
Expected results and controls stay opaque. Original SQL, declarations and
fixture data are never executed. Inputs are not rewritten, extracted from plans,
manufactured from fragments or expanded from loops. Whitespace, comments and
optional terminators cannot pad the population. Active IDs and normalized
SQL token hashes are globally unique.

The original fifty selectors and metadata remain first, with canonical hash
`1d681dc55687e84d4a5346534ffebf35fb33122fedc91437c3c76984d6cf0a99`.
The original 47 static oracle entries also remain first, with canonical hash
`373a558b17f343ddc67946a8df6e444c0f66d14de5d5cbed5ef3f120fec3c30f`.
The prior eighty-entry registry prefix is bound to
`dd563a258ab8dd608d4e004d8b92f451e56df2a499215d8f71e6760e0f2f3055`.

The fixed registry has **97 full-certificate candidates and 110 ordered output
columns**, independently declared before checker replay. Sixty-three are closed;
34 use four conditional catalogs transcribed from complete preceding DuckDB
INTEGER declarations in the retained files. These catalogs assert an unchanged
PostgreSQL namespace and nullable fields; they do not claim DDL execution or
import source fixture data. Scalar comparison nullability combines operand
nullability. Flat row comparisons conservatively remain nullable. The seventeen
activated inputs are closed flat-row comparisons with BOOL output and no result
collation; their metadata follows those independent rules.

Four inputs retain rendering assurance: a PostgreSQL nested-composite comparison,
a PostgreSQL query over `tenk1` without a retained typed catalog, and two Calcite
queries without complete type catalogs, one correlated. No environment is
invented to promote them. Provenance and rendering do not prove native analysis,
runtime success or full PostgreSQL coverage.

Reproduce with `python3 scripts/extract_quantified_subquery_corpus.py --check`.
Add `--oracle` in the pinned pglast 7.21 environment for raw syntax, dependency
and token observations. The extractor returns 101 active inputs; its deferred
mode returns none. `check_quantified_subqueries_cli.py --source-registry` checks
all originals and PostgreSQL canonical queries against the 97 static entries,
and both identity/PostgreSQL rendering for all 101. The v0.36 checkpoint passes
these gates. Source SQL and DDL remain inert parser input.
