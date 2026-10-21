# Application corpus after quantified-query contracts

The typed parser accepts 257 of the 276 pinned application statements (241 of
260 distinct SQL texts). Quantified-query parsing and independent contracts do
not close the remaining nineteen syntax failures in their larger statement
contexts. `results.jsonl` retains unchanged original SQL and measured outcomes;
`audit.json` binds source, runner and executable hashes. `failures.md` trims
trailing whitespace for display.

The replay used CLI SHA256
`26a76ee61035422ba676b3e1d81d054d0b75d8edce7630104f2d16e02df0dfe7`.
The optional pglast 7.21 / PostgreSQL 17.7 raw parser supplies separate syntax
observations. The independent grammar and typed-contract target is PostgreSQL
16.15. No original application input or downloaded setup was executed.

The separate quantified-query population has fifty authored scalar queries,
fifty authored row queries and eighteen operator-direction controls. Its
84 unchanged sources include fifty scalar and 34 row queries, with eighty
preregistered full static certificates. A sixteen-query authentic row shortage
remains explicit; seventeen unchanged VALUES-dependent inputs are deferred.
Full PostgreSQL contracts and the final six-reviewer closure ladder continue to
gate `0.0.1-alpha` publication.

```sh
python scripts/audit_postgresql_corpus.py --output .lake/industrial-audit
```
