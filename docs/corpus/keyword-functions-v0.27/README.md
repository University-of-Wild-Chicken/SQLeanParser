# Industrial PostgreSQL corpus after keyword function heads

The expanded typed parser accepts 257 of the original 276 pinned BenchBase,
River and Temporal statements and rejects 19. Among the 260 distinct SQL
texts, 241 are accepted and 19 rejected.

This increment newly accepts River's `indexReindexArtifacts`. Its ordinary
`left(...)` call previously stopped at the keyword-name restriction. Its
CTE and application catalog remain outside the independent SELECT profile;
syntax acceptance and checked rendering do not establish full query validity.
The new LEFT/RIGHT typing rules are certified separately on the fixed authored
and closed-source populations.

No source statement was executed, and no application catalog or parameter
declarations were invented. `results.jsonl` retains all original statements and
outcomes. `audit.json` records source, runner and binary hashes. The Markdown
failure display trims trailing whitespace; exact SQL remains in JSONL.

The generic interpretation watchlist still flags River's `columnExists`.
The earlier context-value increment contains its supplementary raw-AST
observation; this parser change does not change that context-value rule.

The optional pglast 7.21 / PostgreSQL 17.7 raw-parser oracle accepts all 276
statements. The separate proof-carrying grammar interface targets PostgreSQL
16.15. Neither establishes equivalence to PostgreSQL's semantic actions or
runtime evaluation.

`int32-min-observation.json` separately records authored local observations
of a RIGHT boundary where the pinned C source and installed binary differ.
It identifies their hashes and the executed SQL without attributing a cause.
The portable fifty-query value oracle excludes this case.

Reproduce the industrial audit with `scripts/requirements-corpus.txt` installed:

```sh
lake build
python scripts/audit_postgresql_corpus.py --output .lake/industrial-audit
```

Full PostgreSQL contracts and entire-grammar source populations remain
unfinished. Publication of `0.0.1-alpha` remains held.
