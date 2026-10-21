# Application corpus after row-IN contracts and preflight repairs

The typed parser still accepts 257 of the 276 pinned application inputs
(241 of 260 distinct SQL texts). This increment changes static contracts and
repairs typing/collation rules; it does not claim to close the nineteen original
syntax rejections. Exact original SQL, outcomes, input hashes and runner hashes
are retained in `results.jsonl` and `audit.json`; `failures.md` trims trailing
whitespace for display.

The replay used CLI SHA256
`114b3ec7ec105f69328286934019af86d5885292362ba8c16e65e0eb62ff405f`.
The optional pglast 7.21 / PostgreSQL 17.7 raw parser provides separate syntax
observations; the independent grammar and typed-contract target remains
PostgreSQL 16.15. No application input or downloaded setup was executed.

The new row-IN factor has a separate fifty-query authored population and fifty
unchanged source examples. Twelve preregistered sources, with twenty ordered
output positions, receive full certificates under their stated environments.
All fifty receive checked identity/PostgreSQL rendering. Full PostgreSQL typed
contracts remain required before `0.0.1-alpha` publication.

```sh
python scripts/audit_postgresql_corpus.py --output .lake/industrial-audit
```
