# Application corpus after VALUES query contracts

The typed parser accepts 257 of the 276 pinned application statements (241 of
260 distinct SQL texts). VALUES query bodies and anonymous derived-source
contracts leave the remaining nineteen syntax failures in their larger
statement contexts unchanged. These results measure syntax acceptance, not
complete static validity for application queries.

`audit.json` and `results.jsonl` are byte-for-byte copies of the completed
`/tmp/sqlean-v36-industrial-audit` replay. They retain original SQL and bind
source, runner, Lean-source and executable hashes. `failures.md` changes only
trailing whitespace in the display copy; source fixture bytes and recorded
results remain unchanged. The audit records its base Git HEAD and dirty-tree
state rather than claiming an already committed v0.36 release.

The replay used CLI SHA256
`001e8511ccc5351ca8716131352ca9d4474e39eaa1679eeda88302ed17250dbc`.
Its optional pglast 7.21 / PostgreSQL 17.7 raw parser supplies separate syntax
observations. The independent grammar and typed-contract target remains
PostgreSQL 16.15. No original application input or downloaded setup was executed.

The separate VALUES population has fifty authored queries, thirteen boundary
fixtures and fifty unchanged source queries. All fifty sources have complete
certificates with 65 ordered final columns. Their 54 registered internal VALUES
body descriptors are not separately certified. Twelve sources also require
anonymous derived scope. The quantified population now activates all seventeen
previously deferred inputs unchanged: 101 sources, fifty scalar and 51 row,
with 97 complete certificates and 110 ordered output columns.

The finite source and authored native gates pass. All 56 local integration
gates pass, including the separately rerun legacy anonymous-source boundary
repair. A clean export passes 1,385 Python tests and 89 offline
fixture/provenance checks; CI enforces these regression surfaces. Full PostgreSQL
contracts and the final review/closure ladder continue to gate `0.0.1-alpha` publication.
Development pauses after this iteration; no correlation increment is included.

```sh
python3 scripts/audit_postgresql_corpus.py --output .lake/industrial-audit
```
