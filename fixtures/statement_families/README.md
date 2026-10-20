# Pinned whole-statement sources by PostgreSQL grammar family

The positive corpus contains **3,924 unchanged public statements**, classified
by the outer statement production in the pinned PostgreSQL 16.15 grammar.
It represents **124 of 125** outer families; **53 families have 50 sources**.
The remaining families have fewer than 50 examples. `inventory.json` records
the exact available count, selected count, and shortfall for every family.
Missing statements are not replaced with renamed or synthetic variants.

The selected sources comprise 73 Hatchet application constants, 27 sqlc compiler
regression statements, and 3,824 PostgreSQL engine regression statements.
These source kinds are separate fields in each JSONL record. SQL is never
executed. Parsing does not establish catalog validity, parameter types,
permissions, absence of side effects, or successful execution.

`CreateAssertionStmt` has no positive source in this finite search. PostgreSQL's
grammar includes this production, but its C semantic action reports that
assertions are unsupported. No claim of 50 authentic examples—or native
PostgreSQL support—is made for this family.

## Source and extraction boundary

- [Hatchet](https://github.com/hatchet-dev/hatchet/tree/392e7c472221cdab235cca674640e98f904e1ea0),
  commit `392e7c472221cdab235cca674640e98f904e1ea0`, MIT:
  40 downloaded generated SQL source files.
- [sqlc](https://github.com/sqlc-dev/sqlc/tree/0f1602fe1a4b780336e3e878dde720892fd8578d),
  commit `0f1602fe1a4b780336e3e878dde720892fd8578d`, MIT:
  414 downloaded PostgreSQL/pgx compiler-input files.
- [PostgreSQL](https://github.com/postgres/postgres/tree/f0595c3d839debdb140903621c1b44a4f4d86256),
  commit `f0595c3d839debdb140903621c1b44a4f4d86256`, PostgreSQL License:
  all 222 regression SQL files plus 233 module/contrib regression SQL files
  selected by the pinned catalog.

`mining_sources.json` lists all 909 searched files with SHA-256 hashes.
`concrete_sources.json` identifies the selected complete Go constants or exact
SQL statement slices and pins the source and license bytes needed to reproduce
them. Existing snapshots are reused where available; additional selected
snapshots are under `sources`. License texts are referenced from
`../extended_types/licenses`.

The scanner masks quoted data and nested comments while locating statement
boundaries. SQL `BEGIN ATOMIC` routine bodies, including nested CASE expressions,
remain inside their complete outer statements. It does not execute or interpret
psql meta-commands. One intentionally Windows-1252 input is excluded from this
UTF-8 source population, with its exact source-file hash retained in the mining
catalog and the reproducible exclusion ledger.

## Mining observations and explicit negatives

The finite search produced 42,967 case/whitespace-distinct, whole statements
accepted by `pglast==7.21` (PostgreSQL **17.7** raw-parser grammar).
The PostgreSQL **16.15** grammar recognizer accepted 42,964 and rejected three.
The raw-parser version and source/recognizer version are distinct facts.

`negative.jsonl` keeps the three unchanged rejected statements and their expected
diagnostic fragments:

- PostgreSQL `numerology.sql` explicitly labels `$1a` and `$0_1` parameter-junk
  statements as error cases. The PostgreSQL 17 raw parser accepts them.
- The PostgreSQL 16 `merge.sql` regression includes `MERGE ... RETURNING`,
  which the PostgreSQL 17 raw parser accepts but the pinned PostgreSQL 16
  grammar rejects.

The mining ledger also records 1,841 raw-parser rejections and 11,977 conservative
duplicates. Rejection records retain their original SQL and source locations.
Case/whitespace folding can discard additional distinct SQL, including differences
inside quoted data; it cannot inflate counts by accepting duplicate statements.
This is a finite search boundary, not a claim that all source SQL was extracted
or that every grammatical production is covered.

Within each outer family, selection stops at 50. The deterministic selector
prefers statements that add visited grammar production IDs, then application,
compiler and engine provenance, then shorter source text and stable identity.
It selects whole existing statements and never rewrites SQL.

## Reproduction

Verify the selected corpus and exact family-gap inventory offline:

```sh
python3 scripts/extract_statement_corpus.py --check
python3 -m unittest discover -s scripts -p 'test_statement_extraction.py'
```

Add `--oracle` with the pinned `scripts/requirements-corpus.txt` dependency to
verify the recorded PostgreSQL 17 raw-parser statement kinds. This also checks
the deliberate raw-parser acceptance of the three PostgreSQL 16 negatives.

Reproduce the full search and classification using the built grammar executable
and a source cache:

```sh
python3 scripts/mine_statement_sources.py \
  --source-cache /tmp/sqlean-source-cache \
  --output-dir /tmp/sqlean-statement-search \
  --download
```

`--download` restores only missing commit-pinned inputs and verifies their hashes
before using them. Omit it for an already populated cache. The command writes
the complete pool, exclusions, accepted/rejected grammar observations,
deterministically selected statements and summary. It never executes downloaded
programs or SQL. Grammar reports certify token-grammar derivations and exact
source preservation; C semantic actions and SQL static validity remain outside
that certificate.
