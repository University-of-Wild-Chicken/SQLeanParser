# Optional fixture-catalog observation

The retained observation came from a private PostgreSQL 16.15 UTF8 cluster
with C database collation and glibc 2.39. The exact native version, queries,
authored setup, `localedef` commands, and relevant hashes are recorded in
`fixture-catalog-observation.json`. This is a test-catalog observation,
not an observation of an upstream deployment.

Offline CI does not need `localedef`, ICU locale imports, or these libc locales.
To make a new observation on a machine with PostgreSQL 16, ICU support, and
the `en_US`, `sv_SE`, and `tr_TR` locale source files, run the following from
the repository root. Set `COLLATION_PG_BIN` to the PostgreSQL binary directory.
The repository's connection helper initializes and stops a fresh private
UTF8 cluster; it does not contact an existing database. `LOCPATH` affects
only this process and its child server. Native commands use the frozen,
hash-checked authored setup and catalog queries; downloaded SQL is never
passed to the database.

```sh
COLLATION_PG_BIN=/usr/lib/postgresql/16/bin \
PYTHONPATH=scripts /usr/bin/python3 - <<'PY'
from argparse import Namespace
import json
import os
from pathlib import Path
import subprocess
import tempfile

from collation_source_contracts import ROOT, load_observed_source_contracts
from check_postgresql_cli import connection, run

load_observed_source_contracts()  # verifies the retained evidence hashes
evidence = json.loads((ROOT / "fixtures/collations/provenance/fixture-catalog-observation.json").read_text())
args = Namespace(local_bin=os.environ["COLLATION_PG_BIN"], dsn=None, psql=None)
with tempfile.TemporaryDirectory(prefix="sqlean-collation-locales-") as temporary:
    for locale in ("en_US", "sv_SE", "tr_TR"):
        subprocess.run(
            ["localedef", "--no-archive", "-i", locale, "-f", "UTF-8",
             str(Path(temporary) / (locale + ".utf8"))],
            check=True, timeout=60,
        )
    os.environ["LOCPATH"] = temporary
    with connection(args) as psql:
        run(psql + ["-X", "-v", "ON_ERROR_STOP=1", "-c", evidence["native_setup"]])
        for query in (evidence["version_query"], evidence["catalog_query"]):
            print(run(psql + ["-X", "-qAt", "-v", "ON_ERROR_STOP=1", "-c", query]).stdout)
PY
```

This command prints a new observation and does not replace the frozen files.
OIDs, library versions, and locale hashes can differ between installations.
Any replacement snapshot needs separate review of its identities, metadata,
provenance, and corresponding caller assumptions. A missing locale or provider
is a reproduction limitation; it does not justify silently changing the
registered catalog facts.
