"""Closed source-contract registry and conditional catalog provenance checks.

The source queries are never executed or used to select successful checker
outcomes. Custom identities denote caller assertions tied to written CREATE
statements; they are not OIDs obtained from a database.
"""
from __future__ import annotations

from collections import Counter
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = "fixtures/collations/"
REGISTRY_SHA256 = "730e1ec87dc9af3d38f7e9febbdd81532470803c467948ed54a0e1d5a5c5689a"
PROVENANCE_SHA256 = "da23379bce6c4a447d48fbb536b4d7767117d3a50a93981d221f3440b84a2af1"
OBSERVED_REGISTRY_SHA256 = "055bc4a1bf317f5e3330c544e05e869549ef8dc20317b22fb029dcbfa469f7a9"
OBSERVED_PROVENANCE_SHA256 = "2b793fc5d6754b78c3cc33d9a4d86e07fb4c917bdbe15c3c415f55fff2d4dc11"
NATIVE_OBSERVATION_SHA256 = "6c3894274d1b6e1e726375ca27dd938fa8975af630af47341bca6847f86511ee"
CATALOG_NAMES = (
    "source_builtin.json", "source_icu_declarations.json", "source_portable_declarations.json",
)
PIN = "f0595c3d839debdb140903621c1b44a4f4d86256"


def canonical_sha(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def require(value, message):
    if not value:
        raise ValueError(message)


def builtin_snapshot():
    return {"tables": [], "collations": {"encoding": "UTF8", "entries": [
        {"id": label, "schema": "pg_catalog", "name": label, "encoding": None,
         "deterministic": True, "exposeUnqualified": True}
        for label in ("default", "C", "POSIX")
    ]}}


def declared_snapshots(context, provenance):
    """Apply only the documented finite conversion to caller assertions."""
    by_id = {row["id"]: row for row in context["declarations"]}
    builtin = builtin_snapshot()
    icu = builtin_snapshot()
    portable = builtin_snapshot()
    custom_ids = {}
    for binding in provenance["custom_collation_bindings"]:
        declaration = by_id[binding["declaration_id"]]
        observed = declaration["observed_declaration"]
        require(observed["kind"] == "collation" and len(observed["name"]) == 1,
                "custom identity must denote its complete CREATE COLLATION")
        require(binding["id"] == "custom:" + declaration["id"],
                "custom identity is not tied to its source declaration")
        require(binding["written_options"] == observed["written_options"]
                and binding["source_url"] == declaration["source_url"]
                and binding["sql_sha256"] == declaration["sql_sha256"],
                "custom identity provenance differs from source")
        options = {option["name"]: option["value"] for option in observed["written_options"]}
        require(options.get("provider") == "icu" and options.get("deterministic", "true") in {"true", "false"},
                "unsupported declaration-to-snapshot conversion")
        # PostgreSQL 16 DefineCollation uses encoding -1 for ICU and true when
        # DETERMINISTIC is omitted. The exact source is retained and hashed.
        entry = {"id": binding["id"], "schema": "collate_tests", "name": observed["name"][0],
                 "encoding": None, "deterministic": options.get("deterministic", "true") == "true",
                 "exposeUnqualified": True}
        custom_ids[entry["name"]] = entry["id"]
        icu["collations"]["entries"].append(entry)
    for binding in provenance["table_bindings"]:
        declaration = by_id[binding["declaration_id"]]
        observed = declaration["observed_declaration"]
        require(observed["kind"] == "table" and observed["name"] == [binding["name"]]
                and binding["schema"] == "collate_tests"
                and binding["source_url"] == declaration["source_url"]
                and binding["sql_sha256"] == declaration["sql_sha256"],
                "table snapshot is not backed by its source declaration")
        columns, collations = [], []
        for column in observed["columns"]:
            raw_type = column["raw_type_name"]
            type_ = "int32" if raw_type == ["pg_catalog", "int4"] else "text" if raw_type == ["text"] else None
            require(type_ is not None and column["written_array_bounds"] in ([], [-1]),
                    "unsupported source field type")
            if column["written_array_bounds"]:
                type_ += "[]"
            require(type(column["written_not_null"]) is bool, "non-Boolean source NOT NULL observation")
            columns.append({"name": column["name"], "type": type_,
                            "nullable": not column["written_not_null"]})
            if column["written_collation"] is not None:
                require(len(column["written_collation"]) == 1, "unsupported source field collation")
                name = column["written_collation"][0]
                require(name == "C" or name in custom_ids, "unresolved field collation must remain deferred")
                collations.append({"column": column["name"],
                                   "collation": "C" if name == "C" else custom_ids[name]})
        table = {"name": binding["name"], "schema": binding["schema"],
                 "exposeUnqualified": True, "columns": columns}
        if collations:
            table["columnCollations"] = collations
        destination = icu if declaration["source_file"].endswith("collate.icu.utf8.sql") else portable
        destination["tables"].append(table)
    return dict(zip(CATALOG_NAMES, (builtin, icu, portable)))


def validate_registry(registry, sources, snapshots, context, provenance):
    require(isinstance(registry, list) and len(registry) == 50
            and [row["id"] for row in registry] == [row["id"] for row in sources],
            "all 50 source IDs must occur once in their fixed order")
    require(canonical_sha(registry) == REGISTRY_SHA256,
            "preregistered source statuses or exact output metadata changed")
    require(canonical_sha(provenance) == PROVENANCE_SHA256,
            "conditional source snapshot provenance changed")
    require(provenance["source_execution"] == provenance["native_source_analysis"] == "not-performed",
            "source execution or native-analysis claim is not permitted")
    require(canonical_sha(context) == provenance["source_declaration_context_sha256"],
            "source declaration context changed")
    expected_snapshots = declared_snapshots(context, provenance)
    require(set(snapshots) == set(CATALOG_NAMES), "missing or extra source catalog")
    require(snapshots == expected_snapshots, "catalog metadata differs from its written declaration basis")
    valid, outputs, deferred = [], [], []
    for row, source in zip(registry, sources):
        if row["status"] == "valid":
            require(set(row) == {"id", "status", "eligibility", "catalogFile", "output_columns"}
                    and row["eligibility"] == "checker"
                    and row["catalogFile"] in {DIRECTORY + name for name in CATALOG_NAMES},
                    "invalid checker-eligible source entry")
            require(isinstance(row["output_columns"], list) and row["output_columns"],
                    "checker-eligible source needs complete output metadata")
            snapshot = snapshots[row["catalogFile"].removeprefix(DIRECTORY)]
            identities = {entry["id"] for entry in snapshot["collations"]["entries"]}
            for column in row["output_columns"]:
                require(set(column) == {"name", "type", "nullable", "collation"}
                        and type(column["nullable"]) is bool
                        and column["type"] in {"bool", "int32", "text", "text[]"}
                        and (column["collation"] is None or column["collation"] in identities),
                        "invalid exact source output metadata")
                require((column["type"] in {"text", "text[]"}) == (column["collation"] is not None),
                        "source output collation/type disagreement")
            valid.append(row)
            outputs += row["output_columns"]
        else:
            require(set(row) == {"id", "status", "eligibility", "catalogFile", "output_columns",
                                 "diagnostic", "unresolved_collations"}
                    and row["status"] == "deferred" and row["eligibility"] == "catalog_prerequisite"
                    and row["catalogFile"] is None and row["output_columns"] is None
                    and row["diagnostic"] == "source.collation_snapshot_unresolved",
                    "unresolved source facts must not claim a checker result")
            unresolved = [dependency["parts"] for dependency in
                          source["declaration_provenance"]["collation_dependencies"]
                          if dependency["declaration_id"] is None and dependency["parts"] not in [["C"], ["POSIX"]]]
            require(unresolved and row["unresolved_collations"] == unresolved,
                    "unresolved source collation names changed")
            deferred.append(row)
    require(len(valid) == 18 and len(deferred) == 32 and len(outputs) == 28
            and Counter(c["type"] for c in outputs) == {"bool": 12, "int32": 5, "text": 9, "text[]": 2}
            and Counter(c["nullable"] for c in outputs) == {False: 13, True: 15},
            "fixed source eligibility/output population changed")
    return registry


def load_source_contracts(root=ROOT):
    directory = root / DIRECTORY
    raw_registry = (directory / "source_contracts.json").read_bytes()
    registry = json.loads(raw_registry)
    provenance = json.loads((directory / "source_snapshot_provenance.json").read_text())
    require(canonical_sha(provenance) == PROVENANCE_SHA256, "source snapshot provenance changed")
    require(hashlib.sha256(raw_registry).hexdigest() == provenance["source_contracts_sha256"],
            "source registry file changed")
    sources = [json.loads(line) for line in (directory / "concrete.jsonl").read_text().splitlines()]
    context = json.loads((directory / "declaration_contexts.json").read_text())
    for evidence in provenance["basis_sources"]:
        content = (root / evidence["local_path"]).read_bytes()
        require(hashlib.sha256(content).hexdigest() == evidence["sha256"]
                and evidence["commit"] == PIN, "pinned catalog-semantics source changed")
    snapshots = {}
    for catalog in provenance["catalog_files"]:
        content = (root / catalog["path"]).read_bytes()
        require(hashlib.sha256(content).hexdigest() == catalog["sha256"], "source snapshot file changed")
        snapshots[Path(catalog["path"]).name] = json.loads(content)
    return validate_registry(registry, sources, snapshots, context, provenance)


def observed_identity(row):
    suffix = "all-encodings" if row["collencoding"] == -1 else "UTF8"
    return "custom:fixture-observed:" + row["nspname"] + ":" + row["collname"] + ":" + suffix


def observed_snapshot(context, observation):
    """Merge observed imported objects with conditional, unexecuted source DDL."""
    records = observation["observed"]
    names = {"de-x-icu", "en-x-icu", "en_US", "sv-x-icu", "sv_SE",
             "tr-x-icu", "tr_TR", "ucs_basic", "und-x-icu", "unicode"}
    require(len(records) == 10 and {r["collname"] for r in records} == names
            and len({r["oid"] for r in records}) == 10
            and all(type(r["oid"]) is str and r["oid"].isdigit() for r in records),
            "fixture collation names/OIDs are missing or duplicated")
    require(observation["source_execution"] == "not-performed"
            and observation["scope"] == "isolated authored fixture catalog, not source deployment"
            and observation["native_version"]["server_version_num"] == "160015"
            and observation["native_version"]["server_encoding"] == "UTF8"
            and observation["native_version"]["client_encoding"] == "UTF8",
            "unexpected native catalog observation scope")
    snapshot = builtin_snapshot()
    ids = {entry["name"]: entry["id"] for entry in snapshot["collations"]["entries"]}
    for record in records:
        require(record["nspname"] == "pg_catalog" and record["collprovider"] in {"c", "i"}
                and type(record["collisdeterministic"]) is bool
                and type(record["collencoding"]) is int and record["collencoding"] in {-1, 6},
                "unsupported observed collation metadata")
        entry = {"id": observed_identity(record), "schema": record["nspname"],
                 "name": record["collname"], "encoding": None if record["collencoding"] == -1 else "UTF8",
                 "deterministic": record["collisdeterministic"], "exposeUnqualified": True}
        snapshot["collations"]["entries"].append(entry)
        ids[entry["name"]] = entry["id"]
    for declaration in context["declarations"]:
        value = declaration["observed_declaration"]
        if value["kind"] != "collation":
            continue
        options = {option["name"]: option["value"] for option in value["written_options"]}
        require(options.get("provider") == "icu" and len(value["name"]) == 1
                and options.get("deterministic", "true") in {"true", "false"},
                "unsupported source custom collation")
        entry = {"id": "custom:" + declaration["id"], "schema": "collate_tests", "name": value["name"][0],
                 "encoding": None, "deterministic": options.get("deterministic", "true") == "true",
                 "exposeUnqualified": True}
        snapshot["collations"]["entries"].append(entry)
        ids[entry["name"]] = entry["id"]
    for declaration in context["declarations"]:
        value = declaration["observed_declaration"]
        if value["kind"] != "table" or not declaration["source_file"].endswith("collate.icu.utf8.sql"):
            continue
        columns, collations = [], []
        for column in value["columns"]:
            raw = column["raw_type_name"]
            type_ = "int32" if raw == ["pg_catalog", "int4"] else "text" if raw == ["text"] else None
            require(type_ is not None and column["written_array_bounds"] in ([], [-1])
                    and type(column["written_not_null"]) is bool, "unsupported observed-context field")
            if column["written_array_bounds"]:
                type_ += "[]"
            columns.append({"name": column["name"], "type": type_, "nullable": not column["written_not_null"]})
            if column["written_collation"] is not None:
                require(len(column["written_collation"]) == 1 and column["written_collation"][0] in ids,
                        "field collation is absent from the combined context")
                collations.append({"column": column["name"], "collation": ids[column["written_collation"][0]]})
        table = {"name": value["name"][0], "schema": "collate_tests",
                 "exposeUnqualified": True, "columns": columns}
        if collations:
            table["columnCollations"] = collations
        snapshot["tables"].append(table)
    require(len(snapshot["tables"]) == 7 and len(snapshot["collations"]["entries"]) == 27,
            "observed/declared snapshot population changed")
    return snapshot


def validate_observed_registry(registry, baseline, snapshot, context, observation, provenance):
    require(canonical_sha(registry) == OBSERVED_REGISTRY_SHA256,
            "preregistered observed-context source metadata changed")
    require(canonical_sha(provenance) == OBSERVED_PROVENANCE_SHA256
            and canonical_sha(context) == provenance["source_declaration_context_sha256"],
            "observed-context provenance changed")
    require(len(registry) == 32 and [r["id"] for r in registry] ==
            [r["id"] for r in baseline if r["status"] == "deferred"],
            "observed eligibility must cover precisely the baseline prerequisites")
    require(snapshot == observed_snapshot(context, observation),
            "combined catalog differs from observed identities or source declarations")
    columns = []
    for row in registry:
        require(set(row) == {"id", "status", "eligibility", "catalogFile", "output_columns"}
                and row["status"] == "valid" and row["eligibility"] == "checker"
                and row["catalogFile"] == DIRECTORY + "source_observed_catalog.json",
                "wrong observed-context checker record")
        require(isinstance(row["output_columns"], list) and row["output_columns"],
                "observed-context source needs complete output metadata")
        for column in row["output_columns"]:
            require(set(column) == {"name", "type", "nullable", "collation"}
                    and type(column["nullable"]) is bool
                    and column["type"] in {"bool", "int32", "text"}
                    and (column["collation"] is None or column["collation"] in
                         {entry["id"] for entry in snapshot["collations"]["entries"]}),
                    "invalid observed-context output metadata")
        columns += row["output_columns"]
    require(len(columns) == 43 and Counter(c["type"] for c in columns) ==
            {"bool": 30, "int32": 6, "text": 7}
            and Counter(c["nullable"] for c in columns) == {False: 34, True: 9},
            "observed-context output population changed")
    return registry


def load_observed_source_contracts(root=ROOT):
    baseline = load_source_contracts(root)
    directory = root / DIRECTORY
    raw_registry = (directory / "source_observed_contracts.json").read_bytes()
    registry = json.loads(raw_registry)
    provenance = json.loads((directory / "source_observed_provenance.json").read_text())
    require(canonical_sha(provenance) == OBSERVED_PROVENANCE_SHA256, "observed-context provenance changed")
    require(hashlib.sha256(raw_registry).hexdigest() == provenance["registry_sha256"],
            "observed-context registry file changed")
    context = json.loads((directory / "declaration_contexts.json").read_text())
    raw_observation = (root / provenance["fixture_observation_file"]).read_bytes()
    require(hashlib.sha256(raw_observation).hexdigest() ==
            provenance["fixture_observation_sha256"] == NATIVE_OBSERVATION_SHA256,
            "native fixture catalog observation changed")
    observation = json.loads(raw_observation)
    raw_snapshot = (root / provenance["catalogFile"]).read_bytes()
    require(hashlib.sha256(raw_snapshot).hexdigest() == provenance["catalog_sha256"],
            "observed-context catalog file changed")
    return validate_observed_registry(registry, baseline, json.loads(raw_snapshot), context, observation, provenance)


if __name__ == "__main__":
    load_source_contracts()
    load_observed_source_contracts()
    print("PASS: 18 declaration-context / 28 outputs plus 32 observed-context / 43 outputs; all 50 identities retained")
