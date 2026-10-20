"""Offline preregistered source schemas and conditional catalog integrity."""
from collections import Counter
from copy import deepcopy
import json
from pathlib import Path
import shutil
import tempfile
import unittest

from collation_source_contracts import (
    CATALOG_NAMES, DIRECTORY, ROOT, declared_snapshots, load_source_contracts,
    load_observed_source_contracts, observed_snapshot, validate_observed_registry, validate_registry,
)


class CollationSourceContractTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        directory = ROOT / DIRECTORY
        cls.registry = json.loads((directory / "source_contracts.json").read_text())
        cls.provenance = json.loads((directory / "source_snapshot_provenance.json").read_text())
        cls.sources = [json.loads(line) for line in (directory / "concrete.jsonl").read_text().splitlines()]
        cls.context = json.loads((directory / "declaration_contexts.json").read_text())
        cls.snapshots = {name: json.loads((directory / name).read_text()) for name in CATALOG_NAMES}
        cls.observed_registry = json.loads((directory / "source_observed_contracts.json").read_text())
        cls.observed_provenance = json.loads((directory / "source_observed_provenance.json").read_text())
        cls.observation = json.loads((directory / "provenance/fixture-catalog-observation.json").read_text())
        cls.observed_catalog = json.loads((directory / "source_observed_catalog.json").read_text())

    def validate(self, **changes):
        values = {"registry": self.registry, "sources": self.sources, "snapshots": self.snapshots,
                  "context": self.context, "provenance": self.provenance}
        values.update(changes)
        return validate_registry(**values)

    def test_complete_fixed_registry_and_distinct_evidence_categories(self):
        self.assertEqual(load_source_contracts(), self.registry)
        self.assertEqual(Counter(r["status"] for r in self.registry), {"valid": 18, "deferred": 32})
        self.assertEqual(Counter(r["eligibility"] for r in self.registry),
                         {"checker": 18, "catalog_prerequisite": 32})
        self.assertEqual([r["id"] for r in self.registry], [r["id"] for r in self.sources])
        self.assertTrue(all(r["status"] != "unsupported" for r in self.registry))

    def test_fixed_output_schema_matches_independent_inspection(self):
        valid = {r["id"].split(":statement-")[-1]: r for r in self.registry if r["status"] == "valid"}
        # Labels remain source labels; no expression-label or duplicate-column
        # normalization is introduced by the registry.
        self.assertEqual(valid["25"]["output_columns"],
                         [{"name": "true", "type": "bool", "nullable": False, "collation": None}])
        self.assertEqual(valid["26"]["output_columns"],
                         [{"name": "false", "type": "bool", "nullable": False, "collation": None}])
        self.assertEqual([c["name"] for c in valid["282"]["output_columns"]], ["x", "x"])
        self.assertEqual([c["type"] for c in valid["244"]["output_columns"]], ["int32", "text[]"])
        self.assertEqual(valid["8"]["output_columns"], [
            {"name": "a", "type": "int32", "nullable": True, "collation": None},
            {"name": "b", "type": "text", "nullable": False, "collation": "C"},
        ])
        columns = [c for r in self.registry if r["status"] == "valid" for c in r["output_columns"]]
        self.assertEqual(len(columns), 28)
        self.assertEqual(Counter(c["type"] for c in columns),
                         {"bool": 12, "int32": 5, "text": 9, "text[]": 2})
        self.assertTrue(all(type(c["nullable"]) is bool for c in columns))

    def test_missing_duplicate_reordered_or_unknown_registry_ids_fail(self):
        changed = []
        changed.append(self.registry[:-1])
        changed.append([*self.registry, self.registry[0]])
        swapped = deepcopy(self.registry)
        swapped[0], swapped[1] = swapped[1], swapped[0]
        changed.append(swapped)
        unknown = deepcopy(self.registry)
        unknown[0]["id"] += "-unknown"
        changed.append(unknown)
        for rows in changed:
            with self.subTest(length=len(rows)), self.assertRaises(ValueError):
                self.validate(registry=rows)

    def test_checker_metadata_mutations_cannot_preserve_eligibility(self):
        index = next(i for i, r in enumerate(self.registry) if r["status"] == "valid")
        for field, value in (("name", "renamed"), ("type", "text"), ("nullable", True),
                             ("nullable", 0), ("nullable", None), ("collation", "C")):
            bad = deepcopy(self.registry)
            bad[index]["output_columns"][0][field] = value
            with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                self.validate(registry=bad)
        bad = deepcopy(self.registry)
        bad[index]["output_columns"].pop()
        with self.assertRaises(ValueError):
            self.validate(registry=bad)

    def test_deferred_rows_never_claim_empty_catalog_or_checker_rejection(self):
        index = next(i for i, r in enumerate(self.registry) if r["status"] == "deferred")
        for field, value in (("status", "unsupported"), ("eligibility", "checker"),
                             ("catalogFile", DIRECTORY + CATALOG_NAMES[0]),
                             ("output_columns", []), ("diagnostic", "input.parse"),
                             ("unresolved_collations", [])):
            bad = deepcopy(self.registry)
            bad[index][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.validate(registry=bad)
        for row in self.registry:
            if row["status"] == "deferred":
                self.assertIsNone(row["catalogFile"])
                self.assertIsNone(row["output_columns"])
                self.assertTrue(row["unresolved_collations"])

    def test_unresolved_table_field_collation_is_not_replaced_by_default(self):
        row = next(r for r in self.registry if r["id"].endswith("collate.icu.utf8.sql:statement-17"))
        self.assertEqual(row["status"], "deferred")
        self.assertEqual(row["unresolved_collations"], [["en-x-icu"]])
        # Explicit C in the predicate does not erase unknown provenance of the
        # projected table column, so this source cannot reuse the portable table.
        self.assertIsNone(row["catalogFile"])
        names = {t["name"] for t in self.snapshots["source_icu_declarations.json"]["tables"]}
        self.assertNotIn("collate_test1", names)
        self.assertNotIn("collate_test2", names)

    def test_snapshot_conversion_preserves_exact_source_columns(self):
        converted = declared_snapshots(self.context, self.provenance)
        self.assertEqual(converted, self.snapshots)
        tables = {t["name"]: t for t in converted["source_icu_declarations.json"]["tables"]}
        self.assertEqual(tables["test6a"]["columns"], [
            {"name": "a", "type": "int32", "nullable": True},
            {"name": "b", "type": "text[]", "nullable": True},
        ])
        self.assertNotIn("columnCollations", tables["test6a"])
        self.assertTrue(tables["test1cs"]["columnCollations"][0]["collation"].endswith("context-statement-246"))
        self.assertEqual(len(converted["source_portable_declarations.json"]["tables"]), 1)

    def test_missing_extra_or_changed_snapshot_fails(self):
        missing = deepcopy(self.snapshots)
        missing.pop("source_builtin.json")
        extra = {**self.snapshots, "unreviewed.json": self.snapshots["source_builtin.json"]}
        changed = deepcopy(self.snapshots)
        changed["source_icu_declarations.json"]["tables"][1]["columns"][0]["nullable"] = False
        defaulted = deepcopy(self.snapshots)
        table = next(t for t in defaulted["source_icu_declarations.json"]["tables"] if t["name"] == "test1cs")
        table.pop("columnCollations")
        for snapshots in (missing, extra, changed, defaulted):
            with self.assertRaises(ValueError):
                self.validate(snapshots=snapshots)

    def test_custom_identity_is_distinct_and_has_no_native_oid_claim(self):
        entries = self.snapshots["source_icu_declarations.json"]["collations"]["entries"]
        custom = [e for e in entries if e["id"].startswith("custom:")]
        self.assertEqual(len(custom), 9)
        self.assertEqual(len({e["id"] for e in custom}), 9)
        self.assertTrue(all(e["id"].startswith("custom:collations:postgres:") for e in custom))
        self.assertTrue(all(e["schema"] == "collate_tests" and e["encoding"] is None for e in custom))
        self.assertTrue(all(set(e) == {"id", "schema", "name", "encoding", "deterministic",
                                      "exposeUnqualified"} for e in entries))
        names = {e["name"]: e for e in custom}
        self.assertIs(names["case_insensitive"]["deterministic"], False)
        self.assertIs(names["ctest_det"]["deterministic"], True)
        self.assertIs(names["case_sensitive"]["deterministic"], True)

    def test_declaration_binding_type_or_identity_substitution_fails(self):
        mutations = [
            lambda p: p["custom_collation_bindings"][0].update(id="custom:made-up"),
            lambda p: p["custom_collation_bindings"][0].update(written_options=[]),
            lambda p: p["table_bindings"][0].update(declaration_id=p["table_bindings"][1]["declaration_id"]),
            lambda p: p.update(source_execution="performed"),
            lambda p: p.update(native_source_analysis="performed"),
        ]
        for mutate in mutations:
            provenance = deepcopy(self.provenance)
            mutate(provenance)
            with self.assertRaises(ValueError):
                self.validate(provenance=provenance)
        # Exercise the finite declaration conversion itself, beyond its outer
        # frozen provenance hash.
        provenance = deepcopy(self.provenance)
        provenance["custom_collation_bindings"][0]["id"] = "custom:other"
        with self.assertRaises(ValueError):
            declared_snapshots(self.context, provenance)

    def test_declared_field_conversion_refuses_an_unresolved_identity(self):
        context = deepcopy(self.context)
        table = next(c for c in context["declarations"]
                     if c["observed_declaration"].get("name") == ["test1cs"])
        table["observed_declaration"]["columns"][0]["written_collation"] = ["unprovided-locale"]
        with self.assertRaises(ValueError):
            declared_snapshots(context, self.provenance)

    def test_no_nullable_refinement_is_invented_from_source_predicates(self):
        for suffix in ("statement-238", "statement-239", "statement-244", "statement-245"):
            row = next(r for r in self.registry if r["id"].endswith(suffix))
            self.assertEqual([c["nullable"] for c in row["output_columns"]], [True, True])
        join = next(r for r in self.registry if r["id"].endswith("statement-284"))
        self.assertIs(join["output_columns"][0]["nullable"], True)

    def test_file_integrity_binds_all_catalogs_and_semantic_source_evidence(self):
        paths = [DIRECTORY + name for name in (
            "source_contracts.json", "source_snapshot_provenance.json", "concrete.jsonl",
            "declaration_contexts.json", *CATALOG_NAMES,
        )]
        paths += [e["local_path"] for e in self.provenance["basis_sources"]]
        with tempfile.TemporaryDirectory() as temporary:
            destination = Path(temporary)
            for path in paths:
                target = destination / path
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / path, target)
            self.assertEqual(load_source_contracts(destination), self.registry)
            for path in (DIRECTORY + "source_builtin.json",
                         self.provenance["basis_sources"][0]["local_path"]):
                target = destination / path
                content = target.read_bytes()
                target.write_bytes(content + b"\n")
                with self.subTest(path=path), self.assertRaises(ValueError):
                    load_source_contracts(destination)
                target.write_bytes(content)

    def validate_observed(self, **changes):
        values = {"registry": self.observed_registry, "baseline": self.registry,
                  "snapshot": self.observed_catalog, "context": self.context,
                  "observation": self.observation, "provenance": self.observed_provenance}
        values.update(changes)
        return validate_observed_registry(**values)

    def test_observed_catalog_complements_without_rewriting_baseline(self):
        self.assertEqual(load_observed_source_contracts(), self.observed_registry)
        eligible = [r for r in self.registry if r["status"] == "valid"]
        self.assertEqual(len({r["id"] for r in eligible + self.observed_registry}), 50)
        self.assertFalse({r["id"] for r in eligible} & {r["id"] for r in self.observed_registry})
        self.assertEqual(sum(len(r["output_columns"]) for r in eligible + self.observed_registry), 71)
        self.assertEqual(Counter(r["status"] for r in load_source_contracts()), {"valid": 18, "deferred": 32})

    def test_observed_outputs_preserve_original_names_and_field_collations(self):
        columns = [c for r in self.observed_registry for c in r["output_columns"]]
        self.assertEqual(len(columns), 43)
        self.assertEqual(Counter(c["type"] for c in columns), {"bool": 30, "int32": 6, "text": 7})
        row = next(r for r in self.observed_registry if r["id"].endswith("collate.icu.utf8.sql:statement-17"))
        self.assertEqual(row["output_columns"], [
            {"name": "a", "type": "int32", "nullable": True, "collation": None},
            {"name": "b", "type": "text", "nullable": False,
             "collation": "custom:fixture-observed:pg_catalog:en-x-icu:all-encodings"},
        ])
        # ORDER BY COLLATE does not change the projected table field's identity.
        row = next(r for r in self.observed_registry if r["id"].endswith("statement-203"))
        self.assertEqual(row["output_columns"][1]["collation"],
                         "custom:fixture-observed:pg_catalog:sv-x-icu:all-encodings")

    def test_native_catalog_has_exact_metadata_and_no_source_execution(self):
        observation = self.observation
        self.assertEqual(observation["source_execution"], "not-performed")
        self.assertEqual(observation["scope"], "isolated authored fixture catalog, not source deployment")
        self.assertEqual(observation["native_version"]["server_version_num"], "160015")
        self.assertEqual(observation["native_version"]["server_encoding"], "UTF8")
        self.assertEqual(len(observation["observed"]), 10)
        self.assertEqual(len({r["oid"] for r in observation["observed"]}), 10)
        self.assertEqual(len(observation["localedef_commands"]), 3)
        self.assertIn("FROM pg_collation", observation["catalog_query"])
        self.assertIn("CREATE COLLATION", observation["native_setup"])
        self.assertNotIn("collate_tests", observation["native_setup"])
        imported = {r["collname"]: r for r in observation["observed"]}
        self.assertEqual(imported["en-x-icu"]["collencoding"], -1)
        self.assertEqual(imported["sv_SE"]["collencoding"], 6)
        self.assertEqual(imported["tr_TR"]["collprovider"], "c")
        self.assertTrue(all(type(r["collisdeterministic"]) is bool for r in imported.values()))

    def test_observed_snapshot_derivation_rejects_missing_duplicate_or_wrong_objects(self):
        self.assertEqual(observed_snapshot(self.context, self.observation), self.observed_catalog)
        mutations = [
            lambda o: o["observed"].pop(),
            lambda o: o["observed"][1].update(oid=o["observed"][0]["oid"]),
            lambda o: o["observed"][0].update(nspname="unreviewed"),
            lambda o: o["observed"][0].update(collencoding=True),
            lambda o: o["observed"][0].update(collencoding=8),
            lambda o: o["observed"][0].update(collisdeterministic=1),
            lambda o: o["observed"][0].update(collprovider="unknown"),
            lambda o: o.update(source_execution="performed"),
        ]
        for mutate in mutations:
            bad = deepcopy(self.observation)
            mutate(bad)
            with self.assertRaises(ValueError):
                observed_snapshot(self.context, bad)

    def test_observed_registry_omission_renaming_or_wrong_identity_fails(self):
        for field, value in (("name", "renamed"), ("type", "text"),
                             ("nullable", 0), ("collation", "C")):
            bad = deepcopy(self.observed_registry)
            bad[0]["output_columns"][0][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError):
                self.validate_observed(registry=bad)
        for bad in (self.observed_registry[:-1], self.observed_registry + [self.observed_registry[0]]):
            with self.assertRaises(ValueError):
                self.validate_observed(registry=bad)
        bad = deepcopy(self.observed_catalog)
        table = next(t for t in bad["tables"] if t["name"] == "collate_test1")
        table["columnCollations"][0]["collation"] = "C"
        with self.assertRaises(ValueError):
            self.validate_observed(snapshot=bad)

    def test_fixture_locale_equivalence_cannot_merge_distinct_objects(self):
        entries = {e["name"]: e for e in self.observed_catalog["collations"]["entries"]}
        self.assertNotEqual(entries["ucs_basic"]["id"], entries["C"]["id"])
        self.assertNotEqual(entries["und-x-icu"]["id"], entries["unicode"]["id"])
        self.assertNotEqual(entries["C"]["id"], entries["POSIX"]["id"])
        self.assertEqual(entries["ucs_basic"]["encoding"], "UTF8")
        self.assertIsNone(entries["unicode"]["encoding"])
        bad = deepcopy(self.observed_catalog)
        found = next(e for e in bad["collations"]["entries"] if e["name"] == "unicode")
        found["id"] = entries["und-x-icu"]["id"]
        with self.assertRaises(ValueError):
            self.validate_observed(snapshot=bad)

    def test_observed_file_integrity_is_independent_of_local_locale_installation(self):
        # Copy only inert JSON/source evidence: no PG binary or localedef output
        # is necessary for this offline gate.
        with tempfile.TemporaryDirectory() as temporary:
            destination = Path(temporary)
            shutil.copytree(ROOT / DIRECTORY, destination / DIRECTORY)
            self.assertEqual(load_observed_source_contracts(destination), self.observed_registry)
            path = destination / DIRECTORY / "provenance/fixture-catalog-observation.json"
            original = path.read_bytes()
            changed = json.loads(original)
            changed["observed"][0]["collversion"] = "different"
            path.write_text(json.dumps(changed))
            with self.assertRaises(ValueError):
                load_observed_source_contracts(destination)
            path.write_bytes(original)
            path = destination / DIRECTORY / "source_observed_catalog.json"
            path.write_bytes(path.read_bytes() + b"\n")
            with self.assertRaises(ValueError):
                load_observed_source_contracts(destination)


if __name__ == "__main__":
    unittest.main()
