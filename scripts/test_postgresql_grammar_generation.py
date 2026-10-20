#!/usr/bin/env python3
"""Offline generated-table fidelity and malformed XML regressions."""
from __future__ import annotations

import copy
import hashlib
import json
import shutil
import unittest
import xml.etree.ElementTree as ET

import generate_postgresql_grammar as generation
import inventory_postgresql_grammar as inventory


@unittest.skipUnless(shutil.which("bison"), "Bison is required for XML generation")
class GeneratedGrammarTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report = inventory.bison_report(
            inventory.FIXTURES / "source/src/backend/parser/gram.y")
        cls.keywords = inventory.parse_keywords(
            (inventory.FIXTURES / "source/src/include/parser/kwlist.h").read_text())
        cls.data = generation.read_tables(cls.report)

    def mutated(self):
        return copy.deepcopy(self.report)

    def test_every_shift_and_goto_is_preserved(self):
        _, _, symbols, _, rows, states = self.data
        for source, state in zip(self.report.findall("automaton/state"), states):
            for kind, generated in [("shift", rows[state["shiftRow"]]),
                                    ("goto", state["gotos"])]:
                expected = sorted(
                    (symbols[t.attrib["symbol"]], int(t.attrib["state"]))
                    for t in source.findall(
                        f"actions/transitions/transition[@type='{kind}']"))
                self.assertEqual(sorted(generated), expected)

    def test_every_enabled_reduction_error_and_default_is_preserved(self):
        _, _, symbols, _, _, states = self.data
        for source, state in zip(self.report.findall("automaton/state"), states):
            explicit, default = [], ("reject", None)
            for element in source.findall("actions/reductions/reduction"):
                if element.attrib["enabled"] != "true":
                    continue
                rule = element.attrib["rule"]
                operation = ("accept", None) if rule == "accept" else ("reduce", int(rule))
                terminal = element.attrib["symbol"]
                if terminal == "$default":
                    default = operation
                else:
                    explicit.append((symbols[terminal], operation[1]))
            self.assertEqual(state["reductions"], sorted(explicit))
            self.assertEqual(state["default"], default)
            self.assertEqual(state["errors"], sorted(
                symbols[e.attrib["symbol"]] for e in source.findall("actions/errors/error")))

    def test_complete_generated_files_and_hashes_are_reproducible(self):
        artifacts, counts = generation.generated_sources(self.report, self.keywords)
        self.assertEqual(counts, {
            "production_entries": 3285, "states": 6223,
            "distinct_shift_rows": 1794, "deduplicated_shift_entries": 76118,
            "goto_entries": 15470, "generated_modules": 82})
        manifest = json.loads((inventory.FIXTURES / "lean_generation.json").read_text())
        self.assertEqual(manifest["counts"], counts)
        expected = {
            "SQLean/PostgresGrammar/" + path:
            (hashlib.sha256(content.encode()).hexdigest(), len(content.encode()))
            for path, content in artifacts.items()}
        self.assertEqual(expected, {f["path"]: (f["sha256"], f["bytes"]) for f in manifest["files"]})
        for path, content in artifacts.items():
            self.assertEqual((generation.DESTINATION / path).read_text(), content)

    def test_keywords_map_to_internal_symbols_not_external_codes(self):
        _, terminals, symbols, _, _, _ = self.data
        select = next(t for t in terminals if t["name"] == "SELECT")
        self.assertNotEqual(select["symbol-number"], select["token-number"])
        self.assertEqual(symbols["SELECT"], int(select["symbol-number"]))
        self.assertTrue(all(k["token"] in symbols for k in self.keywords))

    def test_shift_layout_bounds_each_declaration(self):
        artifacts, _ = generation.render_chunks(
            "Shifts", [((3, 7),)] * 65, "Array (Nat × Nat)", generation.pair_array)
        self.assertEqual(len(artifacts), 2)
        self.assertEqual(artifacts["Generated/Shifts000.lean"].count("private def shiftRow"), 64)
        self.assertIn("private def shiftRow0064", artifacts["Generated/Shifts001.lean"])

    def test_nonconsecutive_state_is_rejected(self):
        report = self.mutated()
        report.find("automaton/state").set("number", "1")
        with self.assertRaisesRegex(inventory.InventoryError, "nonconsecutive"):
            generation.read_tables(report)

    def test_out_of_range_and_negative_transition_are_rejected(self):
        for destination in ["6223", "-1"]:
            with self.subTest(destination=destination):
                report = self.mutated()
                report.find(".//transition").set("state", destination)
                with self.assertRaisesRegex(inventory.InventoryError, "transition target"):
                    generation.read_tables(report)

    def test_wrong_transition_kind_is_rejected(self):
        for mutation in [{"type": "future"}, {"symbol": "parse_toplevel"}]:
            with self.subTest(mutation=mutation):
                report = self.mutated()
                report.find(".//transition[@type='shift']").attrib.update(mutation)
                with self.assertRaisesRegex(inventory.InventoryError, "symbol kind"):
                    generation.read_tables(report)

    def test_duplicate_transition_is_rejected(self):
        report = self.mutated()
        transitions = report.find(".//transitions")
        transitions.append(copy.deepcopy(transitions[0]))
        with self.assertRaisesRegex(inventory.InventoryError, "duplicate LR"):
            generation.read_tables(report)

    def test_unknown_reduction_terminal_is_rejected(self):
        report = self.mutated()
        report.find(".//reduction[@enabled='true']").set("symbol", "not_a_terminal")
        with self.assertRaisesRegex(inventory.InventoryError, "unknown terminal"):
            generation.read_tables(report)

    def test_missing_reduction_rule_is_rejected(self):
        for rule in ["3285", "-1"]:
            with self.subTest(rule=rule):
                report = self.mutated()
                report.find(".//reduction[@enabled='true']").set("rule", rule)
                with self.assertRaisesRegex(inventory.InventoryError, "reduction target"):
                    generation.read_tables(report)

    def test_conflicting_resolved_actions_are_rejected(self):
        report = self.mutated()
        state = next(s for s in report.findall("automaton/state")
                     if s.find("actions/transitions/transition[@type='shift']") is not None)
        terminal = state.find("actions/transitions/transition[@type='shift']").attrib["symbol"]
        ET.SubElement(state.find("actions/reductions"), "reduction",
                      {"symbol": terminal, "rule": "1", "enabled": "true"})
        with self.assertRaisesRegex(inventory.InventoryError, "overlapping"):
            generation.read_tables(report)

    def test_disabled_reductions_do_not_override_resolved_actions(self):
        report = self.mutated()
        state = report.find("automaton/state")
        ET.SubElement(state.find("actions/reductions"), "reduction",
                      {"symbol": "SELECT", "rule": "1", "enabled": "false"})
        self.assertEqual(generation.read_tables(report), self.data)


if __name__ == "__main__":
    unittest.main()
