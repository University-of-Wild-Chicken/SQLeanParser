#!/usr/bin/env python3
"""Offline source-pinning, XML inventory, and misleading-C-action regressions."""
from __future__ import annotations

import copy
import json
from pathlib import Path
import shutil
import tempfile
import unittest
import xml.etree.ElementTree as ET

import inventory_postgresql_grammar as inventory


class PinnedSourceTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="sqlean-grammar-test-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        shutil.copytree(inventory.FIXTURES / "source", self.root / "source")
        shutil.copy2(inventory.FIXTURES / "sources.json", self.root / "sources.json")

    def test_pinned_sources_and_version(self):
        manifest = inventory.load_manifest(self.root)
        inventory.verify_sources(self.root, manifest)
        self.assertEqual(manifest["version"], "16.15")
        self.assertEqual(len(manifest["files"]), 6)

    def test_changed_source_bytes_fail(self):
        source = self.root / "source/src/backend/parser/gram.y"
        source.write_bytes(source.read_bytes() + b"\n/* changed */\n")
        with self.assertRaisesRegex(inventory.InventoryError, "hash/size mismatch"):
            inventory.verify_sources(self.root, inventory.load_manifest(self.root))

    def test_missing_lexer_fails(self):
        (self.root / "source/src/backend/parser/scan.l").unlink()
        with self.assertRaisesRegex(inventory.InventoryError, "missing upstream"):
            inventory.verify_sources(self.root, inventory.load_manifest(self.root))

    def mutate_manifest(self, mutation):
        path = self.root / "sources.json"
        manifest = json.loads(path.read_text())
        mutation(manifest)
        path.write_text(json.dumps(manifest))

    def test_wrong_commit_fails(self):
        self.mutate_manifest(lambda m: m.update(commit="0" * 40))
        with self.assertRaisesRegex(inventory.InventoryError, "pinned PostgreSQL"):
            inventory.load_manifest(self.root)

    def test_wrong_version_fails(self):
        self.mutate_manifest(lambda m: m.update(version="17.7"))
        with self.assertRaisesRegex(inventory.InventoryError, "pinned PostgreSQL"):
            inventory.load_manifest(self.root)

    def test_duplicate_or_traversing_input_fails(self):
        for replacement in ["COPYRIGHT", "../gram.y"]:
            with self.subTest(replacement=replacement):
                shutil.copy2(inventory.FIXTURES / "sources.json", self.root / "sources.json")
                self.mutate_manifest(lambda m: m["files"][1].update(path=replacement))
                with self.assertRaisesRegex(inventory.InventoryError, "exactly"):
                    inventory.load_manifest(self.root)

    def test_unpinned_url_fails(self):
        self.mutate_manifest(lambda m: m["files"][0].update(source_url="https://example.invalid/COPYRIGHT"))
        with self.assertRaisesRegex(inventory.InventoryError, "pinned commit"):
            inventory.load_manifest(self.root)

    def test_declared_size_is_checked(self):
        self.mutate_manifest(lambda m: m["files"][0].update(bytes=0))
        with self.assertRaisesRegex(inventory.InventoryError, "hash/size mismatch"):
            inventory.verify_sources(self.root, inventory.load_manifest(self.root))


class KeywordLexerTests(unittest.TestCase):
    GOOD = 'PG_KEYWORD("alpha", ALPHA, UNRESERVED_KEYWORD, BARE_LABEL)'

    def test_comments_strings_and_characters_do_not_invent_keywords(self):
        fake = r'''
/* PG_KEYWORD("fake", FAKE, RESERVED_KEYWORD, AS_LABEL) */
// PG_KEYWORD("fake2", FAKE2, RESERVED_KEYWORD, AS_LABEL)
"PG_KEYWORD(\"fake3\", FAKE3, RESERVED_KEYWORD, AS_LABEL)"
'\''
'''
        self.assertEqual(inventory.parse_keywords(fake + self.GOOD),
                         [{"spelling": "alpha", "token": "ALPHA",
                           "category": "UNRESERVED_KEYWORD", "label": "BARE_LABEL"}])

    def test_all_four_keyword_categories_are_retained(self):
        source = "\n".join(f'PG_KEYWORD("{name}", TOKEN_{index}, {category}, AS_LABEL)'
                           for index, (name, category) in enumerate([
                               ("alpha", "UNRESERVED_KEYWORD"), ("beta", "COL_NAME_KEYWORD"),
                               ("delta", "TYPE_FUNC_NAME_KEYWORD"), ("gamma", "RESERVED_KEYWORD")]))
        self.assertEqual(len({r["category"] for r in inventory.parse_keywords(source)}), 4)

    def test_duplicate_keyword_is_rejected(self):
        with self.assertRaisesRegex(inventory.InventoryError, "duplicate"):
            inventory.parse_keywords(self.GOOD + "\n" + self.GOOD)

    def test_malformed_macro_is_rejected(self):
        with self.assertRaisesRegex(inventory.InventoryError, "malformed"):
            inventory.parse_keywords(self.GOOD.replace(", BARE_LABEL", " BARE_LABEL"))

    def test_unknown_category_is_rejected(self):
        with self.assertRaisesRegex(inventory.InventoryError, "category"):
            inventory.parse_keywords(self.GOOD.replace("UNRESERVED_KEYWORD", "NEW_CATEGORY"))

    def test_unterminated_comment_and_string_are_rejected(self):
        for source in ["/* unmatched", '"unmatched', "'\\"]:
            with self.subTest(source=source), self.assertRaises(inventory.InventoryError):
                inventory.c_tokens(source)


class StoredInventoryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = json.loads((inventory.FIXTURES / "inventory.json").read_text())

    def test_complete_pinned_denominator(self):
        counts = self.data["counts"]
        self.assertEqual(counts["source_productions"], 3284)
        self.assertEqual(counts["source_nonterminals"], 705)
        self.assertEqual(counts["reported_terminals"], 518)
        self.assertEqual(counts["keyword_entries"], 471)
        self.assertEqual(counts["statement_families"], 125)

    def test_family_partition_has_no_claim_of_complete_coverage(self):
        entries = inventory.statement_families(self.data["productions"])
        self.assertEqual(entries, self.data["statement_families"])
        self.assertEqual(sum(e["sqlean_ast_coverage"] == "partial" for e in entries), 8)
        self.assertTrue(all(e["production_coverage"] == "not-measured" for e in entries))
        self.assertTrue(all(not e["full_independent_validity"] and not e["full_renderer_contract"] for e in entries))

    def test_new_statement_family_requires_review(self):
        productions = copy.deepcopy(self.data["productions"])
        productions.append({"id": len(productions), "lhs": "stmt", "rhs": ["FutureStmt"], "attributes": {}})
        with self.assertRaisesRegex(inventory.InventoryError, "partition changed"):
            inventory.statement_families(productions)

    def test_missing_statement_family_requires_review(self):
        productions = [r for r in self.data["productions"] if r["rhs"] != ["SelectStmt"]]
        with self.assertRaisesRegex(inventory.InventoryError, "partition changed"):
            inventory.statement_families(productions)

    def test_non_default_entry_modes_are_explicit(self):
        modes = self.data["entry_modes"]
        self.assertEqual(len(modes), 6)
        self.assertEqual(modes[0]["rhs"], ["stmtmulti"])
        self.assertTrue(all(r["rhs"][0].startswith("MODE_") for r in modes[1:]))

    def test_actions_and_typed_validity_are_outside_evidence(self):
        self.assertEqual(self.data["boundary"]["evidence"], "pinned-grammar-inventory-only")
        for key in ("implements_parser", "proves_lexer_equivalence", "executes_postgresql_actions",
                    "proves_typed_sql_validity", "proves_renderer_semantics"):
            self.assertFalse(self.data["boundary"][key])
        assertion = next(e for e in self.data["statement_families"] if e["name"] == "CreateAssertionStmt")
        self.assertIn("feature-not-supported", assertion["upstream_action_note"])


@unittest.skipUnless(shutil.which("bison"), "Bison is required to regenerate XML, not to check source pins")
class BisonExtractionTests(unittest.TestCase):
    GRAMMAR = r'''
%token WORD STOP
%start entry
%%
entry: WORD {
  /* bogus: STOP | UNKNOWN; } */
  const char *fake = "invented: UNKNOWN | WORD; } \" quoted";
  char brace = '}';
  if (1) { int nested = 0; }
} STOP
| %empty
;
%%
const char *epilogue = "another_rule: UNKNOWN;";
'''

    def report(self, source):
        with tempfile.TemporaryDirectory(prefix="sqlean-bison-test-") as temp:
            path = Path(temp) / "test.y"
            path.write_text(source)
            return inventory.bison_report(path)

    def test_c_actions_and_epilogue_do_not_create_productions(self):
        rules, terminals, nonterminals = inventory.grammar_records(self.report(self.GRAMMAR))
        self.assertEqual([(r["lhs"], r["rhs"]) for r in rules],
                         [("$accept", ["entry", "$end"]), ("$@1", []),
                          ("entry", ["WORD", "$@1", "STOP"]), ("entry", [])])
        self.assertNotIn("UNKNOWN", {t["name"] for t in terminals})
        self.assertEqual({n["name"] for n in nonterminals}, {"$accept", "$@1", "entry"})

    def test_action_only_mutation_leaves_grammar_unchanged(self):
        original = inventory.grammar_records(self.report(self.GRAMMAR))
        mutated = inventory.grammar_records(self.report(self.GRAMMAR.replace(
            "int nested = 0;", 'int nested = 42; /* fake_rule: STOP; */')))
        self.assertEqual(original, mutated)

    def test_real_production_mutation_is_detected(self):
        original = inventory.grammar_records(self.report(self.GRAMMAR))[0]
        mutated = inventory.grammar_records(self.report(self.GRAMMAR.replace("| %empty", "| STOP\n| %empty")))[0]
        self.assertEqual(len(mutated), len(original) + 1)
        self.assertIn(["STOP"], [r["rhs"] for r in mutated])

    def test_invalid_grammar_is_not_inventoried(self):
        with self.assertRaisesRegex(inventory.InventoryError, "Bison rejected"):
            self.report(self.GRAMMAR.replace("} STOP", "} UNDECLARED"))

    def test_undeclared_symbol_in_xml_is_rejected(self):
        report = self.report(self.GRAMMAR)
        report.find("grammar/rules/rule/rhs/symbol").text = "UNDECLARED"
        with self.assertRaisesRegex(inventory.InventoryError, "undeclared"):
            inventory.grammar_records(report)

    def test_duplicate_rule_id_in_xml_is_rejected(self):
        report = self.report(self.GRAMMAR)
        report.find("grammar/rules/rule[2]").set("number", "0")
        with self.assertRaisesRegex(inventory.InventoryError, "consecutive"):
            inventory.grammar_records(report)

    def test_offline_full_regeneration_matches_committed_inventory(self):
        self.assertEqual(inventory.encoded(inventory.build_inventory()),
                         (inventory.FIXTURES / "inventory.json").read_text())


if __name__ == "__main__":
    unittest.main()
