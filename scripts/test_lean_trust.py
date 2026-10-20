#!/usr/bin/env python3
"""Regression tests for the Lean source trust guard's lexical boundary."""

from pathlib import Path
import tempfile
import unittest

from check_lean_trust import (
    ROOT, audit_import_groups, check_specification_independence, code_tokens, local_import_closure,
    module_name, project_sources, source_violations,
)


class LeanTrustSourceTests(unittest.TestCase):
    def forbidden(self, source: str) -> list[str]:
        return [token.value for token in source_violations(source)]

    def test_proof_placeholders(self) -> None:
        self.assertEqual(self.forbidden("theorem p : True := by sorry\nexample : True := by admit"),
                         ["sorry", "admit"])

    def test_custom_assumptions(self) -> None:
        self.assertEqual(self.forbidden("axiom p : False\naxioms q : True"), ["axiom", "axioms"])

    def test_qualified_bypasses(self) -> None:
        self.assertEqual(self.forbidden("Lean.ofReduceBool x\nLean.ofReduceNat x\nsorryAx _ false"),
                         ["ofReduceBool", "ofReduceNat", "sorryAx"])

    def test_native_execution_proof(self) -> None:
        self.assertEqual(self.forbidden("example : True := by native_decide"), ["native_decide"])
        self.assertEqual(self.forbidden("example : True := by decide +native"), ["native"])

    def test_runtime_replacement_attributes(self) -> None:
        self.assertEqual(self.forbidden('@[implemented_by other] def x := 1\n@[extern "x"] opaque y : Nat'),
                         ["implemented_by", "extern"])

    def test_unsafe_partial_and_skipped_kernel(self) -> None:
        self.assertEqual(self.forbidden(
            "unsafe def f := unsafeCast 1\npartial def g := g\nset_option debug.skipKernelTC true"),
            ["unsafe", "unsafeCast", "partial", "skipKernelTC"])

    def test_nested_comments_and_doc_comments_are_data(self) -> None:
        self.assertEqual(self.forbidden(
            "/- sorry /- axiom -/ unsafe -/\n/-- native_decide is forbidden. -/\n"
            "def x := 1 -- admit\n"), [])

    def test_sql_and_escaped_string_literals_are_data(self) -> None:
        self.assertEqual(self.forbidden(
            'def sql := "SELECT \'sorry\', \'axiom\', \'unsafe\'"\n'
            'def quoted := "say \\"native_decide\\""\n'), [])

    def test_raw_strings_are_data(self) -> None:
        self.assertEqual(self.forbidden(
            'def raw := r"axiom sorry"\ndef raw2 := r##"unsafe " native_decide"##'), [])

    def test_character_literals_and_identifier_primes(self) -> None:
        self.assertEqual(self.forbidden("def c := '\\''\ndef c' := 'a'\ndef sorry_count := 1"), [])

    def test_quoted_identifier_reference_is_not_hidden(self) -> None:
        self.assertEqual(self.forbidden("Lean.«ofReduceBool» x"), ["ofReduceBool"])

    def test_interpolation_expression_is_code(self) -> None:
        self.assertEqual(self.forbidden('def s := s!"text sorry {show Nat from by sorry}"'), ["sorry"])

    def test_nested_interpolation_and_record_braces(self) -> None:
        self.assertEqual(self.forbidden(
            'def s := s!"{{literal unsafe}} {({ value := m!"inner {by native_decide}" }).value}"'),
            ["native_decide"])

    def test_comments_and_strings_inside_interpolation(self) -> None:
        self.assertEqual(self.forbidden(
            'def s := s!"{(fun _ => "sorry") /- admit -/ 1}"'), [])

    def test_line_and_column_diagnostics(self) -> None:
        tokens = source_violations("-- ignored\n  theorem x : True := by sorry")
        self.assertEqual([(token.value, token.line, token.column) for token in tokens], [("sorry", 2, 26)])

    def test_unterminated_lexical_regions_fail_closed(self) -> None:
        for source in ("/- unfinished", '"unfinished', 'r##"unfinished', "«unfinished", 's!"{1'):
            with self.subTest(source=source), self.assertRaises(ValueError):
                code_tokens(source)

    def test_foundational_reasoning_is_allowed(self) -> None:
        self.assertEqual(self.forbidden(
            "example (p q : Prop) (h : p ↔ q) : p = q := propext h\n"
            "noncomputable def choose := Classical.choice\n"
            "example := Quot.sound\n"), [])

    def test_inventory_includes_new_modules_but_not_build_artifacts(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ("Main.lean", "SQLean/New.lean", "Tests/Hidden.lean", "Future/Feature.lean",
                         ".lake/build/Generated.lean"):
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text("", encoding="utf-8")
            self.assertEqual([module_name(path, root) for path in project_sources(root)],
                             ["Future.Feature", "Main", "SQLean.New", "Tests.Hidden"])

    def test_all_executable_roots_are_audited_without_name_collisions(self) -> None:
        modules = ["Main", "SQLean.ScopeContract.Spec", "ScopeContractMain",
                   "TestMain", "PostgresGrammarMain", "Tests.ProjectTrust"]
        groups = audit_import_groups(modules)
        roots = {"Main", "TestMain", "ScopeContractMain", "PostgresGrammarMain"}
        self.assertEqual({entrypoint for entrypoint, _ in groups}, roots)
        self.assertEqual(set().union(*(set(imports) for _, imports in groups)), set(modules))
        for entrypoint, imports in groups:
            self.assertEqual(set(imports) & roots, {entrypoint})
            self.assertEqual(set(imports) - roots,
                             {"SQLean.ScopeContract.Spec", "Tests.ProjectTrust"})

    def test_audit_groups_do_not_invent_missing_entrypoints(self) -> None:
        self.assertEqual(audit_import_groups(["Tests.ProjectTrust"]),
                         [(None, ["Tests.ProjectTrust"])])
        self.assertEqual(audit_import_groups(["ScopeContractMain", "Tests.ProjectTrust"]),
                         [("ScopeContractMain", ["Tests.ProjectTrust", "ScopeContractMain"])])

    def test_import_closure_ignores_comment_and_string_lookalikes(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "A.lean").write_text(
                'import B\n/-\nimport Hidden\n-/\ndef text := "\nimport AlsoHidden\n"\n',
                encoding="utf-8",
            )
            (root / "B.lean").write_text("public import C\n", encoding="utf-8")
            self.assertEqual(local_import_closure(root, "A"), {"A", "B", "C"})

    def test_transitive_renderer_dependency_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "SQLean/RenderContract").mkdir(parents=True)
            (root / "SQLean/RenderContract/Admissibility.lean").write_text(
                "import SQLean.RenderContract.Profile\n", encoding="utf-8")
            (root / "SQLean/RenderContract/Profile.lean").write_text(
                "import SQLean.AdvancedPretty\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "AdvancedPretty"):
                check_specification_independence(root)

    def test_multiple_imports_on_one_line_are_all_checked(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "SQLean/RenderContract").mkdir(parents=True)
            (root / "SQLean/RenderContract/Admissibility.lean").write_text(
                "import SQLean.RenderContract.Profile SQLean.AdvancedPretty -- SQLean.Hidden\n",
                encoding="utf-8",
            )
            self.assertEqual(local_import_closure(root, "SQLean.RenderContract.Admissibility"), {
                "SQLean.RenderContract.Admissibility", "SQLean.RenderContract.Profile", "SQLean.AdvancedPretty",
            })
            with self.assertRaisesRegex(ValueError, "AdvancedPretty"):
                check_specification_independence(root)

    def test_actual_render_specification_is_independent(self) -> None:
        for domain in ("Admissibility", "SQLiteAdmissibility"):
            self.assertTrue((ROOT / "SQLean" / "RenderContract" / f"{domain}.lean").is_file())
        check_specification_independence(ROOT)

    def test_actual_select_specification_has_only_reviewed_normative_dependencies(self) -> None:
        self.assertEqual(local_import_closure(ROOT, "SQLean.SelectContract.Spec"), {
            "SQLean.SelectContract.Spec", "SQLean.SelectContract.Profile",
            "SQLean.SelectContract.ScalarSignatures", "SQLean.SelectContract.Recursion",
            "SQLean.SelectContract.ExpressionSpec", "SQLean.SelectContract.Collation",
            "SQLean.SelectContract.CollationApplications", "SQLean.SelectContract.CollationRules",
            "SQLean.CollationSyntax", "SQLean.CatalogSyntax",
            "SQLean.AdvancedSyntax", "SQLean.SyntaxBase", "Std",
        })
        check_specification_independence(ROOT)

    def test_select_spec_rejects_direct_inference_parser_and_renderer_imports(self) -> None:
        for dependency in ("SQLean.SelectContract.Checker", "SQLean.AdvancedParser",
                           "SQLean.AdvancedPretty", "SQLean.RenderContract.Checker"):
            with self.subTest(dependency=dependency), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                (root / "SQLean/SelectContract").mkdir(parents=True)
                (root / "SQLean/SelectContract/Spec.lean").write_text(
                    f"import SQLean.SelectContract.Profile {dependency}\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, "SelectContract.Spec.*" + dependency):
                    check_specification_independence(root)

    def test_select_recursion_helper_cannot_import_executable_inference_transitively(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "SQLean/SelectContract").mkdir(parents=True)
            (root / "SQLean/SelectContract/Spec.lean").write_text(
                "import SQLean.SelectContract.Recursion\n", encoding="utf-8")
            (root / "SQLean/SelectContract/Recursion.lean").write_text(
                "import SQLean.SelectContract.ScalarSignatures SQLean.AdvancedQueryValidation "
                "-- SQLean.Ignored\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "SelectContract.Spec.*AdvancedQueryValidation"):
                check_specification_independence(root)

    def test_select_boundary_is_closed_to_unreviewed_helpers(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "SQLean/SelectContract").mkdir(parents=True)
            (root / "SQLean/SelectContract/Spec.lean").write_text(
                "import SQLean.SelectContract.FutureHelper\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "SelectContract.Spec.*FutureHelper"):
                check_specification_independence(root)

    def test_collation_specification_helpers_cannot_depend_on_inference_or_rendering(self) -> None:
        for helper in ("Collation", "CollationApplications", "CollationRules", "ExpressionSpec"):
            for forbidden in ("SQLean.SelectContract.Checker", "SQLean.RenderContract.ValidityPreservation"):
                with self.subTest(helper=helper, forbidden=forbidden), tempfile.TemporaryDirectory() as directory:
                    root = Path(directory)
                    (root / "SQLean/SelectContract").mkdir(parents=True)
                    (root / "SQLean/SelectContract/Spec.lean").write_text(
                        "import SQLean.SelectContract." + helper + "\n", encoding="utf-8")
                    (root / f"SQLean/SelectContract/{helper}.lean").write_text(
                        "import SQLean.CollationSyntax " + forbidden + "\n", encoding="utf-8")
                    with self.assertRaisesRegex(ValueError, "SelectContract.Spec.*" + forbidden):
                        check_specification_independence(root)

    def test_sqlite_domain_direct_checker_dependency_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "SQLean/RenderContract").mkdir(parents=True)
            (root / "SQLean/RenderContract/SQLiteAdmissibility.lean").write_text(
                "import SQLean.RenderContract.Profile SQLean.RenderContract.Checker\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(ValueError, "SQLiteAdmissibility.*Checker"):
                check_specification_independence(root)

    def test_sqlite_domain_transitive_parser_dependency_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "SQLean/RenderContract").mkdir(parents=True)
            (root / "SQLean/RenderContract/SQLiteAdmissibility.lean").write_text(
                "import SQLean.RenderContract.Profile\n", encoding="utf-8")
            (root / "SQLean/RenderContract/Profile.lean").write_text(
                "import SQLean.AdvancedSyntax SQLean.AdvancedParser -- SQLean.Hidden\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(ValueError, "SQLiteAdmissibility.*AdvancedParser"):
                check_specification_independence(root)

    def test_independent_domains_do_not_implicitly_expand_each_others_boundary(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "SQLean/RenderContract").mkdir(parents=True)
            (root / "SQLean/RenderContract/SQLiteAdmissibility.lean").write_text(
                "import SQLean.RenderContract.Admissibility\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "SQLiteAdmissibility.*Admissibility"):
                check_specification_independence(root)

    def test_both_domains_accept_only_the_reviewed_syntax_closure(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "SQLean/RenderContract").mkdir(parents=True)
            for domain in ("Admissibility", "SQLiteAdmissibility"):
                (root / "SQLean/RenderContract" / f"{domain}.lean").write_text(
                    "import SQLean.RenderContract.Profile -- SQLean.AdvancedPretty\n",
                    encoding="utf-8",
                )
            (root / "SQLean/RenderContract/Profile.lean").write_text(
                "import SQLean.AdvancedSyntax\n", encoding="utf-8")
            (root / "SQLean/AdvancedSyntax.lean").write_text(
                "import SQLean.SyntaxBase\n", encoding="utf-8")
            (root / "SQLean/SyntaxBase.lean").write_text("import Std\n", encoding="utf-8")
            check_specification_independence(root)

    def test_scope_domains_accept_only_the_reviewed_syntax_closure(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "SQLean/ScopeContract").mkdir(parents=True)
            (root / "SQLean/ScopeContract/Embedding.lean").write_text(
                "import SQLean.ScopeContract.Spec\n", encoding="utf-8")
            (root / "SQLean/ScopeContract/Spec.lean").write_text(
                "import SQLean.AdvancedSyntax\n/-\nimport SQLean.AdvancedParser\n-/\n",
                encoding="utf-8")
            (root / "SQLean/AdvancedSyntax.lean").write_text(
                "import SQLean.SyntaxBase\n", encoding="utf-8")
            (root / "SQLean/SyntaxBase.lean").write_text("import Std\n", encoding="utf-8")
            check_specification_independence(root)

    def test_scope_embedding_direct_checker_dependency_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "SQLean/ScopeContract").mkdir(parents=True)
            (root / "SQLean/ScopeContract/Embedding.lean").write_text(
                "import SQLean.ScopeContract.Spec SQLean.AdvancedQueryValidation\n",
                encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "ScopeContract.Embedding.*AdvancedQueryValidation"):
                check_specification_independence(root)

    def test_scope_specification_transitive_parser_dependency_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "SQLean/ScopeContract").mkdir(parents=True)
            (root / "SQLean/ScopeContract/Spec.lean").write_text(
                "import SQLean.AdvancedSyntax\n", encoding="utf-8")
            (root / "SQLean/AdvancedSyntax.lean").write_text(
                "import SQLean.SyntaxBase SQLean.AdvancedParser -- SQLean.Hidden\n",
                encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "ScopeContract.Spec.*AdvancedParser"):
                check_specification_independence(root)

    def test_scope_specification_does_not_depend_on_embedding(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "SQLean/ScopeContract").mkdir(parents=True)
            (root / "SQLean/ScopeContract/Spec.lean").write_text(
                "import SQLean.ScopeContract.Embedding\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "ScopeContract.Spec.*Embedding"):
                check_specification_independence(root)

    def test_scope_boundary_does_not_inherit_render_profile_allowlist(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "SQLean/ScopeContract").mkdir(parents=True)
            (root / "SQLean/ScopeContract/Spec.lean").write_text(
                "import SQLean.RenderContract.Profile\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "ScopeContract.Spec.*RenderContract.Profile"):
                check_specification_independence(root)

    def test_render_boundary_does_not_inherit_scope_allowlist(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "SQLean/RenderContract").mkdir(parents=True)
            (root / "SQLean/RenderContract/Admissibility.lean").write_text(
                "import SQLean.ScopeContract.Spec\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "Admissibility.*ScopeContract.Spec"):
                check_specification_independence(root)


    def test_grammar_spec_accepts_only_immutable_syntax(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "SQLean/PostgresGrammar").mkdir(parents=True)
            (root / "SQLean/PostgresGrammar/Spec.lean").write_text(
                "import SQLean.PostgresGrammar.Syntax\n", encoding="utf-8")
            (root / "SQLean/PostgresGrammar/Syntax.lean").write_text(
                "import Std\n", encoding="utf-8")
            check_specification_independence(root)

    def test_grammar_spec_rejects_executable_and_generated_dependencies(self) -> None:
        for dependency in ("Parser", "Lexer", "Generated"):
            with self.subTest(dependency=dependency), tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                (root / "SQLean/PostgresGrammar").mkdir(parents=True)
                (root / "SQLean/PostgresGrammar/Spec.lean").write_text(
                    "import SQLean.PostgresGrammar.Syntax\n", encoding="utf-8")
                (root / "SQLean/PostgresGrammar/Syntax.lean").write_text(
                    f"import SQLean.PostgresGrammar.{dependency}\n", encoding="utf-8")
                with self.assertRaisesRegex(ValueError, f"PostgresGrammar.Spec.*{dependency}"):
                    check_specification_independence(root)


if __name__ == "__main__":
    unittest.main()
