"""Mutation tests for a design-record check that must never approve a release."""
from contextlib import redirect_stdout
from copy import deepcopy
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

import check_review_ladder as checker


class ReviewLadderTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.plan = checker.read_json(checker.ROOT, checker.PLAN)
        cls.index = checker.read_json(checker.ROOT, checker.INDEX)
        cls.manifest = checker.read_json(checker.ROOT, checker.MANIFEST)

    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        paths = [checker.PLAN, checker.DOCUMENT, checker.INDEX, checker.MANIFEST,
                 checker.TARGET['inventory']] + [row['report'] for row in self.index['reviews']]
        for name in paths:
            target = self.root / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(checker.ROOT / name, target)

    def write(self, path, value):
        (self.root / path).write_text(json.dumps(value, indent=2) + '\n')

    def reject(self):
        with self.assertRaises(checker.RecordError):
            checker.validate(self.root)

    def test_existing_record_is_consistent_but_failed_candidate_never_release_approval(self):
        result = checker.validate(self.root)
        self.assertEqual(result['result'], 'consistent')
        self.assertIs(result['release_approval'], False)
        self.assertIs(result['release_readiness_evaluated'], False)
        self.assertEqual(result['historical_review_result'], 'CONSTRUCTED_BLOCKERS')
        self.assertEqual(result['constructed_blockers'], ['ASTRA1-001', 'ASTRA2-001'])
        self.assertEqual(result['archived_reports'], 6)
        self.assertEqual(result['historical_input_files'], 1483)
        self.assertNotIn('VERIFIED', json.dumps(result))
        # Only records were copied. Historical inputs are not confused with
        # today's repaired files, nor presented as a freshly rechecked build.
        self.assertFalse((self.root / 'SQLean').exists())
        self.assertTrue(any('Luna1' in note for note in result['limitations']))

    def test_exact_two_luna_two_sol_two_astra_order_is_mandatory(self):
        for mutation in ['reorder', 'one-reviewer', 'three-reviewers', 'wrong-model', 'extra-level',
                         'missing-level', 'bool-level', 'bool-reviewers']:
            plan = deepcopy(self.plan)
            ladder = plan['ladder']
            if mutation == 'reorder':
                ladder[0], ladder[1] = ladder[1], ladder[0]
            elif mutation == 'one-reviewer':
                ladder[0]['independent_reviewers'] = 1
            elif mutation == 'three-reviewers':
                ladder[1]['independent_reviewers'] = 3
            elif mutation == 'wrong-model':
                ladder[1]['model'] = 'gpt-6-sol'
            elif mutation == 'extra-level':
                ladder.append(deepcopy(ladder[-1]))
            elif mutation == 'missing-level':
                ladder.pop()
            elif mutation == 'bool-level':
                ladder[0]['level'] = True
            else:
                ladder[0]['independent_reviewers'] = True
            with self.subTest(mutation=mutation), self.assertRaises(checker.RecordError):
                checker.check_plan(plan)

    def test_every_required_review_closure_and_example_policy_fails_closed(self):
        for section in ['review_policy', 'closure_requirements', 'example_policy', 'target']:
            for key, original in self.plan[section].items():
                for mutation in ['missing', 'weakened']:
                    plan = deepcopy(self.plan)
                    if mutation == 'missing':
                        plan[section].pop(key)
                    else:
                        plan[section][key] = not original if type(original) is bool else 'unbound'
                    with self.subTest(section=section, key=key, mutation=mutation), self.assertRaises(checker.RecordError):
                        checker.check_plan(plan)
        plan = deepcopy(self.plan)
        plan['review_policy']['same_frozen_candidate_per_level'] = 1
        with self.assertRaises(checker.RecordError):
            checker.check_plan(plan)

    def test_design_cannot_be_promoted_by_approval_state_or_invented_closure_report(self):
        for mutation in ['approval', 'mode', 'status', 'closure', 'closure-report', 'extra-field']:
            plan = deepcopy(self.plan)
            if mutation == 'approval':
                plan['initial_preflight']['release_approval'] = True
            elif mutation == 'mode':
                plan['mode'] = 'execute'
            elif mutation == 'status':
                plan['status'] = 'VERIFIED'
            elif mutation == 'closure':
                plan['final_closure'] = {'status': 'VERIFIED', 'input_root_sha256': checker.INPUT_ROOT}
            elif mutation == 'closure-report':
                plan['closure_report'] = 'reports/forged-verified.json'
            else:
                plan['manual_approval'] = True
            self.write(checker.PLAN, plan)
            with self.subTest(mutation=mutation):
                self.reject()
        self.write(checker.PLAN, self.plan)
        index = deepcopy(self.index)
        index['release_approval'] = True
        self.write(checker.INDEX, index)
        self.reject()

    def test_all_baseline_identifiers_and_blockers_are_bound(self):
        for field, value in [('candidate_commit', '0' * 40), ('completed_reviewers_by_level', [2, 2, 1]),
                             ('constructed_blockers', []), ('constructed_blockers', ['ASTRA2-001']),
                             ('constructed_blockers', ['ASTRA2-001', 'ASTRA1-001']),
                             ('scope', 'complete PostgreSQL release approval')]:
            plan = deepcopy(self.plan)
            plan['initial_preflight'][field] = value
            with self.subTest(field=field, value=value), self.assertRaises(checker.RecordError):
                checker.check_plan(plan)
        for field, value in [('candidate_commit', '0' * 40), ('review_result', 'CLEAN'),
                             ('input_manifest', '/tmp/unbound.json'), ('input_root_sha256', '0' * 64),
                             ('model_identity_trust', 'Independently verified weights.'), ('limitations', [])]:
            index = deepcopy(self.index)
            index[field] = value
            self.write(checker.INDEX, index)
            with self.subTest(field=field):
                self.reject()

    def test_archive_requires_six_distinct_ordered_unchanged_reports(self):
        for mutation in ['missing', 'duplicate', 'reorder', 'wrong-model', 'wrong-level', 'wrong-reviewer',
                         'wrong-path', 'wrong-hash', 'drop-blocker', 'invent-early-blocker', 'extra-field']:
            index = deepcopy(self.index)
            rows = index['reviews']
            if mutation == 'missing':
                rows.pop()
            elif mutation == 'duplicate':
                rows[1] = deepcopy(rows[0])
            elif mutation == 'reorder':
                rows[2], rows[3] = rows[3], rows[2]
            elif mutation == 'drop-blocker':
                rows[4]['constructed_objections'] = []
            elif mutation == 'invent-early-blocker':
                rows[0]['constructed_objections'] = ['ASTRA1-001']
            elif mutation == 'extra-field':
                rows[4]['discharged'] = True
            else:
                key, value = {'wrong-model': ('requested_model', 'gpt-6-sol'),
                              'wrong-level': ('level', 3), 'wrong-reviewer': ('reviewer', 'luna1'),
                              'wrong-path': ('report', '../unbound.json'), 'wrong-hash': ('report_sha256', '0' * 64)}[mutation]
                rows[2][key] = value
            self.write(checker.INDEX, index)
            with self.subTest(mutation=mutation):
                self.reject()

    def test_report_bytes_remain_immutable_even_if_index_hash_is_rewritten(self):
        name = self.index['reviews'][4]['report']
        for rewrite_index in [False, True]:
            report = checker.read_json(checker.ROOT, name)
            report['objections'] = []
            self.write(name, report)
            index = deepcopy(self.index)
            if rewrite_index:
                index['reviews'][4]['report_sha256'] = hashlib.sha256((self.root / name).read_bytes()).hexdigest()
            self.write(checker.INDEX, index)
            with self.subTest(rewrite_index=rewrite_index):
                self.reject()

    def test_missing_report_manifest_and_external_symlink_are_rejected(self):
        path = self.root / self.index['reviews'][0]['report']
        raw = path.read_bytes()
        path.unlink()
        self.reject()
        with tempfile.TemporaryDirectory() as outside:
            target = Path(outside) / 'report.json'
            target.write_bytes(raw)
            path.symlink_to(target)
            self.reject()
        path.unlink()
        path.write_bytes(raw)
        (self.root / checker.MANIFEST).unlink()
        self.reject()

    def test_manifest_uses_canonical_digest_not_incidental_json_whitespace(self):
        self.write(checker.MANIFEST, self.manifest)
        result = checker.validate(self.root)
        self.assertEqual(result['input_root_sha256'], checker.INPUT_ROOT)
        self.assertEqual(hashlib.sha256(checker.canonical(self.manifest)).hexdigest(), checker.INPUT_ROOT)

    def test_manifest_mutation_cannot_be_rebound_to_a_new_root(self):
        for mutation in ['missing', 'extra', 'duplicate', 'reorder', 'hash', 'uppercase-hash',
                         'absolute-path', 'dotdot-path', 'alias-path', 'backslash-path', 'commit', 'extra-field']:
            manifest = deepcopy(self.manifest)
            files = manifest['files']
            if mutation == 'missing':
                files.pop()
            elif mutation == 'extra':
                files.append({'path': 'z-extra', 'sha256': '0' * 64})
            elif mutation == 'duplicate':
                files[1] = deepcopy(files[0])
            elif mutation == 'reorder':
                files[0], files[1] = files[1], files[0]
            elif mutation == 'commit':
                manifest['candidate_commit'] = '0' * 40
            elif mutation == 'extra-field':
                manifest['final_state'] = 'VERIFIED'
            elif mutation == 'hash':
                files[0]['sha256'] = '0' * 64
            elif mutation == 'uppercase-hash':
                files[0]['sha256'] = files[0]['sha256'].upper()
            else:
                files[0]['path'] = {'absolute-path': '/tmp/file', 'dotdot-path': '../file',
                                    'alias-path': 'a//file', 'backslash-path': 'a\\file'}[mutation]
            self.write(checker.MANIFEST, manifest)
            index = deepcopy(self.index)
            index['input_root_sha256'] = hashlib.sha256(checker.canonical(manifest)).hexdigest()
            self.write(checker.INDEX, index)
            with self.subTest(mutation=mutation):
                self.reject()

    def test_inventory_denominator_cannot_be_inflated_or_replaced(self):
        path = checker.TARGET['inventory']
        for mutation in ['version', 'commit', 'productions', 'families']:
            inventory = checker.read_json(checker.ROOT, path)
            if mutation in ['version', 'commit']:
                inventory['upstream'][mutation] = 'changed'
            else:
                inventory['counts']['source_productions' if mutation == 'productions' else 'statement_families'] += 1
            self.write(path, inventory)
            with self.subTest(mutation=mutation):
                self.reject()

    def test_retained_report_binding_and_constructed_witness_schema(self):
        name = self.index['reviews'][4]['report']
        report = checker.read_json(checker.ROOT, name)
        files = {item['path']: item['sha256'] for item in self.manifest['files']}
        for mutation in ['commit', 'candidate_commit', 'cli_sha256', 'model', 'reviewer', 'attempts',
                         'claimed_surface', 'objections', 'objection-line', 'objection-locus',
                         'objection-sql', 'objection-expected', 'objection-evidence']:
            value = deepcopy(report)
            if mutation == 'objections':
                value['objections'] = []
            elif mutation.startswith('objection-'):
                item = value['objections'][0]
                key = mutation[len('objection-'):]
                if key == 'sql':
                    item['reproducer'].pop('sql')
                else:
                    field, replacement = {'line': ('line', True), 'locus': ('file', 'missing.lean'),
                                          'expected': ('expected', {}), 'evidence': ('evidence_paths', [])}[key]
                    item[field] = replacement
            elif mutation in ('attempts', 'reviewer', 'claimed_surface'):
                value[mutation] = []
            else:
                value[mutation] = 'changed'
            with self.subTest(mutation=mutation), self.assertRaises(checker.RecordError):
                checker.check_report(value, 'astra1', 'gpt-6-astra', ['ASTRA1-001'], files)

    def test_duplicate_json_and_nonfinite_numbers_are_rejected(self):
        for raw in ['{"release_approval":false,"release_approval":true}', '{"x":NaN}', '{"x":Infinity}']:
            with self.subTest(raw=raw), self.assertRaises(checker.RecordError):
                checker.parse_json(raw)

    def test_document_must_preserve_required_policy_and_historical_boundaries(self):
        original = (checker.ROOT / checker.DOCUMENT).read_text()
        for old, new in [('GPT-6.1 Sol', 'GPT-6 Sol'), ('3,284', '3,285'),
                         ('ASTRA1-001', 'CLOSED-001'), ('cannot authorize publication', 'authorizes publication'),
                         ('not a completed mechanical-closure report', 'a completed mechanical-closure report'),
                         (checker.BASELINE, '0' * 40)]:
            (self.root / checker.DOCUMENT).write_text(original.replace(old, new))
            with self.subTest(old=old):
                self.reject()

    def test_cli_success_and_failure_never_emit_release_verified(self):
        output = io.StringIO()
        with redirect_stdout(output):
            code = checker.main(['--root', str(self.root)])
        self.assertEqual(code, 0)
        result = json.loads(output.getvalue())
        self.assertEqual(result['result'], 'consistent')
        self.assertIs(result['release_readiness_evaluated'], False)
        (self.root / checker.INDEX).write_text('invalid json')
        output = io.StringIO()
        with redirect_stdout(output):
            code = checker.main(['--root', str(self.root)])
        self.assertEqual(code, 1)
        result = json.loads(output.getvalue())
        self.assertEqual(result['result'], 'inconsistent')
        self.assertIs(result['release_approval'], False)
        self.assertNotIn('VERIFIED', output.getvalue())

    def test_optimized_python_cannot_disable_gate_rejection(self):
        plan = deepcopy(self.plan)
        plan['initial_preflight']['release_approval'] = True
        self.write(checker.PLAN, plan)
        result = subprocess.run(['/usr/bin/python3', '-O', str(checker.ROOT / 'scripts/check_review_ladder.py'),
                                 '--root', str(self.root)], capture_output=True, text=True, check=False)
        self.assertEqual(result.returncode, 1)
        self.assertEqual(json.loads(result.stdout)['result'], 'inconsistent')
        self.assertIs(json.loads(result.stdout)['release_approval'], False)


if __name__ == '__main__':
    unittest.main()
