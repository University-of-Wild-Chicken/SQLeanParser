#!/usr/bin/env python3
"""Check the release-gate design record and immutable failed preflight archive.

This is not a mechanical-closure runner or a release-readiness certificate.
Success means that the design policy and historical evidence bindings agree.
No future closure assertion, approval field, or repaired input root is accepted
by this version. A future release needs its own complete closure verifier.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
PLAN = 'release/0.0.1-alpha/plan.json'
DOCUMENT = 'docs/releases/review-closure-ladder.md'
ARCHIVE = 'docs/reviews/21cd72b'
INDEX = ARCHIVE + '/index.json'
MANIFEST = ARCHIVE + '/input-manifest.json'
BASELINE = '21cd72b60b9b42825ac568ad5f3cb4f47db153c3'
INPUT_ROOT = '847d1e0f5d749066bb976c296d38be3082183ddd7a5ccc82f3ba4f87bf51a7f4'
BASELINE_CLI = '2c00c6692f3acf23d027849b18d8efc3036f033339e5a87dfd6e165a7d60824a'
PG_COMMIT = 'f0595c3d839debdb140903621c1b44a4f4d86256'
REPORTS = (
    ('luna1', 1, 'gpt-6-luna', 'd51d618fc9e47e79f502c9c86de71b913cfbaf40c3e0c042deedaeb4bfbb6c46', ()),
    ('luna2', 1, 'gpt-6-luna', 'b1a8cf42c21623f0cc735299143b307a64967f2f167957b0dd0b797af1510e41', ()),
    ('sol1', 2, 'gpt-6.1-sol', 'ef82877071ad7b33237e3bd07554eaf7034c8e6dae2cdf7789161de0e52d3c4c', ()),
    ('sol2', 2, 'gpt-6.1-sol', '854709309291f5c6a26946b15e20c19ece282fec73388b910e5f2c265eaef068', ()),
    ('astra1', 3, 'gpt-6-astra', 'e1d8f24380e3e0b53c0615bbe4ccb32155696b1468608b5954654c052b21c640', ('ASTRA1-001',)),
    ('astra2', 3, 'gpt-6-astra', '5ecae5a2a461fd7597a916096784a2b9bf166d396109ae8bd28bde75dc187523', ('ASTRA2-001',)),
)
LADDER = [{'level': level, 'model': model, 'independent_reviewers': 2}
          for level, model in [(1, 'gpt-6-luna'), (2, 'gpt-6.1-sol'), (3, 'gpt-6-astra')]]
BLOCKERS = ['ASTRA1-001', 'ASTRA2-001']
TARGET = {
    'postgresql_version': '16.15', 'postgresql_commit': PG_COMMIT,
    'inventory': 'fixtures/postgresql_grammar/inventory.json',
    'source_productions': 3284, 'outer_statement_families': 125,
    'full_independent_validity_required': True, 'full_renderer_contract_required': True,
    'grammar_recognition_is_not_typed_validity': True,
}
REVIEW_POLICY = dict.fromkeys((
    'same_frozen_candidate_per_level', 'both_reviews_required_before_escalation',
    'constructed_objections_block_escalation', 'retain_original_failure_evidence',
    'independent_registered_regression_required', 'independent_repair_recheck_required',
    'missing_or_unavailable_review_blocks', 'input_mutation_invalidates_release_evidence',
    'llm_opinion_is_not_claim_discharge'), True) | {'manual_override_allowed': False}
CLOSURE_REQUIREMENTS = dict.fromkeys((
    'frozen_finite_claims', 'canonical_input_manifest', 'registered_hashed_verifiers',
    'explicit_trusted_computing_base', 'unique_implementation_proof_correspondence',
    'checked_concrete_witnesses', 'determinism_required', 'public_claim_provenance_required',
    'unresolved_is_blocking', 'warning_affecting_required_claim_is_blocking'), True) | {
        'required_isolated_clean_builds': 2, 'final_required_state': 'VERIFIED'}
EXAMPLE_POLICY = {
    'synthetic_per_syntactic_factor': 50, 'unchanged_authentic_per_syntactic_factor': 50,
    'retain_exact_input_and_immutable_source_provenance': True,
    'do_not_execute_downloaded_sql_or_setup': True,
    'do_not_pad_shortages_with_transformed_or_synthetic_sources': True,
    'source_origin_does_not_supply_catalog_or_validity': True,
}


class RecordError(ValueError):
    """An absent, malformed, weakened or inconsistent design record."""


def require(condition, message):
    # Do not use assert: python -O must not turn a gate failure into success.
    if not condition:
        raise RecordError(message)


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()


def equal(actual, expected, context):
    require(canonical(actual) == canonical(expected), context + ': unexpected value or schema')


def unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON key: ' + key)
        result[key] = value
    return result


def invalid_constant(value):
    raise RecordError('non-finite JSON number: ' + value)


def parse_json(raw):
    return json.loads(raw, object_pairs_hook=unique_pairs, parse_constant=invalid_constant)


def relative_path(path):
    require(isinstance(path, str) and bool(path), 'empty or non-string archive path')
    value = PurePosixPath(path)
    require(not value.is_absolute() and str(value) == path and '\\' not in path and
            all(part not in ('.', '..') for part in value.parts), 'unsafe/noncanonical path: ' + path)
    return path


def read_bytes(root, name):
    path = root / relative_path(name)
    require(root.resolve() in path.resolve().parents, 'archive path escapes root: ' + name)
    require(path.is_file(), 'required file missing: ' + name)
    return path.read_bytes()


def read_json(root, name):
    return parse_json(read_bytes(root, name))


def keys(value, expected, context):
    require(isinstance(value, dict) and set(value) == set(expected), context + ': missing or extra fields')


def no_approval(value, context):
    if isinstance(value, dict):
        if 'release_approval' in value:
            require(value['release_approval'] is False, context + ': design/historical record cannot authorize release')
        for key, child in value.items():
            no_approval(child, context + '.' + key)
    elif isinstance(value, list):
        for index, child in enumerate(value):
            no_approval(child, f'{context}[{index}]')


def check_plan(plan):
    keys(plan, ('schema_version', 'mode', 'release', 'target', 'ladder', 'review_policy',
                'closure_requirements', 'example_policy', 'initial_preflight'), 'plan')
    equal({k: plan[k] for k in ('schema_version', 'mode', 'release')},
          {'schema_version': '1.0', 'mode': 'design', 'release': '0.0.1-alpha'}, 'design identity')
    for key, wanted in [('target', TARGET), ('ladder', LADDER), ('review_policy', REVIEW_POLICY),
                        ('closure_requirements', CLOSURE_REQUIREMENTS), ('example_policy', EXAMPLE_POLICY)]:
        equal(plan[key], wanted, 'plan.' + key)
    equal(plan['initial_preflight'], {
        'candidate_commit': BASELINE,
        'scope': 'bounded v0.33 admitted contract surface, not full PostgreSQL or release approval',
        'completed_reviewers_by_level': [2, 2, 2], 'constructed_blockers': BLOCKERS,
        'release_approval': False}, 'plan.initial_preflight')


def check_manifest(manifest, index):
    keys(manifest, ('schema_version', 'candidate_commit', 'files'), 'manifest')
    equal(manifest['schema_version'], '1.0', 'manifest version')
    equal(manifest['candidate_commit'], BASELINE, 'manifest baseline')
    require(isinstance(manifest['files'], list) and len(manifest['files']) == 1483,
            'historical input inventory must contain exactly 1483 entries')
    paths = []
    for item in manifest['files']:
        keys(item, ('path', 'sha256'), 'manifest entry')
        paths.append(relative_path(item['path']))
        require(isinstance(item['sha256'], str) and re.fullmatch('[0-9a-f]{64}', item['sha256']),
                'invalid input SHA256: ' + item['path'])
    require(paths == sorted(set(paths)), 'manifest paths must be unique and sorted')
    digest = hashlib.sha256(canonical(manifest)).hexdigest()
    equal(digest, INPUT_ROOT, 'immutable historical input root')
    equal(index['input_root_sha256'], digest, 'index input root binding')
    return {item['path']: item['sha256'] for item in manifest['files']}


def check_inventory(root, files):
    raw = read_bytes(root, TARGET['inventory'])
    equal(hashlib.sha256(raw).hexdigest(), files[TARGET['inventory']], 'pinned grammar inventory bytes')
    inventory = parse_json(raw)
    equal(inventory['upstream']['version'], TARGET['postgresql_version'], 'inventory PostgreSQL version')
    equal(inventory['upstream']['commit'], PG_COMMIT, 'inventory PostgreSQL commit')
    equal(inventory['counts']['source_productions'], 3284, 'production denominator')
    equal(inventory['counts']['statement_families'], 125, 'statement-family denominator')
    require(len(inventory['statement_families']) == 125, 'statement-family population changed')


def check_report(report, name, model, blocker_ids, files):
    require(isinstance(report, dict), name + ': report must be an object')
    no_approval(report, name)
    bindings = [report[key] for key in ('candidate_commit', 'commit') if key in report]
    require(bindings and all(value == BASELINE for value in bindings), name + ': missing/stale candidate binding')
    model_name = report.get('model', report.get('requested_model_identity'))
    aliases = {'gpt-6-luna': ('gpt-6-luna', 'GPT-6 Luna'),
               'gpt-6.1-sol': ('gpt-6.1-sol', 'GPT-6.1 Sol'),
               'gpt-6-astra': ('gpt-6-astra', 'GPT-6 Astra')}
    require(model_name in aliases[model], name + ': wrong requested model')
    require(isinstance(report.get('reviewer'), str) and report['reviewer'].strip(), name + ': missing reviewer')
    require(bool(report.get('claimed_surface')), name + ': missing bounded claimed surface')
    attempts = report.get('attempts', report.get('actual_attempts', report.get('actual_adversarial_attempts')))
    if attempts is None and isinstance(report.get('nonblocking_notes'), dict):
        attempts = report['nonblocking_notes'].get('attempts')
    require(isinstance(attempts, list) and bool(attempts), name + ': missing completed review attempts')
    for key in ('cli_sha256', 'binary_sha256'):
        if key in report:
            equal(report[key], BASELINE_CLI, name + ': recorded CLI identity')
    if name == 'luna2':
        binary = [item for item in attempts if item.get('id') == 'binary-identity']
        require(len(binary) == 1 and binary[0].get('result', '').startswith(BASELINE_CLI + ','),
                'luna2: missing recorded binary identity')
    objections = report.get('objections')
    require(isinstance(objections, list), name + ': missing objection list')
    equal([item.get('id') for item in objections], list(blocker_ids), name + ': historical blockers changed')
    for objection in objections:
        required = ('id', 'severity', 'file', 'line', 'claim', 'reproducer', 'expected', 'actual', 'evidence_paths')
        require(all(key in objection and bool(objection[key]) for key in required), name + ': incomplete constructed objection')
        require(type(objection['line']) is int and objection['line'] > 0, name + ': invalid code location')
        require(relative_path(objection['file']) in files, name + ': code locus outside frozen inventory')
        require(isinstance(objection['reproducer'], dict) and bool(objection['reproducer'].get('sql')),
                name + ': missing constructed SQL')
        require(isinstance(objection['evidence_paths'], list) and bool(objection['evidence_paths']),
                name + ': missing raw evidence references')


def check_document(document):
    text = ' '.join(document.split())
    required = [
        '1. Two independent **GPT-6 Luna** reviewers. 2. Two independent **GPT-6.1 Sol** reviewers. '
        '3. Two independent **GPT-6 Astra** reviewers.',
        'Both reviewers at a level inspect the same frozen candidate.',
        'A concrete constructed objection stops advancement:',
        'An unavailable or incomplete review does not count as a clean result.',
        'Their opinions are not proofs or final verifiers.',
        'There is no manual override or conversion of an unresolved result into a pass.',
        'earlier review or proof results are not inherited by a new release candidate.',
        '3,284 upstream productions and 125 outer statement families',
        BASELINE, PG_COMMIT, '**ASTRA1-001:**', '**ASTRA2-001:**',
        'this baseline remains a recorded failed candidate and cannot authorize publication.',
        'It is a design record, not a completed mechanical-closure report or permission to publish.',
        '../../release/0.0.1-alpha/plan.json',
    ]
    for fragment in required:
        require(fragment in text, 'missing required documentation boundary: ' + fragment)


def validate(root=ROOT):
    root = Path(root)
    plan, index = read_json(root, PLAN), read_json(root, INDEX)
    no_approval(plan, 'plan')
    no_approval(index, 'index')
    check_plan(plan)
    keys(index, ('schema_version', 'mode', 'candidate_commit', 'input_root_sha256', 'input_manifest',
                 'model_identity_trust', 'reviews', 'review_result', 'release_approval', 'limitations'), 'index')
    for key, wanted in {'schema_version': '1.0', 'mode': 'bounded-development-preflight',
                        'candidate_commit': BASELINE, 'input_manifest': MANIFEST,
                        'review_result': 'CONSTRUCTED_BLOCKERS', 'release_approval': False}.items():
        equal(index[key], wanted, 'index.' + key)
    equal(index['model_identity_trust'],
          'Requested routing through the collaboration tool; not an independent model-weights attestation.',
          'model identity trust boundary')
    equal(index['limitations'], [
        'Not a full PostgreSQL release candidate.', 'LLM findings are candidate issues, not proof discharge.',
        'Historical experiment paths may be temporary; registered regression fixtures preserve the objections.',
        'Release requires fresh reviews and complete bound mechanical closure.'], 'historical limitations')
    files = check_manifest(read_json(root, MANIFEST), index)
    check_inventory(root, files)
    reviews = index['reviews']
    require(isinstance(reviews, list) and len(reviews) == 6, 'all six ordered reports are required')
    blockers = []
    for entry, (name, level, model, digest, ids) in zip(reviews, REPORTS):
        report_path = ARCHIVE + '/' + name + '.json'
        equal(entry, {'level': level, 'requested_model': model, 'reviewer': name,
                      'report': report_path, 'report_sha256': digest, 'constructed_objections': list(ids)},
              name + ': ordered archive binding')
        raw = read_bytes(root, report_path)
        equal(hashlib.sha256(raw).hexdigest(), digest, name + ': immutable raw report SHA256')
        check_report(parse_json(raw), name, model, ids, files)
        blockers.extend(ids)
    equal(blockers, plan['initial_preflight']['constructed_blockers'], 'plan/archive blocker reconciliation')
    equal([Counter(entry['level'] for entry in reviews)[level] for level in (1, 2, 3)],
          plan['initial_preflight']['completed_reviewers_by_level'], 'completed review counts')
    # Earlier stages must have no constructed blocker before the next stage is
    # represented as complete. The final stage is intentionally failed here.
    require(not any(entry['constructed_objections'] for entry in reviews if entry['level'] < 3),
            'escalation past an unresolved earlier-level objection')
    check_document(read_bytes(root, DOCUMENT).decode('utf-8'))
    return {
        'check': 'review-ladder-design-record', 'result': 'consistent',
        'release_readiness_evaluated': False, 'release_approval': False,
        'candidate_commit': BASELINE, 'input_root_sha256': INPUT_ROOT,
        'historical_input_files': len(files), 'archived_reports': len(reviews),
        'historical_review_result': 'CONSTRUCTED_BLOCKERS', 'constructed_blockers': blockers,
        'scope': 'Design policy and immutable historical archive consistency only; no closure state is produced.',
        'limitations': [
            'The historical manifest is bound to its pinned root; the repaired working tree is not that candidate.',
            'Requested model routing is not independent model-weights attestation.',
            'Luna1 records the candidate commit without a CLI hash; five other reports record the baseline CLI hash.',
            'Historical experiment paths are not replayed; archived review opinions do not discharge claims.',
            'Required prose boundary statements are checked, not general natural-language semantic equivalence.',
            'No final closure package is validated; this design-only schema rejects release approval.'],
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT, help='repository root containing the design/archive records')
    args = parser.parse_args(argv)
    try:
        result = validate(args.root)
    except (RecordError, OSError, ValueError, KeyError, TypeError, UnicodeError) as error:
        print(json.dumps({'check': 'review-ladder-design-record', 'result': 'inconsistent',
                          'release_readiness_evaluated': False, 'release_approval': False,
                          'error': str(error)}, sort_keys=True))
        return 1
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == '__main__':
    sys.exit(main())
