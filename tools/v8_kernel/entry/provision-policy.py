#!/usr/bin/env python3
"""Author-only policy capture for the version-8 entry, revision 6. Without an entry review it reports ReviewPending.

Revision 6 pins every source relative to the installation root and carries the
reviews as pin data, so an installation reads no receipt. The endpoint review of
the version-8 gate is recorded by its hash and bindings. With --entry-review,
the entry review receipt is read here, once: it must have passed and name this
entry's source pins and the policy without the review slot, and its hash, status
and named sources become the policy's entry_review. Machine-specific values
(HOME, toolchain, Python, project, helper objects, trees) are not in the policy;
the installer writes them to installation.json.
"""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
ENTRY = 'tools/v8_kernel/entry'
GENERATOR = 'tools/v8_kernel/generator'
DIRECTORY = 'tools/v8_kernel/recipe/equality'
MIXED = 'tools/v8_kernel/recipe/mixed'
GATE_PIN = 'e8dbfe675733e2b708870349e4eed81d2ef5dea2f02f3c97b2a3a2214d75a5ea'
LINK_PIN = 'c0f18bbe3457610f7972c49cd2b6ede5270727fa844c3d2b174bd748b94dac0c'
REVIEW = {
    'sha256': '9454d117e63f255ad0ce3a461f3aa920c23e30cf185b0fd2dbb664540f2db438',
    'bindings': {'pins.link_v2': LINK_PIN, 'pins.proof': GATE_PIN},
    'provenance': 'evidence/verification/tptp-expanded-certificate-independent-review-v2-20261024/manifest.json',
}
ENTRY_SOURCES = ('main.py', 'invoke.py', 'check.py', 'trees.py', 'origin.json', 'provision-policy.py')


def digest(data):
    return hashlib.sha256(data).hexdigest()


def encode(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--entry-review', help='Review receipt manifest, relative to the repository root')
    parser.add_argument('--entry-review-sha256')
    args = parser.parse_args()
    if bool(args.entry_review) != bool(args.entry_review_sha256):
        parser.error('Give the review receipt path and its SHA-256 together')
    mapping = json.loads((ROOT / MIXED / 'sources.json').read_bytes())
    paths = [DIRECTORY + '/' + name for name in ('generate-cnf.py', 'generate-quantified.py', 'generate-certificate.py')]
    paths += [GENERATOR + '/generate-v8.py']
    paths += [ENTRY + '/' + name for name in ENTRY_SOURCES]
    paths += [MIXED + '/' + name for name in ['sources.json', *mapping['emitters']]]
    paths += ['tools/fang_szs/supervisor.py', 'tools/fang_szs/__init__.py', 'tools/replay/axiom_audit.py']
    pins = {path: digest((ROOT / path).read_bytes()) for path in paths}
    for name, expected in mapping['emitters'].items():
        assert pins[MIXED + '/' + name] == expected
    value = {'schema': 'fang-v8-equality-kernel-entry-policy-v2', 'files': pins,
             'entry_directory': ENTRY, 'generator_directory': GENERATOR,
             'batch_sha256': LINK_PIN, 'independent_review': REVIEW, 'entry_review': None,
             'inventory': {'runner': ENTRY + '/trees.py'},
             'provenance': {'gate_manifest_sha256': GATE_PIN, 'link_sha256': LINK_PIN,
                            'note': 'Receipts named here are provenance; the installation reads none of them.'}}
    unprovisioned = digest(encode(value))
    if args.entry_review:
        receipt = (ROOT / args.entry_review).read_bytes()
        reviewed = json.loads(receipt)
        own = {name: pins[ENTRY + '/' + name] for name in ENTRY_SOURCES}
        own['policy.json'] = unprovisioned
        assert digest(receipt) == args.entry_review_sha256 and reviewed['status'] == 'passed'
        assert reviewed['inputs']['entry_sources_sha256'] == own, 'Entry review does not name these sources'
        value['entry_review'] = {'sha256': args.entry_review_sha256, 'status': 'passed', 'entry_sources_sha256': own,
                                 'provenance': args.entry_review}
    data = encode(value)
    (HERE / 'policy.json').write_bytes(data)
    print(json.dumps({'status': 'review-pending' if value['entry_review'] is None else 'provisioned',
                      'files': len(pins), 'policy_sha256': digest(data), 'unprovisioned_policy_sha256': unprovisioned}))


if __name__ == '__main__':
    main()
