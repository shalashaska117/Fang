#!/usr/bin/env python3
"""Install the version-8 kernel entry, revision 6, into a fresh installation root.

Inputs: a lean-v8 project built by tools/build-v8-lean.py, the helper build
written by build-helpers.py against that project, the pinned toolchain and the
Python interpreter. Every file the entry policy pins is copied from the
repository to the same relative path under the root and checked against its
pin. The helper build must have been made by this build-helpers.py with these
helper and closure pins, and the project's source of every module in the
kernel's lean-v8 import closure must still match pins/lean-v8-closure.json; the
install stops otherwise. The installer then records the tree manifests
(toolchain, every directory on the recorded LEAN_PATH, the helper objects) and
writes installation.json next to the entry: the root, the output root, HOME,
Python, the toolchain, the project, the helper objects and closure pins, the
recorded Lean environment and the tree record. No receipt is read.
"""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys
import types

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
POLICY = HERE / 'entry/policy.json'
CLOSURE = HERE / 'pins/lean-v8-closure.json'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def encode(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', required=True, type=Path)
    parser.add_argument('--project', required=True, type=Path)
    parser.add_argument('--lean-build', required=True, type=Path, help='the tools/build-v8-lean.py output directory')
    parser.add_argument('--helpers', required=True, type=Path, help='the build-helpers.py output directory')
    parser.add_argument('--lean-toolchain', required=True, type=Path)
    parser.add_argument('--output-root', type=Path, help='fresh directory for kernel runs; default <root>/run')
    args = parser.parse_args()
    root = args.root.resolve()
    root.mkdir(parents=True, exist_ok=False)
    project, toolchain = args.project.resolve(), args.lean_toolchain.resolve()
    policy_data = POLICY.read_bytes()
    policy = json.loads(policy_data)
    if policy['schema'] != 'fang-v8-equality-kernel-entry-policy-v2':
        raise SystemExit('Unknown entry policy')
    for relative, pin in policy['files'].items():
        data = (ROOT / relative).read_bytes()
        if digest(data) != pin:
            raise SystemExit('Repository file differs from the entry policy: ' + relative)
        target = root / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    entry = root / policy['entry_directory']
    (entry / 'policy.json').write_bytes(policy_data)
    lean_build_data = (args.lean_build / 'manifest.json').read_bytes()
    lean_build = json.loads(lean_build_data)
    if lean_build['status'] != 'built-and-audited' or Path(lean_build['toolchain']['path']).resolve() != toolchain:
        raise SystemExit('The lean-v8 build did not pass with this toolchain')
    helpers_data = (args.helpers / 'manifest.json').read_bytes()
    helpers = json.loads(helpers_data)
    if helpers['status'] != 'built-and-audited' or Path(helpers['project']) != project or Path(helpers['toolchain']) != toolchain:
        raise SystemExit('The helper build did not pass against this project and toolchain')
    if helpers.get('schema') != 'fang-v8-kernel-helpers-build-v2':
        raise SystemExit('Unknown helper build record')
    for key, path in (('runner_sha256', HERE / 'build-helpers.py'), ('pins_sha256', HERE / 'pins/helper-sources.json'),
                      ('closure_sha256', CLOSURE)):
        if helpers.get(key) != digest(path.read_bytes()):
            raise SystemExit('The helper build used another ' + path.relative_to(HERE).as_posix())
    closure_data = CLOSURE.read_bytes()
    closure = json.loads(closure_data)
    differing = [name for name, pin in sorted(closure['sources_sha256'].items())
                 if not (project / (name.replace('.', '/') + '.lean')).is_file()
                 or digest((project / (name.replace('.', '/') + '.lean')).read_bytes()) != pin]
    if differing:
        raise SystemExit('lean-v8 differs from the kernel import closure: ' + ', '.join(differing[:10]))
    helper_directory = (args.helpers / 'source').resolve()
    for relative, pin in helpers['objects_sha256'].items():
        if digest((helper_directory / relative).read_bytes()) != pin:
            raise SystemExit('Helper object differs from its build record: ' + relative)
    environment = helpers['lean_environment']
    trees = {'toolchain': str(toolchain), 'helpers': str(helper_directory)}
    for index, item in enumerate(part for part in environment['LEAN_PATH'].split(':') if part):
        if Path(item).is_dir():
            trees['lean_path_%02d' % index] = item
    collector_path = entry / 'trees.py'
    collector = types.ModuleType('installed_trees')
    collector.__file__ = str(collector_path)
    exec(compile(collector_path.read_bytes(), str(collector_path), 'exec'), collector.__dict__)
    recorded = {}
    for name, directory in sorted(trees.items()):
        files = collector.tree(directory)
        recorded[name] = {'directory': directory, 'files': len(files), 'sha256': collector.summary(files), 'files_sha256': files}
    trees_data = encode(recorded)
    (entry / 'trees.json').write_bytes(trees_data)
    output_root = (args.output_root or root / 'run').resolve()
    output_root.mkdir(parents=True, exist_ok=False)
    (root / 'home').mkdir()
    python = Path(sys.executable).resolve()
    record = {'schema': 'fang-v8-kernel-installation-v2', 'installed_utc': datetime.now(timezone.utc).isoformat(),
              'root': str(root), 'output_root': str(output_root), 'home': str(root / 'home'),
              'python': {'path': str(python), 'sha256': digest(python.read_bytes())},
              'toolchain': {'directory': str(toolchain), 'lean_sha256': digest((toolchain / 'bin/lean').read_bytes()),
                            'lake_sha256': digest((toolchain / 'bin/lake').read_bytes())},
              'project': {'directory': str(project), 'build_manifest_sha256': digest(lean_build_data),
                          'source_map_sha256': lean_build.get('source_map_sha256')},
              'helpers': {'directory': str(helper_directory), 'objects_sha256': helpers['objects_sha256'],
                          'build_manifest_sha256': digest(helpers_data), 'audits': helpers['audits'],
                          'runner_sha256': helpers['runner_sha256'], 'pins_sha256': helpers['pins_sha256']},
              'closure': {'sha256': digest(closure_data), 'sources_checked': len(closure['sources_sha256'])},
              'lean_environment': environment,
              'trees': {'path': str(entry / 'trees.json'), 'sha256': digest(trees_data),
                        'summary': {name: [item['files'], item['sha256']] for name, item in recorded.items()}},
              'policy_sha256': digest(policy_data), 'installer_sha256': digest(Path(__file__).read_bytes())}
    data = encode(record)
    (entry / 'installation.json').write_bytes(data)
    print(json.dumps({'root': str(root), 'installation_sha256': digest(data), 'policy_sha256': digest(policy_data),
                      'trees': record['trees']['summary']}))


if __name__ == '__main__':
    main()
