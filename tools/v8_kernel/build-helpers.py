#!/usr/bin/env python3
"""Provide the 43 kernel helper modules on a built lean-v8 project: compile those it lacks and rerun their audits.

Inputs: a lean-v8 Lake project built by tools/build-v8-lean.py and the pinned
Lean toolchain. The helper sources come from tools/v8_kernel/lean/ (or
--sources); every one must match its pin in pins/helper-sources.json. The
project's source of every module in the kernel's lean-v8 import closure must
match pins/lean-v8-closure.json, or the build stops. The Lean environment is
taken once from `lake env` in the project; every search path must lie inside
the project or the toolchain. Of the helper modules, only those pinned as
provided by lean-v8 may already be on that search path: they are not compiled
again, their lean-v8 sources must be byte-identical to the pinned helper
sources, and the lean-v8 objects are used. Every other module is compiled with
the direct compiler launch under a 60-second/4-GiB guard, in the pinned order,
and its axiom report must equal its pin. The output directory receives the
sources, the objects, the logs and a manifest with every object hash.
"""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from fang_szs.supervisor import Limits, Supervisor  # noqa: E402

PINS = HERE / 'pins/helper-sources.json'
CLOSURE = HERE / 'pins/lean-v8-closure.json'
LAUNCH = ('import json,os,sys; os.chdir(sys.argv[1]); '
          'os.execve(sys.argv[3], sys.argv[3:], dict(os.environ, **json.loads(sys.argv[2])))')
SEARCH = ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LD_LIBRARY_PATH')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
REPORT = re.compile(r"'([^'\n]+)'\s+(?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])")


def digest(data):
    return hashlib.sha256(data).hexdigest()


def lake_environment(toolchain, project, home):
    """The search variables `lake env` sets in the built project; nothing is built."""
    environment = {'HOME': str(home), 'PATH': str(toolchain / 'bin') + ':/usr/bin:/bin', 'LANG': 'C.UTF-8',
                   'LC_ALL': 'C.UTF-8', 'GIT_ALLOW_PROTOCOL': 'file'}
    result = subprocess.run([str(toolchain / 'bin/lake'), '-d', str(project), 'env', '/usr/bin/env'], capture_output=True,
                            timeout=300, env=environment, cwd=str(project))
    if result.returncode != 0:
        raise ValueError('lake env failed: ' + result.stderr.decode('utf-8', 'replace')[-800:])
    values = dict(line.split('=', 1) for line in result.stdout.decode('utf-8').splitlines() if '=' in line)
    return {key: values.get(key, '') for key in SEARCH}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project', required=True, type=Path)
    parser.add_argument('--lean-toolchain', required=True, type=Path)
    parser.add_argument('--sources', type=Path, default=HERE / 'lean')
    parser.add_argument('--out', required=True, type=Path)
    args = parser.parse_args()
    project, toolchain = args.project.resolve(), args.lean_toolchain.resolve()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    source = out / 'source'
    source.mkdir()
    (out / 'stages').mkdir()
    (out / 'home').mkdir()
    pins = json.loads(PINS.read_bytes())
    report = {'schema': 'fang-v8-kernel-helpers-build-v2', 'status': 'running', 'started_utc': datetime.now(timezone.utc).isoformat(),
              'runner_sha256': digest(Path(__file__).read_bytes()), 'pins_sha256': digest(PINS.read_bytes()),
              'closure_sha256': digest(CLOSURE.read_bytes()),
              'project': str(project), 'toolchain': str(toolchain),
              'toolchain_sha256': {name: digest((toolchain / 'bin' / name).read_bytes()) for name in ('lean', 'lake')},
              'scope': 'The 43 kernel helper modules compiled against a built lean-v8 project; audits rerun and compared.',
              'modules': {}}

    def save():
        (out / 'manifest.json').write_bytes((json.dumps(report, indent=2, sort_keys=True) + '\n').encode())

    try:
        closure = json.loads(CLOSURE.read_bytes())
        differing = [name for name, pin in sorted(closure['sources_sha256'].items())
                     if not (project / (name.replace('.', '/') + '.lean')).is_file()
                     or digest((project / (name.replace('.', '/') + '.lean')).read_bytes()) != pin]
        if differing:
            raise ValueError('lean-v8 differs from the kernel import closure: ' + ', '.join(differing[:10]))
        report['closure_modules_checked'] = len(closure['sources_sha256'])
        for name in pins['module_order']:
            if name in pins['provided_by_lean_v8']:
                continue
            relative = name.replace('.', '/') + '.lean'
            data = (args.sources / relative).read_bytes()
            if digest(data) != pins['sources_sha256'][name]:
                raise ValueError('Helper source differs from its pin: ' + name)
            target = source / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        environment = lake_environment(toolchain, project, out / 'home')
        report['lean_environment'] = environment
        roots = (project, toolchain)
        for key in SEARCH:
            for item in environment[key].split(':'):
                if item and not any(Path(item).resolve().is_relative_to(root) for root in roots):
                    raise ValueError('Search path outside the project and toolchain: ' + item)
        if Path(environment['LEAN_SYSROOT']).resolve() != toolchain:
            raise ValueError('Lean sysroot differs from the toolchain')
        existing = set()
        for item in environment['LEAN_PATH'].split(':'):
            if item and Path(item).is_dir():
                existing.update(path.relative_to(item).with_suffix('').as_posix().replace('/', '.')
                                for path in Path(item).rglob('*.olean'))
        provided = sorted(set(pins['module_order']) & existing)
        if provided != sorted(pins['provided_by_lean_v8']):
            raise ValueError('lean-v8 provides other helper modules than pinned: ' + ', '.join(provided))
        for name in provided:
            shipped = project / (name.replace('.', '/') + '.lean')
            if not shipped.is_file() or digest(shipped.read_bytes()) != pins['sources_sha256'][name]:
                raise ValueError('Helper name on the search path with a different source: ' + name)
            if pins['axiom_audits'].get(name):
                raise ValueError('A provided helper has recorded audits; compile it here instead: ' + name)
        report['provided_by_project'] = provided
        added = {key: environment[key] for key in ('LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LD_LIBRARY_PATH')}
        compile_environment = {'HOME': str(out / 'home'), 'PATH': str(toolchain / 'bin') + ':/usr/bin:/bin',
                               'LEAN_PATH': environment['LEAN_PATH'].rstrip(':') + ':' + str(source),
                               'LEAN_NUM_THREADS': '1', 'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8'}
        report['compile_environment'] = {'supervised': compile_environment, 'added_at_exec': added, 'working_directory': str(project)}
        total = 0
        for name in [item for item in pins['module_order'] if item not in provided]:
            relative = name.replace('.', '/')
            supervisor = Supervisor(Limits(wall_seconds=60, memory_mib=4096, log_bytes=8 << 20, artifact_bytes=1 << 30))
            command = [sys.executable, '-c', LAUNCH, str(project), json.dumps(added, sort_keys=True), str(toolchain / 'bin/lean'),
                       '-j1', '-M4096', '--root', str(source), '-o', str(source / (relative + '.olean')),
                       str(source / (relative + '.lean'))]
            try:
                stage, stdout, stderr = supervisor.run(name, command, out / 'stages' / name, out, environment=compile_environment)
            finally:
                supervisor.close()
            text = stdout.decode('utf-8', 'replace')
            record = {'exit_code': stage['exit_code'], 'classification': stage['classification'],
                      'seconds': round(stage.get('elapsed_seconds') or 0, 2), 'peak_kib': stage.get('peak_adapter_tree_rss_kib')}
            report['modules'][name] = record
            if stage['classification'] != 'completed' or stage['exit_code'] != 0 or stderr or REPORT.sub('', text).strip():
                record['output'] = (text + stderr.decode('utf-8', 'replace'))[-2000:]
                raise ValueError('Helper compile failed or printed diagnostics: ' + name)
            audits = {}
            for theorem, axioms in REPORT.findall(text):
                used = sorted(item.strip() for item in axioms.split(',') if item.strip())
                if not set(used) <= ALLOWED:
                    raise ValueError('Unapproved axiom in ' + theorem)
                audits[theorem] = used
            if audits != pins['axiom_audits'].get(name, {}):
                raise ValueError('Axiom report differs from its pin: ' + name)
            record['audits'] = len(audits)
            total += len(audits)
            save()
        report['objects_sha256'] = {path.relative_to(source).as_posix(): digest(path.read_bytes())
                                    for path in sorted(source.rglob('*')) if path.is_file()}
        report.update(status='built-and-audited', audits=total, modules_built=len(report['modules']),
                      finished_utc=datetime.now(timezone.utc).isoformat())
    except BaseException as error:
        report.update(status='failed', error=str(error), failure_type=type(error).__name__,
                      finished_utc=datetime.now(timezone.utc).isoformat())
    save()
    print(json.dumps({key: report.get(key) for key in ('status', 'modules_built', 'audits', 'error')}))
    return int(report['status'] != 'built-and-audited')


if __name__ == '__main__':
    raise SystemExit(main())
