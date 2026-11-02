#!/usr/bin/env python3
"""Bounded local version-8 kernel entry for expanded CNF/FOF input, direct compiler launch. No installed profile or native fallback.

Revision 6 is installed, not run from the development tree. installation.json
next to this file is written by the installer and names the installation
root, the output root, HOME, the Python interpreter, the toolchain, the built
lean-v8 project, the helper objects, the recorded Lean environment and the tree
manifests that replace the dependency inventory. The policy pins every source
relative to the installation root and carries the reviews as pin data: no
receipt is read at run time. Everything else is revision 5: no supervised child
starts before a refusal, ReviewPending included; for an output directory under
/mnt/c, case_sensitive() runs wslpath and fsutil.exe once, unsupervised, before
the review checks; and the entry accepts its own review only if the review's
pin data names this entry's source pins and its policy without the review slot.
"""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import stat
import sys
import time
import types

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
CAPS = {'input': 4096, 'certificate': 65536, 'witness': 16 << 20}
EXPECTED_AUDITS = ['EqInstance.actual_sealed_acceptance',
                   'EqInstance.actual_original_bytes_unsat']
EXIT = {'KernelChecked': 0, 'Rejected': 3, 'ReviewPending': 4, 'ResourceOut': 5,
        'Error': 6, 'Timeout': 7, 'MemoryOut': 8, 'Forced': 9}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def bootstrap_read(path, cap):
    """Bootstrap only: no executable imports before source bytes are pinned."""
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    try:
        if not stat.S_ISREG(os.fstat(fd).st_mode):
            raise ValueError('Regular file required')
        chunks, count = [], 0
        while count <= cap:
            chunk = os.read(fd, min(65536, cap + 1 - count))
            if not chunk:
                return b''.join(chunks)
            chunks.append(chunk)
            count += len(chunk)
        raise ValueError('Bootstrap byte cap exceeded')
    finally:
        os.close(fd)


def execute_buffer(data, path, name):
    module = types.ModuleType(name)
    module.__file__ = str(path)
    sys.modules[name] = module
    exec(compile(data, str(path), 'exec'), module.__dict__)
    return module


def case_sensitive(directory):
    """The version-8 library has case-only module pairs; make a new /mnt/c output case-sensitive and prove it."""
    if str(directory).startswith('/mnt/c/'):
        import subprocess
        windows = subprocess.run(['/usr/bin/wslpath', '-w', str(directory)], capture_output=True, check=True).stdout.decode().strip()
        subprocess.run(['/mnt/c/Windows/System32/fsutil.exe', 'file', 'setCaseSensitiveInfo', windows, 'enable'],
                       capture_output=True, timeout=60)
    lower, upper = directory / 'case-probe', directory / 'CASE-PROBE'
    lower.write_bytes(b'lower')
    upper.write_bytes(b'upper')
    distinct = lower.read_bytes() == b'lower' and upper.read_bytes() == b'upper'
    lower.unlink()
    if upper.exists():
        upper.unlink()
    if not distinct:
        raise ValueError('Output directory is not case-sensitive')


def require(condition, reason):
    if not condition:
        raise ValueError(reason)


def check_child(record, sealed):
    require(record['status'] == 'kernel-bundle-passed', 'Kernel stage did not pass')
    require(record['archive_hashes_verified'] is True, 'Kernel archive differs')
    require(record['sealed_sha256'] == sealed, 'Kernel receipt detached from sealed bytes')
    require(set(record['axiom_audits']['EqInstanceFixedAudit']) == set(EXPECTED_AUDITS),
            'Missing exact endpoint audit')
    require(record['modules'] > 0 and record['audits'] >= 2, 'Empty proof result')
    expected = [name for phase in record['phases'] for name in phase]
    require(expected and len(expected) == len(set(expected)), 'Invalid phase schedule')
    require(record['modules'] == len(expected), 'Module count differs')
    require(record['audits'] == sum(len(names) for names in record['axiom_audits'].values()),
            'Audit count differs')
    require(expected == record['module_order'], 'Detached module schedule')
    require([stage['stage'] for stage in record['stages']] == expected, 'Incomplete proof stages')
    require(expected[-1] == 'EqInstanceFixedAudit', 'Final endpoint is not last')
    require(all(stage['classification'] == 'completed' and stage['exit_code'] == 0
                for stage in record['stages']), 'Unsuccessful proof stage')
    require(record['limits'] == {'phase_seconds': 60, 'sampled_tree_rss_mib': 4096,
                                'checking_seconds': 600}, 'Proof guards differ')


def failure_status(mode, stage, record):
    if mode == 'check' and record.get('status') == 'failed':
        kind = record.get('failure_class')
        if kind in ('Timeout', 'MemoryOut', 'Forced', 'ResourceOut', 'Rejected'):
            return kind
    return 'Error'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('input', 'certificate', 'witness', 'out'):
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    if sys.platform != 'linux':
        parser.error('Use Linux/WSL')
    installation_data = bootstrap_read(HERE / 'installation.json', 4 << 20)
    installation = json.loads(installation_data)
    ROOT = Path(installation['root'])
    out = args.out.resolve()
    if not out.is_relative_to(Path(installation['output_root'])):
        parser.error('Use a fresh directory under the installation output root')
    started = time.monotonic()
    out.mkdir(parents=True, exist_ok=False)
    # Unsupervised and before the review checks; see the module docstring.
    case_sensitive(out)
    capture = out / 'capture'
    capture.mkdir()
    (out / 'stages').mkdir()
    report = {'schema': 'fang-v8-equality-kernel-entry-v2', 'status': 'Error',
              'installation_sha256': digest(installation_data),
              'started_utc': datetime.now(timezone.utc).isoformat(), 'stages': [],
              'limits': {'wall_seconds': 600, 'sampled_tree_rss_mib': 4096,
                         'artifact_bytes': 1 << 30, 'input_bytes': CAPS},
              'scope': 'One exact source/certificate pair of the bounded version-8 expanded grammar. Witnesses suggest values; Lean checks actual calls. No installed profile or full TPTP claim.',
              'trust': 'This local entry and policy provisioning, Python, Lean/backend, OS and filesystem are trusted. Inventories detect retained changes, not change-and-restore attacks.'}
    supervisor = None
    snapshots = []
    pins = {}
    try:
        policy_data = bootstrap_read(HERE / 'policy.json', 2 << 20)
        policy = json.loads(policy_data)
        require(policy['schema'] == 'fang-v8-equality-kernel-entry-policy-v2', 'Unknown policy')
        (capture / 'policy.json').write_bytes(policy_data)
        (capture / 'installation.json').write_bytes(installation_data)
        supervisor_relative = 'tools/fang_szs/supervisor.py'
        data = bootstrap_read(ROOT / supervisor_relative, 1 << 20)
        require(digest(data) == policy['files'][supervisor_relative], 'Supervisor pin differs')
        target = capture / supervisor_relative
        target.parent.mkdir(parents=True)
        target.write_bytes(data)
        support = execute_buffer(data, target, 'captured_entry_supervisor')
        supervisor = support.Supervisor(support.Limits(wall_seconds=600, memory_mib=4096,
            log_bytes=8 << 20, artifact_bytes=1 << 30), started=started)
        report['stages'] = supervisor.records

        def read(path, cap=64 << 20):
            return support.read_regular(path, cap, supervisor.check)

        def pin(path, target, expected=None):
            data = read(path)
            actual = digest(data)
            require(expected is None or actual == expected, 'Pinned file differs: ' + str(path))
            target.parent.mkdir(parents=True, exist_ok=True)
            if target.exists():
                require(read(target) == data, 'Existing captured file differs')
            else:
                target.write_bytes(data)
            pins[str(path)] = actual
            return data

        pin(HERE / 'main.py', capture / 'entry/main.py')
        pin(HERE / 'invoke.py', capture / 'entry/invoke.py')
        pins[str(HERE / 'policy.json')] = digest(policy_data)
        for relative, expected in policy['files'].items():
            require(not Path(relative).is_absolute() and '..' not in Path(relative).parts,
                    'Policy path escapes repository')
            pin(ROOT / relative, capture / relative, expected)
        for name, cap in CAPS.items():
            data = read(getattr(args, name), cap)
            snapshot = support.Snapshot(capture / {'input': 'input.p', 'certificate': 'proof.fang',
                                                  'witness': 'witness.json'}[name], data)
            snapshots.append(snapshot)
        sealed = dict(zip(CAPS, (item.sha256 for item in snapshots)))
        report.update(sealed_sha256=sealed, source_helper_sha256=pins,
                      policy_sha256=digest(policy_data))
        # The reviews are pin data in the policy; no receipt is read at run time.
        review = policy['independent_review']
        if review is None:
            raise support.Failure('ReviewPending', 'Version-8 endpoint independent review is not provisioned')
        require(review['bindings'].get('pins.link_v2') == policy['batch_sha256'], 'Endpoint review does not bind the policy link')
        # This entry's own review gates every proof child; until it exists the entry stops here.
        entry_review = policy['entry_review']
        if entry_review is None:
            raise support.Failure('ReviewPending', 'Version-8 entry independent review is not provisioned')
        require(ROOT / policy['entry_directory'] == HERE, 'Policy names another entry directory')
        # The review must name this entry's own sources and its policy before the review slot was filled.
        unprovisioned = dict(policy, entry_review=None)
        own = {'main.py': pins[str(HERE / 'main.py')], 'invoke.py': pins[str(HERE / 'invoke.py')],
               'policy.json': digest((json.dumps(unprovisioned, indent=2, sort_keys=True) + '\n').encode())}
        for name in ('check.py', 'trees.py', 'origin.json', 'provision-policy.py'):
            own[name] = policy['files'][policy['entry_directory'] + '/' + name]
        require(entry_review.get('status') == 'passed' and entry_review.get('entry_sources_sha256') == own,
                'Version-8 entry review does not name this entry and its policy')
        report['entry_review_sha256'] = entry_review['sha256']
        report['independent_review_sha256'] = review['sha256']
        interpreter = Path(sys.executable).resolve(strict=True)
        require(str(interpreter) == installation['python']['path'] and
                digest(read(interpreter)) == installation['python']['sha256'], 'Python pin differs')
        pins[str(interpreter)] = installation['python']['sha256']
        environment = {'HOME': installation['home'], 'PATH': '/usr/bin:/bin',
                       'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8', 'PYTHONDONTWRITEBYTECODE': '1'}

        def save():
            support.write_json(out / 'manifest.json', report)

        def child(mode, arguments, result_path, pass_fds=()):
            supervisor.check(mode)
            stage_name = mode if mode != 'inventory' else result_path.parent.name
            command = [str(interpreter), str(capture / 'entry/invoke.py'), str(capture),
                       str(ROOT), mode, *map(str, arguments)]
            stage, _, _ = supervisor.run(stage_name, command, out / 'stages' / stage_name,
                                         out, pass_fds=pass_fds, environment=environment)
            save()
            value = json.loads(read(result_path)) if result_path.exists() else {}
            if stage['classification'] != 'completed' or stage['exit_code'] != 0:
                raise support.Failure(failure_status(mode, stage, value),
                                      'Captured child failed: ' + stage_name, stage_name)
            return value

        child('inventory', [out / 'before'], out / 'before/manifest.json')
        arguments = []
        for name, snapshot in zip(CAPS, snapshots):
            arguments.extend(['--' + name, snapshot.argument])
        arguments.extend(['--out', str(out / 'proof'),
                          '--sealed-sha256', json.dumps(sealed, sort_keys=True),
                          '--installation', str(capture / 'installation.json'),
                          '--installation-sha256', digest(installation_data)])
        proof = child('check', arguments, out / 'proof/manifest.json',
                      pass_fds=tuple(item.fd for item in snapshots))
        check_child(proof, sealed)
        # invoke.py relocates the child's scratch tree under this evidence root.
        native = Path(proof['native_workspace'])
        require(native == out / 'proof-native', 'Unexpected proof workspace')
        child('inventory', [out / 'after'], out / 'after/manifest.json')
        for name in ('before', 'after'):
            record = json.loads(read(out / name / 'manifest.json'))
            require(record['status'] == 'unchanged' and record['installation_sha256'] == digest(installation_data),
                    'Installed Lean trees changed')
        for snapshot in snapshots:
            snapshot.verify(supervisor.check)
        for path, expected in pins.items():
            require(digest(read(Path(path))) == expected, 'Source/tool identity changed')
        for relative, expected in policy['files'].items():
            require(digest(read(capture / relative)) == expected, 'Captured helper changed')
        require(read(capture / 'policy.json') == policy_data, 'Captured policy changed')
        require(read(capture / 'installation.json') == installation_data and
                read(HERE / 'installation.json') == installation_data, 'Installation record changed')
        for name in ('main.py', 'invoke.py'):
            require(digest(read(capture / 'entry' / name)) == pins[str(HERE / name)],
                    'Captured entry changed')
        artifacts = {}
        for path in sorted(out.rglob('*')):
            supervisor.check('archive')
            if path.is_symlink():
                raise ValueError('Symlink in evidence')
            if path.is_file() and path != out / 'manifest.json':
                artifacts[path.relative_to(out).as_posix()] = digest(read(path, 256 << 20))
        supervisor.tree_bytes(out)
        supervisor.memory()
        supervisor.check('final')
        report.update(status='KernelChecked', modules=proof['modules'], audits=proof['audits'],
                      artifacts_sha256=artifacts,
                      proof_manifest_sha256=digest(read(out / 'proof/manifest.json')),
                      before_sha256=digest(read(out / 'before/manifest.json')),
                      after_sha256=digest(read(out / 'after/manifest.json')))
        supervisor.check('positive-result')
    except BaseException as error:
        report.update(status=getattr(error, 'status', 'Error'), error=str(error),
                      failure_type=type(error).__name__)
        if report['status'] not in EXIT:
            report['status'] = 'Error'
    finally:
        for snapshot in snapshots:
            snapshot.close()
        if supervisor is not None:
            report['peak_kib'] = supervisor.peak_kib
            supervisor.close()
        report.update(finished_utc=datetime.now(timezone.utc).isoformat(),
                      wall_seconds=time.monotonic() - started)
        (out / 'manifest.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n', encoding='utf-8')
    print(json.dumps({'status': report['status'], 'error': report.get('error'),
                      'manifest': str(out / 'manifest.json')}), flush=True)
    return EXIT[report['status']]


if __name__ == '__main__':
    raise SystemExit(main())
