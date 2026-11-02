#!/usr/bin/env python3
"""Version-8 exact-instance proof bundle for one sealed pair, direct compiler launch (generator version 4, entry revision 6).

Revision 6 takes every machine-specific value from the installation record
named by --installation and pinned by --installation-sha256: HOME, the
toolchain, the Lean search environment that `lake env` gives in the built
lean-v8 project, the helper objects and the output root. The library is no
longer copied into the run: the compiler reads the installed lean-v8 objects and
helper objects through the recorded search path, and the entry checks those
trees against the installation record before and after the run. Generation,
the per-phase guards, the audits, the endpoint and the archive are unchanged.
"""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import argparse
import fcntl
import gc
import stat
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import sys
import tempfile
import time
import traceback

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def installed_paths():
    """Run in place, the installation root and generator directory come from the files installed next to this one.

    Through invoke.py both are replaced by the captured copies before main() runs.
    """
    try:
        record = json.loads((HERE / 'installation.json').read_bytes())
        policy = json.loads((HERE / 'policy.json').read_bytes())
        return Path(record['root']), Path(record['root']) / policy['generator_directory']
    except (OSError, ValueError, KeyError):
        return HERE, HERE.parent


TOOLS_ROOT, SOURCE = installed_paths()
# Generator version 4, captured under this pin.
GENERATOR_PIN = '4d133fbf6310720f323accb0c411b4be7bc4e5dc7a26888490114334f6f6cfc9'
OUTPUT_ROOT = None
RECIPES = 'tools/v8_kernel/recipe/equality'
MIXED = 'tools/v8_kernel/recipe/mixed'
# The reviewed version-7 recipe files (pins of the reviewed entry policies).
RECIPE_PINS = {'generate-cnf.py': 'be7ff73dd9669bd9b5eb60798cb53a65ec8aa49ff11a2f96376076c1e26539ba',
               'generate-quantified.py': 'd58d8bcd8aabf9d01b12545cc0d8cc93c5a25d6450f2699c55e443816a7cae2c',
               'generate-certificate.py': '2f79c2b7846dbc9664cd4acd41be959038ed6a11688d5ab2f6251066141df534',
               'sources.json': '2edc2f9756923e3ca4542c7aa0ceae2e7a5bf41636432a863e43654625695947'}
AUDITS = re.compile(r'^#print axioms ([A-Za-z0-9_.]+)\r?$', re.M)
# Replaces `lake env lean`: set the recorded search variables, then exec the compiler in place.
LAUNCH = ('import json,os,sys; os.chdir(sys.argv[1]); '
          'os.execve(sys.argv[3], sys.argv[3:], dict(os.environ, **json.loads(sys.argv[2])))')
SEARCH = ('LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LD_LIBRARY_PATH')


class ConstructionRejected(ValueError):
    status = 'Rejected'


def digest(data):
    return hashlib.sha256(data).hexdigest()


def sha(path):
    if path.is_symlink() or not path.is_file():
        raise ValueError('Expected regular file: ' + str(path))
    return digest(path.read_bytes())


def read_source(path, cap):
    descriptor = path.parent == Path('/proc/self/fd') and path.name.isdecimal()
    if descriptor:
        fd = int(path.name)
        required = fcntl.F_SEAL_SEAL | fcntl.F_SEAL_SHRINK | fcntl.F_SEAL_GROW | fcntl.F_SEAL_WRITE
        if fcntl.fcntl(fd, fcntl.F_GET_SEALS) & required != required or not stat.S_ISREG(os.fstat(fd).st_mode):
            raise ValueError('Expected sealed regular descriptor')
    else:
        fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    try:
        if not stat.S_ISREG(os.fstat(fd).st_mode):
            raise ValueError('Expected regular source')
        chunks, size = [], 0
        while size <= cap:
            chunk = os.pread(fd, min(65536, cap + 1 - size), size)
            if not chunk:
                return b''.join(chunks)
            chunks.append(chunk)
            size += len(chunk)
        raise ValueError('Source byte cap exceeded')
    finally:
        if not descriptor:
            os.close(fd)


def case_sensitive(directory):
    """The archived library has case-only module pairs; prove the new output keeps such pairs apart."""
    lower, upper = directory / 'case-probe', directory / 'CASE-PROBE'
    lower.write_bytes(b'lower')
    upper.write_bytes(b'upper')
    distinct = lower.read_bytes() == b'lower' and upper.read_bytes() == b'upper'
    lower.unlink()
    if upper.exists():
        upper.unlink()
    if not distinct:
        raise ValueError('Output directory is not case-sensitive; enable it on a new parent first')


def runner_rss_kib():
    for line in Path('/proc/self/status').read_text().splitlines():
        if line.startswith('VmRSS:'):
            return int(line.split()[1])
    raise ValueError('Runner RSS unavailable')


def generator_name(raw):
    # This selects a construction recipe, never an acceptance result. Each
    # recipe checks the actual independent decoder and the same sealed bytes.
    def unique(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError('Duplicate witness field')
            result[key] = value
        return result
    try:
        witness = json.loads(raw, object_pairs_hook=unique)
    except (ValueError, RecursionError) as error:
        raise ConstructionRejected('Invalid witness JSON') from error
    declarations = witness.get('source_declarations') if isinstance(witness, dict) else None
    if isinstance(declarations, list) and declarations and all(
            isinstance(item, dict) and isinstance(item.get('body'), list) and
            len(item['body']) == 2 and item['body'][0] == 'cnf' for item in declarations):
        return 'generate-cnf.py'
    return 'generate-quantified.py'


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--installation', type=Path)
    p.add_argument('--installation-sha256')
    p.add_argument('--input', type=Path)
    p.add_argument('--certificate', type=Path)
    p.add_argument('--witness', type=Path)
    p.add_argument('--sealed-sha256', required=True)
    args = p.parse_args()
    sealed = json.loads(args.sealed_sha256)
    if set(sealed) != {'input', 'certificate', 'witness'}:
        p.error('Expected three sealed input pins')
    out = args.out.resolve()
    if not (args.installation and args.installation_sha256 and args.input and args.certificate and args.witness):
        p.error('A version-8 instance requires the pinned installation record and the sealed triple')
    record_data = read_source(args.installation, 4 << 20)
    if digest(record_data) != args.installation_sha256:
        p.error('Installation record differs from its pin')
    installation = json.loads(record_data)
    output_root = Path(OUTPUT_ROOT if OUTPUT_ROOT is not None else installation['output_root'])
    if sys.platform != 'linux' or not out.is_relative_to(output_root):
        p.error('Use Linux/WSL and a fresh directory under the installation output root')
    TOOLS = Path(installation['toolchain']['directory']) / 'bin'
    PROJECT = Path(installation['project']['directory'])
    HELPERS = Path(installation['helpers']['directory'])
    out.mkdir(parents=True, exist_ok=False)
    case_sensitive(out)
    native = Path(tempfile.mkdtemp(prefix='fang-equality-instance-', dir='/var/tmp'))
    source = native / 'source'
    source.mkdir()
    helpers = native / 'helpers'
    (helpers / 'fang_szs').mkdir(parents=True)
    (native / 'stages').mkdir()
    pins, captured, owners, new = {}, {}, {}, {}
    source_caps = {}
    start = time.monotonic()
    report = {'status': 'starting', 'started_utc': datetime.now(timezone.utc).isoformat(),
              'native_workspace': str(native), 'dependency_after_link_pending': True,
              'limits': {'phase_seconds': 60, 'sampled_tree_rss_mib': 4096, 'checking_seconds': 600},
              'stages': [], 'axiom_audits': {}, 'installation_sha256': args.installation_sha256,
              'scope': 'Exact sealed version-8 instance: actual decoding, transport, preprocessing, conversion and v8 acceptance.'}
    supervisor = None

    def within():
        if time.monotonic() - start >= 600:
            raise TimeoutError('Whole checking deadline exceeded')

    def capture(path, target, expected=None, cap=256 << 20):
        data = read_source(path, cap)
        if len(data) > cap or expected is not None and digest(data) != expected:
            raise ValueError('Capture identity/size: ' + str(path))
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        pins[str(path)] = digest(data)
        source_caps[str(path)] = cap
        captured[target.relative_to(native).as_posix()] = digest(data)
        within()
        return data

    def save():
        (out / 'manifest.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')

    try:
        capture(Path(__file__), native / 'driver/entry-check.py')
        capture(args.installation, native / 'installation.json', args.installation_sha256, cap=4 << 20)
        # The helper objects are read in place through the search path; each is pinned and checked again at the end.
        for rel, pin in installation['helpers']['objects_sha256'].items():
            data = read_source(HELPERS / rel, 256 << 20)
            if digest(data) != pin:
                raise ValueError('Installed helper object differs: ' + rel)
            pins[str(HELPERS / rel)] = pin
            owners[rel] = 'helpers'
            within()
        pair = [capture(path, native / 'sealed' / filename, cap=cap) for path, filename, cap in
                [(args.input, 'input.p', 4096), (args.certificate, 'proof.fang', 65536),
                 (args.witness, 'witness.json', 16 << 20)]]
        if {key: digest(data) for key, data in zip(('input', 'certificate', 'witness'), pair)} != sealed:
            raise ValueError('Input capture differs from outer sealed bytes')
        import types

        def load(path, target, pin, name):
            data = capture(path, target, pin, cap=1 << 20)
            module = types.ModuleType(name)
            module.__file__ = str(target)
            exec(compile(data, str(target), 'exec'), module.__dict__)
            return module

        selected = generator_name(pair[2])
        recipes, mixed = TOOLS_ROOT / RECIPES, TOOLS_ROOT / MIXED
        recipe = load(recipes / selected, native / 'driver' / selected, RECIPE_PINS[selected], 'captured_recipe')
        report['selected_generator'] = selected
        source_map = json.loads(capture(mixed / 'sources.json', native / 'emitters/sources.json', RECIPE_PINS['sources.json']))
        emitters = {key: load(mixed / filename, native / 'emitters' / filename, source_map['emitters'][filename], 'captured_' + key)
                    for key, filename in recipe.EMITTERS.items()}
        emitters['certificate'] = load(recipes / 'generate-certificate.py', native / 'driver/generate-certificate.py',
                                       RECIPE_PINS['generate-certificate.py'], 'captured_certificate')
        generator = load(SOURCE / 'generate-v8.py', native / 'driver/generate-v8.py', GENERATOR_PIN, 'captured_v8_generator')
        try:
            new, phases = generator.build(*pair, emitters, recipe)
        except ValueError as error:
            raise ConstructionRejected(str(error)) from error
        for name, data in new.items():
            if (source / (name + '.lean')).exists():
                raise ValueError('Generated module collision')
            (source / (name + '.lean')).write_bytes(data)
        report.update(sealed_sha256={key: digest(data) for key, data in zip(('input', 'certificate', 'witness'), pair)},
                      installation_sha256=args.installation_sha256)
        for name in ('__init__.py', 'supervisor.py'):
            capture(TOOLS_ROOT / 'tools/fang_szs' / name, helpers / 'fang_szs' / name)
        capture(TOOLS_ROOT / 'tools/replay/axiom_audit.py', helpers / 'axiom_audit.py')
        for path in (TOOLS / 'lean', TOOLS / 'lake', Path(sys.executable).resolve()):
            pins[str(path)] = sha(path)
        sys.path.insert(0, str(helpers))
        from fang_szs.supervisor import Limits, Supervisor
        from axiom_audit import REPORT, audit_axioms
        # Generation is complete. Retain the emitted source and every identity
        # pin, but release parsed ancestor receipts and executable emitter graphs.
        # The outer and phase supervisors still account for the full process tree.
        before_rss = runner_rss_kib()
        source_map = recipe = emitters = generator = pair = data = None
        gc.collect()
        report['generation_buffer_release'] = {
            'runner_rss_before_kib': before_rss, 'runner_rss_after_kib': runner_rss_kib(),
            'released': ['emitter module/global graphs',
                         'temporary capture buffers and decoded sealed triple'],
            'retained': ['generated Lean source', 'source/tool pins', 'captured pins',
                         'sealed input hashes', 'import ownership and ordered stages']}
        report.update(status='running', module_order=list(new), phases=phases,
                      source_sha256={name: digest(data) for name, data in new.items()},
                      imported_dependency_owners=owners, input_helper_tool_sha256=pins)
        # The compiler environment is the `lake env` environment recorded at install in the built lean-v8
        # project, plus the helper objects and this run's source root. Every search path stays inside the
        # installed project or toolchain tree; the compiler is the installed toolchain binary.
        effective = installation['lean_environment']
        toolchain = TOOLS.parent
        if effective.get('LD_PRELOAD') or effective.get('LD_AUDIT'):
            raise ValueError('Unexpected recorded compiler environment')
        for key in ('LEAN_PATH', *SEARCH):
            for item in effective[key].split(':'):
                resolved = Path(item).resolve()
                if item and not (resolved.is_relative_to(PROJECT.resolve()) or resolved.is_relative_to(toolchain.resolve())):
                    raise ValueError('Compiler search path outside the installed trees: ' + item)
        if Path(effective['LEAN_SYSROOT']).resolve() != toolchain.resolve():
            raise ValueError('Compiler sysroot differs from the installed toolchain')
        added = {key: effective[key] for key in SEARCH}
        environment = {'HOME': installation['home'], 'PATH': str(TOOLS) + ':/usr/bin:/bin',
                       'LEAN_PATH': effective['LEAN_PATH'].rstrip(':') + ':' + str(HELPERS) + ':' + str(source),
                       'LEAN_NUM_THREADS': '1', 'LANG': 'C.UTF-8', 'LC_ALL': 'C.UTF-8'}
        report['compiler_environment'] = {
            'compiler': str(TOOLS / 'lean'), 'working_directory': str(PROJECT),
            'supervised': environment, 'added_at_exec': added, 'installation_sha256': args.installation_sha256,
            'run_specific': {'LEAN_PATH_suffix': str(HELPERS) + ':' + str(source)},
            'scope': 'Replaces the resident `lake env` wrapper; recorded search values are copied unchanged.'}
        save()
        for phase in phases:
            within()
            supervisor = Supervisor(Limits(wall_seconds=min(60, 600 - (time.monotonic() - start)),
                memory_mib=4096, log_bytes=8 << 20, artifact_bytes=1 << 30))
            supervisor.additional_artifact_roots.append(native)
            for name in phase:
                command = [sys.executable, '-c', LAUNCH, str(PROJECT), json.dumps(added, sort_keys=True),
                    str(TOOLS / 'lean'), '-j1', '-M4096', '--root', str(source),
                    '-o', str(source / (name + '.olean')), str(source / (name + '.lean'))]
                stage, stdout, stderr = supervisor.run(name, command, native / 'stages' / name, native, environment=environment)
                report['stages'].append(stage)
                save()
                if stage['classification'] != 'completed' or stage['exit_code'] != 0 or stderr:
                    raise ValueError('Lean stage failed: ' + name)
                required = set(AUDITS.findall(new[name].decode()))
                text = stdout.decode()
                if len(list(REPORT.finditer(text))) != len(required) or REPORT.sub('', text).strip():
                    raise ValueError('Unexpected diagnostics/audits: ' + name)
                report['axiom_audits'][name] = audit_axioms(text, required) if required else {}
            supervisor.close()
            supervisor = None
        if any(digest(read_source(Path(path), source_caps.get(path, 256 << 20))) != pin
               for path, pin in pins.items()):
            raise ValueError('Input/helper/tool changed')
        if any(sha(native / path) != pin for path, pin in captured.items()):
            raise ValueError('Captured input changed')
        within()
        report.update(status='kernel-bundle-passed', modules=len(new),
                      audits=sum(len(AUDITS.findall(data.decode())) for data in new.values()),
                      checking_seconds=time.monotonic() - start)
    except BaseException as error:
        report.update(status='failed', error=str(error), failure_type=type(error).__name__, failure_class=getattr(error, 'status', 'Timeout' if isinstance(error, TimeoutError) else 'Error'), traceback=traceback.format_exc())
    finally:
        if supervisor is not None:
            supervisor.close()
        frozen = {path.relative_to(native).as_posix(): sha(path) for path in native.rglob('*') if path.is_file()}
        shutil.copytree(native, out / 'run')
        archived = {path.relative_to(out / 'run').as_posix(): sha(path) for path in (out / 'run').rglob('*') if path.is_file()}
        report.update(artifacts_sha256=archived, archive_hashes_verified=frozen == archived,
                      captured_inputs_sha256=captured, finished_utc=datetime.now(timezone.utc).isoformat())
        if frozen != archived:
            report.update(status='failed', error='Archive differs')
        save()
    print(json.dumps({key: report.get(key) for key in ('status', 'modules', 'audits', 'error')}))
    return int(report['status'] != 'kernel-bundle-passed')


if __name__ == '__main__':
    raise SystemExit(main())
