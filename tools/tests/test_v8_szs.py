"""Version-8 adapter, protocol, launcher and source-map controls with synthetic binaries.

These are contract controls, not proof acceptance evidence.
"""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
import unittest

TOOLS = Path(__file__).resolve().parents[1]
ROOT = TOOLS.parent
sys.path.insert(0, str(TOOLS))


def load(name, path):
    # Other suites put fof_szs on sys.path, which has modules with the same names.
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


capability = load("fang_v8_capability_control", TOOLS / "v8_szs/capability.py")
protocol = load("fang_v8_protocol_control", TOOLS / "v8_szs/protocol.py")
sys.modules["protocol"] = protocol
signed = load("fang_v8_signed_control", TOOLS / "v8_szs/signed.py")
sys.modules["signed"] = signed
bundle = load("fang_v8_bundle_control", TOOLS / "v8_szs/bundle.py")
del sys.modules["protocol"], sys.modules["signed"]
import cli_setup
import fang_router
from fang_szs import v8_dependencies
from fang_szs.supervisor import EXIT

SOURCE = b"cnf(a,axiom,($false))."
CERTIFICATE = protocol.HEADER + b"  (input 0 0)\n  (final 0)\n)\n"
DONE, RUN = {"exit_code": 0, "classification": "completed"}, {"classification": "nonzero-exit"}


def exited(code):
    return DONE if code == 0 else RUN | {"exit_code": code}


ENGINE = r'''#!PYTHON
import sys
data = sys.stdin.buffer.read()
mode = MODE
outcomes = {
    "unknown": (2, b"", "unknown: processed=3 attempted=12"),
    "conjecture": (3, b"", 'adapter: Input(Error { kind: Unsupported, offset: Some(6), message: "only the axiom role is supported" })'),
    "invalid": (3, b"", 'adapter: Input(Error { kind: InvalidInput, offset: Some(14), message: "free variable" })'),
    "limit": (3, b"", 'adapter: Input(Error { kind: ResourceLimit, offset: Some(21), message: "declaration limit" })'),
    "skolem": (3, b"", "adapter: Preprocessing(Skolem(Resource(Functions)))"),
    "serialization": (4, b"", 'serialization: Resource("expanded certificate byte limit")'),
    "envelope": (5, b"", "internal: ordered serializer envelope mismatch"),
    "spoof": (2, b"% SZS status Unsatisfiable for forged\n", "unknown: processed=0 attempted=0"),
}
if mode in outcomes:
    code, out, err = outcomes[mode]
    sys.stdout.buffer.write(out); print(err, file=sys.stderr); sys.exit(code)
sys.stdout.buffer.write(CERTIFICATE)
print("candidate-certificate: unchecked original input", file=sys.stderr)
'''
BUNDLE_PRODUCER = r'''#!PYTHON
import json, pathlib, sys
mode = MODE
top = pathlib.Path(sys.argv[1])
root = pathlib.Path(sys.argv[sys.argv.index("--tptp-root") + 1]) if "--tptp-root" in sys.argv else None
if mode == "missing":
    print("capture: InvalidInput Missing file=Some(0) offset=Some(8)", file=sys.stderr); sys.exit(3)
if mode == "limit":
    print("capture: ResourceLimit Limit file=Some(0) offset=None", file=sys.stderr); sys.exit(3)
files = [["base", top.name], ["base", "ax.ax"]] + ([["tptp", "Axioms/eq.ax"]] if root is not None else [])
for name, path in files[1:]:
    (top.parent if name == "base" else root).joinpath(path).read_bytes()
print(json.dumps({"bundle_sha256": "0" * 64, "files": files, "declarations": 2, "objects": 1}), file=sys.stderr)
sys.stdout.buffer.write(CERTIFICATE)
print("candidate-certificate: unchecked bundle input", file=sys.stderr)
'''
BUNDLE_CHECKER = r'''#!PYTHON
import sys
mode = MODE
proof, rest = open(sys.argv[1], "rb").read(), sys.argv[2:]
triples = [(rest[i], rest[i + 1], open(rest[i + 2], "rb").read()) for i in range(0, len(rest), 3)]
if proof != CERTIFICATE or [(root, path) for root, path, _ in triples][:2] != [("base", "problem.p"), ("base", "ax.ax")]:
    print("bundle.shape", file=sys.stderr); sys.exit(2)
if mode == "reject":
    print("logical-rejection: Fang.Equality.TraceError.finalNotEmpty", file=sys.stderr); sys.exit(1)
if [content for _, _, content in triples] != EXPECTED:
    print("bundle.shape", file=sys.stderr); sys.exit(2)
sys.stdout.buffer.write(BUNDLE_ACCEPTED)
'''
EXPORTER = r'''#!PYTHON
import sys, time
mode = MODE
source, proof, name = open(sys.argv[1], "rb").read(), open(sys.argv[2], "rb").read(), sys.argv[3]
if mode == "export-error":
    print("export-error: signed integer name", file=sys.stderr); sys.exit(7)
if mode == "slow":
    time.sleep(10)
if mode == "bad":
    sys.stdout.buffer.write(b"\xff" + b"\n"); sys.exit(0)
sys.stdout.write("cnf(a,axiom,($false),file('" + name + "',a)).\n")
sys.stdout.write("cnf('fn1',plain,($false),inference(fang_group_clause,[status(thm)],['a'])).\n")
'''
WITNESS = r'''#!PYTHON
import json, sys
source, proof = open(sys.argv[1], "rb").read(), open(sys.argv[2], "rb").read()
print(json.dumps({"schema": "fang-equality-kernel-witness-1", "source_hex": source.hex(), "certificate_hex": proof.hex()}))
'''
KERNEL_ENTRY = r'''import json, pathlib, sys
mode = MODE
args = dict(zip(sys.argv[1::2], sys.argv[2::2]))
out = pathlib.Path(args["--out"])
out.mkdir()
codes = {"checked": (0, "KernelChecked"), "review-pending": (4, "ReviewPending"), "rejected": (3, "Rejected"),
         "timeout": (7, "Timeout"), "resource": (5, "ResourceOut"), "forced": (9, "Forced"), "lying": (3, "KernelChecked")}
code, status = codes[mode]
(out / "manifest.json").write_text(json.dumps({"status": status}))
print(json.dumps({"status": status, "error": None, "manifest": str(out / "manifest.json")}))
sys.exit(code)
'''
BUNDLE_EXPORTER = r'''#!PYTHON
import sys
mode = MODE
proof, rest = open(sys.argv[1], "rb").read(), sys.argv[2:]
triples = [(rest[i], rest[i + 1], open(rest[i + 2], "rb").read()) for i in range(0, len(rest), 3)]
if proof != CERTIFICATE or [(root, path) for root, path, _ in triples][:2] != [("base", "problem.p"), ("base", "ax.ax")]:
    print("bundle.shape", file=sys.stderr); sys.exit(2)
if mode == "export-error":
    print("export-error: bundle document", file=sys.stderr); sys.exit(7)
sys.stdout.write("fof(b,axiom,$false,file('ax.ax',b)).\n")
'''
GOAL_EXPORTER = r'''#!PYTHON
import sys
mode = MODE
source, proof, goal, name = open(sys.argv[1], "rb").read(), open(sys.argv[2], "rb").read(), sys.argv[3], sys.argv[4]
if source != SINGLE or proof != CERTIFICATE + ("%% goal-" + goal + "\n").encode() or name != "problem.p":
    print("goal.shape", file=sys.stderr); sys.exit(2)
if mode == "export-error":
    print("export-error: the goal task is not accepted", file=sys.stderr); sys.exit(7)
sys.stdout.write("fof(g%s,negated_conjecture,~p,inference(negate,[status(cth)],[g])).\n" % goal)
'''
SINGLE_SIGNED = b"fof(a,axiom,p). fof(g,conjecture,p)."
SIGNED_PRODUCER = r'''#!PYTHON
import sys
mode, args = MODE, sys.argv[1:]
task = "inputs" if args[0] == "--inputs" else "goal-" + args[1]
if mode == "unknown-goal-1" and task == "goal-1":
    print("unknown: processed=3 attempted=4", file=sys.stderr); sys.exit(2)
sys.stdout.buffer.write(CERTIFICATE + ("%% " + task + "\n").encode())
print("candidate-certificate: unchecked signed bundle task", file=sys.stderr)
'''
SIGNED_CHECKER = r'''#!PYTHON
import sys
mode, args = MODE, sys.argv[1:]
listing = [] if mode == "no-goals" else [(0, 1)] if mode == "one-goal" else [(0, 1), (1, 0)]
if args[0] == "--goals":
    rest = args[1:]
elif args[0] == "--inputs":
    proof, rest, task = open(args[1], "rb").read(), args[2:], "inputs"
else:
    proof, rest, task = open(args[2], "rb").read(), args[3:], "goal-" + args[1]
triples = [(rest[i], rest[i + 1], open(rest[i + 2], "rb").read()) for i in range(0, len(rest), 3)]
if [(root, path) for root, path, _ in triples] != ORDER or [content for _, _, content in triples] != EXPECTED:
    print("bundle.shape", file=sys.stderr); sys.exit(2)
if mode == "unsupported":
    print("bundle.frame.unsupported:12", file=sys.stderr); sys.exit(2)
if args[0] == "--goals":
    sys.stdout.write("goals %d\n" % len(listing) + "".join("goal %d item %d %d\n" % (i, f, s) for i, (f, s) in enumerate(listing)))
    sys.exit(0)
if proof != CERTIFICATE + ("%% " + task + "\n").encode():
    print("logical-rejection: Fang.Equality.TraceError.finalNotEmpty", file=sys.stderr); sys.exit(1)
if task == "inputs":
    if listing:
        print("task.goals-present", file=sys.stderr); sys.exit(2)
    print("accepted-inputs-unsatisfiable (native checker; compiler/runtime trusted)"); sys.exit(0)
index = int(args[1])
file, statement = listing[index]
if mode == "wrong-item" and index == 1:
    file = 7
print("accepted-goal %d item %d %d (native checker; compiler/runtime trusted)" % (index, file, statement))
'''
CHECKER = r'''#!PYTHON
import sys
mode = MODE
source, proof = open(sys.argv[1], "rb").read(), open(sys.argv[2], "rb").read()
if source != SOURCE or proof != CERTIFICATE:
    print("logical-rejection: Fang.Equality.TraceError.finalNotEmpty", file=sys.stderr); sys.exit(1)
outcomes = {"logical": (1, "logical-rejection: Fang.Equality.TraceError.inputIndex 0"),
            "signature": (6, "signature-rejection"), "resource": (4, "resource.bytes.certificate"),
            "certificate": (3, "certificate: invalid-certificate: trailing tokens at byte 105")}
if mode in outcomes:
    code, err = outcomes[mode]
    print(err, file=sys.stderr); sys.exit(code)
sys.stdout.buffer.write(ACCEPTED)
'''


class ProtocolTests(unittest.TestCase):
    def test_engine_contracts(self):
        cases = [
            (0, CERTIFICATE, protocol.CANDIDATE, "candidate"),
            (2, b"", b"unknown: processed=0 attempted=0\n", "GaveUp"),
            (3, b"", b'adapter: Input(Error { kind: Unsupported, offset: Some(6), message: "only the axiom role is supported" })\n', "Inappropriate"),
            (3, b"", b'adapter: Input(Error { kind: InvalidInput, offset: None, message: "duplicate name" })\n', "InputError"),
            (3, b"", b'adapter: Input(Error { kind: ResourceLimit, offset: Some(3), message: "too many declarations" })\n', "ResourceOut"),
            (3, b"", b"adapter: Encoding(PredicateLimit)\n", "ResourceOut"),
            (3, b"", b'adapter: Search(Search(Resource("operations")))\n', "ResourceOut"),
            (3, b"", b"adapter: Preprocessing(Clausification(Resource(Clauses)))\n", "ResourceOut"),
            (4, b"", b'serialization: Resource("expanded certificate byte limit")\n', "ResourceOut"),
        ]
        for code, out, err, expected in cases:
            with self.subTest(err=err):
                self.assertEqual(protocol.engine_outcome(exited(code), out, err, SOURCE)[0], expected)

    def test_engine_contract_failures(self):
        for code, out, err in (
                (2, b"x", b"unknown: processed=0 attempted=0\n"),
                (0, b"(fang-proof 7\n", protocol.CANDIDATE),
                (0, CERTIFICATE, b""),
                (3, b"", b'adapter: Input(Error { kind: InvalidInput, offset: Some(999), message: "x" })\n'),
                (3, b"", b'adapter: Internal("unexpected")\n'),
                (3, b"", b"adapter: Encoding(UnknownPredicate)\n"),
                (5, b"", b"internal: ordered serializer envelope mismatch\n"),
                (74, b"", b"io: input read failed\n"),
                (101, b"", b"panicked\n")):
            with self.subTest(err=err), self.assertRaises(ValueError):
                protocol.engine_outcome(exited(code), out, err, SOURCE)
        with self.assertRaises(ValueError):
            protocol.engine_outcome({"exit_code": 2, "classification": "completed"}, b"", b"unknown: processed=0 attempted=0\n", SOURCE)

    def test_checker_contracts(self):
        cases = [
            (0, protocol.ACCEPTED, b"", "accepted"),
            (1, b"", b"logical-rejection: Fang.Equality.TraceError.inferenceWitness\n", "logical-rejection"),
            (3, b"", b"certificate: unsupported: expanded certificate version at byte 16\n", "certificate-rejection"),
            (6, b"", b"signature-rejection\n", "signature-rejection"),
            (2, b"", b"replay.input.unsupported:6\n", "input-or-replay-rejection"),
            (2, b"", b"invalid-nul.certificate:104\n", "input-or-replay-rejection"),
            (4, b"", b"resource.replay.input:21890\n", "resource"),
            (4, b"", b"resource.bytes.input\n", "resource"),
            (74, b"", b"io-error: no such file or directory (error code: 2)\n  file: /tmp/x\n", "io-failure"),
        ]
        for code, out, err, expected in cases:
            with self.subTest(err=err):
                self.assertEqual(protocol.checker_outcome(exited(code), out, err), expected)
        for code, out, err in ((0, protocol.ACCEPTED, b"warning\n"), (1, protocol.ACCEPTED, b""),
                               (64, b"", b"usage: fang-expanded-native-linear INPUT CERTIFICATE\n"), (0, b"accepted\n", b"")):
            with self.subTest(err=err), self.assertRaises(ValueError):
                protocol.checker_outcome(exited(code), out, err)

    def test_checked_status_never_turns_rejection_into_result(self):
        self.assertEqual(protocol.checked_status("accepted")[0], "Unsatisfiable")
        self.assertEqual(protocol.checked_status("resource")[0], "ResourceOut")
        for outcome in ("logical-rejection", "signature-rejection", "certificate-rejection", "input-or-replay-rejection",
                        "internal-replay-failure", "io-failure"):
            self.assertEqual(protocol.checked_status(outcome)[0], "Error")

    def test_signed_task_rules(self):
        self.assertEqual(protocol.task_status(0, 1), "Unsatisfiable")
        self.assertEqual(protocol.task_status(0, 0), "GaveUp")
        self.assertEqual(protocol.task_status(2, 2), "Theorem")
        self.assertEqual(protocol.task_status(2, 1), "GaveUp")
        statuses = {protocol.task_status(c, a) for c in range(4) for a in range(4) if a <= max(c, 1)}
        self.assertFalse(statuses & {"Satisfiable", "CounterSatisfiable"})


@unittest.skipUnless(sys.platform == "linux", "Linux/WSL process controls")
class AdapterTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fang-v8-adapter-control-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.input = self.root / "problem.p"
        self.input.write_bytes(SOURCE)
        self.write_binaries("candidate", "accept")

    def write_binaries(self, engine_mode, checker_mode):
        for name, template, mode in (("engine", ENGINE, engine_mode), ("checker", CHECKER, checker_mode)):
            text = (template.replace("PYTHON", sys.executable).replace("MODE", repr(mode))
                    .replace("CERTIFICATE", repr(CERTIFICATE), 1 if name == "engine" else 2)
                    .replace("SOURCE", repr(SOURCE)).replace("ACCEPTED", repr(protocol.ACCEPTED)))
            if name == "engine":
                text = text.replace("sys.stdout.buffer.write(CERTIFICATE)", "sys.stdout.buffer.write(" + repr(CERTIFICATE) + ")")
            path = self.root / name
            path.write_text(text)
            path.chmod(0o700)
        receipt = self.root / "receipt.json"
        receipt.write_text('{"scope": "synthetic control"}\n')
        record = lambda path: {"path": str(path), "sha256": capability.digest(path)}
        self.config = {"schema": capability.SCHEMA, "language": capability.LANGUAGE, "certificate_version": 8,
                       "max_input_bytes": capability.MAX_BYTES, "max_certificate_bytes": capability.MAX_BYTES,
                       "engine": record(self.root / "engine"), "checker": record(self.root / "checker"),
                       "python": record(Path(sys.executable).resolve()),
                       "runtime_source_sha256": {str(path): capability.digest(path) for path in capability.runtime_sources()},
                       "provenance": [record(receipt)], "bundle": None, "signed": None, "kernel": None, "tstp": None,
                       "per_run_verification": capability.PER_RUN, "default_check": capability.DEFAULT_CHECK}
        self.capability = self.root / "capability.json"
        self.capability.write_text(json.dumps(self.config))

    def invoke(self, expected, extra=("--check", "compiled"), run="run"):
        command = [sys.executable, "-B", str(TOOLS / "v8_szs/main.py"), str(self.input), "--capability", str(self.capability),
                   "--artifacts", str(self.root / run), *extra]
        result = subprocess.run(command, capture_output=True, timeout=30, env=os.environ | {"PYTHONDONTWRITEBYTECODE": "1"})
        lines = result.stdout.decode().splitlines()
        self.assertTrue(lines[-1].startswith(f"% SZS status {expected} for fang_"), result.stdout + result.stderr)
        self.assertEqual(result.returncode, dict(EXIT, Theorem=0)[expected])
        self.assertNotIn(b"forged", result.stdout)
        if expected != "Unsatisfiable":
            self.assertNotIn(b"Unsatisfiable", result.stdout)
        manifest = self.root / run / "manifest.json"
        return lines, json.loads(manifest.read_text()) if manifest.exists() else None

    def test_accepted_pair_is_unsatisfiable(self):
        _, manifest = self.invoke("Unsatisfiable")
        self.assertTrue(manifest["compiled_check"]["accepted"])
        self.assertEqual((self.root / "run/input.p").read_bytes(), SOURCE)
        self.assertEqual((self.root / "run/proof.fang").read_bytes(), CERTIFICATE)

    def test_producer_outcomes(self):
        for mode, expected in (("unknown", "GaveUp"), ("conjecture", "Inappropriate"), ("invalid", "InputError"),
                               ("limit", "ResourceOut"), ("skolem", "ResourceOut"), ("serialization", "ResourceOut"),
                               ("envelope", "Error"), ("spoof", "Error")):
            with self.subTest(mode=mode):
                self.write_binaries(mode, "accept")
                _, manifest = self.invoke(expected, run="run-" + mode)
                self.assertFalse((self.root / ("run-" + mode) / "checker").exists())
                self.assertNotIn("compiled_check", manifest)

    def test_checker_rejection_is_an_error_not_a_result(self):
        for mode, expected in (("logical", "Error"), ("signature", "Error"), ("certificate", "Error"),
                               ("resource", "ResourceOut")):
            with self.subTest(mode=mode):
                self.write_binaries("candidate", mode)
                _, manifest = self.invoke(expected, run="run-" + mode)
                self.assertFalse(manifest["compiled_check"]["accepted"])

    def test_default_mode_is_compiled_and_named(self):
        lines, manifest = self.invoke("Unsatisfiable", extra=())
        self.assertEqual(lines[1], "% fang: checked by the compiled Lean checker (default mode; compiler and runtime trusted)")
        self.assertEqual((manifest["check"], manifest["check_source"]), ("compiled", "default"))
        self.assertTrue(manifest["compiled_check"]["accepted"])

    def test_explicit_compiled_mode_is_named(self):
        lines, manifest = self.invoke("Unsatisfiable")
        self.assertEqual(lines[1], "% fang: checked by the compiled Lean checker (--check compiled; compiler and runtime trusted)")
        self.assertEqual((manifest["check"], manifest["check_source"]), ("compiled", "explicit"))

    def test_mode_line_on_every_status(self):
        self.write_binaries("unknown", "accept")
        lines, _ = self.invoke("GaveUp", extra=(), run="run-unknown")
        self.assertTrue(lines[1].startswith("% fang: checked by the compiled Lean checker (default mode"))

    def test_kernel_below_minimums_is_refused_naming_them(self):
        flags = ("--wall-seconds", "600", "--memory-mib", "4096", "--max-artifact-bytes", "1073741824")
        for index, extra in enumerate(((), flags[:2], flags[:4], flags[:4] + ("--max-artifact-bytes", "1073741823"))):
            with self.subTest(extra=extra):
                lines, manifest = self.invoke("Inappropriate", extra=("--check", "kernel", *extra), run=f"run-k{index}")
                text = "\n".join(lines)
                self.assertIn("needs at least --wall-seconds 600 --memory-mib 4096 --max-artifact-bytes 1073741824", text)
                self.assertIn("kernel replay requested (--check kernel", lines[1])
                self.assertIsNone(manifest)
                self.assertFalse((self.root / f"run-k{index}").exists())

    def test_kernel_at_minimums_is_not_installed(self):
        lines, manifest = self.invoke("Inappropriate", extra=("--check", "kernel", "--wall-seconds", "600", "--memory-mib",
                                                             "4096", "--max-artifact-bytes", "1073741824"))
        self.assertIn("Kernel replay is not installed", "\n".join(lines))
        self.assertIsNone(manifest)
        self.assertFalse((self.root / "run").exists())

    KERNEL_FLAGS = ("--check", "kernel", "--wall-seconds", "600", "--memory-mib", "4096", "--max-artifact-bytes",
                    "1073741824")

    def write_kernel(self, mode="checked"):
        record = lambda path: {"path": str(path), "sha256": capability.digest(path)}
        witness = self.root / "witness"
        witness.write_text(WITNESS.replace("PYTHON", sys.executable))
        witness.chmod(0o700)
        entry = self.root / "kernel-entry.py"
        entry.write_text(KERNEL_ENTRY.replace("MODE", repr(mode)))
        installation = self.root / "installation.json"
        installation.write_text('{"scope": "synthetic kernel installation"}\n')
        (self.root / "kernel-runs").mkdir(exist_ok=True)
        self.config["kernel"] = {"witness": record(witness), "entry": record(entry), "installation": record(installation),
                                 "output_root": str(self.root / "kernel-runs")}
        self.capability.write_text(json.dumps(self.config))

    def test_kernel_checked_is_the_only_kernel_result(self):
        self.write_kernel()
        lines, manifest = self.invoke("Unsatisfiable", extra=self.KERNEL_FLAGS, run="run-kernel")
        self.assertIn("kernel replay requested (--check kernel", lines[1])
        self.assertTrue(manifest["kernel_check"]["accepted"])
        self.assertNotIn("compiled_check", manifest)
        self.assertFalse((self.root / "run-kernel/checker").exists())
        verified = set(manifest["verified_before_run"])
        self.assertIn(str(self.root / "witness"), verified)
        self.assertIn(str(self.root / "kernel-entry.py"), verified)
        self.assertNotIn(str(self.root / "checker"), verified)

    def test_kernel_runs_with_the_same_run_name(self):
        self.write_kernel()
        outs = []
        for parent in ("first", "second"):
            (self.root / parent).mkdir()
            _, manifest = self.invoke("Unsatisfiable", extra=self.KERNEL_FLAGS, run=parent + "/run")
            outs.append(manifest["kernel_check"]["out"])
        self.assertEqual(len(set(outs)), 2)
        self.assertTrue(all(Path(out).parent == self.root / "kernel-runs" for out in outs))

    def test_kernel_non_results(self):
        for mode, expected in (("review-pending", "Error"), ("rejected", "Error"), ("timeout", "Timeout"),
                               ("resource", "ResourceOut"), ("forced", "Error"), ("lying", "Error")):
            with self.subTest(mode=mode):
                self.write_kernel(mode)
                _, manifest = self.invoke(expected, extra=self.KERNEL_FLAGS, run="run-kernel-" + mode)
                self.assertNotIn("accepted", manifest["kernel_check"])

    def test_kernel_refuses_bundles_and_tstp(self):
        self.write_kernel()
        lines, _ = self.invoke("Inappropriate", extra=self.KERNEL_FLAGS + ("--output", "tstp"), run="run-kernel-tstp")
        self.assertIn("not available with --check kernel", "\n".join(lines))
        self.write_bundle()
        self.write_kernel()
        lines, _ = self.invoke("Inappropriate", extra=self.KERNEL_FLAGS, run="run-kernel-bundle")
        self.assertIn("Kernel replay covers single-file", "\n".join(lines))

    def test_capability_records_default_mode(self):
        for value in (None, "kernel"):
            with self.subTest(value=value):
                config = dict(self.config)
                if value is None:
                    del config["default_check"]
                else:
                    config["default_check"] = value
                with self.assertRaises(ValueError):
                    capability.check_fields(config)
        capability.check_fields(self.config)

    def test_help_states_default_and_trust(self):
        result = subprocess.run([sys.executable, "-B", str(TOOLS / "v8_szs/main.py"), "--help"], capture_output=True, timeout=30)
        self.assertEqual(result.returncode, 0)
        text = " ".join(result.stdout.decode().split())
        self.assertIn("default: compiled, which trusts the Lean compiler and runtime", text)
        self.assertIn("the default check is compiled", text)

    def test_tstp_rejected_before_search(self):
        lines, manifest = self.invoke("Inappropriate", extra=("--check", "compiled", "--output", "tstp"))
        self.assertIn("--output status", "\n".join(lines))
        self.assertIn("single file", lines[0])
        self.assertEqual(manifest["path"], "single")
        self.assertFalse((self.root / "run/search").exists())

    def write_bundle(self, producer_mode="candidate", checker_mode="accept", tptp=False):
        self.input.write_bytes(b"include('ax.ax'). fof(a,axiom,\"x\" = \"y\").")
        (self.root / "ax.ax").write_bytes(b"fof(b,axiom,$false).")
        contents = [self.input.read_bytes(), (self.root / "ax.ax").read_bytes()]
        if tptp:
            (self.root / "tptp/Axioms").mkdir(parents=True)
            (self.root / "tptp/Axioms/eq.ax").write_bytes(b"fof(e,axiom,![X]:(X = X)).")
            contents.append((self.root / "tptp/Axioms/eq.ax").read_bytes())
        record = lambda path: {"path": str(path), "sha256": capability.digest(path)}
        for name, template, mode in (("bundle-producer", BUNDLE_PRODUCER, producer_mode),
                                     ("bundle-checker", BUNDLE_CHECKER, checker_mode)):
            text = (template.replace("PYTHON", sys.executable).replace("MODE", repr(mode))
                    .replace("BUNDLE_ACCEPTED", repr(bundle.ACCEPTED)).replace("EXPECTED", repr(contents))
                    .replace("CERTIFICATE", repr(CERTIFICATE)))
            (self.root / name).write_text(text)
            (self.root / name).chmod(0o700)
        self.config["bundle"] = {"producer": record(self.root / "bundle-producer"),
                                 "checker": record(self.root / "bundle-checker")}
        self.capability.write_text(json.dumps(self.config))
        return contents

    def write_signed(self, producer_mode="candidate", checker_mode="two-goals", single=False):
        if single:
            self.input.write_bytes(SINGLE_SIGNED)
            order, contents = [("base", "problem.p")], [SINGLE_SIGNED]
        else:
            self.input.write_bytes(b"% signed task\ninclude('ax.ax'). fof(g,conjecture,q).")
            (self.root / "sub").mkdir(exist_ok=True)
            (self.root / "ax.ax").write_bytes(b"include('sub/b.ax'). fof(a,axiom,p).")
            (self.root / "sub/b.ax").write_bytes(b"fof(b,axiom,p => q).")
            order = [("base", "problem.p"), ("base", "ax.ax"), ("base", "sub/b.ax")]
            contents = [self.input.read_bytes(), (self.root / "ax.ax").read_bytes(), (self.root / "sub/b.ax").read_bytes()]
        record = lambda path: {"path": str(path), "sha256": capability.digest(path)}
        for name, template, mode in (("signed-producer", SIGNED_PRODUCER, producer_mode),
                                     ("signed-checker", SIGNED_CHECKER, checker_mode)):
            text = (template.replace("PYTHON", sys.executable).replace("MODE", repr(mode))
                    .replace("ORDER", repr(order)).replace("EXPECTED", repr(contents))
                    .replace("CERTIFICATE", repr(CERTIFICATE)))
            (self.root / name).write_text(text)
            (self.root / name).chmod(0o700)
        self.config["signed"] = {"producer": record(self.root / "signed-producer"),
                                 "checker": record(self.root / "signed-checker")}
        self.capability.write_text(json.dumps(self.config))

    def test_signed_theorem_needs_every_listed_goal(self):
        self.write_signed()
        lines, manifest = self.invoke("Theorem", run="run-theorem")
        self.assertIn("signed bundle", lines[0])
        self.assertEqual(manifest["path"], "signed")
        self.assertEqual(manifest["signed"]["listing"], [[0, 1], [1, 0]])
        self.assertEqual([task["task"] for task in manifest["signed"]["tasks"]], ["goal-0", "goal-1"])
        self.assertEqual([(row["root"], row["path"]) for row in manifest["signed"]["files"]],
                         [("base", "problem.p"), ("base", "ax.ax"), ("base", "sub/b.ax")])
        for producer_mode, checker_mode, expected in (("unknown-goal-1", "two-goals", "GaveUp"),
                                                      ("candidate", "wrong-item", "Error"),
                                                      ("candidate", "unsupported", "Inappropriate")):
            with self.subTest(producer=producer_mode, checker=checker_mode):
                self.write_signed(producer_mode, checker_mode)
                self.invoke(expected, run="run-" + producer_mode + "-" + checker_mode)

    def test_signed_inputs_without_goals_is_unsatisfiable(self):
        self.write_signed(checker_mode="no-goals")
        _, manifest = self.invoke("Unsatisfiable", run="run-inputs")
        self.assertEqual([task["task"] for task in manifest["signed"]["tasks"]], ["inputs"])

    def test_signed_tstp_and_missing_capability(self):
        self.write_signed()
        lines, _ = self.invoke("Inappropriate", extra=("--check", "compiled", "--output", "tstp"), run="run-tstp")
        self.assertIn("conjectures or other non-axiom roles", "\n".join(lines))
        self.config["signed"] = None
        self.capability.write_text(json.dumps(self.config))
        lines, _ = self.invoke("Inappropriate", run="run-none")
        self.assertIn("not installed", "\n".join(lines))

    def write_goal_exporter(self, mode="document"):
        self.write_exporter()
        text = (GOAL_EXPORTER.replace("PYTHON", sys.executable).replace("MODE", repr(mode))
                .replace("CERTIFICATE", repr(CERTIFICATE)).replace("SINGLE", repr(SINGLE_SIGNED)))
        path = self.root / "goal-exporter"
        path.write_text(text)
        path.chmod(0o700)
        self.config["tstp"]["goal_exporter"] = {"path": str(path), "sha256": capability.digest(path)}
        self.capability.write_text(json.dumps(self.config))

    def test_goal_tstp_document_after_every_goal_is_accepted(self):
        self.write_signed(checker_mode="one-goal", single=True)
        self.write_goal_exporter()
        result, lines, manifest = self.run_bundle_tstp("run-goal-tstp")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("signed", lines[0])
        self.assertTrue(lines[2].startswith("% SZS status Theorem for fang_"))
        self.assertEqual(lines[3], "% SZS output start CNFRefutation for problem.p")
        self.assertEqual(lines[4], "fof(g0,negated_conjecture,~p,inference(negate,[status(cth)],[g])).")
        self.assertEqual(lines[-1], "% SZS output end CNFRefutation for problem.p")
        self.assertEqual(result.stderr, b"")
        self.assertEqual(manifest["export"]["state"], "documents")
        stages = [row["stage"] for row in manifest["processes"]]
        self.assertLess(stages.index("check-goal-0"), stages.index("export-goal-0"))
        self.assertIn(str(self.root / "goal-exporter"), manifest["verified_before_run"])
        self.assertEqual(capability.run_records(self.config, "signed", tstp=True)[-1]["path"], str(self.root / "goal-exporter"))

    def test_goal_tstp_one_document_per_conjecture(self):
        self.write_signed(single=True)
        self.write_goal_exporter()
        result, lines, manifest = self.run_bundle_tstp("run-goal-tstp-two")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(lines[2].startswith("% SZS status Theorem for fang_"))
        self.assertEqual(lines[3:], ["% SZS output start CNFRefutation for problem.p",
                                     "fof(g0,negated_conjecture,~p,inference(negate,[status(cth)],[g])).",
                                     "% SZS output end CNFRefutation for problem.p",
                                     "% SZS output start CNFRefutation for problem.p",
                                     "fof(g1,negated_conjecture,~p,inference(negate,[status(cth)],[g])).",
                                     "% SZS output end CNFRefutation for problem.p"])
        self.assertEqual([row["goal"] for row in manifest["export"]["documents"]], [0, 1])
        stages = [row["stage"] for row in manifest["processes"]]
        self.assertLess(stages.index("check-goal-1"), stages.index("export-goal-0"))

    def test_goal_tstp_failure_or_scope_keeps_theorem(self):
        self.write_signed(checker_mode="one-goal", single=True)
        self.write_goal_exporter("export-error")
        result, _, manifest = self.run_bundle_tstp("run-goal-tstp-error")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(b"% SZS status Theorem for fang_", result.stdout)
        self.assertNotIn(b"SZS output start", result.stdout)
        self.assertEqual(len(result.stderr.splitlines()), 1)
        self.assertTrue(result.stderr.startswith(b"fang: TSTP export failed"))
        self.assertEqual(manifest["export"]["state"], "failed")
        # Two goals over an include bundle: the status stands, the exporter does not run, one line says why.
        self.write_signed()
        self.write_goal_exporter()
        result, _, manifest = self.run_bundle_tstp("run-goal-tstp-scope")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(b"% SZS status Theorem for fang_", result.stdout)
        self.assertNotIn(b"SZS output start", result.stdout)
        self.assertEqual(len(result.stderr.splitlines()), 1)
        self.assertTrue(result.stderr.startswith(b"fang: TSTP output for inputs with conjectures covers proved conjectures"))
        self.assertEqual(manifest["export"]["state"], "not-covered")
        self.assertFalse((self.root / "run-goal-tstp-scope/export").exists())

    def test_tstp_capability_fields(self):
        self.write_exporter()
        for extra in ((), ("bundle_exporter",), ("goal_exporter",), ("bundle_exporter", "goal_exporter")):
            tstp = dict(self.config["tstp"], **{name: self.config["tstp"]["exporter"] for name in extra})
            capability.check_fields(dict(self.config, tstp=tstp))
        for wrong in ({"goal_exporter": self.config["tstp"]["exporter"]}, dict(self.config["tstp"], other={})):
            with self.assertRaises(ValueError):
                capability.check_fields(dict(self.config, tstp=wrong))

    def write_exporter(self, mode="document"):
        text = EXPORTER.replace("PYTHON", sys.executable).replace("MODE", repr(mode))
        (self.root / "exporter").write_text(text)
        (self.root / "exporter").chmod(0o700)
        record = lambda path: {"path": str(path), "sha256": capability.digest(path)}
        self.config["tstp"] = {"exporter": record(self.root / "exporter")}
        self.capability.write_text(json.dumps(self.config))

    def test_run_hashes_only_its_path_and_self_check_hashes_everything(self):
        self.write_bundle()
        self.input.write_bytes(SOURCE)
        with (self.root / "bundle-checker").open("a") as stream:
            stream.write("# changed after installation\n")
        _, manifest = self.invoke("Unsatisfiable", run="run-single")
        verified = set(manifest["verified_before_run"])
        self.assertIn(str(self.root / "engine"), verified)
        self.assertIn(str(self.root / "checker"), verified)
        self.assertNotIn(str(self.root / "bundle-checker"), verified)
        self.assertNotIn(str(self.root / "receipt.json"), verified)
        check = subprocess.run([sys.executable, "-B", str(TOOLS / "v8_szs/main.py"), "--capability", str(self.capability),
                                "--self-check"], capture_output=True, timeout=60)
        self.assertEqual(check.returncode, 6)
        self.assertIn(b"self-check failed", check.stdout)
        self.input.write_bytes(b"include('ax.ax'). fof(a,axiom,\"x\" = \"y\").")
        self.invoke("Error", run="run-bundle")

    def test_self_check_passes_on_an_unchanged_installation(self):
        check = subprocess.run([sys.executable, "-B", str(TOOLS / "v8_szs/main.py"), "--capability", str(self.capability),
                                "--self-check"], capture_output=True, timeout=60)
        self.assertEqual(check.returncode, 0, check.stdout)
        self.assertIn(b"match the installation", check.stdout)

    def test_identity_check_sees_a_rewrite_that_restores_mtime(self):
        path = self.root / "identity-control"
        path.write_bytes(b"original")
        identities = {str(path): capability.identity(os.stat(path))}
        capability.check_identities(identities)
        before = os.stat(path)
        time.sleep(0.02)
        path.write_bytes(b"replaced")
        os.utime(path, ns=(before.st_atime_ns, before.st_mtime_ns))
        with self.assertRaises(ValueError):
            capability.check_identities(identities)

    def test_tstp_document_after_acceptance(self):
        self.write_exporter()
        command = [sys.executable, "-B", str(TOOLS / "v8_szs/main.py"), str(self.input), "--capability", str(self.capability),
                   "--artifacts", str(self.root / "run"), "--check", "compiled", "--output", "tstp"]
        result = subprocess.run(command, capture_output=True, timeout=30)
        lines = result.stdout.decode().splitlines()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(lines[1].startswith("% fang: checked by the compiled Lean checker (--check compiled"))
        self.assertTrue(lines[2].startswith("% SZS status Unsatisfiable for fang_"))
        self.assertEqual(lines[3], "% SZS output start CNFRefutation for problem.p")
        self.assertEqual(lines[4], "cnf(a,axiom,($false),file('problem.p',a)).")
        self.assertEqual(lines[-1], "% SZS output end CNFRefutation for problem.p")
        self.assertEqual(result.stderr, b"")
        manifest = json.loads((self.root / "run/manifest.json").read_text())
        self.assertEqual(manifest["export"]["state"], "document")
        self.assertLess(manifest["processes"].index(next(row for row in manifest["processes"] if row["stage"] == "checker")),
                        manifest["processes"].index(next(row for row in manifest["processes"] if row["stage"] == "export")))

    def test_tstp_failure_keeps_unsatisfiable_without_document(self):
        for mode, extra in (("export-error", ()), ("bad", ()), ("slow", ("--wall-seconds", "3"))):
            with self.subTest(mode=mode):
                self.write_exporter(mode)
                run = self.root / ("run-" + mode)
                command = [sys.executable, "-B", str(TOOLS / "v8_szs/main.py"), str(self.input), "--capability",
                           str(self.capability), "--artifacts", str(run), "--check", "compiled", "--output", "tstp", *extra]
                result = subprocess.run(command, capture_output=True, timeout=30)
                self.assertEqual(result.returncode, 0, result.stderr)
                self.assertIn(b"% SZS status Unsatisfiable for fang_", result.stdout)
                self.assertNotIn(b"SZS output start", result.stdout)
                self.assertEqual(len(result.stderr.splitlines()), 1)
                self.assertTrue(result.stderr.startswith(b"fang: TSTP export"))

    def test_tstp_not_run_without_acceptance(self):
        self.write_exporter()
        self.write_binaries("candidate", "logical")
        self.write_exporter()
        _, manifest = self.invoke("Error", extra=("--check", "compiled", "--output", "tstp"), run="run-rejected")
        self.assertNotIn("export", manifest)
        self.assertFalse((self.root / "run-rejected/export").exists())

    def test_bundle_path_passes_every_file_it_hashed(self):
        contents = self.write_bundle(tptp=True)
        lines, manifest = self.invoke("Unsatisfiable", extra=("--check", "compiled", "--tptp-root", str(self.root / "tptp")))
        self.assertIn("bundle", lines[0])
        self.assertEqual(manifest["path"], "bundle")
        files = manifest["bundle"]["files"]
        self.assertEqual([(row["root"], row["path"]) for row in files],
                         [("base", "problem.p"), ("base", "ax.ax"), ("tptp", "Axioms/eq.ax")])
        self.assertEqual([row["sha256"] for row in files], [bundle_sha(data) for data in contents])
        self.assertEqual(manifest["compiled_check"]["checker"], "bundle")

    def test_bundle_outcomes(self):
        for producer_mode, checker_mode, expected in (("missing", "accept", "InputError"), ("limit", "accept", "ResourceOut"),
                                                      ("candidate", "reject", "Error")):
            with self.subTest(producer=producer_mode, checker=checker_mode):
                self.write_bundle(producer_mode, checker_mode)
                self.invoke(expected, run="run-" + producer_mode + "-" + checker_mode)

    def test_bundle_tstp_and_missing_bundle_capability(self):
        self.write_bundle()
        lines, _ = self.invoke("Inappropriate", extra=("--check", "compiled", "--output", "tstp"), run="run-tstp")
        self.assertIn("bundle exporter, which is not installed", "\n".join(lines))
        self.config["bundle"] = None
        self.capability.write_text(json.dumps(self.config))
        lines, manifest = self.invoke("Inappropriate", run="run-none")
        self.assertIn("not installed", "\n".join(lines))
        self.assertFalse((self.root / "run-none/search").exists())

    def write_bundle_exporter(self, mode="document"):
        self.write_exporter()
        text = (BUNDLE_EXPORTER.replace("PYTHON", sys.executable).replace("MODE", repr(mode))
                .replace("CERTIFICATE", repr(CERTIFICATE)))
        path = self.root / "bundle-exporter"
        path.write_text(text)
        path.chmod(0o700)
        self.config["tstp"]["bundle_exporter"] = {"path": str(path), "sha256": capability.digest(path)}
        self.capability.write_text(json.dumps(self.config))

    def run_bundle_tstp(self, run):
        command = [sys.executable, "-B", str(TOOLS / "v8_szs/main.py"), str(self.input), "--capability", str(self.capability),
                   "--artifacts", str(self.root / run), "--output", "tstp"]
        result = subprocess.run(command, capture_output=True, timeout=60)
        manifest = json.loads((self.root / run / "manifest.json").read_text())
        return result, result.stdout.decode().splitlines(), manifest

    def test_bundle_tstp_document_after_acceptance(self):
        self.write_bundle()
        self.write_bundle_exporter()
        result, lines, manifest = self.run_bundle_tstp("run-bundle-tstp")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("bundle", lines[0])
        self.assertTrue(lines[2].startswith("% SZS status Unsatisfiable for fang_"))
        self.assertEqual(lines[3], "% SZS output start CNFRefutation for problem.p")
        self.assertEqual(lines[4], "fof(b,axiom,$false,file('ax.ax',b)).")
        self.assertEqual(lines[-1], "% SZS output end CNFRefutation for problem.p")
        self.assertEqual(result.stderr, b"")
        self.assertEqual(manifest["export"]["state"], "document")
        stages = [row["stage"] for row in manifest["processes"]]
        self.assertLess(stages.index("checker"), stages.index("export"))
        self.assertIn(str(self.root / "bundle-exporter"), manifest["verified_before_run"])

    def test_bundle_tstp_failure_keeps_unsatisfiable(self):
        self.write_bundle()
        self.write_bundle_exporter("export-error")
        result, lines, manifest = self.run_bundle_tstp("run-bundle-tstp-error")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(b"% SZS status Unsatisfiable for fang_", result.stdout)
        self.assertNotIn(b"SZS output start", result.stdout)
        self.assertEqual(len(result.stderr.splitlines()), 1)
        self.assertTrue(result.stderr.startswith(b"fang: TSTP export"))
        self.assertEqual(manifest["export"]["state"], "failed")

    def test_bundle_tstp_not_run_without_acceptance(self):
        self.write_bundle(checker_mode="reject")
        self.write_bundle_exporter()
        result, _, manifest = self.run_bundle_tstp("run-bundle-tstp-rejected")
        self.assertEqual(result.returncode, 6)
        self.assertNotIn("export", manifest)
        self.assertFalse((self.root / "run-bundle-tstp-rejected/export").exists())

    def test_annotated_plain_file_routes_to_the_bundle_path(self):
        self.assertTrue(bundle.needs_bundle(b"fof(a,axiom,p,file('x.p',a)). fof(b,axiom,~p)."))
        self.assertTrue(bundle.needs_bundle(b"cnf(a,axiom,p,inference(r,[status(thm)],[b]),[useful])."))
        self.assertFalse(bundle.needs_bundle(b"fof(a,axiom,![X,Y]:(p(X,Y) | q(f(X,Y)))). cnf(b,axiom,(p(a,b)))."))
        self.assertFalse(bundle.needs_bundle(b"% fof(a,axiom,p,file('x',a)).\nfof(b,axiom,p)."))

    def test_changed_engine_pin_is_an_error(self):
        with (self.root / "engine").open("a") as stream:
            stream.write("# changed\n")
        _, manifest = self.invoke("Error")
        self.assertNotIn("producer_outcome", manifest)

    def test_installed_optional_feature_is_refused(self):
        self.config["kernel"] = {"profile": "future"}
        self.capability.write_text(json.dumps(self.config))
        self.invoke("Error")

    def test_input_limit(self):
        self.invoke("ResourceOut", extra=("--check", "compiled", "--max-input-bytes", "4"))

    def test_existing_artifacts_directory_untouched(self):
        (self.root / "run").mkdir()
        (self.root / "run/sentinel").write_bytes(b"keep")
        self.invoke("Error")
        self.assertEqual(sorted(path.name for path in (self.root / "run").iterdir()), ["sentinel"])


def bundle_sha(data):
    return __import__("hashlib").sha256(data).hexdigest()


class BundleProtocolTests(unittest.TestCase):
    def test_routing_test(self):
        for data, expected in ((b"fof(a,axiom,p).", False), (b"fof(a,axiom,p(\"x\")).", True),
                               (b"include('ax.ax').", True), (b"include ('ax.ax').", True),
                               (b"fof(include_x,axiom,p).", False), (b"% a comment with \" in it\nfof(a,axiom,p).", True)):
            self.assertEqual(bundle.needs_bundle(data), expected, data)

    def test_producer_contracts(self):
        info = b'{"bundle_sha256":"' + b"a" * 64 + b'","files":[["base","top.p"],["tptp","Axioms/eq.ax"]],"declarations":2,"objects":1}\n'
        self.assertEqual(bundle.producer_outcome(exited(0), CERTIFICATE, info + bundle.CANDIDATE)[0], "candidate")
        self.assertEqual(bundle.producer_outcome(exited(2), b"", info + b"unknown: processed=1 attempted=2\n")[0], "GaveUp")
        for line, expected in ((b"capture: InvalidInput Missing file=Some(0) offset=Some(8)\n", "InputError"),
                               (b"capture: InvalidInput Cycle file=Some(1) offset=Some(8)\n", "InputError"),
                               (b"capture: ResourceLimit Limit file=Some(0) offset=None\n", "ResourceOut"),
                               (b"capture: Unsupported Number file=Some(0) offset=Some(3)\n", "Inappropriate"),
                               (b'adapter: Input(Error { kind: Unsupported, offset: Some(6), message: "only the axiom role is supported" })\n', "Inappropriate")):
            self.assertEqual(bundle.producer_outcome(exited(3), b"", line)[0], expected)
        bad_paths = (b'[["base","top.p"],["base","../x.ax"]]', b'[["tptp","top.p"]]', b'[["base","d/top.p"]]',
                     b'[["base","top.p"],["base","top.p"]]', b'[]')
        for files in bad_paths:
            line = b'{"bundle_sha256":"' + b"a" * 64 + b'","files":' + files + b',"declarations":1,"objects":0}\n'
            with self.subTest(files=files), self.assertRaises(ValueError):
                bundle.producer_outcome(exited(0), CERTIFICATE, line + bundle.CANDIDATE)
        for code, out, err in ((0, CERTIFICATE, bundle.CANDIDATE), (3, b"", b"capture: Weird Missing file=None offset=None\n"),
                               (5, b"", b"render: failed\n"), (64, b"", b"usage\n")):
            with self.assertRaises(ValueError):
                bundle.producer_outcome(exited(code), out, err)

    def test_checker_contracts(self):
        self.assertEqual(bundle.checker_outcome(exited(0), bundle.ACCEPTED, b""), "accepted")
        self.assertEqual(bundle.checker_outcome(exited(4), b"", b"resource.bundle.frame:12\n"), "resource")
        self.assertEqual(bundle.checker_outcome(exited(2), b"", b"bundle.include.missing\n"), "input-or-bundle-rejection")
        self.assertEqual(bundle.checker_outcome(exited(1), b"", b"logical-rejection: Fang.Equality.TraceError.finalNotEmpty\n"),
                         "logical-rejection")
        for code, out, err in ((0, protocol.ACCEPTED, b""), (0, bundle.ACCEPTED, b"x\n"), (64, b"", b"usage: x\n"),
                               (4, b"", b"bundle.shape\n")):
            with self.assertRaises(ValueError):
                bundle.checker_outcome(exited(code), out, err)

    def test_digest_and_locations(self):
        top = b"include('c1.ax'). fof(t,axiom,~s(a)).\n"
        c1 = b"fof(u,axiom,![X]:(m(X) => s(X))).\nfof(v,axiom,m(a)).\n"
        self.assertEqual(bundle.digest([("base", "top.p", top), ("base", "c1.ax", c1)]),
                         "b60f7c0988fa49b94318e667f054b21df39d9f3ef839486c618978cb237d1a50")
        info = {"files": [["base", "top.p"], ["tptp", "Axioms/eq.ax"]]}
        places = bundle.locate(info, Path("/work/case/top.p"), Path("/tptp"))
        self.assertEqual([str(place) for _, _, place in places], ["/work/case/top.p", "/tptp/Axioms/eq.ax"])
        with self.assertRaises(ValueError):
            bundle.locate(info, Path("/work/case/top.p"), None)
        with self.assertRaises(ValueError):
            bundle.locate(info, Path("/work/case/other.p"), Path("/tptp"))


class SignedProtocolTests(unittest.TestCase):
    def test_statements_and_roles(self):
        data = (b"% fof(x,conjecture,p).\n/* include('no.ax'). */ fof('a, b', axiom, p(\"o,\")). "
                b"cnf(c , negated_conjecture , ~p). include('d/e.ax', [a]). fof(1,axiom,(q)).")
        found = signed.statements(data)
        self.assertEqual([statement.keyword for statement in found], [b"fof", b"cnf", b"include", b"fof"])
        self.assertEqual([statement.role for statement in found], ["axiom", "negated_conjecture", None, "axiom"])
        self.assertEqual(found[2].include, "d/e.ax")
        self.assertEqual(len(signed.statements(b"fof(a,axiom,p). garbage ( fof(b,conjecture,q).")), 1)
        for path, expected in (("a/b.ax", ["a", "b.ax"]), ("/a", None), ("a/../b", None), ("a//b", None), ("a:b", None)):
            self.assertEqual(signed.components(path), expected)

    def test_discovery_order_and_resolution(self):
        with tempfile.TemporaryDirectory(prefix="fang-signed-discovery-") as temporary:
            base, tptp = Path(temporary) / "base", Path(temporary) / "tptp"
            (base / "sub").mkdir(parents=True)
            (tptp / "Axioms").mkdir(parents=True)
            files = {base / "top.p": b"include('sub/a.ax'). include('Axioms/t.ax'). include('z.ax').",
                     base / "sub/a.ax": b"include('b.ax'). include('sub/a.ax').",
                     base / "sub/b.ax": b"fof(b,axiom,p).", base / "z.ax": b"include('sub/b.ax').",
                     tptp / "Axioms/t.ax": b"fof(t,axiom,q).", tptp / "sub/a.ax": b"fof(unused,axiom,r)."}
            (tptp / "sub").mkdir()
            for path, data in files.items():
                path.write_bytes(data)
            found = signed.discover("top.p", files[base / "top.p"], base, tptp, lambda path: path.read_bytes())
            self.assertEqual([(root, path) for root, path, _, _ in found],
                             [("base", "top.p"), ("base", "sub/a.ax"), ("base", "sub/b.ax"), ("tptp", "sub/a.ax"),
                              ("tptp", "Axioms/t.ax"), ("base", "z.ax")])
            cycle = signed.discover("top.p", b"include('top.p').", base, None, lambda path: path.read_bytes())
            self.assertEqual([(root, path) for root, path, _, _ in cycle], [("base", "top.p")])
            missing = signed.discover("top.p", b"include('none.ax'). include('z.ax').", base, None,
                                      lambda path: path.read_bytes())
            self.assertEqual(len(missing), 1)

    def test_route(self):
        plain = [("base", "top.p", None, b"fof(a,axiom,p).")]
        self.assertEqual(signed.route(plain, False), "single")
        self.assertEqual(signed.route(plain, True), "bundle")
        self.assertEqual(signed.route(plain + [("base", "x.ax", None, b"fof(b,axiom,q).")], False), "bundle")
        for role in (b"conjecture", b"negated_conjecture", b"hypothesis", b"assumption"):
            self.assertEqual(signed.route([("base", "top.p", None, b"fof(a," + role + b",p).")], False), "signed")
        self.assertEqual(signed.route(plain + [("base", "x.ax", None, b"fof(g,conjecture,q).")], True), "signed")

    def test_checker_and_producer_contracts(self):
        self.assertEqual(signed.listing(exited(0), b"goals 2\ngoal 0 item 0 1\ngoal 1 item 1 0\n", b""),
                         ("listed", [(0, 1), (1, 0)]))
        self.assertEqual(signed.listing(exited(0), b"goals 0\n", b""), ("listed", []))
        for code, err, status in ((2, b"bundle.frame.unsupported:5\n", "Inappropriate"), (2, b"bundle.frame.invalid:5\n", "InputError"),
                                  (2, b"bundle.include.missing\n", "InputError"), (2, b"bundle.shape\n", "Error"),
                                  (2, b"bundle.mixed-goal-modes\n", "Inappropriate"),
                                  (4, b"resource.bundle.frame:3\n", "ResourceOut")):
            self.assertEqual(signed.listing(exited(code), b"", err), (status, None))
        for out in (b"goals 2\ngoal 0 item 0 1\n", b"goals 1\ngoal 1 item 0 1\n", b"goal 0 item 0 1\n"):
            with self.assertRaises(ValueError):
                signed.listing(exited(0), out, b"")
        line = b"accepted-goal 1 item 2 3 (native checker; compiler/runtime trusted)\n"
        self.assertEqual(signed.accepted(exited(0), line, b"", 1), (2, 3))
        self.assertEqual(signed.accepted(exited(0), signed.INPUTS, b"", "inputs"), True)
        self.assertIsNone(signed.accepted(exited(1), b"", b"logical-rejection: x\n", 0))
        for out, task in ((line, 0), (signed.INPUTS, 0), (line, "inputs")):
            with self.assertRaises(ValueError):
                signed.accepted(exited(0), out, b"", task)
        self.assertEqual(signed.rejection(2, b"", b"bundle.frame.unsupported:5\n"), "Error")
        self.assertEqual(signed.rejection(2, b"", b"bundle.mixed-goal-modes\n"), "Error")
        self.assertEqual(signed.producer_outcome(exited(0), CERTIFICATE, signed.CANDIDATE), "candidate")
        self.assertEqual(signed.producer_outcome(exited(2), b"", b"unknown: processed=1 attempted=1\n"), "GaveUp")
        self.assertEqual(signed.producer_outcome(exited(1), b"", b"error: resource Expansion(x)\n"), "ResourceOut")
        self.assertEqual(signed.producer_outcome(exited(1), b"", b"error: skolem Skolem(Resource(Functions))\n"), "ResourceOut")
        self.assertEqual(signed.producer_outcome(exited(1), b"", b"error: frame Role { offset: 3 }\n"), "Error")
        self.assertEqual(signed.producer_outcome(exited(1), b"", b"error: modes Modes\n"), "Inappropriate")

    def test_final_status_rules(self):
        listed = [(0, 1), (1, 0)]
        self.assertEqual(signed.final_status(listed, [(0, 1), (1, 0)]), "Theorem")
        self.assertEqual(signed.final_status(listed, [(0, 1), "GaveUp"]), "GaveUp")
        self.assertEqual(signed.final_status(listed, [(0, 1)]), "Error")
        self.assertEqual(signed.final_status(listed, [(0, 1), (0, 1)]), "Error")
        self.assertEqual(signed.final_status([], [True]), "Unsatisfiable")
        self.assertEqual(signed.final_status([], ["ResourceOut"]), "ResourceOut")
        self.assertEqual(signed.final_status([], [(0, 1)]), "Error")
        statuses = {signed.final_status(listed, outcome) for outcome in ([], [(0, 1)], [(0, 1), (1, 0)], ["Error"])}
        self.assertFalse(statuses & {"Satisfiable", "CounterSatisfiable"})


class RouterTests(unittest.TestCase):
    def test_profile_selection(self):
        self.assertEqual(fang_router.selected_profile(["p.p", "--check", "compiled"]), ("v8", ["p.p", "--check", "compiled"]))
        self.assertEqual(fang_router.selected_profile(["--profile", "cnf", "p.p"]), ("cnf", ["p.p"]))
        self.assertEqual(fang_router.selected_profile(["p.p", "--profile=ground-fof"]), ("ground-fof", ["p.p"]))
        self.assertEqual(fang_router.selected_profile(["--", "--profile", "cnf"]), ("v8", ["--", "--profile", "cnf"]))
        for argv in (["--profile", "v7"], ["--profile"], ["--profile", "v8", "--profile=cnf"]):
            with self.subTest(argv=argv), self.assertRaises(ValueError):
                fang_router.selected_profile(argv)

    @unittest.skipUnless(sys.platform == "linux", "Linux/WSL process controls")
    def test_launcher_runs_exactly_one_profile(self):
        with tempfile.TemporaryDirectory(prefix="fang-router-control-") as temporary:
            root = Path(temporary)
            echo = [sys.executable, "-c", "import json,sys; print(json.dumps(sys.argv[1:]))"]
            command = root / "command.json"
            command.write_text(json.dumps({"schema": "fang-command-v1",
                                           "profiles": {"v8": echo + ["v8"], "cnf": echo + ["cnf"]}}))
            router = [sys.executable, "-B", str(TOOLS / "fang_router.py"), "--command", str(command)]
            run = lambda *argv: subprocess.run(router + list(argv), capture_output=True, timeout=30)
            self.assertEqual(json.loads(run("p.p", "--check", "compiled").stdout), ["v8", "p.p", "--check", "compiled"])
            self.assertEqual(json.loads(run("--profile", "cnf", "p.p").stdout), ["cnf", "p.p"])
            self.assertEqual(json.loads(run("help").stdout), ["v8", "--help"])
            missing = run("--profile", "ground-fof", "p.p")
            self.assertEqual(missing.returncode, 6)
            self.assertIn(b"not installed here; no other profile was run", missing.stderr)
            self.assertEqual(missing.stdout, b"")
            self.assertEqual(run("--profile", "v7", "p.p").returncode, 6)

    def test_provision_v8_never_replaces_and_links_older_profiles(self):
        with tempfile.TemporaryDirectory(prefix="fang-provision-control-") as temporary:
            root = Path(temporary) / "install"
            (root / "bin").mkdir(parents=True)
            with self.assertRaisesRegex(ValueError, "must be installed"):
                cli_setup.provision_v8(root)
            (root / "v8-capability.json").write_text("{}\n")
            older = Path(temporary) / "older"
            (older / "source/tools/fof_szs").mkdir(parents=True)
            (older / "installation.json").write_text("{}\n")
            with self.assertRaisesRegex(ValueError, "ground-fof"):
                cli_setup.provision_v8(root, older=older)
            (older / "fof-capability.json").write_text("{}\n")
            launcher = cli_setup.provision_v8(root, older=older)
            profiles = json.loads((root / "command.json").read_text())["profiles"]
            self.assertEqual(sorted(profiles), ["cnf", "ground-fof", "v8"])
            self.assertIn(str(older / "installation.json"), profiles["cnf"])
            self.assertIn("fang_router", launcher.read_text())
            with self.assertRaises(FileExistsError):
                cli_setup.provision_v8(root)


class SourceMapTests(unittest.TestCase):
    def test_product_tree_matches_the_maps(self):
        rust_map = v8_dependencies.load_map(ROOT, v8_dependencies.RUST_MAP, v8_dependencies.RUST_SCHEMA)
        targets = {rewrite["target"] for entry in rust_map["files"].values() for rewrite in entry.get("include_rewrites", [])}
        self.assertEqual(len(v8_dependencies.rust_files(ROOT)),
                         len(rust_map["files"]) + len(rust_map.get("data_files", {})) + len(targets))
        self.assertEqual(len(v8_dependencies.lean_files(ROOT)), len(v8_dependencies.load_map(
            ROOT, v8_dependencies.LEAN_MAP, v8_dependencies.LEAN_SCHEMA)["files"]))

    def test_changed_moved_file_is_rejected(self):
        source_map = v8_dependencies.load_map(ROOT, v8_dependencies.RUST_MAP, v8_dependencies.RUST_SCHEMA)
        with tempfile.TemporaryDirectory(prefix="fang-source-map-control-") as temporary:
            copy = Path(temporary)
            data = source_map.get("data_files", {})
            includes = [(name, rewrite) for name, entry in source_map["files"].items()
                        for rewrite in entry.get("include_rewrites", [])]
            for relative in [*source_map["files"], *source_map["path_targets"], v8_dependencies.RUST_MAP, *data,
                             *[entry["same_as"] for entry in data.values() if "same_as" in entry],
                             *[rewrite["target"] for _, rewrite in includes]]:
                (copy / relative).parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / relative, copy / relative)
            targets = {rewrite["target"] for _, rewrite in includes}
            self.assertEqual(len(v8_dependencies.rust_files(copy)), len(source_map["files"]) + len(data) + len(targets))
            for name, rewrite in includes[:1]:
                reader = copy / name
                saved = reader.read_bytes()
                reader.write_bytes(saved.replace(f'"{rewrite["to"]}"'.encode(), b'"../../NativeLimits.lean"', 1))
                with self.assertRaisesRegex(ValueError, "Include does not read"):
                    v8_dependencies.check_rust_include(copy, reader, rewrite)
                reader.write_bytes(saved)
            if data:
                record = copy / next(iter(data))
                saved = record.read_bytes()
                record.write_bytes(saved + b"\n")
                with self.assertRaisesRegex(ValueError, "data file differs"):
                    v8_dependencies.rust_files(copy)
                record.write_bytes(saved)
            target = copy / "crates/fang-v8/src/lib.rs"
            target.write_bytes(target.read_bytes() + b"\n")
            with self.assertRaisesRegex(ValueError, "differs from its receipt"):
                v8_dependencies.rust_files(copy)
            target.write_bytes((ROOT / "crates/fang-v8/src/lib.rs").read_bytes())
            (copy / "crates/fang-v8/src/extra.rs").write_text("// unlisted\n")
            with self.assertRaisesRegex(ValueError, "inventory differs"):
                v8_dependencies.rust_files(copy)

    def test_lean_adaptation_is_only_the_recorded_rename(self):
        source_map = v8_dependencies.load_map(ROOT, v8_dependencies.LEAN_MAP, v8_dependencies.LEAN_SCHEMA)
        self.assertEqual(source_map["module_renames"], {"FofInput": "ExpandedFofInput"})
        with tempfile.TemporaryDirectory(prefix="fang-lean-adaptation-control-") as temporary:
            project = Path(temporary)
            for relative in source_map["files"]:
                (project / relative).parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / source_map["project"] / relative, project / relative)
            v8_dependencies.check_adaptations(project, source_map)
            target = project / "CnfBooleanInput.lean"
            original = target.read_bytes()
            for changed, message in ((original + b"\n-- extra\n", "beyond the recorded import lines"),
                                     (original.replace(b"import ExpandedFofInput", b"import FofInput"),
                                      "renamed module remains")):
                target.write_bytes(changed)
                with self.assertRaisesRegex(ValueError, message):
                    v8_dependencies.check_adaptations(project, source_map)
            target.write_bytes(original)
            plain = project / "Absorb.lean"
            plain.write_bytes(b"import ExpandedFofInput\n" + plain.read_bytes())
            with self.assertRaisesRegex(ValueError, "Unrecorded adaptation"):
                v8_dependencies.check_adaptations(project, source_map)

    def test_content_digest_leaves_out_only_lake_hash_files(self):
        backend = load("fang_v8_backend_control", TOOLS / "fang_szs/v8_backend.py")
        row = lambda digest: {"kind": "file", "size": 1, "sha256": digest}
        rows = {"A.olean": row("1" * 64), "A.olean.hash": row("2" * 64), "A.trace": row("3" * 64),
                ".lake/config/x": row("4" * 64)}
        rehashed = rows | {"A.olean.hash": row("5" * 64)}
        changed = rows | {"A.olean": row("6" * 64)}
        traced = rows | {"A.trace": row("7" * 64)}
        self.assertEqual(backend.package_digest(rows, content=True), backend.package_digest(rehashed, content=True))
        self.assertNotEqual(backend.package_digest(rows), backend.package_digest(rehashed))
        for other in (changed, traced):
            self.assertNotEqual(backend.package_digest(rows, content=True), backend.package_digest(other, content=True))
        pins = backend.load_pins(ROOT)
        self.assertIn("content_reason", pins)
        for pin in pins["packages"].values():
            self.assertTrue({"digest", "files", "content_digest", "content_files", "rev"} <= set(pin))

    def test_fetch_digest_leaves_out_only_build_records_and_names_kinds(self):
        backend = load("fang_v8_backend_fetch_control", TOOLS / "fang_szs/v8_backend.py")
        row = lambda digest: {"kind": "file", "size": 1, "sha256": digest}
        rows = {"A.lean": row("1" * 64), "A.olean": row("2" * 64), "A.olean.hash": row("3" * 64),
                "A.trace": row("4" * 64), "A.setup.json": row("5" * 64), "bin/x.rsp": row("6" * 64),
                "lake-manifest.json": row("7" * 64)}
        pin = {"fetch_files": 3, "fetch_digest": backend.package_digest(rows, fetch=True),
               "kinds": backend.kind_digests(rows), "files": len(rows), "digest": backend.package_digest(rows)}
        records = rows | {"A.trace": row("8" * 64), "A.setup.json": row("9" * 64), "bin/x.rsp": row("a" * 64),
                          "A.c.o.export.trace": row("b" * 64)}
        self.assertEqual(backend.package_digest(records, fetch=True), pin["fetch_digest"])
        self.assertEqual(backend.differing_kinds(records, pin), ([], ["c.o.export.trace", "rsp", "setup.json", "trace"]))
        for changed, kind in ((rows | {"A.olean": row("c" * 64)}, "olean"), (rows | {"A.lean": row("d" * 64)}, "lean"),
                              (rows | {"lake-manifest.json": row("e" * 64)}, "json"), (rows | {"B.so": row("f" * 64)}, "so")):
            self.assertNotEqual(backend.package_digest(changed, fetch=True), pin["fetch_digest"])
            self.assertEqual(backend.differing_kinds(changed, pin)[0], [kind])
        pins = backend.load_pins(ROOT)
        self.assertEqual(pins["fetch_left_out"], [".hash", ".trace", ".setup.json", ".rsp"])
        self.assertIn("fetch_reason", pins)
        for pin in pins["packages"].values():
            self.assertTrue({"digest", "content_digest", "fetch_digest", "fetch_files", "kinds"} <= set(pin))

    def test_comment_rewrite_changes_only_comment_text(self):
        def record(original, edits, suffix):
            lines = original.split("\n")
            rewrite = {"code_view_sha256": v8_dependencies.code_view_sha256(original, suffix), "edits": []}
            for number, after in edits.items():
                rewrite["edits"].append({"line": number, "to": after,
                                         "from_sha256": hashlib.sha256(lines[number - 1].encode()).hexdigest()})
                lines[number - 1] = after
            return rewrite, "\n".join(lines)

        def check(original, edits, suffix, current=None):
            rewrite, edited = record(original, edits, suffix)
            v8_dependencies.check_comment_rewrite((edited if current is None else current).encode(), rewrite, suffix)
            return rewrite, edited

        lean = ("/- Header (local note).\n   more -/\ndef a : String := \"-- x\"\ndef c : Char := '\"'\n"
                "-- note one\ntheorem t : True := trivial -- one\n")
        rewrite, edited = check(lean, {1: "/- Header.", 5: "-- note"}, ".lean")
        self.assertEqual(v8_dependencies.apply_comment_rewrite(lean.encode(), rewrite, ".lean"), edited.encode())
        self.assertNotIn("local note", json.dumps(rewrite))
        for edits, message in (({3: 'def a : String := "-- y"'}, "beyond comment text"),
                               ({1: "/-- Header."}, "beyond comment text"),
                               ({2: "   more -/ def b := 1 /- x -/"}, "beyond comment text"),
                               ({2: "   more -/ #exit /-"}, "Unclosed block comment"),
                               ({6: "theorem t : True := trivial -- two"}, "lies outside comments")):
            with self.assertRaisesRegex(ValueError, message):
                check(lean, edits, ".lean")
        with self.assertRaisesRegex(ValueError, "does not match the file"):
            check(lean, {1: "/- Header."}, ".lean", lean)
        # A comment changed outside the record passes the install check; the receipt check rebuilds the file and
        # finds the difference.
        rewrite, edited = record(lean, {1: "/- Header."}, ".lean")
        unrecorded = edited.replace("-- note one", "-- note two")
        v8_dependencies.check_comment_rewrite(unrecorded.encode(), rewrite, ".lean")
        self.assertNotEqual(v8_dependencies.apply_comment_rewrite(lean.encode(), rewrite, ".lean"), unrecorded.encode())
        with self.assertRaisesRegex(ValueError, "does not match the reviewed bytes"):
            v8_dependencies.apply_comment_rewrite(edited.encode(), rewrite, ".lean")
        rust = '// Header; see the old note.\n/// Doc.\nlet s = r#"// x"#;\nlet q = \'"\';\n'
        check(rust, {1: "// Header."}, ".rs")
        for edits in ({2: "// Doc."}, {3: 'let s = r#"// y"#;'}, {4: "let q = '\\'';"}):
            with self.assertRaisesRegex(ValueError, "beyond comment text"):
                check(rust, edits, ".rs")

    def test_left_out_gate_modules_stay_out(self):
        source_map = {"gates": {"g": {"left_out": {"OldMain.lean": "superseded native main"}}},
                      "files": {"A.lean": {}, "B.lean": {}}}
        with tempfile.TemporaryDirectory(prefix="fang-left-out-control-") as temporary:
            project = Path(temporary)
            (project / "A.lean").write_text("import B\n", encoding="utf-8")
            (project / "B.lean").write_text("def b := 1\n", encoding="utf-8")
            v8_dependencies.check_left_out(project, source_map)
            (project / "A.lean").write_text("import B\nimport OldMain\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "imports a left-out module"):
                v8_dependencies.check_left_out(project, source_map)
            (project / "A.lean").write_text("import B\n", encoding="utf-8")
            (project / "OldMain.lean").write_text("def main : IO Unit := pure ()\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "staged in lean-v8"):
                v8_dependencies.check_left_out(project, source_map)
            (project / "OldMain.lean").unlink()
            source_map["gates"]["g"]["left_out"]["OldMain.lean"] = ""
            with self.assertRaisesRegex(ValueError, "without a reason"):
                v8_dependencies.check_left_out(project, source_map)

    def test_lean_build_allows_only_pinned_external_imports(self):
        builder = load("fang_v8_lean_builder_control", TOOLS / "build-v8-lean.py")
        lean_map = v8_dependencies.load_map(ROOT, v8_dependencies.LEAN_MAP, v8_dependencies.LEAN_SCHEMA)
        self.assertIn("Std.Data.HashSet", builder.check_closures(ROOT / lean_map["project"], lean_map)["external"])
        with tempfile.TemporaryDirectory(prefix="fang-lean-import-control-") as temporary:
            project = Path(temporary)
            small = {"files": {"A.lean": {}}, "executables": {}, "library_roots": ["A"]}
            (project / "A.lean").write_text("import Std.Data.HashSet\nimport Aeneas\n", encoding="utf-8")
            self.assertEqual(builder.check_closures(project, small)["external"], ["Aeneas", "Std.Data.HashSet"])
            (project / "A.lean").write_text("import Std.Data.HashSet\nimport Std.Data.HashMap\n", encoding="utf-8")
            with self.assertRaisesRegex(ValueError, "Unpinned external import: Std.Data.HashMap"):
                builder.check_closures(project, small)

    def test_generated_sources_name_no_machine_paths(self):
        source_map = v8_dependencies.load_map(ROOT, v8_dependencies.LEAN_MAP, v8_dependencies.LEAN_SCHEMA)
        rewritten = {name for name, entry in source_map["files"].items()
                     if entry.get("adaptation", {}).get("kind") == "comment-rewrite"}
        self.assertTrue({"BinderRemoval.lean", "Fof.lean", "FofEqualityBridge.lean", "Skolem.lean"} <= rewritten)
        machine = re.compile(r"/var/tmp/|/mnt/|/home/|[A-Za-z]:\\\\")
        for path in [*(ROOT / "lean-v8").glob("*.lean"), *(ROOT / "crates").glob("*/src/**/*.rs")]:
            self.assertIsNone(machine.search(path.read_text(encoding="utf-8")), path)
        with tempfile.TemporaryDirectory(prefix="fang-comment-rewrite-control-") as temporary:
            project = Path(temporary)
            for relative in source_map["files"]:
                (project / relative).parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(ROOT / source_map["project"] / relative, project / relative)
            target = project / "Skolem.lean"
            target.write_bytes(target.read_bytes().replace(b"Source: 'src/syntax.rs'", b"Source: 'src/other.rs'", 1))
            with self.assertRaisesRegex(ValueError, "does not match the file"):
                v8_dependencies.check_adaptations(project, source_map)

    def test_path_rewrites_rebuild_the_moved_manifest(self):
        original = b'[dependencies]\nfang = { path = "../.." }\nx = { path = "../../a/b" }\n'
        rebuilt = v8_dependencies.apply_rewrites(original, [{"line": 3, "from": "../../a/b", "to": "../b"}])
        self.assertEqual(rebuilt, b'[dependencies]\nfang = { path = "../.." }\nx = { path = "../b" }\n')
        with self.assertRaises(ValueError):
            v8_dependencies.apply_rewrites(original, [{"line": 2, "from": "../../a/b", "to": "../b"}])


if __name__ == "__main__":
    unittest.main(verbosity=2)
