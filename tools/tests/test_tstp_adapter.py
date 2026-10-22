"""Synthetic TSTP integration controls, separate from native proof acceptance."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))
sys.path.insert(0, str(Path(__file__).resolve().parent))
from test_fang_szs import FAKE, INPUT, PROOF, source_fixture
from fang_szs import app, tstp
from fang_szs.installation import make_installation, verify_installation
from fang_szs.supervisor import Failure, Limits, Supervisor, digest_bytes

SOLUTION = (b"cnf('a',axiom,(p),file('input.p','a')).\n"
            b"cnf('b',axiom,(~p),file('input.p','b')).\n"
            b"cnf('fang:step:2',plain,($false),inference(fang_resolution,[status(thm)],[a,b])).\n")
EXPORTER = '''#!/usr/bin/env python3
import fcntl, os, pathlib, sys, time
assert pathlib.Path(sys.argv[1]).read_bytes() == INPUT_BYTES
assert pathlib.Path(sys.argv[2]).read_bytes() == PROOF_BYTES
assert sys.argv[3] == "input.p"
for argument in sys.argv[1:3]:
    assert argument.startswith("/proc/self/fd/")
    seals = fcntl.fcntl(int(argument.rsplit("/", 1)[1]), fcntl.F_GET_SEALS)
    assert seals & (fcntl.F_SEAL_WRITE | fcntl.F_SEAL_SHRINK | fcntl.F_SEAL_GROW | fcntl.F_SEAL_SEAL) == 15
MODE_BODY
'''


@unittest.skipUnless(sys.platform == "linux", "Linux sealed-descriptor controls")
class TstpAdapterTests(unittest.TestCase):
    artifact_root = None

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fang-tstp-control-")
        self.root = Path(self.temporary.name)
        self.source = source_fixture(self.root)
        for name in ("TstpExport.lean", "TstpMain.lean"):
            (self.source / "lean" / name).write_text("-- synthetic source identity control\n")
        (self.source / "lean/tstp-sources.json").write_text(json.dumps({
            "schema": "fang-tstp-source-link-v2", "sources": {
                "lean/" + name: hashlib.sha256((self.source / "lean" / name).read_bytes()).hexdigest()
                for name in ("TstpExport.lean", "TstpMain.lean")}}))
        self.library = self.root / "library"
        (self.library / "Fang").mkdir(parents=True)
        for name in ("FrontendSoundness", "CertificateInput"):
            (self.library / "Fang" / (name + ".olean")).write_bytes(b"synthetic, not proof evidence")
        for name in ("engine", "checker", "lean"):
            path = self.root / name
            path.write_text(FAKE.replace("PROOF", repr(PROOF)))
            path.chmod(0o700)
        self.exporter = self.root / "exporter"
        self.provenance = self.root / "provenance.json"
        self.provenance.write_text('{"scope":"synthetic TSTP protocol controls"}')
        self.installation = self.root / "installation.json"
        self.input = self.root / "source with newline\n.p"
        self.input.write_bytes(INPUT)
        self.output = self.root / "run"
        self.receipts = []
        self.configure()

    def configure(self, body=None, version=2, engine_mode="candidate"):
        body = body if body is not None else "os.write(1, " + repr(SOLUTION) + ")"
        text = EXPORTER.replace("INPUT_BYTES", repr(INPUT)).replace("PROOF_BYTES", repr(PROOF)).replace("MODE_BODY", body)
        self.exporter.write_text(text)
        self.exporter.chmod(0o700)
        for name in ("engine", "checker", "lean"):
            (self.root / name).write_text(FAKE.replace("PROOF", repr(PROOF)).replace(
                'os.environ.get("FANG_TEST_MODE", "candidate")', repr(engine_mode)))
        self.config = make_installation(self.root / "engine", self.root / "checker", self.root / "lean",
            self.library, self.source, [self.provenance], self.exporter if version == 2 else None)
        self.installation.write_text(json.dumps(self.config))

    def command(self, extra=(), output="tstp"):
        return [sys.executable, "-B", str(TOOLS / "fang-szs.py"), str(self.input),
            "--installation", str(self.installation), "--artifacts", str(self.output),
            "--check", "compiled", "--output", output, "--wall-seconds", "3", *extra]

    def invoke(self, expected="Unsatisfiable", extra=(), output="tstp"):
        result = subprocess.run(self.command(extra, output), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=8, env=os.environ | {"PYTHONDONTWRITEBYTECODE": "1"})
        self.receipts.append({"arguments": self.command(extra, output), "exit_code": result.returncode,
            "stdout": result.stdout.decode("ascii"), "stderr": result.stderr.decode("ascii")})
        self.assertEqual(result.stderr, b"")
        self.assertIn(("% SZS status " + expected + " for fang_").encode(), result.stdout)
        if expected != "Unsatisfiable":
            self.assertNotIn(b"SZS status Unsatisfiable", result.stdout)
            self.assertNotIn(b"SZS output start", result.stdout)
            self.assertNotEqual(result.returncode, 0)
        else:
            self.assertEqual(result.returncode, 0)
        manifest = json.loads((self.output / "manifest.json").read_text())
        self.assertEqual(manifest["status"], expected)
        return result, manifest

    def tearDown(self):
        if self.artifact_root is not None:
            destination = self.artifact_root / self._testMethodName
            destination.mkdir()
            (destination / "receipts.json").write_text(json.dumps(self.receipts, indent=2) + "\n")
            for path in self.root.rglob("*"):
                if path.is_file() and not path.is_symlink() and path.stat().st_size <= 2 << 20:
                    target = destination / path.relative_to(self.root)
                    target.parent.mkdir(parents=True, exist_ok=True)
                    shutil.copyfile(path, target)
        self.temporary.cleanup()

    def test_success_captures_exact_bytes_and_complete_closing_marker(self):
        result, manifest = self.invoke()
        self.assertEqual((self.output / "solution.tstp").read_bytes(), SOLUTION)
        self.assertEqual(manifest["solution"]["sha256"], digest_bytes(SOLUTION))
        self.assertFalse(manifest["solution"]["per_instance_kernel_check_of_printed_bytes"])
        self.assertEqual([r["stage"] for r in manifest["processes"]], ["search", "checker", "exporter"])
        self.assertTrue(all(r["classification"] == "completed" for r in manifest["processes"]))
        self.assertIn(SOLUTION, result.stdout)
        self.assertTrue(result.stdout.endswith(("% SZS output end CNFRefutation for " + manifest["problem_id"] + "\n").encode()))
        self.assertTrue(manifest["output_delivery"]["closing_marker_delivered"])
        self.assertEqual(manifest["output_delivery"]["sha256"], digest_bytes(result.stdout))
        self.assertNotIn(b"source with", result.stdout)

    def test_v1_status_works_and_tstp_fails_before_search(self):
        (self.source / "lean/tstp-sources.json").unlink()
        self.configure(version=1)
        result, manifest = self.invoke(output="status")
        self.assertEqual(len(result.stdout.splitlines()), 2)
        self.assertNotIn("solution", manifest)
        self.output = self.root / "tstp-run"
        _, manifest = self.invoke("Error")
        self.assertEqual(manifest["processes"], [])

    def test_exporter_source_record_must_match_canonical_bytes(self):
        path = self.source / "lean/tstp-sources.json"
        record = json.loads(path.read_text())
        record["sources"]["lean/TstpExport.lean"] = "0" * 64
        path.write_text(json.dumps(record))
        with self.assertRaisesRegex(Failure, "source/proof provenance changed"):
            verify_installation(self.config)
        with self.assertRaisesRegex(Failure, "Exporter source record differs"):
            self.configure()
        path.unlink()
        with self.assertRaisesRegex(Failure, "missing its exporter source record"):
            self.configure()

    def test_status_mode_does_not_execute_exporter(self):
        self.configure("raise RuntimeError('exporter must not execute')")
        _, manifest = self.invoke(output="status")
        self.assertEqual([r["stage"] for r in manifest["processes"]], ["search", "checker"])
        self.assertFalse(manifest["output_delivery"]["closing_marker_delivered"])

    def test_exporter_pin_and_required_source_are_enforced(self):
        self.exporter.write_text(self.exporter.read_text() + "\n# changed\n")
        _, manifest = self.invoke("Error")
        self.assertEqual(manifest["processes"], [])
        self.configure()
        del self.config["source_sha256"]["lean/TstpExport.lean"]
        with self.assertRaisesRegex(Failure, "missing exporter source"):
            verify_installation(self.config)

    def test_v2_without_exporter_and_v1_with_exporter_rejected(self):
        missing = self.config.copy()
        del missing["exporter"]
        with self.assertRaisesRegex(Failure, "Unsupported installation schema"):
            verify_installation(missing)
        wrong = self.config | {"schema": "fang-local-installation-v1"}
        with self.assertRaisesRegex(Failure, "Unsupported installation schema"):
            verify_installation(wrong)

    def test_checker_rejection_never_runs_exporter(self):
        self.configure(engine_mode="reject")
        _, manifest = self.invoke("Error")
        self.assertEqual([r["stage"] for r in manifest["processes"]], ["search", "checker"])

    def test_exporter_failures_never_publish_positive_output(self):
        modes = ["sys.exit(3)", "os.write(2,b'warning\\n'); os.write(1," + repr(SOLUTION) + ")",
                 "os.write(1," + repr(SOLUTION[:-1]) + ")", "os.write(1,b'% SZS status Unsatisfiable\\n')",
                 "os.write(1,b\"cnf('x',plain,(p),file('input.p','a')).\\n\")", "pass"]
        for index, body in enumerate(modes):
            with self.subTest(index=index):
                self.configure(body)
                self.output = self.root / ("run" + str(index))
                _, manifest = self.invoke("Error")
                self.assertNotIn("solution", manifest)

    def test_recognized_resource_exit_stays_resource_and_partial_stdout_is_error(self):
        diagnostic = b"resource-exhaustion: export supports at most 1000 certificate nodes\n"
        self.configure("os.write(2," + repr(diagnostic) + "); sys.exit(2)")
        self.invoke("ResourceOut")
        self.configure("os.write(1,b'partial'); os.write(2," + repr(diagnostic) + "); sys.exit(2)")
        self.output = self.root / "partial"
        self.invoke("Error")

    def test_solution_limit_exact_boundary_and_stdout_override(self):
        self.invoke(extra=("--max-solution-bytes", str(len(SOLUTION))))
        self.output = self.root / "below"
        self.invoke("ResourceOut", extra=("--max-solution-bytes", str(len(SOLUTION) - 1)))
        # The exporter stdout cap may exceed the stderr/log cap.
        many = b"".join(b"cnf('x" + str(i).encode() + b"',axiom,(p),file('input.p','a')).\n" for i in range(80)) + SOLUTION.splitlines(keepends=True)[-1]
        self.configure("os.write(1," + repr(many) + ")")
        self.output = self.root / "large-stdout"
        _, manifest = self.invoke(extra=("--max-log-bytes", "256", "--max-solution-bytes", str(len(many))))
        self.assertGreater(manifest["solution"]["bytes"], 256)
        self.assertEqual(manifest["processes"][-1]["stream_byte_limits"], {"stdout": len(many), "stderr": 256})

    def test_stderr_limit_does_not_inherit_solution_limit(self):
        self.configure("os.write(2,b'x'*257); os.write(1," + repr(SOLUTION) + ")")
        self.invoke("ResourceOut", extra=("--max-log-bytes", "256", "--max-solution-bytes", "10000"))

    def test_captured_source_or_certificate_mutation_is_rejected(self):
        for name in ("input.p", "proof.fang"):
            with self.subTest(name=name):
                self.configure("p=pathlib.Path('../" + name + "'); p.chmod(0o600); p.write_bytes(b'changed'); os.write(1," + repr(SOLUTION) + ")")
                self.output = self.root / name
                self.invoke("Error")
                self.assertFalse((self.output / "solution.tstp").exists())

    def test_solution_capture_hash_detects_equal_length_change(self):
        path = self.root / "solution.tstp"
        path.write_bytes(SOLUTION)
        record = {"bytes": len(SOLUTION), "sha256": digest_bytes(SOLUTION)}
        self.assertEqual(tstp.read_solution(self.root, record, lambda: None), SOLUTION)
        path.write_bytes(SOLUTION.replace(b"(p)", b"(q)", 1))
        with self.assertRaisesRegex(Failure, "Captured solution changed"):
            tstp.read_solution(self.root, record, lambda: None)

    def test_kernel_profile_calls_selected_check_before_export(self):
        args = app.arguments([str(self.input), "--installation", str(self.installation), "--artifacts", str(self.output), "--output", "tstp"])
        self.output.mkdir()
        manifest = {}
        supervisor = Supervisor(Limits(wall_seconds=10))
        def checked(supervisor_arg, config, root, source, certificate, storage):
            self.assertFalse((root / "exporter").exists())
            self.assertEqual((source.data, certificate.data), (INPUT, PROOF))
            return {"synthetic_control": True}
        try:
            with mock.patch.object(app.kernel, "verify", side_effect=checked) as replay:
                self.assertEqual(app.run_pipeline(args, supervisor, manifest, self.output)[0], "Unsatisfiable")
                replay.assert_called_once()
            self.assertTrue(manifest["kernel_check"]["synthetic_control"])
            self.assertIn("solution", manifest)
        finally:
            supervisor.close()

    def test_kernel_failure_has_no_compiled_fallback_or_export(self):
        args = app.arguments([str(self.input), "--installation", str(self.installation), "--artifacts", str(self.output), "--output", "tstp"])
        self.output.mkdir()
        supervisor = Supervisor(Limits(wall_seconds=10))
        try:
            with mock.patch.object(app.kernel, "verify", side_effect=Failure("Timeout", "synthetic replay limit", "kernel")):
                with self.assertRaisesRegex(Failure, "synthetic replay limit"):
                    app.run_pipeline(args, supervisor, {}, self.output)
            self.assertFalse((self.output / "exporter").exists())
        finally:
            supervisor.close()

    def test_full_pipe_records_incomplete_solution_delivery(self):
        row = b"cnf('x',axiom,(p),file('input.p','a')).\n"
        many = row * 4096 + SOLUTION.splitlines(keepends=True)[-1]
        self.configure("os.write(1," + repr(many) + ")")
        process = subprocess.Popen(self.command(), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            self.assertEqual(process.wait(timeout=7), 7)
            stdout, stderr = process.communicate(timeout=1)
        finally:
            if process.poll() is None:
                process.kill(); process.wait()
        manifest = json.loads((self.output / "manifest.json").read_text())
        self.assertEqual(stderr, b"")
        self.assertEqual(manifest["status"], "Timeout")
        self.assertEqual(manifest["output_delivery"]["state"], "incomplete")
        self.assertFalse(manifest["output_delivery"]["closing_marker_delivered"])
        self.assertNotIn(b"% SZS output end", stdout)
        self.receipts.append({"exit_code": process.returncode, "stdout": stdout.decode(), "stderr": stderr.decode()})

    def test_closed_output_pipe_records_error(self):
        reader, writer = os.pipe()
        process = subprocess.Popen(self.command(), stdout=writer, stderr=subprocess.PIPE)
        os.close(writer); os.close(reader)
        try:
            _, stderr = process.communicate(timeout=7)
        finally:
            if process.poll() is None:
                process.kill(); process.wait()
        self.assertEqual(process.returncode, 6, stderr)
        manifest = json.loads((self.output / "manifest.json").read_text())
        self.assertEqual(manifest["output_delivery"]["state"], "incomplete")
        self.assertFalse(manifest["output_delivery"]["closing_marker_delivered"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=False)
    TstpAdapterTests.artifact_root = args.out / "cases"
    TstpAdapterTests.artifact_root.mkdir()
    source_files = sorted((TOOLS / "fang_szs").glob("*.py")) + [TOOLS / "fang-szs.py", TOOLS / "fang-install.py",
        TOOLS / "build-local.py", Path(__file__), Path(__file__).with_name("test_fang_szs.py")]
    pins = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in source_files}
    log = io.StringIO()
    result = unittest.TextTestRunner(stream=log, verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(TstpAdapterTests))
    (args.out / "controls.log").write_text(log.getvalue())
    unchanged = all(hashlib.sha256(Path(p).read_bytes()).hexdigest() == h for p, h in pins.items())
    report = {"status": "passed" if result.wasSuccessful() and not result.skipped and unchanged else "failed",
        "scope": "Synthetic adapter control flow, identity, delivery and limits; no native exporter or kernel acceptance evidence",
        "tests": result.testsRun, "skipped": result.skipped, "source_unchanged": unchanged,
        "source_sha256": pins, "python": sys.version,
        "failures": [{"test": str(t), "trace": trace} for t, trace in result.failures],
        "errors": [{"test": str(t), "trace": trace} for t, trace in result.errors]}
    (args.out / "manifest.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ("status", "tests", "source_unchanged")}))
    return int(report["status"] != "passed")


if __name__ == "__main__":
    raise SystemExit(main())
