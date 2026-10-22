"""Adapter controls use synthetic binaries; they are not proof acceptance evidence."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import importlib.util
import fcntl
import json
import os
from pathlib import Path
import signal
import shutil
import stat
import subprocess
import sys
import tempfile
import time
import unittest
from unittest import mock

TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))
from fang_szs.installation import CONFIGS, HELPERS, make_installation, source_inventory, verify_installation
from fang_szs.dependencies import CORE, CORE_FILES
from fang_szs.app import emit_status, terminal_checkpoint
from fang_szs.protocol import HEADER, FOOTER, REQUIRED_AUDITS, engine_outcome, exact_axioms, fixed_replay, quote
from fang_szs.supervisor import Failure, Limits, Snapshot, Supervisor, strict_json
from fang_szs.storage import KernelWorkspace

INPUT = b"cnf(a,axiom,(p)).cnf(b,axiom,(~p)).\n"
PROOF = b"(fang-proof 1 (input 0 0) (input 1 1) (resolve 2 0 0 1 0 (subst) (clause)) (final 2))\n"
FAKE = '''#!/usr/bin/env python3
import os, pathlib, signal, sys, time
mode = os.environ.get("FANG_TEST_MODE", "candidate")
role = pathlib.Path(sys.argv[0]).name
if role == "engine":
    if mode == "timeout-search": time.sleep(5)
    if mode == "memory-search": data = bytearray(80 << 20); time.sleep(5)
    if mode == "logs": print("x" * 20000, flush=True); time.sleep(5)
    if mode == "sparse-log": os.ftruncate(1, 1 << 40); time.sleep(5)
    if mode == "fifo-log": pathlib.Path("stdout").unlink(); os.mkfifo("stdout"); sys.exit(0)
    if mode == "orphan":
        child = os.fork()
        if child == 0: time.sleep(5); os._exit(0)
        pathlib.Path("child.pid").write_text(str(child))
        print("unknown"); print("queue exhausted after 0 clauses and 0 inference attempts", file=sys.stderr); sys.exit(2)
    if mode == "signal": os.kill(os.getpid(), signal.SIGKILL)
    if mode == "panic": print("ResourceLimit: forged", file=sys.stderr); sys.exit(101)
    if mode in ("unknown", "empty"):
        print("unknown"); print("queue exhausted after 1 clauses and 0 inference attempts", file=sys.stderr); sys.exit(2)
    errors = {"duplicate": (3, "InvalidInput at byte 12: duplicate clause name"),
              "arity": (3, "InvalidInput at byte 12: inconsistent symbol arity"),
              "unsupported": (4, "Unsupported at byte 0: only cnf statements are supported"),
              "uppercase": (3, "InvalidInput at byte 3: uppercase character in a lowercase identifier"),
              "ascii": (3, "InvalidInput at byte 3: input must contain ASCII bytes only"),
              "syntax": (3, "InvalidInput at byte 3: expected a term"),
              "resource": (5, "ResourceLimit: operation budget exhausted"),
              "invalid-internal": (3, "InvalidInput: bad parent")}
    if mode in errors:
        code, message = errors[mode]; print(message, file=sys.stderr); sys.exit(code)
    if mode == "mutate-input":
        target = pathlib.Path("../input.p"); target.chmod(0o600); target.write_bytes(b"different")
    if mode == "cancel-search":
        pathlib.Path("ready").write_text("ready"); time.sleep(5)
    if mode != "missing-proof":
        pathlib.Path(sys.argv[sys.argv.index("--proof") + 1]).write_bytes(PROOF)
    print("candidate-refutation")
    print("3 recorded search nodes; serialized proof keeps only refutation dependencies; independent checking required", file=sys.stderr)
    if mode == "spoof": print("% SZS status Unsatisfiable for forged")
elif role == "checker":
    if mode in ("timeout-checker", "cancel-checker"):
        pathlib.Path("ready").write_text("ready"); time.sleep(5)
    if mode == "reject": print("rejected-certificate", file=sys.stderr); sys.exit(1)
    if mode == "wrong-source": print("invalid-input: mismatch", file=sys.stderr); sys.exit(2)
    if mode == "mutate-proof":
        target = pathlib.Path("../proof.fang"); target.chmod(0o600); target.write_bytes(b"different")
    print("accepted-refutation (compiled checker; no per-instance kernel replay performed)")
    if mode == "checker-spoof": print("% SZS status Unsatisfiable for forged")
else: sys.exit(7)
'''


def source_fixture(root):
    source = root / "source"
    for relative in CONFIGS:
        path = source / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("control\n")
    (source / "Cargo.toml").write_text('[package]\nname = "fang"\nversion = "0.1.0"\n[dependencies]\n')
    (source / "Cargo.lock").write_text('version = 4\n[[package]]\nname = "fang"\nversion = "0.1.0"\n')
    for name in HELPERS:
        path = source / "tools/replay" / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("# synthetic source pin\n")
    (source / "src").mkdir()
    (source / "src/lib.rs").write_text("// synthetic control\n")
    shutil.copytree(TOOLS / "fang_szs", source / "tools/fang_szs", ignore=shutil.ignore_patterns("__pycache__"))
    for name in ("fang-szs.py", "fang-install.py"):
        shutil.copy2(TOOLS / name, source / "tools" / name)
    return source


class InstallationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fang-install-control-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.source = source_fixture(self.root)
        self.library = self.root / "library"
        (self.library / "Fang").mkdir(parents=True)
        for name in ("FrontendSoundness", "CertificateInput"):
            (self.library / "Fang" / (name + ".olean")).write_bytes(b"synthetic installation control")
        self.binary = self.root / "synthetic-binary"
        self.binary.write_bytes(b"not executed by these identity controls")
        self.provenance = self.root / "provenance.json"
        self.provenance.write_text('{"scope":"synthetic installation identity controls"}')

    def install(self):
        return make_installation(self.binary, self.binary, self.binary, self.library,
                                 self.source, [self.provenance])

    def indexed_source(self):
        canonical = TOOLS.parent
        for name in ("Cargo.toml", "Cargo.lock"):
            shutil.copyfile(canonical / name, self.source / name)
        for name in CORE_FILES:
            destination = self.source / CORE / name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(canonical / CORE / name, destination)

    def test_dependency_free_p0_installation(self):
        config = self.install()
        verify_installation(config)
        self.assertFalse(any(name.startswith("crates/") for name in config["source_sha256"]))

    def test_replay_helpers_are_pinned_without_historical_tree(self):
        self.assertFalse((self.source / "experiments").exists())
        config = self.install()
        self.assertEqual({name for name in config["source_sha256"] if name.startswith("tools/replay/")},
                         {"tools/replay/" + name for name in HELPERS})
        for name in HELPERS:
            with self.subTest(name=name):
                path = self.source / "tools/replay" / name
                before = path.read_bytes()
                path.write_bytes(before + b"# changed helper\n")
                with self.assertRaisesRegex(Failure, "source/proof provenance changed"):
                    verify_installation(config)
                path.write_bytes(before)

    def test_local_crate_notes_are_optional_and_outside_source_inventory(self):
        self.indexed_source()
        config = self.install()
        for name in ("README.md", "CONTRACT.md", "PROMOTION.md"):
            (self.source / CORE / name).write_text("Local notes, not executable input.\n")
        verify_installation(config)
        self.assertEqual(self.install()["source_sha256"], config["source_sha256"])
        path = self.source / CORE / "README.md"
        path.unlink()
        path.symlink_to(self.source / "Cargo.toml")
        with self.assertRaisesRegex(ValueError, "Unexpected dependency member"):
            self.install()

    def test_legal_notices_are_pinned_without_a_provenance_directory(self):
        legal = self.source / "LICENSES"
        legal.mkdir()
        for name in ("Vampire.txt", "Vampire.AUTHORS", "Vampire.THANKS", "Vampire.ORIGIN"):
            (legal / name).write_text("Synthetic legal inventory control.\n")
        config = self.install()
        self.assertFalse((self.source / "provenance").exists())
        self.assertIn("LICENSES/Vampire.ORIGIN", config["source_sha256"])
        (legal / "Vampire.ORIGIN").write_text("Changed origin record.\n")
        with self.assertRaisesRegex(Failure, "source/proof provenance changed"):
            verify_installation(config)

    def test_indexed_installation_pins_all_declared_files(self):
        self.indexed_source()
        config = self.install()
        verify_installation(config)
        self.assertEqual({name for name in config["source_sha256"] if name.startswith("crates/")},
                         {CORE + "/" + name for name in CORE_FILES})

    def test_installed_core_config_and_license_changes_are_rejected(self):
        self.indexed_source()
        config = self.install()
        for name in ("src/lib.rs", "Cargo.toml", "LICENSE"):
            with self.subTest(name=name):
                path = self.source / CORE / name
                before = path.read_bytes()
                path.write_bytes(before + b"\n")
                with self.assertRaisesRegex(Failure, "source/proof provenance changed"):
                    verify_installation(config)
                path.write_bytes(before)

    def test_missing_core_config_and_license_rejected_before_and_after_install(self):
        self.indexed_source()
        config = self.install()
        for name in ("src/lib.rs", "Cargo.toml", "LICENSE"):
            with self.subTest(name=name):
                path = self.source / CORE / name
                before = path.read_bytes()
                path.unlink()
                with self.assertRaisesRegex(ValueError, "Incomplete dependency inventory"):
                    self.install()
                with self.assertRaisesRegex(ValueError, "Incomplete dependency inventory"):
                    verify_installation(config)
                path.write_bytes(before)

    def test_implicit_build_scripts_rejected_before_and_after_install(self):
        self.indexed_source()
        config = self.install()
        for relative in ("build.rs", CORE + "/build.rs"):
            with self.subTest(relative=relative):
                path = self.source / relative
                path.write_text("fn main() {}\n")
                with self.assertRaises(ValueError):
                    self.install()
                with self.assertRaises(ValueError):
                    verify_installation(config)
                path.unlink()

    def test_unlisted_dependency_source_rejected(self):
        self.indexed_source()
        config = self.install()
        (self.source / CORE / "src/hidden.rs").write_text("// unlisted source\n")
        with self.assertRaisesRegex(ValueError, "Unexpected dependency member"):
            self.install()
        with self.assertRaisesRegex(ValueError, "Unexpected dependency member"):
            verify_installation(config)

    def test_dependency_parent_symlinks_rejected_before_and_after_install(self):
        self.indexed_source()
        config = self.install()
        for relative in ("crates", CORE + "/src"):
            with self.subTest(relative=relative):
                path = self.source / relative
                retained = self.root / "retained-parent"
                path.rename(retained)
                path.symlink_to(retained, target_is_directory=True)
                with self.assertRaises(ValueError):
                    self.install()
                with self.assertRaises(ValueError):
                    verify_installation(config)
                path.unlink()
                retained.rename(path)

    def test_undeclared_local_crate_rejected(self):
        config = self.install()
        (self.source / "crates").mkdir()
        with self.assertRaisesRegex(ValueError, "without a declared dependency"):
            self.install()
        with self.assertRaisesRegex(ValueError, "without a declared dependency"):
            verify_installation(config)

    def test_unreviewed_lockfile_graph_rejected(self):
        self.indexed_source()
        config = self.install()
        path = self.source / "Cargo.lock"
        path.write_text(path.read_text() + '\n[[package]]\nname = "extra"\nversion = "1.0.0"\n')
        with self.assertRaisesRegex(ValueError, "Unreviewed Cargo lockfile"):
            self.install()
        with self.assertRaisesRegex(ValueError, "Unreviewed Cargo lockfile"):
            verify_installation(config)

    def test_bootstrap_inventory_includes_dependency_notices_and_rejects_build_script(self):
        self.indexed_source()
        spec = importlib.util.spec_from_file_location("fang_build_inventory_control", TOOLS / "build-local.py")
        bootstrap = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(bootstrap)
        paths = {path.relative_to(self.source).as_posix() for path in bootstrap.source_files(self.source)}
        self.assertEqual({name for name in paths if name.startswith("crates/")},
                         {CORE + "/" + name for name in CORE_FILES})
        (self.source / CORE / "build.rs").write_text("fn main() {}\n")
        with self.assertRaisesRegex(ValueError, "Unexpected dependency member"):
            bootstrap.source_files(self.source)

    def test_cache_ancestor_does_not_exclude_project_sources(self):
        spec = importlib.util.spec_from_file_location("fang_build_nested_inventory_control", TOOLS / "build-local.py")
        bootstrap = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(bootstrap)
        for ancestor in (".local", "evidence", ".lake", "Generated"):
            with self.subTest(ancestor=ancestor):
                nested = source_fixture(self.root / ancestor)
                (nested / "lean/Visible.lean").write_text("-- source inventory control\n")
                visible = {"tests/visible.rs", "examples/problems/visible.p", "LICENSES/Vampire.ORIGIN"}
                for name in visible:
                    path = nested / name
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text("source inventory control\n")
                hidden = {"src/.local/stale.rs", "tests/evidence/stale.rs", "tools/runs/stale.py",
                          "tools/logs/stale.py", "tools/__pycache__/stale.py", "lean/.lake/Hidden.lean",
                          "lean/Generated/Hidden.lean"}
                for name in hidden:
                    path = nested / name
                    path.parent.mkdir(parents=True, exist_ok=True)
                    path.write_text("cache contents\n")
                paths = {path.relative_to(nested).as_posix() for path in bootstrap.source_files(nested)}
                self.assertTrue({"src/lib.rs", "tools/fang-szs.py", "tools/fang_szs/app.py",
                                 "tools/replay/axiom_audit.py", "lean/Visible.lean"} <= paths)
                self.assertTrue(visible <= paths)
                self.assertFalse(hidden & paths)
                installed = source_inventory(nested)
                self.assertIn("lean/Visible.lean", installed)
                self.assertNotIn("lean/.lake/Hidden.lean", installed)


class ProtocolTests(unittest.TestCase):
    def scanner(self, entries, side_effect=None):
        supervisor = Supervisor(Limits())
        context = mock.MagicMock()
        context.__enter__.return_value = context
        context.__iter__.return_value = iter(entries)
        context.__exit__.return_value = False
        try:
            with mock.patch("fang_szs.supervisor.os.scandir", side_effect=side_effect or [context]):
                return supervisor.tree_bytes(Path("/owned-run"))
        finally:
            supervisor.close()

    def test_artifact_scan_tolerates_disappearing_temporary_file(self):
        entry = mock.Mock()
        entry.stat.side_effect = FileNotFoundError("temporary file was renamed")
        self.assertEqual(self.scanner([entry]), 0)
        entry.stat.assert_called_once_with(follow_symlinks=False)

    def test_artifact_scan_tolerates_disappearing_queued_directory(self):
        entry = mock.Mock(path="/owned-run/temporary")
        entry.stat.return_value = mock.Mock(st_mode=stat.S_IFDIR)
        context = mock.MagicMock()
        context.__enter__.return_value = context
        context.__iter__.return_value = iter([entry])
        context.__exit__.return_value = False
        self.assertEqual(self.scanner([], [context, FileNotFoundError("temporary directory removed")]), 0)
        entry.stat.assert_called_once_with(follow_symlinks=False)

    def test_artifact_scan_missing_root_is_still_an_error(self):
        with self.assertRaises(FileNotFoundError):
            self.scanner([], [FileNotFoundError("run root removed")])

    def test_artifact_scan_other_io_failures_remain_errors(self):
        entry = mock.Mock()
        entry.stat.side_effect = PermissionError("access denied")
        with self.assertRaises(PermissionError):
            self.scanner([entry])

    def test_blocked_status_output_is_bounded(self):
        reader, writer = os.pipe()
        try:
            fcntl.fcntl(writer, fcntl.F_SETFL, os.O_NONBLOCK)
            try:
                while True: os.write(writer, b"x" * 4096)
            except BlockingIOError: pass
            self.assertFalse(emit_status(b"% SZS status Error for fang_control\n", time.monotonic() + 0.03, writer))
        finally:
            os.close(reader); os.close(writer)

    def test_failed_terminal_write_cannot_report_success(self):
        manifest = {"status": "Unsatisfiable"}
        with mock.patch("fang_szs.app.write_json", side_effect=OSError("unwritable artifact")):
            self.assertEqual(terminal_checkpoint(Path("unused"), manifest, None), "Error")

    def test_expired_success_with_failed_retry_still_reports_timeout(self):
        manifest = {"status": "Unsatisfiable"}
        supervisor = mock.Mock()
        supervisor.check.side_effect = Failure("Timeout", "expired")
        with mock.patch("fang_szs.app.write_json", side_effect=[None, OSError("retry failed")]):
            self.assertEqual(terminal_checkpoint(Path("unused"), manifest, supervisor), "Timeout")
        self.assertEqual(manifest["status"], "Timeout")

    def test_strict_json_duplicate(self):
        with self.assertRaises(ValueError): strict_json('{"a":1,"a":2}')

    def test_strict_json_nonfinite(self):
        with self.assertRaises(ValueError): strict_json('{"a":NaN}')

    def test_sealed_snapshot_cannot_be_written(self):
        with tempfile.TemporaryDirectory() as tmp:
            snapshot = Snapshot(Path(tmp) / "input", INPUT)
            try:
                with self.assertRaises(OSError): os.write(snapshot.fd, b"changed")
                snapshot.verify()
            finally: snapshot.close()

    def test_metadata_inconsistency(self):
        with self.assertRaises(Failure): engine_outcome({"exit_code": 2, "classification": "completed"}, b"unknown\n", b"")

    def test_higher_order_at_and_lambda_are_outside_scope(self):
        for source in (b"thf(c,axiom,(f @ X)).", b"thf(c,axiom,(^ [X]: p(X)))."):
            position = next(index for index, byte in enumerate(source) if byte in b"@^")
            status, _ = engine_outcome({"exit_code": 3, "classification": "nonzero-exit"}, b"",
                f"InvalidInput at byte {position}: invalid character\n".encode(), source)
            self.assertEqual(status, "Inappropriate")

    def test_control_byte_is_established_input_error(self):
        status, _ = engine_outcome({"exit_code": 3, "classification": "nonzero-exit"}, b"",
            b"InvalidInput at byte 0: invalid character\n", b"\0")
        self.assertEqual(status, "InputError")

    def fixture(self):
        return (HEADER + "def originalInput : String := " + quote(INPUT) + "\n\n"
            + "def originalCertificate : String := " + quote(PROOF) + "\n\n"
            + "def problem : Problem := []\n\n"
            + "def certificate : Certificate := Certificate.mk [] 0\n\n" + FOOTER).encode()

    def test_fixed_template_retains_only_constructor_data(self):
        self.assertIn("def problem : Problem := []", fixed_replay(self.fixture(), INPUT, PROOF))

    def test_export_cannot_select_imports(self):
        with self.assertRaises(Failure): fixed_replay(self.fixture().replace(b"import Fang.CertificateInput", b"import Malicious"), INPUT, PROOF)

    def test_export_cannot_inject_commands(self):
        with self.assertRaises(Failure): fixed_replay(self.fixture().replace(b"def problem : Problem := []", b"def problem : Problem := by exact []"), INPUT, PROOF)

    def test_export_cannot_substitute_input(self):
        with self.assertRaises(Failure): fixed_replay(self.fixture(), INPUT + b" ", PROOF)

    def test_export_cannot_substitute_certificate(self):
        with self.assertRaises(Failure): fixed_replay(self.fixture(), INPUT, PROOF + b" ")

    def test_export_cannot_select_axiom(self):
        with self.assertRaises(Failure): fixed_replay(self.fixture().replace(b"by cbv", b"by exact sorry"), INPUT, PROOF)


class StorageTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fang-storage-control-")
        self.public = Path(self.temporary.name) / "public"
        self.public.mkdir()
        self.supervisor = Supervisor(Limits(wall_seconds=10))
        self.report = {}
        self.workspace = KernelWorkspace(self.supervisor, self.public, self.report)

    def tearDown(self):
        self.supervisor.close()
        if self.workspace.native.exists():
            shutil.rmtree(self.workspace.native)
        self.temporary.cleanup()

    def library(self):
        source = Path(self.temporary.name) / "library"
        source.mkdir()
        (source / "checked.olean").write_bytes(b"checked library control")
        digest = __import__("hashlib").sha256((source / "checked.olean").read_bytes()).hexdigest()
        return {"proof_library": {"path": str(source), "files_sha256": {"checked.olean": digest}}}

    def test_copy_archive_and_owned_cleanup(self):
        self.workspace.stage_library(self.library())
        (self.workspace.native / "kernel").mkdir()
        (self.workspace.native / "kernel/Audit.lean").write_bytes(b"fixed audit control")
        self.workspace.archive()
        self.workspace.cleanup()
        self.assertEqual((self.public / "kernel/Audit.lean").read_bytes(), b"fixed audit control")
        self.assertFalse((self.public / ".proof-library").exists())
        self.assertEqual(self.report["state"], "archived-and-removed")
        self.assertFalse(self.workspace.native.exists())
        self.assertEqual(self.supervisor.additional_artifact_roots, [])

    def test_bad_library_pin_retains_failed_workspace(self):
        config = self.library()
        config["proof_library"]["files_sha256"]["checked.olean"] = "0" * 64
        with self.assertRaises(Failure) as caught:
            self.workspace.stage_library(config)
        self.workspace.retain_failure(caught.exception)
        self.assertEqual(self.report["state"], "retained-after-failure")
        self.assertTrue(self.workspace.native.is_dir())

    def test_changed_staged_library_is_rejected(self):
        self.workspace.stage_library(self.library())
        (self.workspace.library / "checked.olean").write_bytes(b"changed")
        with self.assertRaises(Failure):
            self.workspace.verify_library()

    def test_archive_checks_previously_checked_source_hash(self):
        (self.workspace.native / "Audit.lean").write_bytes(b"changed")
        with self.assertRaises(Failure):
            self.workspace.archive({"Audit.lean": "0" * 64})
        self.assertFalse((self.public / "Audit.lean").exists())

    def test_public_and_native_bytes_share_one_cap(self):
        (self.public / "public-data").write_bytes(b"123456")
        (self.workspace.native / "native-data").write_bytes(b"abcdef")
        self.supervisor.limits = Limits(artifact_bytes=10)
        with self.assertRaises(Failure) as caught:
            self.supervisor.tree_bytes(self.public)
        self.assertEqual(caught.exception.status, "ResourceOut")

    def test_expired_archive_retains_native_evidence(self):
        (self.workspace.native / "proof-data").write_bytes(b"keep")
        self.supervisor.deadline = time.monotonic() - 1
        with self.assertRaises(Failure) as caught:
            self.workspace.archive()
        self.workspace.retain_failure(caught.exception)
        self.assertEqual(caught.exception.status, "Timeout")
        self.assertEqual((self.workspace.native / "proof-data").read_bytes(), b"keep")
        self.assertEqual(self.report["retained_path"], str(self.workspace.native))

    def test_archive_does_not_overwrite_public_files(self):
        (self.workspace.native / "proof-data").write_bytes(b"new")
        (self.public / "proof-data").write_bytes(b"old")
        with self.assertRaises(FileExistsError):
            self.workspace.archive()
        self.assertEqual((self.public / "proof-data").read_bytes(), b"old")

    def test_changed_native_directory_identity_is_rejected(self):
        self.workspace.archive()
        device, inode = self.workspace.identity
        self.workspace.identity = device, inode + 1
        with self.assertRaises(Failure):
            self.workspace.cleanup()
        self.assertTrue(self.workspace.native.is_dir())

    def test_symlink_in_workspace_is_rejected(self):
        (self.workspace.native / "link").symlink_to(self.public, target_is_directory=True)
        with self.assertRaises(Failure):
            self.workspace.archive()

    def test_failure_after_cleanup_does_not_claim_retained_native_files(self):
        self.workspace.archive()
        self.workspace.cleanup()
        self.workspace.retain_failure(Failure("Timeout", "final deadline"))
        self.assertEqual(self.report["state"], "removed-before-terminal-failure")
        self.assertTrue(self.report["native_removed"])

    def test_missing_native_directory_does_not_claim_archive_or_cleanup(self):
        self.workspace.native.rmdir()
        self.workspace.retain_failure(OSError("native path disappeared"))
        self.assertEqual(self.report["state"], "native-missing-after-failure")
        self.assertFalse(self.report["archive_completed"])
        self.assertFalse(self.report["cleanup_completed"])
        self.assertFalse(self.report["native_removed"])

    def test_cleanup_failure_preserves_completed_archive_state(self):
        (self.workspace.native / "Audit.lean").write_bytes(b"checked archive control")
        self.workspace.archive()
        with mock.patch("pathlib.Path.unlink", side_effect=PermissionError("cleanup denied")):
            with self.assertRaises(PermissionError) as caught:
                self.workspace.cleanup()
        self.workspace.retain_failure(caught.exception)
        self.assertTrue(self.report["archive_completed"])
        self.assertFalse(self.report["cleanup_completed"])
        self.assertEqual(self.report["state"], "retained-after-failure")
        self.assertEqual((self.public / "Audit.lean").read_bytes(), b"checked archive control")


class AxiomTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        path = TOOLS.parent / "tools/replay/axiom_audit.py"
        spec = importlib.util.spec_from_file_location("fixed_audit_test", path)
        cls.parser = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(cls.parser)

    def reports(self):
        return "\n".join("'" + name + "' depends on axioms: [propext, Classical.choice, Quot.sound]" for name in sorted(REQUIRED_AUDITS))

    def test_exact_reports(self):
        self.assertEqual(set(exact_axioms(self.reports(), self.parser)), REQUIRED_AUDITS)

    def test_missing(self):
        with self.assertRaises((Failure, ValueError)): exact_axioms("\n".join(self.reports().splitlines()[1:]), self.parser)

    def test_extra(self):
        with self.assertRaises((Failure, ValueError)): exact_axioms(self.reports() + "\n'Other' does not depend on any axioms", self.parser)

    def test_duplicate(self):
        with self.assertRaises((Failure, ValueError)): exact_axioms(self.reports() + "\n" + self.reports().splitlines()[0], self.parser)

    def test_custom_axiom(self):
        with self.assertRaises((Failure, ValueError)): exact_axioms(self.reports().replace("propext", "Invented.fact"), self.parser)

    def test_spoofing_comment(self):
        with self.assertRaises((Failure, ValueError)): exact_axioms("unexpected\n" + self.reports(), self.parser)


@unittest.skipUnless(sys.platform == "linux", "Linux/WSL process controls")
class ProcessTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fang-adapter-control-")
        self.root = Path(self.temporary.name)
        source = source_fixture(self.root)
        library = self.root / "library/Fang"; library.mkdir(parents=True)
        for name in ("FrontendSoundness", "CertificateInput"): (library / (name + ".olean")).write_bytes(b"synthetic")
        for name in ("engine", "checker", "lean"):
            path = self.root / name
            path.write_text(FAKE.replace("PROOF", repr(PROOF))); path.chmod(0o700)
        provenance = self.root / "provenance.json"; provenance.write_text('{"scope":"synthetic protocol controls only"}')
        self.installation = self.root / "installation.json"
        self.installation.write_text(json.dumps(make_installation(self.root / "engine", self.root / "checker", self.root / "lean",
            library.parent, source, [provenance])))
        self.input = self.root / "source with\nnewline.p"; self.input.write_bytes(INPUT)
        self.output = self.root / "run"

    def tearDown(self):
        archive_root = getattr(self, "artifact_root", None)
        if archive_root is not None:
            destination = archive_root / self._testMethodName
            destination.mkdir()
            for source in (self.root / "installation.json", self.input):
                if source.is_file() and not source.is_symlink():
                    shutil.copy2(source, destination / ("captured-caller-input.p" if source == self.input else source.name))
            if self.output.is_dir():
                for path in self.output.rglob("*"):
                    target = destination / "run" / path.relative_to(self.output)
                    if path.is_dir():
                        target.mkdir(parents=True, exist_ok=True)
                    elif path.is_file() and not path.is_symlink():
                        target.parent.mkdir(parents=True, exist_ok=True)
                        if path.stat().st_size <= 16 << 20:
                            shutil.copy2(path, target)
                        else:
                            target.with_name(target.name + ".omitted.json").write_text(json.dumps({
                                "bytes": path.stat().st_size, "scope": "Oversized synthetic artifact retained as size metadata; content was not read or copied"}))
        self.temporary.cleanup()

    def command(self, extra=()):
        return [sys.executable, str(TOOLS / "fang-szs.py"), str(self.input), "--installation", str(self.installation),
            "--artifacts", str(self.output), "--check", "compiled", "--wall-seconds", "3", *extra]

    def invoke(self, mode, expected, code, extra=()):
        self.set_mode(mode)
        result = subprocess.run(self.command(extra), env=os.environ | {"FANG_TEST_MODE": mode, "PYTHONDONTWRITEBYTECODE": "1"},
            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=8)
        self.assertEqual(result.returncode, code, result.stderr)
        lines = result.stdout.decode().splitlines()
        self.assertEqual(len(lines), 2, result.stdout)
        self.assertEqual(lines[0], "% Fang checking profile: compiled")
        self.assertTrue(lines[1].startswith("% SZS status " + expected + " for fang_"), result.stdout)
        self.assertNotIn(b"forged", result.stdout)
        if expected != "Unsatisfiable": self.assertNotIn(b"Unsatisfiable", result.stdout)
        self.assertEqual(result.stderr, b"")
        return json.loads((self.output / "manifest.json").read_text()) if (self.output / "manifest.json").exists() else None

    def set_mode(self, mode):
        if mode == "candidate": return
        config = json.loads(self.installation.read_text())
        for name in ("engine", "checker", "lean"):
            target = self.root / name
            target.write_text(FAKE.replace("PROOF", repr(PROOF)).replace('os.environ.get("FANG_TEST_MODE", "candidate")', repr(mode)))
            config[name]["sha256"] = __import__("hashlib").sha256(target.read_bytes()).hexdigest()
        self.installation.write_text(json.dumps(config))

    def test_candidate_protocol(self):
        manifest = self.invoke("candidate", "Unsatisfiable", 0)
        self.assertTrue(manifest["compiled_check"]["accepted"])
        self.assertNotIn("kernel_check", manifest)
        self.assertEqual((self.output / "input.p").read_bytes(), INPUT)

    def test_unknown(self): self.invoke("unknown", "GaveUp", 2)
    def test_duplicate(self): self.invoke("duplicate", "InputError", 3)
    def test_arity(self): self.invoke("arity", "InputError", 3)
    def test_unsupported(self): self.invoke("unsupported", "Inappropriate", 4)
    def test_uppercase(self): self.invoke("uppercase", "Inappropriate", 4)
    def test_nonascii_boundary(self): self.invoke("ascii", "Inappropriate", 4)
    def test_uncertain_syntax(self): self.invoke("syntax", "Inappropriate", 4)
    def test_internal_invalid_input(self): self.invoke("invalid-internal", "Error", 6)
    def test_resource(self): self.invoke("resource", "ResourceOut", 5)
    def test_panic_partial_resource(self): self.invoke("panic", "Error", 6)
    def test_signal_without_resource_evidence(self): self.invoke("signal", "Error", 6)
    def test_spoofed_status(self): self.invoke("spoof", "Error", 6)
    def test_missing_certificate(self): self.invoke("missing-proof", "Error", 6)
    def test_checker_rejects(self): self.invoke("reject", "Error", 6)
    def test_checker_wrong_source(self): self.invoke("wrong-source", "Error", 6)
    def test_checker_spoof(self): self.invoke("checker-spoof", "Error", 6)
    def test_changed_input_snapshot(self): self.invoke("mutate-input", "Error", 6)
    def test_changed_certificate_snapshot(self): self.invoke("mutate-proof", "Error", 6)
    def test_input_limit(self): self.invoke("candidate", "ResourceOut", 5, ("--max-input-bytes", "2"))
    def test_proof_limit(self): self.invoke("candidate", "ResourceOut", 5, ("--max-certificate-bytes", "2"))
    def test_log_limit(self): self.invoke("logs", "ResourceOut", 5, ("--max-log-bytes", "100"))
    def test_sparse_log_has_bounded_failure_accounting(self):
        manifest = self.invoke("sparse-log", "ResourceOut", 5)
        self.assertEqual(manifest["processes"][0]["stdout_hash_status"], "skipped-over-log-limit")
    def test_replaced_fifo_log_does_not_block_finalization(self):
        manifest = self.invoke("fifo-log", "Error", 6)
        self.assertEqual(manifest["processes"][0]["stdout_hash_status"], "nonregular-or-replaced-path")
    def test_timeout_search(self): self.invoke("timeout-search", "Timeout", 7, ("--wall-seconds", "0.4"))
    def test_timeout_checker(self): self.invoke("timeout-checker", "Timeout", 7, ("--wall-seconds", "0.5"))
    def test_memory(self): self.invoke("memory-search", "MemoryOut", 8, ("--memory-mib", "48"))

    def test_orphan_is_killed_and_reaped(self):
        self.invoke("orphan", "Error", 6)
        pid = int((self.output / "search/child.pid").read_text())
        self.assertFalse(Path(f"/proc/{pid}").exists())

    def test_stale_directory_untouched(self):
        self.output.mkdir(); sentinel = self.output / "sentinel"; sentinel.write_bytes(b"keep")
        self.invoke("candidate", "Error", 6)
        self.assertEqual(sentinel.read_bytes(), b"keep")
        self.assertEqual(list(self.output.iterdir()), [sentinel])

    def test_executable_pin_mismatch(self):
        with (self.root / "engine").open("a") as stream: stream.write("# changed\n")
        self.invoke("candidate", "Error", 6)

    def test_running_adapter_mismatch(self):
        config = json.loads(self.installation.read_text())
        target = Path(config["source_root"]) / "tools/fang_szs/protocol.py"
        target.write_text(target.read_text() + "\n# changed installed source\n")
        config["source_sha256"]["tools/fang_szs/protocol.py"] = __import__("hashlib").sha256(target.read_bytes()).hexdigest()
        self.installation.write_text(json.dumps(config))
        self.invoke("candidate", "Error", 6)

    def test_inherited_loader_and_python_overrides_not_forwarded(self):
        manifest = self.invoke("candidate", "Unsatisfiable", 0)
        for process in manifest["processes"]:
            self.assertEqual(set(process["environment"]), {"PATH", "LANG", "LC_ALL", "PYTHONDONTWRITEBYTECODE"})

    def test_fifo_input_is_rejected_without_waiting(self):
        self.input.unlink(); os.mkfifo(self.input)
        self.invoke("candidate", "Error", 6)

    def cancel(self, mode, stage):
        self.set_mode(mode)
        process = subprocess.Popen(self.command(), env=os.environ | {"FANG_TEST_MODE": mode, "PYTHONDONTWRITEBYTECODE": "1"},
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        try:
            deadline = time.monotonic() + 2
            while not (self.output / stage / "ready").exists():
                if process.poll() is not None or time.monotonic() > deadline: self.fail("Control child did not become ready")
                time.sleep(0.01)
            process.send_signal(signal.SIGTERM)
            stdout, stderr = process.communicate(timeout=3)
            self.assertEqual(process.returncode, 9, stderr)
            self.assertIn(b"% SZS status Forced for fang_", stdout)
            self.assertNotIn(b"Unsatisfiable", stdout)
            manifest = json.loads((self.output / "manifest.json").read_text())
            for record in manifest["processes"]:
                for pid in record.get("terminated_owned_pids", []): self.assertFalse(Path(f"/proc/{pid}").exists())
        finally:
            if process.poll() is None: process.kill(); process.wait()

    def test_cancel_before_candidate(self): self.cancel("cancel-search", "search")
    def test_cancel_after_candidate(self): self.cancel("cancel-checker", "checker")


if __name__ == "__main__":
    unittest.main(verbosity=2)
