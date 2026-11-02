"""Public help and automatic artifact controls; no proof execution."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
from contextlib import redirect_stdout
import importlib.util
import io
import json
import os
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock

TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))
sys.path.insert(0, str(TOOLS / "fof_szs"))
from fang_szs import app, cli
from fang_szs.supervisor import EXIT, Failure

SPEC = importlib.util.spec_from_file_location("fang_public_fof_test", TOOLS / "fof_szs/main.py")
fof = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(fof)


class PublicCliTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fang-public-cli-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        previous = Path.cwd()
        os.chdir(self.root)
        self.addCleanup(os.chdir, previous)

    def variants(self):
        return ((app, "--installation", "run_pipeline", 64 << 20),
                (fof, "--capability", "pipeline", 1 << 20))

    def test_legacy_requires_explicit_config_and_artifacts(self):
        for module, config, _, _ in self.variants():
            for args in (["input.p"], ["input.p", config, "config.json"],
                         ["input.p", "--artifacts", "run"]):
                with self.subTest(module=module.__name__, args=args), mock.patch.object(cli.uuid, "uuid4") as uuid:
                    with self.assertRaises(Failure):
                        module.arguments(args)
                    uuid.assert_not_called()
        self.assertEqual(list(self.root.iterdir()), [])

    def test_public_execution_still_requires_launcher_configuration(self):
        for module, _, _, _ in self.variants():
            with mock.patch.object(cli.uuid, "uuid4") as uuid:
                with self.assertRaises(Failure):
                    module.arguments(["input.p"], public=True)
                uuid.assert_not_called()
        self.assertEqual(list(self.root.iterdir()), [])

    def test_defaults_preserve_both_adapter_contracts(self):
        for module, config, _, certificate_cap in self.variants():
            args = module.arguments(["input.p", config, "config.json", "--artifacts", "run"])
            self.assertEqual((args.check, args.output), ("kernel", "status"))
            self.assertEqual((args.wall_seconds, args.memory_mib), (60, 2048))
            self.assertEqual((args.max_steps, args.max_clauses, args.max_operations), (100000, 1000, 5000000))
            self.assertEqual((args.max_input_bytes, args.max_certificate_bytes), (1 << 20, certificate_cap))
            self.assertEqual((args.max_solution_bytes, args.max_log_bytes, args.max_artifact_bytes), (16 << 20, 4 << 20, 256 << 20))
            self.assertFalse(args.auto_artifacts)

    def test_public_paths_are_unique_without_creating_directories(self):
        paths = []
        for module, config, _, _ in self.variants():
            for _ in range(2):
                args = module.arguments(["input.p", config, "config.json"], public=True)
                self.assertTrue(args.auto_artifacts)
                self.assertEqual(args.artifacts.parent, self.root / ".local/runs")
                self.assertRegex(args.artifacts.name, r"^[0-9a-f]{32}$")
                paths.append(args.artifacts)
        self.assertEqual(len(set(paths)), 4)
        self.assertEqual(list(self.root.iterdir()), [])

    def test_public_explicit_artifacts_are_preserved(self):
        for module, config, _, _ in self.variants():
            with mock.patch.object(cli.uuid, "uuid4") as uuid:
                args = module.arguments(["input.p", config, "config.json", "--artifacts", "my run"], public=True)
                self.assertEqual(args.artifacts, Path("my run"))
                self.assertFalse(args.auto_artifacts)
                uuid.assert_not_called()

    def test_invalid_limits_do_not_allocate_a_run_name(self):
        bad = [("--wall-seconds", "nan"), ("--wall-seconds", "inf"), ("--wall-seconds", "0.24"),
               ("--wall-seconds", "86401"), ("--memory-mib", "15"), ("--memory-mib", "1048577"),
               ("--max-solution-bytes", "16777217"), ("--check", "unchecked"), ("--output", "sat")]
        for name in ("steps", "clauses", "operations", "input-bytes", "certificate-bytes", "log-bytes", "artifact-bytes"):
            bad += [("--max-" + name, "-1"), ("--max-" + name, str(1 << 63))]
        for module, config, _, _ in self.variants():
            for flag, value in bad:
                with self.subTest(module=module.__name__, flag=flag, value=value), mock.patch.object(cli.uuid, "uuid4") as uuid:
                    with self.assertRaises(Failure):
                        module.arguments(["input.p", config, "config.json", flag, value], public=True)
                    uuid.assert_not_called()
        self.assertEqual(list(self.root.iterdir()), [])

    def test_fof_byte_caps_remain_distinct_from_cnf(self):
        for flag in ("--max-input-bytes", "--max-certificate-bytes"):
            with self.assertRaises(Failure):
                fof.arguments(["input.p", "--capability", "config.json", flag, str((1 << 20) + 1)], public=True)
            args = app.arguments(["input.p", "--installation", "config.json", flag, str((1 << 20) + 1)], public=True)
            self.assertEqual(getattr(args, flag[2:].replace("-", "_")), (1 << 20) + 1)

    def test_help_and_alias_explain_all_flags_without_side_effects(self):
        for module, config, _, _ in self.variants():
            outputs = []
            for args in (["help"], ["--help"]):
                capture = io.StringIO()
                with redirect_stdout(capture), mock.patch.object(module, "Supervisor") as supervisor, mock.patch.object(cli.uuid, "uuid4") as uuid:
                    with self.assertRaises(SystemExit) as exit_status:
                        module.main(args, public=True)
                    self.assertEqual(exit_status.exception.code, 0)
                    supervisor.assert_not_called()
                    uuid.assert_not_called()
                outputs.append(capture.getvalue())
            self.assertEqual(outputs[0], outputs[1])
            text = outputs[0]
            self.assertTrue(text.startswith("usage: fang "))
            for option in (config, "--help", "--artifacts", "--check", "--output", "--wall-seconds", "--memory-mib",
                           "--max-steps", "--max-clauses", "--max-operations", "--max-input-bytes",
                           "--max-certificate-bytes", "--max-solution-bytes", "--max-log-bytes", "--max-artifact-bytes"):
                self.assertIn(option, text)
            normalized = " ".join(text.split())
            for description in ("no SAT result", "default: kernel", "default: status", "seconds", "MiB", "bytes",
                                "current directory", "compiled checker", "fresh exact-input Lean proof"):
                self.assertIn(description, normalized)
        self.assertEqual(list(self.root.iterdir()), [])

    def test_help_filename_is_not_a_broad_alias(self):
        for module, config, _, _ in self.variants():
            for public in (False, True):
                args = module.arguments(["help", config, "config.json", "--artifacts", "run"], public=public)
                self.assertEqual(args.input, Path("help"))
                args = module.arguments(["./help", config, "config.json", "--artifacts", "run"], public=public)
                self.assertEqual(args.input, Path("help"))

    def test_main_creates_and_announces_only_automatic_runs(self):
        for module, config, pipeline, _ in self.variants():
            for explicit in (False, True):
                with self.subTest(module=module.__name__, explicit=explicit):
                    writes = []
                    captured = []

                    def run(args, supervisor, manifest, root):
                        captured.append(root)
                        self.assertTrue((root / "manifest.json").is_file())
                        return "GaveUp", "Synthetic search exhaustion"

                    def emit(data, deadline, descriptor=1, cancelled=None):
                        writes.append((descriptor, data))
                        if descriptor == 2:
                            location = Path(data.decode().removeprefix("Fang artifacts: ").strip())
                            self.assertTrue((location / "manifest.json").is_file())
                            self.assertIsNotNone(cancelled)
                            self.assertFalse(cancelled())
                        return True

                    argv = ["input.p", config, "config.json"]
                    if explicit:
                        argv += ["--artifacts", str(self.root / (module.__name__ + "-explicit"))]
                    with mock.patch.object(module, pipeline, side_effect=run), mock.patch.object(module, "emit_status", side_effect=emit):
                        self.assertEqual(module.main(argv, public=True), EXIT["GaveUp"])
                    self.assertEqual(len(captured), 1)
                    self.assertEqual([descriptor for descriptor, _ in writes], [1] if explicit else [2, 1])
                    receipt = json.loads((captured[0] / "manifest.json").read_text())
                    self.assertEqual((receipt["status"], receipt["profile"], receipt["output"]), ("GaveUp", "kernel", "status"))
                    self.assertNotIn("certificate", receipt)

    def test_announcement_failure_prevents_search_and_is_recorded(self):
        for module, config, pipeline, _ in self.variants():
            for failure, expected in ((False, "Timeout"), (Failure("Forced", "Synthetic cancellation"), "Forced"),
                                      (BrokenPipeError("closed stderr"), "Error")):
                with self.subTest(module=module.__name__, status=expected):
                    root = self.root / ".local/runs" / (module.__name__ + expected)
                    writes = []

                    def emit(data, deadline, descriptor=1, cancelled=None):
                        writes.append(descriptor)
                        if descriptor == 2:
                            if isinstance(failure, BaseException):
                                raise failure
                            return False
                        return True

                    with mock.patch.object(cli.uuid, "uuid4", return_value=mock.Mock(hex=root.name)), \
                         mock.patch.object(module, pipeline) as work, mock.patch.object(module, "emit_status", side_effect=emit):
                        self.assertEqual(module.main(["input.p", config, "config.json"], public=True), EXIT[expected])
                        work.assert_not_called()
                    receipt = json.loads((root / "manifest.json").read_text())
                    self.assertEqual(receipt["status"], expected)
                    self.assertEqual(writes, [2, 1])

    def test_uuid_collision_never_overwrites_existing_run(self):
        for module, config, pipeline, _ in self.variants():
            root = self.root / ".local/runs" / module.__name__
            root.mkdir(parents=True)
            marker = root / "manifest.json"
            marker.write_bytes(b"original bytes")
            writes = []
            with mock.patch.object(cli.uuid, "uuid4", return_value=mock.Mock(hex=root.name)), \
                 mock.patch.object(module, pipeline) as work, \
                 mock.patch.object(module, "emit_status", side_effect=lambda *args, **kwargs: writes.append(kwargs.get("descriptor", 1)) or True):
                self.assertEqual(module.main(["input.p", config, "config.json"], public=True), EXIT["Error"])
                work.assert_not_called()
            self.assertEqual(marker.read_bytes(), b"original bytes")
            self.assertEqual(writes, [1])


if __name__ == "__main__":
    unittest.main()
