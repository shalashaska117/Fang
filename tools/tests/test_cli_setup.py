"""Exercise public launcher dispatch, quoting and preservation of old installs."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))
import cli_setup


class LauncherTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fang cli '$ test ")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / "bin").mkdir()

    def install(self, *, fof=False):
        config = self.root / ("fof-capability.json" if fof else "installation.json")
        config.write_text("{}\n")
        package = self.root / "source/tools" / ("fof_szs" if fof else "fang_szs")
        package.mkdir(parents=True)
        (package / "__init__.py").write_text("")
        (package / ("main.py" if fof else "app.py")).write_text(
            "import json,sys\ndef main(*, public=False):\n"
            "    print(json.dumps({'public': public, 'argv': sys.argv[1:]}))\n"
            "    return 17\n")
        return cli_setup.provision(self.root, fof=fof)

    def run_command(self, launcher, *args):
        result = subprocess.run([str(launcher), *args], capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 17)
        self.assertEqual(result.stderr, "")
        return json.loads(result.stdout)

    def test_cnf_dispatch_preserves_literal_arguments_and_exit_code(self):
        launcher = self.install()
        args = ["problem 'with spaces' $(literal).p", "--wall-seconds", "2"]
        value = self.run_command(launcher, *args)
        self.assertTrue(value["public"])
        self.assertEqual(value["argv"], ["--installation", str(self.root / "installation.json"), *args])

    def test_fof_dispatch_uses_the_installed_mixed_pipeline(self):
        launcher = self.install(fof=True)
        value = self.run_command(launcher, "problem.p", "--output", "tstp")
        self.assertEqual(value["argv"], ["--capability", str(self.root / "fof-capability.json"), "problem.p", "--output", "tstp"])
        self.assertTrue(value["public"])

    def test_help_alias_is_exact_and_passes_no_input(self):
        launcher = self.install()
        self.assertEqual(self.run_command(launcher, "help"), self.run_command(launcher, "--help"))
        self.assertEqual(self.run_command(launcher, "./help")["argv"][-1], "./help")
        self.assertEqual(self.run_command(launcher, "help", "--output", "status")["argv"][-3:], ["help", "--output", "status"])

    def test_existing_raw_engine_or_command_is_never_overwritten(self):
        existing = self.root / "bin/fang"
        existing.write_bytes(b"existing raw engine")
        with self.assertRaises(FileExistsError):
            self.install()
        self.assertEqual(existing.read_bytes(), b"existing raw engine")
        self.assertFalse((self.root / "command-receipt.json").exists())

    def test_missing_pipeline_cannot_install_launcher(self):
        with self.assertRaisesRegex(ValueError, "must be installed"):
            cli_setup.provision(self.root)
        self.assertFalse((self.root / "bin/fang").exists())


if __name__ == "__main__":
    unittest.main()
