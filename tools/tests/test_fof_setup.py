"""Controls for optional FOF setup trust boundaries and proof requirements."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import copy
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest

TOOLS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS))
import fof_setup


class SetupControls(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fang-fof-setup-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)

    def toolchain(self):
        root = self.root / "toolchain"
        (root / "bin").mkdir(parents=True)
        (root / "lib").mkdir()
        (root / "bin/lean").write_bytes(b"compiler")
        (root / "lib/module.olean").write_bytes(b"checked module")
        return root

    def source(self):
        source = self.root / "source"
        for package in ("fof_szs", "fang_szs"):
            path = source / "tools" / package / "capability.py"
            path.parent.mkdir(parents=True)
            path.write_text("raise RuntimeError('must not execute')\n")
        pins = {path.relative_to(source).as_posix(): fof_setup.digest(path)
                for path in source.rglob("*.py")}
        return source, pins

    def proof(self):
        (self.root / "tools").mkdir()
        shutil.copyfile(TOOLS / "fof_audits.json", self.root / "tools/fof_audits.json")
        shutil.copyfile(TOOLS / "fof_proof_inventory.json", self.root / "tools/fof_proof_inventory.json")
        inventory = json.loads((TOOLS / "fof_proof_inventory.json").read_text())
        expected = inventory["audits"]
        rows = [{"module": module, "declaration": name, "axioms": ["propext", "Quot.sound"]}
                for module, names in expected.items() for name in names]
        return {"status": "passed", "completed_modules": inventory["modules"],
                "declared_axiom_audits": len(rows), "axiom_audits": rows}

    def test_full_toolchain_inventory_accepts_internal_symlink(self):
        root = self.toolchain()
        (root / "bin/internal").symlink_to("../lib/module.olean")
        inventory = fof_setup.capture_toolchain(root)
        self.assertEqual(set(inventory), {"bin/lean", "bin/internal", "lib/module.olean"})
        self.assertEqual(inventory["bin/internal"]["resolved"], "lib/module.olean")
        fof_setup.toolchain.verify(root, inventory)

    def test_external_toolchain_symlink_is_rejected(self):
        root = self.toolchain()
        external = self.root / "external"
        external.write_bytes(b"external")
        (root / "bin/escape").symlink_to(external)
        with self.assertRaisesRegex(ValueError, "escapes"):
            fof_setup.capture_toolchain(root)

    def test_retargeted_toolchain_symlink_is_rejected(self):
        root = self.toolchain()
        link = root / "bin/link"
        link.symlink_to("../lib/module.olean")
        inventory = fof_setup.capture_toolchain(root)
        link.unlink()
        link.symlink_to("lean")
        with self.assertRaisesRegex(ValueError, "differs"):
            fof_setup.toolchain.verify(root, inventory)

    def test_changed_toolchain_file_is_rejected(self):
        root = self.toolchain()
        inventory = fof_setup.capture_toolchain(root)
        (root / "lib/module.olean").write_bytes(b"changed module")
        with self.assertRaisesRegex(ValueError, "differs"):
            fof_setup.toolchain.verify(root, inventory)

    def test_added_toolchain_file_is_rejected(self):
        root = self.toolchain()
        inventory = fof_setup.capture_toolchain(root)
        (root / "lib/extra.olean").write_bytes(b"extra")
        with self.assertRaisesRegex(ValueError, "differs"):
            fof_setup.toolchain.verify(root, inventory)

    def test_inventory_deadline_is_honored(self):
        def expired():
            raise TimeoutError("shared deadline")
        with self.assertRaisesRegex(TimeoutError, "shared deadline"):
            fof_setup.capture_toolchain(self.toolchain(), expired)

    def test_source_verification_does_not_execute_helpers(self):
        source, pins = self.source()
        fof_setup.verify_sources_before_import(source, pins)

    def test_changed_helper_is_rejected_before_import(self):
        source, pins = self.source()
        (source / "tools/fof_szs/capability.py").write_text("raise AssertionError('changed')\n")
        with self.assertRaisesRegex(ValueError, "changed before provisioning"):
            fof_setup.verify_sources_before_import(source, pins)

    def test_unlisted_executable_helper_is_rejected(self):
        source, pins = self.source()
        (source / "tools/fof_szs/extra.py").write_text("raise AssertionError('unlisted')\n")
        with self.assertRaisesRegex(ValueError, "Unexpected executable helper"):
            fof_setup.verify_sources_before_import(source, pins)

    def test_helper_symlink_is_rejected(self):
        source, pins = self.source()
        path = source / "tools/fof_szs/capability.py"
        path.unlink()
        path.symlink_to(source / "tools/fang_szs/capability.py")
        with self.assertRaisesRegex(ValueError, "changed before provisioning"):
            fof_setup.verify_sources_before_import(source, pins)

    def test_exact_added_audit_set_is_accepted(self):
        proof = self.proof()
        result = fof_setup.check_proofs(self.root, proof)
        self.assertEqual(sum(map(len, result.values())), 64)

    def test_missing_theorem_with_same_total_is_rejected(self):
        proof = self.proof()
        proof["axiom_audits"][0]["declaration"] = "Unrelated.theorem"
        with self.assertRaisesRegex(ValueError, "audit differs"):
            fof_setup.check_proofs(self.root, proof)

    def test_duplicate_audit_with_same_total_is_rejected(self):
        proof = self.proof()
        proof["axiom_audits"][0] = copy.deepcopy(proof["axiom_audits"][1])
        with self.assertRaisesRegex(ValueError, "audit differs"):
            fof_setup.check_proofs(self.root, proof)

    def test_unexpected_axiom_is_rejected(self):
        proof = self.proof()
        proof["axiom_audits"][0]["axioms"].append("Unproved.assumption")
        with self.assertRaisesRegex(ValueError, "Unexpected FOF theorem axiom"):
            fof_setup.check_proofs(self.root, proof)

    def test_incomplete_combined_proof_is_rejected(self):
        proof = self.proof()
        proof["completed_modules"].pop()
        with self.assertRaisesRegex(ValueError, "inventory did not pass"):
            fof_setup.check_proofs(self.root, proof)


if __name__ == "__main__":
    unittest.main(verbosity=2)
