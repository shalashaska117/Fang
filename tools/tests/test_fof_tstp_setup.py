"""Adversarial controls for portable FOF exporter provisioning and receipt links.

Synthetic files model completed build records; no test invokes a compiler or
claims that the fixture's placeholder object files are valid Lean modules.
"""
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
sys.path.insert(0, str(TOOLS / "fof_szs"))
import fof_tstp_setup
from fof_szs import capability, toolchain


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


class ExporterSetupControls(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="fang-fof-tstp-setup-")
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.source = self.root / "source"
        source_names = (
            "lean/Fang/FOF/TstpExport.lean", "lean/FofTstpMain.lean",
            "lean/Fang/BoundedInput.lean", "proofs/fof-tstp/CheckedText.lean",
            "proofs/fof-tstp/Audit.lean", "tools/fof_proof_inventory.json",
            "tools/replay/fof_replay.py", "tools/replay/source_witness.py",
            "tools/replay/axiom_audit.py")
        for name in source_names:
            path = self.source / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text("synthetic source: " + name + "\n")
        shutil.copyfile(TOOLS / "fof_proof_inventory.json", self.source / "tools/fof_proof_inventory.json")
        self.inventory = fof_tstp_setup.read_inventory(self.source)
        source_hashes = {name: capability.digest(self.source / name) for name in source_names}
        checked_sources = {
            name.removeprefix("lean/") if name.startswith("lean/") else
                "Fang/FOF/TSTP/" + name.removeprefix("proofs/fof-tstp/"): value
            for name, value in source_hashes.items() if name.endswith(".lean")}
        library = self.root / "proof-library"
        for name in ("Fang/FOF/VersionedCheck.olean", "Fang/FOF/FOFByteSemantics.olean",
                     "Fang/FOF/FofCertificateInput.olean", "Fang/FOF/Replay.olean"):
            path = library / name
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(b"synthetic checked object")
        library_record = {"path": str(library), "files_sha256": capability.inventory(library)}
        binary = self.root / "bin"
        binary.mkdir()
        for name in ("fang-ground-fof-driver", "fang-fof-check", "fang-fof-tstp-export"):
            (binary / name).write_text("synthetic executable: " + name + "\n")
        rows = [{"module": module, "declaration": theorem, "axioms": ["propext", "Quot.sound"]}
                for module, names in self.inventory["audits"].items() for theorem in names]
        self.proof = {"status": "passed", "completed_modules": self.inventory["modules"],
            "declared_axiom_audits": len(rows), "axiom_audits": rows,
            "source_sha256": checked_sources, "build_output_sha256": library_record["files_sha256"]}
        proof_path = self.root / "proof-suite.json"
        write_json(proof_path, self.proof)
        self.build = {"status": "built-and-checked", "proof_suite": str(proof_path),
            "proof_suite_sha256": capability.digest(proof_path), "source_sha256": source_hashes,
            "library_sha256": library_record["files_sha256"],
            "python": capability.record(Path(sys.executable).resolve()),
            "fof": {"binaries_sha256": {name: capability.digest(binary / name) for name in
                ("fang-ground-fof-driver", "fang-fof-check", "fang-fof-tstp-export")},
                "exporter": {"theorem": fof_tstp_setup.TEXT_THEOREM,
                    "inventory_sha256": source_hashes["tools/fof_proof_inventory.json"]}}}
        write_json(self.root / "build-manifest.json", self.build)
        self.exporter = capability.record(binary / "fang-fof-tstp-export") | {
            "sources_sha256": {str(self.source / name): value for name, value in source_hashes.items()},
            "proof_receipt": capability.record(proof_path),
            "build_receipt": capability.record(self.root / "build-manifest.json")}
        sysroot = self.root / "lean-toolchain"
        (sysroot / "bin").mkdir(parents=True)
        (sysroot / "bin/lean").write_bytes(b"synthetic Lean executable")
        inventory_path = self.root / "toolchain.json"
        write_json(inventory_path, {"bin/lean": {"kind": "file", **toolchain.stable_file(sysroot / "bin/lean", lambda: None)}})
        self.build["fof"]["toolchain"] = {"path": str(sysroot), "inventory": str(inventory_path),
            "inventory_sha256": capability.digest(inventory_path), "verified_before_and_after": True,
            "lean_sha256": capability.digest(sysroot / "bin/lean")}
        self.flush_build()
        self.config = {"schema": capability.TSTP_SCHEMA, "language": capability.LANGUAGE,
            "certificate": capability.ENVELOPE, "profiles": ["kernel", "compiled"], "outputs": ["status", "tstp"],
            "max_input_bytes": capability.MAX_BYTES, "max_certificate_bytes": capability.MAX_BYTES,
            "engine": capability.record(binary / "fang-ground-fof-driver"),
            "checker": capability.record(binary / "fang-fof-check"), "python": self.build["python"],
            "proof_library": library_record,
            "runtime_source_sha256": {str(path): capability.digest(path) for path in capability.runtime_sources()},
            "dependency_source_sha256": dict(self.exporter["sources_sha256"]),
            "receipts": [self.exporter["build_receipt"]], "exporter": self.exporter,
            "kernel": {"profile": capability.KERNEL_PROFILE, "limits": dict(capability.KERNEL_LIMITS),
                "lean": capability.record(sysroot / "bin/lean"), "library": copy.deepcopy(library_record),
                "helpers": {name: capability.record(self.source / "tools/replay" / filename) for name, filename in
                    (("generate.py", "fof_replay.py"), ("source_witness.py", "source_witness.py"), ("axiom_audit.py", "axiom_audit.py"))},
                "receipt": self.exporter["build_receipt"],
                "toolchain": {"path": str(sysroot), "inventory": capability.record(inventory_path),
                              "receipt": self.exporter["build_receipt"]}}}

    def flush_build(self):
        write_json(self.root / "build-manifest.json", self.build)
        self.exporter["build_receipt"]["sha256"] = capability.digest(self.root / "build-manifest.json")

    def flush_proof(self):
        path = Path(self.build["proof_suite"])
        write_json(path, self.proof)
        value = capability.digest(path)
        self.exporter["proof_receipt"]["sha256"] = value
        self.build["proof_suite_sha256"] = value
        self.flush_build()

    def reject_exporter(self):
        with self.assertRaises((ValueError, FileNotFoundError)):
            capability.verify_exporter(self.exporter)

    def test_exact_portable_link_is_accepted(self):
        self.assertEqual(capability.verify_exporter(self.exporter), self.build)
        capability.verify(self.config)

    def test_failed_proof_is_rejected_even_with_updated_receipt_hash(self):
        self.proof["status"] = "failed"
        self.flush_proof()
        self.reject_exporter()

    def test_missing_connected_theorem_is_rejected(self):
        self.proof["axiom_audits"] = [row for row in self.proof["axiom_audits"]
            if row["declaration"] != fof_tstp_setup.TEXT_THEOREM]
        self.flush_proof()
        self.reject_exporter()

    def test_duplicate_connected_theorem_is_rejected(self):
        row = next(row for row in self.proof["axiom_audits"] if row["declaration"] == fof_tstp_setup.TEXT_THEOREM)
        self.proof["axiom_audits"].append(copy.deepcopy(row))
        self.flush_proof()
        self.reject_exporter()

    def test_duplicate_other_audit_with_same_total_is_rejected(self):
        rows = self.proof["axiom_audits"]
        other = [i for i, row in enumerate(rows) if row["declaration"] != fof_tstp_setup.TEXT_THEOREM]
        rows[other[0]] = copy.deepcopy(rows[other[1]])
        self.flush_proof()
        self.reject_exporter()

    def test_unexpected_axiom_in_other_theorem_is_rejected(self):
        row = next(row for row in self.proof["axiom_audits"] if row["declaration"] != fof_tstp_setup.TEXT_THEOREM)
        row["axioms"] = ["sorryAx"]
        self.flush_proof()
        self.reject_exporter()

    def test_missing_or_duplicate_completed_module_is_rejected(self):
        self.proof["completed_modules"] = list(self.proof["completed_modules"])
        self.proof["completed_modules"][0] = self.proof["completed_modules"][1]
        self.flush_proof()
        self.reject_exporter()

    def test_declared_audit_count_is_required(self):
        self.proof["declared_axiom_audits"] -= 1
        self.flush_proof()
        self.reject_exporter()

    def test_altered_source_bytes_are_rejected(self):
        (self.source / "lean/Fang/FOF/TstpExport.lean").write_bytes(b"altered source")
        self.reject_exporter()

    def test_omitted_source_closure_is_rejected(self):
        del self.exporter["sources_sha256"][str(self.source / "proofs/fof-tstp/CheckedText.lean")]
        self.reject_exporter()

    def test_missing_required_source_in_both_maps_is_rejected(self):
        name = "proofs/fof-tstp/CheckedText.lean"
        del self.exporter["sources_sha256"][str(self.source / name)]
        del self.build["source_sha256"][name]
        self.flush_build()
        self.reject_exporter()

    def test_detached_proof_source_map_is_rejected(self):
        self.proof["source_sha256"]["Fang/FOF/TstpExport.lean"] = "0" * 64
        self.flush_proof()
        self.reject_exporter()

    def test_altered_exporter_binary_is_rejected(self):
        Path(self.exporter["path"]).write_bytes(b"changed exporter")
        self.reject_exporter()

    def test_repinning_exporter_without_build_link_is_rejected(self):
        Path(self.exporter["path"]).write_bytes(b"changed exporter")
        self.exporter["sha256"] = capability.digest(self.exporter["path"])
        self.reject_exporter()

    def test_altered_proof_object_is_rejected(self):
        (self.root / "proof-library/Fang/FOF/VersionedCheck.olean").write_bytes(b"changed object")
        with self.assertRaisesRegex(ValueError, "library inventory changed"):
            capability.verify(self.config)

    def test_detached_proof_library_receipt_is_rejected(self):
        self.proof["build_output_sha256"] = dict(self.proof["build_output_sha256"])
        self.proof["build_output_sha256"]["Fang/FOF/VersionedCheck.olean"] = "0" * 64
        self.flush_proof()
        self.reject_exporter()

    def test_same_bytes_at_unrecorded_proof_receipt_path_are_rejected(self):
        old = Path(self.exporter["proof_receipt"]["path"])
        detached = self.root / "detached-proof.json"
        shutil.copyfile(old, detached)
        self.exporter["proof_receipt"] = capability.record(detached)
        self.reject_exporter()

    def test_changed_build_receipt_is_rejected(self):
        (self.root / "build-manifest.json").write_text("{}\n")
        self.reject_exporter()

    def test_source_path_escape_is_rejected(self):
        self.build["source_sha256"]["../outside.lean"] = "0" * 64
        self.flush_build()
        self.reject_exporter()

    def test_checked_module_collision_is_rejected(self):
        name = "lean/Fang/FOF/TSTP/CheckedText.lean"
        path = self.source / name
        path.parent.mkdir(parents=True)
        path.write_text("duplicate module")
        value = capability.digest(path)
        self.build["source_sha256"][name] = value
        self.exporter["sources_sha256"][str(path)] = value
        self.flush_build()
        self.reject_exporter()

    def test_repinning_checker_without_build_link_is_rejected(self):
        path = Path(self.config["checker"]["path"])
        path.write_bytes(b"detached checker")
        self.config["checker"]["sha256"] = capability.digest(path)
        with self.assertRaises(ValueError):
            capability.verify(self.config)

    def test_detached_kernel_receipt_is_rejected(self):
        detached = self.root / "detached-kernel.json"
        detached.write_text("{}\n")
        self.config["kernel"]["receipt"] = capability.record(detached)
        with self.assertRaises(ValueError):
            capability.verify(self.config)

    def test_detached_kernel_library_is_rejected(self):
        detached = self.root / "detached-library"
        shutil.copytree(self.root / "proof-library", detached)
        (detached / "Fang/FOF/Replay.olean").write_bytes(b"different replay object")
        self.config["kernel"]["library"] = {"path": str(detached), "files_sha256": capability.inventory(detached)}
        with self.assertRaises(ValueError):
            capability.verify(self.config)

    def test_repinning_engine_without_build_link_is_rejected(self):
        path = Path(self.config["engine"]["path"])
        path.write_bytes(b"detached engine")
        self.config["engine"]["sha256"] = capability.digest(path)
        with self.assertRaisesRegex(ValueError, "binary differs from its build"):
            capability.verify(self.config)

    def test_same_engine_bytes_at_detached_path_are_rejected(self):
        detached = self.root / "detached-engine"
        shutil.copyfile(self.config["engine"]["path"], detached)
        self.config["engine"] = capability.record(detached)
        with self.assertRaisesRegex(ValueError, "binary differs from its build"):
            capability.verify(self.config)

    def test_same_checker_bytes_at_detached_path_are_rejected(self):
        detached = self.root / "detached-checker"
        shutil.copyfile(self.config["checker"]["path"], detached)
        self.config["checker"] = capability.record(detached)
        with self.assertRaisesRegex(ValueError, "binary differs from its build"):
            capability.verify(self.config)

    def test_same_helper_bytes_at_detached_path_are_rejected(self):
        detached = self.root / "detached-helper.py"
        shutil.copyfile(self.config["kernel"]["helpers"]["generate.py"]["path"], detached)
        self.config["kernel"]["helpers"]["generate.py"] = capability.record(detached)
        with self.assertRaisesRegex(ValueError, "helpers/toolchain differ"):
            capability.verify(self.config)

    def test_different_repinned_helper_is_rejected(self):
        detached = self.root / "detached-helper.py"
        detached.write_bytes(b"detached replay helper")
        self.config["kernel"]["helpers"]["generate.py"] = capability.record(detached)
        with self.assertRaisesRegex(ValueError, "helpers/toolchain differ"):
            capability.verify(self.config)

    def test_detached_toolchain_receipt_is_rejected(self):
        detached = self.root / "detached-toolchain-receipt.json"
        detached.write_text("{}\n")
        self.config["kernel"]["toolchain"]["receipt"] = capability.record(detached)
        with self.assertRaisesRegex(ValueError, "helpers/toolchain differ"):
            capability.verify(self.config)

    def test_same_inventory_bytes_at_detached_path_are_rejected(self):
        detached = self.root / "detached-toolchain-inventory.json"
        shutil.copyfile(self.config["kernel"]["toolchain"]["inventory"]["path"], detached)
        self.config["kernel"]["toolchain"]["inventory"] = capability.record(detached)
        with self.assertRaisesRegex(ValueError, "helpers/toolchain differ"):
            capability.verify(self.config)

    def test_detached_same_toolchain_is_rejected(self):
        detached = self.root / "detached-toolchain"
        shutil.copytree(self.config["kernel"]["toolchain"]["path"], detached)
        self.config["kernel"]["lean"] = capability.record(detached / "bin/lean")
        self.config["kernel"]["toolchain"]["path"] = str(detached)
        with self.assertRaisesRegex(ValueError, "helpers/toolchain differ"):
            capability.verify(self.config)

    def test_unbracketed_toolchain_is_rejected(self):
        self.build["fof"]["toolchain"]["verified_before_and_after"] = False
        self.flush_build()
        with self.assertRaisesRegex(ValueError, "helpers/toolchain differ"):
            capability.verify(self.config)

    def test_detached_outer_receipt_is_rejected(self):
        detached = self.root / "detached-outer-receipt.json"
        detached.write_text("{}\n")
        self.config["receipts"] = [capability.record(detached)]
        with self.assertRaisesRegex(ValueError, "library/receipt differs"):
            capability.verify(self.config)


if __name__ == "__main__":
    unittest.main()
