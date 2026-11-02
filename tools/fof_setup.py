"""Build and provision the bounded ground-FOF addition to a local CNF install."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
from datetime import datetime, timezone
import importlib.util
import json
import os
from pathlib import Path
import shlex
import shutil
import stat
import sys

from fang_szs.supervisor import write_json
from fof_szs import toolchain
import fof_tstp_setup

LEAVES = ("ground-fof-core", "ground-fof-frontend", "ground-fof-search", "ground-fof-versioned")
AUDIT_MODULES = {"Fang.FOF.Audit", "Fang.FOF.GroundFormula", "Fang.FOF.FOFDiagnostics",
                 "Fang.FOF.GrammarAudit", "Fang.FOF.CompletenessAudit"}


def digest(path, check=lambda: None):
    return toolchain.stable_file(Path(path), check)["sha256"]


def capture_toolchain(root, check=lambda: None):
    root = Path(root)
    if not root.is_absolute() or root.is_symlink() or not root.is_dir():
        raise ValueError("Lean toolchain root must be an absolute real directory")
    before, result = toolchain.tree(root, check), {}
    for relative, identity in sorted(before.items()):
        check()
        path = root / relative
        if stat.S_ISDIR(identity[2]):
            continue
        if stat.S_ISLNK(identity[2]):
            resolved = path.resolve(strict=True)
            if not resolved.is_relative_to(root) or not resolved.is_file():
                raise ValueError("Lean toolchain symlink escapes its root")
            result[relative] = {"kind": "symlink", "target": os.readlink(path),
                "resolved": resolved.relative_to(root).as_posix(), **toolchain.stable_file(resolved, check)}
        elif stat.S_ISREG(identity[2]):
            result[relative] = {"kind": "file", **toolchain.stable_file(path, check)}
        else:
            raise ValueError("Nonregular Lean toolchain dependency")
    if toolchain.tree(root, check) != before:
        raise ValueError("Lean toolchain changed during capture")
    toolchain.verify(root, result, check)
    return result


def prepare(output, tools, check):
    root = tools.parent
    inventory = capture_toolchain(root, check)
    path = output / "toolchain-inventory.json"
    write_json(path, inventory)
    return {"root": root, "inventory": inventory, "path": path,
        "lean_sha256": digest(tools / "lean", check), "lake_sha256": digest(tools / "lake", check)}


def build(frozen, output, cargo_prefix, lake, run):
    target = output / "fof-rust-target"
    for name in LEAVES:
        options = ["--manifest-path", str(frozen / "crates" / name / "Cargo.toml"),
                   "--locked", "--offline", "--target-dir", str(target)]
        run(name + "-tests", cargo_prefix + ["test", *options])
        if name == "ground-fof-versioned":
            run("fof-driver-clippy", cargo_prefix + ["clippy", "--all-targets", *options, "--", "-D", "warnings"])
            run("fof-driver-build", cargo_prefix + ["build", "--release", "--bin", "fang-ground-fof-driver", *options])
    run("fof-checker-build", [str(lake), "-d", str(frozen / "lean"), "build",
                             "fang-fof-check", "fang-fof-tstp-export"])


def check_proofs(frozen, proof):
    fof_tstp_setup.check_proofs(frozen, proof)
    expected = json.loads((frozen / "tools/fof_audits.json").read_text())
    if (set(expected) != AUDIT_MODULES or sum(map(len, expected.values())) != 64
            or any(len(names) != len(set(names)) for names in expected.values())
            or proof["status"] != "passed"):
        raise ValueError("The required combined FOF proof inventory did not pass")
    for module, names in expected.items():
        rows = [row for row in proof["axiom_audits"] if row["module"] == module]
        if len(rows) != len(names) or {row["declaration"] for row in rows} != set(names):
            raise ValueError("Required FOF theorem audit differs: " + module)
        if any(not set(row["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"} for row in rows):
            raise ValueError("Unexpected FOF theorem axiom")
    return expected


def finish(frozen, output, context, fixed_audits, check):
    for original, name in ((output / "fof-rust-target/release/fang-ground-fof-driver", "fang-ground-fof-driver"),
                           (frozen / "lean/.lake/build/bin/fang-fof-check", "fang-fof-check"),
                           (frozen / "lean/.lake/build/bin/fang-fof-tstp-export", "fang-fof-tstp-export")):
        expected = digest(original, check)
        shutil.copy2(original, output / "bin" / name)
        if digest(output / "bin" / name, check) != expected:
            raise ValueError("Copied FOF binary differs")
    toolchain.verify(context["root"], context["inventory"], check)
    if (digest(context["root"] / "bin/lean", check) != context["lean_sha256"]
            or digest(context["root"] / "bin/lake", check) != context["lake_sha256"]):
        raise ValueError("Lean build executable changed")
    inventory = fof_tstp_setup.read_inventory(frozen)
    return {"scope": "Bounded ground-FOF status and TSTP; original-byte checking; no general quantified FOF, equality or SAT acceptance",
        "binaries_sha256": {name: digest(output / "bin" / name, check)
            for name in ("fang-ground-fof-driver", "fang-fof-check", "fang-fof-tstp-export")},
        "toolchain": {"path": str(context["root"]), "inventory": str(context["path"]),
            "inventory_sha256": digest(context["path"], check), "entries": len(context["inventory"]),
            "verified_before_and_after": True, "lean_sha256": context["lean_sha256"], "lake_sha256": context["lake_sha256"]},
        "fixed_audits": fixed_audits, "general_modules": len(inventory["modules"]),
        "general_audits": sum(map(len, inventory["audits"].values())),
        "exporter": {"theorem": fof_tstp_setup.TEXT_THEOREM,
                     "inventory_sha256": digest(frozen / "tools/fof_proof_inventory.json", check)}}


def verify_sources_before_import(frozen, source_hashes, check=lambda: None):
    for relative, expected in source_hashes.items():
        path = frozen / relative
        if path.is_symlink() or not path.is_file() or digest(path, check) != expected:
            raise ValueError("Installed source changed before provisioning: " + relative)
    for package in ("tools/fof_szs", "tools/fang_szs"):
        actual = {path.relative_to(frozen).as_posix() for path in (frozen / package).glob("*.py")}
        expected = {name for name in source_hashes if name.startswith(package + "/") and name.endswith(".py")}
        if actual != expected:
            raise ValueError("Unexpected executable helper before provisioning")


def provision(output, build, check):
    frozen, provenance = output / "source", output / "build-manifest.json"
    before = {name: digest(output / name, check) for name in
              ("build-manifest.json", "installation.json", "installation-receipt.json")}
    if json.loads(provenance.read_text()) != build or build["status"] != "built-and-checked":
        raise ValueError("Finalized build receipt differs")
    verify_sources_before_import(frozen, build["source_sha256"], check)
    for name, expected in build["fof"]["binaries_sha256"].items():
        if digest(output / "bin" / name, check) != expected:
            raise ValueError("Built FOF binary changed")
    sys.path.insert(0, str(frozen / "tools/fof_szs"))
    spec = importlib.util.spec_from_file_location("fang_installed_fof_capability", frozen / "tools/fof_szs/capability.py")
    capability = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(capability)
    def record(path):
        return {"path": str(path.absolute()), "sha256": capability.digest(path, check)}
    library = {"path": str(output / "proof-library"), "files_sha256": capability.inventory(output / "proof-library", check)}
    if library["files_sha256"] != build["library_sha256"]:
        raise ValueError("Checked proof library changed")
    info = build["fof"]["toolchain"]
    config = {"schema": capability.TSTP_SCHEMA, "language": capability.LANGUAGE,
        "certificate": capability.ENVELOPE, "profiles": ["kernel", "compiled"], "outputs": ["status", "tstp"],
        "max_input_bytes": capability.MAX_BYTES, "max_certificate_bytes": capability.MAX_BYTES,
        "engine": record(output / "bin/fang-ground-fof-driver"), "checker": record(output / "bin/fang-fof-check"),
        "python": record(Path(sys.executable).resolve()), "proof_library": library,
        "runtime_source_sha256": {str(path): capability.digest(path, check) for path in capability.runtime_sources()},
        "dependency_source_sha256": {str(frozen / name): value for name, value in build["source_sha256"].items()},
        "receipts": [record(provenance)],
        "kernel": {"profile": capability.KERNEL_PROFILE, "limits": dict(capability.KERNEL_LIMITS),
            "lean": record(Path(info["path"]) / "bin/lean"), "library": library,
            "helpers": {name: record(frozen / "tools/replay" / filename) for name, filename in
                (("generate.py", "fof_replay.py"), ("source_witness.py", "source_witness.py"), ("axiom_audit.py", "axiom_audit.py"))},
            "receipt": record(provenance), "toolchain": {"path": info["path"],
                "inventory": record(Path(info["inventory"])), "receipt": record(provenance)}}}
    config["exporter"] = record(output / "bin/fang-fof-tstp-export") | {
        "sources_sha256": dict(config["dependency_source_sha256"]),
        "proof_receipt": record(Path(build["proof_suite"])), "build_receipt": record(provenance)}
    if config["kernel"]["toolchain"]["inventory"]["sha256"] != info["inventory_sha256"]:
        raise ValueError("Captured toolchain inventory changed")
    capability.verify(config, check)
    config_path, launcher = output / "fof-capability.json", output / "bin/fang-fof-szs"
    with config_path.open("x") as stream:
        json.dump(config, stream, indent=2, sort_keys=True)
        stream.write("\n")
    with launcher.open("x") as stream:
        stream.write("#!/bin/sh\nexec " + shlex.join([sys.executable, str(frozen / "tools/fang-fof-szs.py"),
            "--capability", str(config_path)]) + ' "$@"\n')
    launcher.chmod(0o755)
    if any(digest(output / name, check) != expected for name, expected in before.items()):
        raise ValueError("FOF provisioning changed the finalized CNF installation")
    write_json(output / "fof-installation-receipt.json", {"status": "installed", "finished_utc": datetime.now(timezone.utc).isoformat(),
        "capability": str(config_path), "capability_sha256": digest(config_path, check),
        "launcher": str(launcher), "launcher_sha256": digest(launcher, check), "cnf_files_sha256": before,
        "scope": "CNF and ground-FOF commands with TSTP; per-input checking occurs when invoked; printed bytes rely on compiled exporter execution"})
    return config_path
