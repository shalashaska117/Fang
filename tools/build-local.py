#!/usr/bin/env python3
"""Build a local Fang installation from a fresh, checked source snapshot."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import sys
import tomllib

from fang_szs.supervisor import Failure, Limits, Supervisor, write_json
from fang_szs.dependencies import dependency_files


ROOT = Path(__file__).resolve().parents[1]
def digest(path):
    hasher = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(65536), b""):
            hasher.update(block)
    return hasher.hexdigest()


def source_files(root, check=lambda: None):
    files = [root / name for name in ("Cargo.toml", "Cargo.lock", "rust-toolchain.toml",
             "LICENSE", "CONTRIBUTORS.md")]
    for folder in ("src", "tests", "examples", "LICENSES", "tools"):
        files.extend(path for path in (root / folder).rglob("*")
                     if path.is_file() and not {"__pycache__", ".local", "evidence", "runs", "logs"}.intersection(path.relative_to(root).parts)
                     and path.suffix != ".pyc" and path.relative_to(root).as_posix() != "tools/tests/native_integration.py")
    files.extend(path for path in (root / "lean").rglob("*.lean")
                 if not {".lake", "Generated"}.intersection(path.relative_to(root).parts))
    files.extend(root / "lean" / name for name in ("lean-toolchain", "lakefile.toml", "check-local.sh", "tstp-sources.json"))
    files.append(root / "LICENSES/Vampire.ORIGIN")
    files.extend(dependency_files(root, check))
    return sorted(set(files))


def snapshot(root, target, supervisor):
    hashes = {}
    for source in source_files(root, lambda: supervisor.check("source-inventory")):
        supervisor.check("snapshot")
        if source.is_symlink() or not source.is_file():
            raise ValueError(f"Source must be a regular file: {source}")
        relative = source.relative_to(root)
        before = digest(source)
        destination = target / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, destination)
        if digest(source) != before or digest(destination) != before:
            raise ValueError(f"Source changed during capture: {relative}")
        hashes[relative.as_posix()] = before
    return hashes


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True, help="Fresh local installation directory")
    parser.add_argument("--lean-tools", type=Path, required=True, help="Pinned Lean bin directory containing lean and lake")
    parser.add_argument("--cargo", default="cargo", help="Installed rustup-managed Cargo command")
    args = parser.parse_args()
    if sys.platform != "linux":
        parser.error("Local setup currently requires Linux or WSL")
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=False, mode=0o700)
    supervisor = Supervisor(Limits(wall_seconds=1800, memory_mib=4096,
                            log_bytes=16 << 20, artifact_bytes=4 << 30))
    manifest = {"status": "building", "started_utc": datetime.now(timezone.utc).isoformat(),
                "scope": "Local executable build and general independent Lean proof suite; no per-instance UNSAT claim",
                "limits": {"wall_seconds": 1800, "sampled_tree_rss_mib": 4096}, "stages": supervisor.records}
    (output / "stages").mkdir()
    frozen = output / "source"
    allowed_environment = ("PATH", "HOME", "USER", "RUSTUP_HOME", "CARGO_HOME", "TMPDIR", "TMP", "TEMP",
                           "LANG", "LC_ALL", "LC_CTYPE", "XDG_CACHE_HOME")
    environment = {key: os.environ[key] for key in allowed_environment if key in os.environ}
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    environment["CARGO_NET_OFFLINE"] = "true"
    environment["CARGO_BUILD_JOBS"] = "2"
    environment["LEAN_NUM_THREADS"] = "1"
    tools = args.lean_tools.resolve()
    environment["PATH"] = str(tools) + os.pathsep + environment.get("PATH", "")
    lean, lake = tools / "lean", tools / "lake"
    cargo = shutil.which(args.cargo)
    manifest["declared_build_environment"] = environment.copy()

    def run(stage, command):
        record, stdout, stderr = supervisor.run(stage, command, output / "stages" / stage,
                                                output, environment=environment)
        if record["exit_code"] != 0:
            raise RuntimeError(f"{stage} failed; see {output / 'stages' / stage}")
        return stdout.decode("utf-8", errors="strict").strip()

    try:
        if cargo is None or not lean.is_file() or not lake.is_file():
            raise ValueError("Install the pinned Rust and Lean toolchains before setup")
        manifest["source_sha256"] = snapshot(ROOT, frozen, supervisor)
        exporter_link = json.loads((frozen / "lean/tstp-sources.json").read_text())
        if exporter_link.get("schema") != "fang-tstp-source-link-v2":
            raise ValueError("Missing reviewed TSTP source-link record")
        expected_sources = {"lean/TstpExport.lean", "lean/TstpMain.lean"}
        if set(exporter_link["sources"]) != expected_sources:
            raise ValueError("Incomplete TSTP source-link record")
        for source, expected_hash in exporter_link["sources"].items():
            if digest(frozen / source) != expected_hash:
                raise ValueError("Compiled exporter differs from the reviewed source bytes")
        manifest["tstp_source_link"] = exporter_link
        rust_version = tomllib.loads((frozen / "rust-toolchain.toml").read_text())["toolchain"]["channel"]
        lean_version = (frozen / "lean/lean-toolchain").read_text().strip().rsplit(":v", 1)[1]
        cargo_prefix = [cargo, "+" + rust_version]
        manifest["cargo_version"] = run("cargo-version", cargo_prefix + ["--version"])
        manifest["lean_version"] = run("lean-version", [str(lean), "--version"])
        if not manifest["cargo_version"].startswith("cargo " + rust_version + " "):
            raise ValueError("Cargo version differs from the pinned toolchain")
        if "version " + lean_version + "," not in manifest["lean_version"]:
            raise ValueError("Lean version differs from the pinned toolchain")
        manifest["lean_sha256"] = digest(lean)
        cargo_args = ["--manifest-path", str(frozen / "Cargo.toml"), "--locked", "--offline",
                      "--target-dir", str(output / "rust-target")]
        run("rust-tests", cargo_prefix + ["test"] + cargo_args)
        run("rust-build", cargo_prefix + ["build", "--release"] + cargo_args)
        run("lean-checker-build", [str(lake), "-d", str(frozen / "lean"), "build", "fang-check", "fang-tstp-export"])
        proof_path = output / "proof-suite" / "manifest.json"
        run("lean-proof-suite", [sys.executable, str(frozen / "tools/replay/check-suite.py"),
                                 str(frozen), str(lean), "--out", str(proof_path.parent)])
        proof = json.loads(proof_path.read_text())
        if (proof["status"] != "passed" or "Fang.FrontendSoundness" not in proof["completed_modules"]
                or "Fang.FrontendComplete" not in proof["completed_modules"]):
            raise ValueError("The required independent proof suite did not pass")
        library = output / "proof-library"
        for relative, expected in proof["build_output_sha256"].items():
            source = Path(proof["native_project"]) / relative
            destination = library / relative
            if source.is_symlink() or digest(source) != expected:
                raise ValueError("Checked library changed")
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, destination)
            if digest(destination) != expected:
                raise ValueError("Copied checked library differs")
        binaries = output / "bin"
        binaries.mkdir()
        for source, name in ((output / "rust-target/release/fang", "fang"),
                             (frozen / "lean/.lake/build/bin/fang-check", "fang-check"),
                             (frozen / "lean/.lake/build/bin/fang-tstp-export", "fang-tstp-export")):
            shutil.copy2(source, binaries / name)
        shutil.copytree(frozen / "LICENSES", output / "LICENSES")
        shutil.copy2(frozen / "LICENSE", output / "LICENSE")
        for checked_root in (ROOT, frozen):
            actual_names = {path.relative_to(checked_root).as_posix()
                            for path in source_files(checked_root, lambda: supervisor.check("final-source-inventory"))}
            if actual_names != set(manifest["source_sha256"]):
                raise ValueError("Source inventory changed while setup ran")
        for relative, expected in manifest["source_sha256"].items():
            if digest(frozen / relative) != expected or digest(ROOT / relative) != expected:
                raise ValueError(f"Source changed while setup ran: {relative}")
        manifest.update(status="built-and-checked", proof_suite=str(proof_path),
                        proof_suite_sha256=digest(proof_path), library_sha256=proof["build_output_sha256"],
                        binaries_sha256={name: digest(binaries / name) for name in ("fang", "fang-check", "fang-tstp-export")},
                        completed_utc=datetime.now(timezone.utc).isoformat(),
                        sampled_peak_rss_kib=supervisor.peak_kib)
        provenance = output / "build-manifest.json"
        write_json(provenance, manifest)
        config = output / "installation.json"
        # The finalized build manifest is pinned by the installer. Its own receipt
        # is separate so installation cannot change those provenance bytes.
        run("install", [sys.executable, str(frozen / "tools/fang-install.py"),
                        "--engine", str(binaries / "fang"), "--checker", str(binaries / "fang-check"),
                        "--exporter", str(binaries / "fang-tstp-export"),
                        "--lean", str(lean), "--proof-library", str(library), "--source-root", str(frozen),
                        "--provenance", str(provenance), "--out", str(config)])
        launcher = binaries / "fang-szs"
        launcher.write_text("#!/bin/sh\nexec " + shlex.join([
            sys.executable, str(frozen / "tools/fang-szs.py"), "--installation", str(config)])
            + ' "$@"\n', encoding="utf-8")
        launcher.chmod(0o755)
        write_json(output / "installation-receipt.json", {"status": "installed", "configuration": str(config),
                   "configuration_sha256": digest(config), "build_manifest_sha256": digest(provenance),
                   "launcher": str(launcher), "launcher_sha256": digest(launcher),
                   "install_stage": supervisor.records[-1]})
        print(json.dumps({"status": "installed", "configuration": str(config),
                          "example_command": shlex.join([str(launcher),
                              str(frozen / "examples/problems/mortality.p"), "--artifacts",
                              str(output / "runs/mortality-kernel")])}))
        return 0
    except (Failure, OSError, ValueError, RuntimeError) as error:
        write_json(output / "setup-failure.json", {"status": "failed", "reason": str(error),
                   "stages": supervisor.records, "sampled_peak_rss_kib": supervisor.peak_kib})
        print(f"Setup failed: {error}", file=sys.stderr)
        return 1
    finally:
        supervisor.close()


if __name__ == "__main__":
    raise SystemExit(main())
