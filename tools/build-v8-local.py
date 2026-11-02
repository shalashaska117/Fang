#!/usr/bin/env python3
"""Install the version-8 fang command into a fresh directory from a checked source snapshot.

Steps: snapshot and check every source against its map, run the Rust workspace
checks and the release build of the three producers, build lean-v8 with
tools/build-v8-lean.py (or take a finished build of the same sources), which
builds the single-file, bundle and signed checkers and the TSTP exporter, copy
the source maps and build manifests as provenance, pin everything in
v8-capability.json, and create bin/fang. Installation reads only the files of
the repository: the maps name the receipt every source came from, as data, and
no receipt is read.
"""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True
TOOLS = Path(__file__).resolve().parent
ROOT = TOOLS.parent
sys.path.insert(0, str(TOOLS))
from fang_szs import v8_dependencies as sources
from fang_szs.supervisor import Limits, Supervisor, write_json

V8_TOOLS = ("check-v8-sources.py", "build-v8-lean.py", "build-v8-local.py", "fetch-v8-backend.py", "fang_router.py",
            "cli_setup.py")
INSTALLED = ("fang-v8-engine", "fang-v8-check", "fang-v8-tstp", "fang-bundle-producer", "fang-bundle-check",
             "fang-signed-producer", "fang-signed-check")
# Built only when lean-v8 holds the bundle exporter or goal document gate, or when the kernel witness crate is staged.
OPTIONAL = ("fang-bundle-tstp", "fang-goal-tstp", "fang-v8-witness")
# Shared files the kernel policy pins; changing any of them needs a new kernel policy and a new review.
KERNEL_SHARED = ("fang_szs/__init__.py", "fang_szs/supervisor.py", "replay/axiom_audit.py")


def require(value, message):
    if not value:
        raise ValueError(message)


def digest(path):
    return sources.digest(path)


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


# Provenance copied into the installation: the source maps, the audit list and the backend pins.
PROVENANCE = ("tools/v8_szs/rust-sources.json", "tools/v8_szs/lean-sources.json", "lean-v8/audits.json",
              "tools/v8_szs/backend-pins.json")


def snapshot_files():
    """The product inventory of build-local.py plus lean-v8 and the version-8 tools."""
    build_local = load_module("fang_v8_build_local_inventory", TOOLS / "build-local.py")
    files = set(build_local.source_files(ROOT))
    files.update(sources.lean_files(ROOT))
    files.update(TOOLS / name for name in V8_TOOLS)
    files.update((TOOLS / "v8_szs").glob("*.py"))
    files.update((TOOLS / "v8_szs").glob("*.json"))
    # Kernel mode: every file under tools/v8_kernel/, plus the shared files its policy pins.
    files.update(path for path in (TOOLS / "v8_kernel").rglob("*")
                 if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc")
    files.update(TOOLS / name for name in KERNEL_SHARED)
    return sorted(files)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True, help="fresh installation directory")
    parser.add_argument("--cargo", default="cargo", help="rustup-managed Cargo command with the pinned toolchain")
    parser.add_argument("--lean-toolchain", type=Path, required=True, help="pinned Lean 4.35.0 toolchain root")
    lean = parser.add_mutually_exclusive_group(required=True)
    lean.add_argument("--lean-build", type=Path, help="finished build directory of tools/build-v8-lean.py for these sources")
    lean.add_argument("--backend", type=Path, help="pinned local Aeneas backend; builds lean-v8 under --lean-work")
    lean.add_argument("--packages", type=Path,
                      help="Lake package directory from tools/fetch-v8-backend.py; builds lean-v8 under --lean-work")
    parser.add_argument("--aeneas-checkout", type=Path, help="local Aeneas checkout, with --backend")
    parser.add_argument("--lean-work", type=Path, help="fresh native directory for the Lean build, with --backend or --packages")
    parser.add_argument("--older", type=Path, help="earlier CNF and ground-FOF installation to expose by --profile")
    args = parser.parse_args()
    require(sys.platform == "linux", "Installation requires Linux or WSL")
    output = args.out.resolve()
    output.mkdir(mode=0o700, parents=True, exist_ok=False)
    case_sensitivity = None
    if output.is_relative_to("/mnt"):
        # lean-v8 holds FofInput and FOFInput; Windows drives are case-insensitive by default.
        fsutil = "/mnt/c/Windows/System32/fsutil.exe"
        windows = subprocess.run(["/usr/bin/wslpath", "-w", str(output)], capture_output=True, check=True).stdout.decode().strip()
        subprocess.run([fsutil, "file", "setCaseSensitiveInfo", windows, "enable"], capture_output=True, check=True)
        query = subprocess.run([fsutil, "file", "queryCaseSensitiveInfo", windows], capture_output=True, check=True)
        case_sensitivity = query.stdout.decode().strip()
        require(case_sensitivity == "Case sensitive attribute on directory " + windows + " is enabled.",
                "Installation directory is not case sensitive")
    supervisor = Supervisor(Limits(wall_seconds=7200, memory_mib=6144, log_bytes=64 << 20, artifact_bytes=8 << 30))
    manifest = {"schema": "fang-v8-installation-v1", "status": "building",
                "started_utc": datetime.now(timezone.utc).isoformat(),
                "scope": "Version-8 command built from the repository alone: Rust producers, compiled Lean checkers "
                         "and SZS status on the single-file, bundle and signed paths, and TSTP output on the single-file "
                         "path. Kernel replay is not installed; --check kernel is refused before the input is read.",
                "case_sensitivity": case_sensitivity}
    (output / "stages").mkdir()
    try:
        check = supervisor.check
        python = Path(sys.executable).resolve()
        manifest["python"] = {"path": str(python), "sha256": digest(python)}
        frozen = output / "source"
        hashes = {}
        for path in snapshot_files():
            relative = path.relative_to(ROOT).as_posix()
            data = path.read_bytes()
            target = frozen / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
            hashes[relative] = hashlib.sha256(data).hexdigest()
        manifest["source_sha256"] = hashes
        frozen_tools = frozen / "tools"
        check_report = subprocess.run([str(python), "-B", str(frozen_tools / "check-v8-sources.py"), "--root", str(frozen)],
                                      capture_output=True, timeout=600)
        require(check_report.returncode == 0, "Snapshot source check failed: " + check_report.stdout.decode()[-500:])
        manifest["source_check"] = json.loads(check_report.stdout)
        cargo = shutil.which(args.cargo)
        require(cargo is not None, "Install the pinned Rust toolchain first")
        environment = {key: os.environ[key] for key in ("PATH", "HOME", "RUSTUP_HOME", "CARGO_HOME", "RUSTUP_TOOLCHAIN",
                                                        "LANG", "LC_ALL") if key in os.environ}
        environment.update(CARGO_NET_OFFLINE="true", CARGO_BUILD_JOBS="2", CARGO_TARGET_DIR=str(output / "rust-target"),
                           TMPDIR=str(output / "tmp"))
        (output / "tmp").mkdir()
        manifest["build_environment"] = environment

        def run(stage, command):
            wrapped = [str(python), "-c", "import os,sys; os.chdir(sys.argv[1]); os.execv(sys.argv[2],sys.argv[2:])",
                       str(frozen), *map(str, command)]
            record, stdout, stderr = supervisor.run(stage, wrapped, output / "stages" / stage, output / "stages",
                                                    environment=environment)
            require(record["classification"] == "completed" and record["exit_code"] == 0, stage + " failed")
            return (stdout + stderr).decode("utf-8", "replace")

        manifest["cargo_version"] = run("cargo-version", [cargo, "--version"]).strip()
        require(manifest["cargo_version"].startswith("cargo 1.90.0 "), "Cargo differs from the pinned 1.90.0")
        run("rust-fmt", [cargo, "fmt", "--all", "--", "--check"])
        run("rust-tests", [cargo, "test", "--workspace", "--locked", "--offline", "--all-targets"])
        run("rust-clippy", [cargo, "clippy", "--workspace", "--locked", "--offline", "--all-targets", "--", "-D", "warnings"])
        rust_map = sources.load_map(frozen, sources.RUST_MAP, sources.RUST_SCHEMA)
        produced = rust_map["installed_binaries"]
        packages = sorted({entry["package"] for entry in produced.values()})
        run("rust-build", [cargo, "build", "--release", "--locked", "--offline",
                           *[item for package in packages for item in ("-p", package)]])
        if args.lean_build is not None:
            lean_build = args.lean_build.resolve()
        else:
            require(args.lean_work is not None, "--backend and --packages need --lean-work")
            lean_build = args.lean_work.resolve()
            if args.backend is not None:
                require(args.aeneas_checkout is not None, "--backend needs --aeneas-checkout")
                backend = ["--backend", str(args.backend), "--aeneas-checkout", str(args.aeneas_checkout)]
            else:
                backend = ["--packages", str(args.packages)]
            done = subprocess.run([str(python), "-B", str(frozen_tools / "build-v8-lean.py"), "--out", str(lean_build),
                                   "--lean-toolchain", str(args.lean_toolchain), *backend], timeout=6000)
            require(done.returncode == 0, "lean-v8 build failed; see " + str(lean_build / "manifest.json"))
        lean_report = json.loads((lean_build / "manifest.json").read_text(encoding="utf-8"))
        require(lean_report["status"] == "built-and-audited", "lean-v8 build did not pass")
        require(lean_report["source_map_sha256"] == hashes[sources.LEAN_MAP], "lean-v8 build used other sources")
        require(lean_report["backend_pins_sha256"] == hashes["tools/v8_szs/backend-pins.json"], "Backend pins differ")
        lean_map = sources.load_map(frozen, sources.LEAN_MAP, sources.LEAN_SCHEMA)
        audit_list = json.loads((frozen / lean_map["project"] / "audits.json").read_text(encoding="utf-8"))
        require(lean_report["axiom_audits"]["count"] == len(audit_list["names"]), "Fixed axiom audits are incomplete")
        require(sorted(lean_report["axiom_audits"]["gates"]) == sorted(lean_map["gates"]), "Not every gate was audited")
        manifest["lean_build"] = {"path": str(lean_build), "manifest_sha256": digest(lean_build / "manifest.json")}
        kernel = None
        if (frozen_tools / "v8_kernel/install-kernel.py").is_file():
            # Kernel helpers on the built lean-v8 project, then the kernel installation; either failing stops the install.
            helpers = output / "kernel-helpers"
            done = subprocess.run([str(python), "-B", str(frozen_tools / "v8_kernel/build-helpers.py"), "--project",
                                   str(lean_build / "project"), "--lean-toolchain", str(args.lean_toolchain), "--out",
                                   str(helpers)], timeout=3600)
            helper_report = json.loads((helpers / "manifest.json").read_text(encoding="utf-8")) \
                if (helpers / "manifest.json").is_file() else {}
            require(done.returncode == 0 and helper_report.get("status") == "built-and-audited",
                    "Kernel helper build failed; see " + str(helpers / "manifest.json"))
            kernel_root = output / "kernel"
            done = subprocess.run([str(python), "-B", str(frozen_tools / "v8_kernel/install-kernel.py"), "--root",
                                   str(kernel_root), "--project", str(lean_build / "project"), "--lean-build", str(lean_build),
                                   "--helpers", str(helpers), "--lean-toolchain", str(args.lean_toolchain)], timeout=3600)
            installation = kernel_root / "tools/v8_kernel/entry/installation.json"
            require(done.returncode == 0 and installation.is_file(), "Kernel installation failed")
            kernel = {"root": kernel_root, "installation": installation, "helpers_manifest": helpers / "manifest.json"}
            manifest["kernel"] = {"helpers_manifest_sha256": digest(helpers / "manifest.json"),
                                  "installation_sha256": digest(installation)}
        binaries = output / "bin"
        binaries.mkdir()
        built = {}
        for name, entry in sorted(produced.items()):
            built[name] = output / "rust-target/release" / entry["binary"]
        for exe, entry in sorted(lean_map["executables"].items()):
            require(lean_report["executables"][exe]["sha256"] == digest(Path(lean_report["executables"][exe]["path"])),
                    "Lean executable differs from its build: " + exe)
            built[entry["installed_as"]] = Path(lean_report["executables"][exe]["path"])
        require(set(built) - set(OPTIONAL) == set(INSTALLED), "Installed binary set differs: " + ", ".join(sorted(built)))
        for name, source in sorted(built.items()):
            shutil.copy2(source, binaries / name)
            require(digest(binaries / name) == digest(source), "Copied binary differs: " + name)
        record = lambda name: {"path": str(binaries / name), "sha256": digest(binaries / name)}
        provenance_dir = output / "provenance"
        provenance_dir.mkdir()
        provenance = []
        for relative in PROVENANCE:
            target = provenance_dir / Path(relative).name
            shutil.copyfile(frozen / relative, target)
            require(digest(target) == hashes[relative], "Copied provenance differs: " + relative)
            provenance.append({"path": str(target), "sha256": hashes[relative]})
        shutil.copyfile(lean_build / "manifest.json", provenance_dir / "lean-v8-build.json")
        provenance.append({"path": str(provenance_dir / "lean-v8-build.json"),
                           "sha256": digest(provenance_dir / "lean-v8-build.json")})
        # The installation carries the repository's license and notice files next to the binaries built from it.
        notices = output / "LICENSES"
        notices.mkdir()
        for relative in sorted(name for name in hashes if name == "LICENSE" or name.startswith("LICENSES/")):
            target = notices / Path(relative).name
            shutil.copyfile(frozen / relative, target)
            require(digest(target) == hashes[relative], "Copied notice differs: " + relative)
            provenance.append({"path": str(target), "sha256": hashes[relative]})
        manifest["provenance"] = provenance
        bundle = {"producer": record("fang-bundle-producer"), "checker": record("fang-bundle-check")}
        signed_path = {"producer": record("fang-signed-producer"), "checker": record("fang-signed-check")}
        tstp = {"exporter": record("fang-v8-tstp")}
        kernel_section = None
        if kernel is not None:
            require("fang-v8-witness" in built, "Kernel mode needs the witness binary")
            kernel_section = {"witness": record("fang-v8-witness"),
                              "entry": {"path": str(kernel["root"] / "tools/v8_kernel/entry/main.py"),
                                        "sha256": digest(kernel["root"] / "tools/v8_kernel/entry/main.py")},
                              "installation": {"path": str(kernel["installation"]), "sha256": digest(kernel["installation"])},
                              "output_root": str(kernel["root"] / "run")}
        if "fang-bundle-tstp" in built:
            tstp["bundle_exporter"] = record("fang-bundle-tstp")
        if "fang-goal-tstp" in built:
            tstp["goal_exporter"] = record("fang-goal-tstp")
        manifest.update(bundle=bundle, signed=signed_path, tstp=tstp)
        manifest.update(status="built-and-checked", completed_utc=datetime.now(timezone.utc).isoformat(),
                        binaries_sha256={path.name: digest(path) for path in sorted(binaries.iterdir())},
                        sampled_peak_rss_kib=supervisor.peak_kib, stages=supervisor.records)
        write_json(output / "build-manifest.json", manifest)
        sys.path.insert(0, str(frozen_tools / "v8_szs"))
        capability = load_module("fang_v8_installed_capability", frozen_tools / "v8_szs/capability.py")
        config = {"schema": capability.SCHEMA, "language": capability.LANGUAGE, "certificate_version": 8,
                  "max_input_bytes": capability.MAX_BYTES, "max_certificate_bytes": capability.MAX_BYTES,
                  "engine": {"path": str(binaries / "fang-v8-engine"), "sha256": digest(binaries / "fang-v8-engine")},
                  "checker": {"path": str(binaries / "fang-v8-check"), "sha256": digest(binaries / "fang-v8-check")},
                  "python": {"path": str(python), "sha256": digest(python)},
                  "runtime_source_sha256": {str(path): digest(path) for path in capability.runtime_sources()},
                  "provenance": [{"path": str(output / "build-manifest.json"),
                                  "sha256": digest(output / "build-manifest.json")}, *provenance],
                  "bundle": bundle, "signed": signed_path, "tstp": tstp, "kernel": kernel_section,
                  "per_run_verification": capability.PER_RUN, "default_check": capability.DEFAULT_CHECK}
        capability.verify(config)
        with (output / "v8-capability.json").open("x", encoding="utf-8") as stream:
            json.dump(config, stream, indent=2, sort_keys=True)
            stream.write("\n")
        cli_setup = load_module("fang_v8_installed_cli_setup", frozen_tools / "cli_setup.py")
        launcher = cli_setup.provision_v8(output, older=args.older, python=python)
        write_json(output / "installation-receipt.json", {
            "status": "installed", "finished_utc": datetime.now(timezone.utc).isoformat(),
            "build_manifest_sha256": digest(output / "build-manifest.json"),
            "capability_sha256": digest(output / "v8-capability.json"),
            "command": str(launcher), "command_sha256": digest(launcher),
            "command_configuration_sha256": digest(output / "command.json")})
        print(json.dumps({"status": "installed", "command": str(launcher),
                          "add_to_path": "export PATH=" + shlex.quote(str(binaries)) + ':"$PATH"'}))
        return 0
    except BaseException as error:
        manifest.update(status="failed", error=f"{type(error).__name__}: {error}", stages=supervisor.records)
        write_json(output / "setup-failure.json", manifest)
        print("Setup failed: " + str(error), file=sys.stderr)
        return 1
    finally:
        supervisor.close()


if __name__ == "__main__":
    raise SystemExit(main())
