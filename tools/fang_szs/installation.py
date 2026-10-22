"""Create and verify an explicit local tool installation; never build implicitly."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import argparse
import hashlib
from pathlib import Path
import re
import stat
import sys
from .supervisor import Failure, strict_json, write_json
from .dependencies import dependency_files


HELPERS = ("generic_source_replay.py", "native_source_replay.py", "replay_storage_probe.py",
           "source_witness.py", "axiom_audit.py", "decomposed_replay_probe.py")
CONFIGS = ("Cargo.toml", "Cargo.lock", "rust-toolchain.toml", "lean/lakefile.toml", "lean/lean-toolchain")


def digest_file(path, check=lambda: None):
    if not stat.S_ISREG(path.lstat().st_mode):
        raise Failure("Error", "Installation member must be a regular file")
    result = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(65536), b""):
            check()
            result.update(block)
    return result.hexdigest()


def directory_inventory(root, check=lambda: None):
    result = {}
    if not root.is_dir() or root.is_symlink():
        raise Failure("Error", "Installed library must be a real directory")
    for path in sorted(root.rglob("*")):
        if path.is_symlink():
            raise Failure("Error", "Installation contains a symlink")
        if path.is_file():
            result[path.relative_to(root).as_posix()] = digest_file(path, check)
        elif not path.is_dir():
            raise Failure("Error", "Installation contains a nonregular member")
    return result


def source_inventory(root, check=lambda: None):
    paths = [root / name for name in CONFIGS]
    paths += dependency_files(root, check)
    paths += sorted((root / "src").rglob("*.rs"))
    paths += sorted(path for path in (root / "lean").rglob("*.lean") if ".lake" not in path.relative_to(root).parts)
    paths += [root / "tools/replay" / name for name in HELPERS]
    paths += sorted((root / "tools/fang_szs").glob("*.py"))
    paths += [root / "tools/fang-szs.py", root / "tools/fang-install.py"]
    # Legacy status-only source trees may not contain the exporter record or
    # legal inventory. Pin every such file present in a new installation.
    paths += [root / name for name in ("lean/tstp-sources.json", "LICENSE", "CONTRIBUTORS.md")
              if (root / name).exists()]
    paths += sorted(path for path in (root / "LICENSES").rglob("*") if path.is_file())
    return {path.relative_to(root).as_posix(): digest_file(path, check) for path in paths}


def verify_exporter_sources(source, hashes):
    path = source / "lean/tstp-sources.json"
    if "lean/tstp-sources.json" not in hashes:
        raise Failure("Error", "New TSTP installation is missing its exporter source record")
    record = strict_json(path.read_text(encoding="utf-8"))
    names = {"lean/TstpExport.lean", "lean/TstpMain.lean"}
    if (not isinstance(record, dict) or record.get("schema") != "fang-tstp-source-link-v2"
            or not isinstance(record.get("sources"), dict) or set(record["sources"]) != names
            or any(record["sources"][name] != hashes.get(name) for name in names)):
        raise Failure("Error", "Exporter source record differs from the installed source bytes")


def verify_running_adapter(config, check=lambda: None):
    package = Path(__file__).resolve().parent
    actual = {"tools/fang_szs/" + path.name: digest_file(path, check) for path in package.glob("*.py")}
    for name in ("fang-szs.py", "fang-install.py"):
        actual["tools/" + name] = digest_file(package.parent / name, check)
    expected = {name: value for name, value in config["source_sha256"].items()
        if name.startswith("tools/fang_szs/") or name in ("tools/fang-szs.py", "tools/fang-install.py")}
    if actual != expected:
        raise Failure("Error", "Running adapter differs from the installed source snapshot")


def absolute_existing(path):
    # Resolve the caller's installation argument once; symlink members are rejected.
    return Path(path).resolve(strict=True)


def make_installation(engine, checker, lean, library, source, provenance, exporter=None):
    source, library = absolute_existing(source), absolute_existing(library)
    result = {"schema": "fang-local-installation-v1", "platform": "linux",
        "source_root": str(source), "source_sha256": source_inventory(source),
        "proof_library": {"path": str(library), "files_sha256": directory_inventory(library)},
        "provenance": []}
    for name, path in (("engine", engine), ("checker", checker), ("lean", lean), ("python", sys.executable)):
        path = absolute_existing(path)
        result[name] = {"path": str(path), "sha256": digest_file(path)}
    if exporter is not None:
        path = absolute_existing(exporter)
        result["schema"] = "fang-local-installation-v2"
        result["exporter"] = {"path": str(path), "sha256": digest_file(path)}
        for name in ("lean/TstpExport.lean", "lean/TstpMain.lean"):
            if name not in result["source_sha256"]:
                raise Failure("Error", "TSTP installation is missing exporter source")
        verify_exporter_sources(source, result["source_sha256"])
    for path in provenance:
        path = absolute_existing(path)
        result["provenance"].append({"path": str(path), "sha256": digest_file(path)})
    if not result["provenance"]:
        raise Failure("Error", "At least one reviewed build/proof provenance record is required")
    for name in ("Fang/FrontendSoundness.olean", "Fang/CertificateInput.olean"):
        if name not in result["proof_library"]["files_sha256"]:
            raise Failure("Error", f"Installed proof library is missing {name}")
    return result


def verify_installation(config, check=lambda: None):
    expected = {"schema", "platform", "source_root", "source_sha256", "proof_library", "provenance", "engine", "checker", "lean", "python"}
    binaries = ["engine", "checker", "lean", "python"]
    if config.get("schema") == "fang-local-installation-v2":
        expected.add("exporter")
        binaries.append("exporter")
        for name in ("lean/TstpExport.lean", "lean/TstpMain.lean"):
            if name not in config.get("source_sha256", {}):
                raise Failure("Error", "TSTP installation is missing exporter source")
    if set(config) != expected or config["schema"] not in ("fang-local-installation-v1", "fang-local-installation-v2") or config["platform"] != "linux":
        raise Failure("Error", "Unsupported installation schema")
    for name in binaries:
        record = config[name]
        if set(record) != {"path", "sha256"} or not Path(record["path"]).is_absolute() or not re.fullmatch("[a-f0-9]{64}", record["sha256"]):
            raise Failure("Error", "Malformed executable pin")
        if digest_file(Path(record["path"]), check) != record["sha256"]:
            raise Failure("Error", "Installed executable differs from its pin")
    if digest_file(Path(sys.executable).resolve(), check) != config["python"]["sha256"]:
        raise Failure("Error", "Running Python differs from the installed interpreter")
    source = Path(config["source_root"])
    if not source.is_absolute() or source_inventory(source, check) != config["source_sha256"]:
        raise Failure("Error", "Installed source/proof provenance changed")
    if "exporter" in config and "lean/tstp-sources.json" in config["source_sha256"]:
        verify_exporter_sources(source, config["source_sha256"])
    library = config["proof_library"]
    if set(library) != {"path", "files_sha256"} or not Path(library["path"]).is_absolute() or directory_inventory(Path(library["path"]), check) != library["files_sha256"]:
        raise Failure("Error", "Shared proof-library inventory changed")
    for name in ("Fang/FrontendSoundness.olean", "Fang/CertificateInput.olean"):
        if name not in library["files_sha256"]:
            raise Failure("Error", "Required checked module is missing")
    if not config["provenance"]:
        raise Failure("Error", "Missing installation provenance")
    for record in config["provenance"]:
        if set(record) != {"path", "sha256"} or not Path(record["path"]).is_absolute() or digest_file(Path(record["path"]), check) != record["sha256"]:
            raise Failure("Error", "Installation build/proof record changed")


def main(argv=None):
    parser = argparse.ArgumentParser(description="Pin already built and reviewed local Fang tools; this command does not prove build provenance.")
    for name in ("engine", "checker", "lean", "proof-library", "source-root", "out"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--provenance", type=Path, action="append", required=True)
    parser.add_argument("--exporter", type=Path)
    args = parser.parse_args(argv)
    if sys.platform != "linux":
        parser.error("Linux/WSL is required")
    if args.out.exists():
        parser.error("Installation output must be new")
    result = make_installation(args.engine, args.checker, args.lean, args.proof_library,
        args.source_root, args.provenance, args.exporter)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    write_json(args.out, result)
    print(str(args.out.absolute()))
    return 0
