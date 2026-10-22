"""Inventory the declared local Rust dependency before snapshotting or checking it.

Shared by the local build snapshot and installation identity checks.
"""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import os
from pathlib import Path
import stat
import tomllib


CORE = "crates/fang-predicate-index"
CORE_PACKAGE = {"name": "fang-predicate-index-core", "version": "0.0.0"}
CORE_FILES = frozenset(("Cargo.toml", "Cargo.lock", "rust-toolchain.toml", "LICENSE",
                        "src/lib.rs", "tests/index.rs"))
LOCAL_NOTES = frozenset(("README.md", "CONTRACT.md", "PROMOTION.md"))


def regular(path, check):
    check()
    if not stat.S_ISREG(path.lstat().st_mode):
        raise ValueError(f"Dependency input must be a regular file: {path}")


def read_toml(path, check):
    regular(path, check)
    return tomllib.loads(path.read_text(encoding="utf-8"))


def reject_other_dependencies(manifest):
    # New dependency sources require an explicit inventory policy.
    for key in ("dev-dependencies", "build-dependencies", "target", "workspace", "patch", "replace"):
        if key in manifest:
            raise ValueError(f"Unreviewed Cargo dependency section: {key}")
    if "build" in manifest.get("package", {}):
        raise ValueError("Explicit build scripts require review")
    if "workspace" in manifest.get("package", {}):
        raise ValueError("External package workspaces require review")
    for key in ("lib", "bin", "example", "test", "bench"):
        if key in manifest:
            raise ValueError(f"Explicit Cargo source targets require review: {key}")


def real_directory(path, check):
    check()
    if not stat.S_ISDIR(path.lstat().st_mode):
        raise ValueError(f"Dependency parent must be a real directory: {path}")


def check_lock(path, packages, check):
    expected = {"version": 4, "package": packages}
    if read_toml(path, check) != expected:
        raise ValueError(f"Unreviewed Cargo lockfile graph: {path}")


def dependency_files(root, check=lambda: None):
    """Return all declared dependency inputs, or reject an unreviewed graph.

    This validates inventory membership, not file contents against a prior pin.
    The caller must hash each returned file and compare the captured inventory.
    Ancestor/Cargo-home configuration and source-level includes still depend on
    reviewed source and the declared build environment. This is not a hermetic
    build guarantee.
    """
    root = Path(root)
    manifest = read_toml(root / "Cargo.toml", check)
    reject_other_dependencies(manifest)
    if os.path.lexists(root / "build.rs"):
        raise ValueError("Implicit root build scripts require review")
    package = manifest.get("package", {})
    if (package.get("name"), package.get("version")) != ("fang", "0.1.0"):
        raise ValueError("Unreviewed root package identity")
    dependencies = manifest.get("dependencies", {})
    root_package = {"name": "fang", "version": "0.1.0"}
    if dependencies == {}:
        check_lock(root / "Cargo.lock", [root_package], check)
        if os.path.lexists(root / "crates"):
            raise ValueError("Local crates exist without a declared dependency")
        return []
    if dependencies != {"fang-predicate-index-core": {"path": CORE}}:
        raise ValueError("Unreviewed local Rust dependency graph")
    root_package["dependencies"] = ["fang-predicate-index-core"]
    check_lock(root / "Cargo.lock", [root_package, CORE_PACKAGE], check)
    real_directory(root / "crates", check)
    crate = root / CORE
    real_directory(crate, check)
    with os.scandir(root / "crates") as entries:
        for entry in entries:
            check()
            if entry.name != "fang-predicate-index":
                raise ValueError("Unexpected local crate")

    found = set()
    pending = [crate]
    while pending:
        directory = pending.pop()
        real_directory(directory, check)
        with os.scandir(directory) as entries:
            for entry in entries:
                check()
                path = Path(entry.path)
                relative = path.relative_to(crate).as_posix()
                mode = entry.stat(follow_symlinks=False).st_mode
                if stat.S_ISDIR(mode):
                    if relative == "target":
                        continue  # Build outputs are never copied or hashed as source.
                    if relative not in ("src", "tests"):
                        raise ValueError(f"Unexpected dependency directory: {relative}")
                    pending.append(path)
                elif stat.S_ISREG(mode) and relative in CORE_FILES:
                    found.add(relative)
                elif stat.S_ISREG(mode) and relative in LOCAL_NOTES:
                    continue  # Local research notes are outside the build and publication inventory.
                else:
                    raise ValueError(f"Unexpected dependency member: {relative}")
    if found != CORE_FILES:
        raise ValueError(f"Incomplete dependency inventory: {sorted(CORE_FILES - found)}")
    core_manifest = read_toml(crate / "Cargo.toml", check)
    reject_other_dependencies(core_manifest)
    if core_manifest.get("dependencies", {}) != {}:
        raise ValueError("Transitive core dependencies require review")
    core_package = core_manifest.get("package", {})
    if any(core_package.get(key) != value for key, value in CORE_PACKAGE.items()):
        raise ValueError("Unexpected core package identity")
    check_lock(crate / "Cargo.lock", [CORE_PACKAGE], check)
    return [crate / relative for relative in sorted(CORE_FILES)]
