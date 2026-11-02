"""Inventory the explicitly declared FOF installed-tool graph."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import json
import os
from pathlib import Path
import stat
import tomllib

OLD = frozenset({"fang-predicate-index"})
LEAVES = frozenset({"ground-fof-core", "ground-fof-frontend", "ground-fof-search", "ground-fof-versioned"})
ORDER = ("ground-fof-core", "ground-fof-frontend", "ground-fof-search", "ground-fof-versioned")


def graph(name, manifest, lock):
    index = ORDER.index(name)
    expected_dependencies = {"fang": {"path": "../.."}}
    expected_dependencies.update({"fang-" + earlier: {"path": "../" + earlier} for earlier in ORDER[:index]})
    package = {"name": "fang-" + name, "version": "0.0.0", "edition": "2024",
               "publish": False, "license": "BSD-3-Clause"}
    if index < 2:
        package["rust-version"] = "1.90"
    expected = {"package": package, "dependencies": expected_dependencies,
                "lints": {"rust": {"unsafe_code": "forbid"}}, "profile": {"release": {"overflow-checks": True}}}
    if name == "ground-fof-versioned":
        package["autobins"] = False
        expected["bin"] = [{"name": "fang-ground-fof-driver", "path": "src/bin/driver.rs"}]
    if manifest != expected:
        raise ValueError("Unreviewed FOF package or path graph")
    packages = [{"name": "fang", "version": "0.1.0", "dependencies": ["fang-predicate-index-core"]},
                {"name": "fang-predicate-index-core", "version": "0.0.0"}]
    for position, leaf in enumerate(ORDER[:index + 1]):
        packages.append({"name": "fang-" + leaf, "version": "0.0.0",
                         "dependencies": ["fang", *["fang-" + earlier for earlier in ORDER[:position]]]})
    packages.sort(key=lambda value: value["name"])
    if lock != {"version": 4, "package": packages}:
        raise ValueError("Unreviewed FOF transitive lock graph")


def leaf_files(root, check=lambda: None):
    root = Path(root)
    crate_root = root / "crates"
    if not crate_root.exists():
        return [], OLD
    mode = crate_root.lstat().st_mode
    if not stat.S_ISDIR(mode):
        raise ValueError("Crate root must be a real directory")
    actual = set()
    for child in crate_root.iterdir():
        check()
        if not stat.S_ISDIR(child.lstat().st_mode):
            raise ValueError("Crate entry must be a real directory")
        actual.add(child.name)
    if actual == OLD:
        return [], OLD
    version8 = frozenset()
    if "workspace" in tomllib.loads((root / "Cargo.toml").read_text()):
        # The version-8 crates are checked file by file against their source map by the caller.
        from .v8_dependencies import crate_names
        version8 = crate_names(root, check)
    if actual != OLD | LEAVES | version8:
        raise ValueError("Incomplete or unknown FOF leaf graph")
    policy_path = root / "tools/fof_szs/sources.json"
    if not stat.S_ISREG(policy_path.lstat().st_mode):
        raise ValueError("FOF source policy must be regular")
    policy = json.loads(policy_path.read_text())
    if set(policy) != {"schema", "crates"} or policy["schema"] != "fang-fof-source-graph-v1" or set(policy["crates"]) != LEAVES:
        raise ValueError("FOF source policy differs")
    result = [policy_path]
    for name in sorted(LEAVES):
        crate, declared = crate_root / name, policy["crates"][name]
        if set(declared) != {"files", "manifest", "lock"}:
            raise ValueError("Malformed FOF crate policy")
        expected = set(declared["files"])
        reviewed_files = {"Cargo.toml", "Cargo.lock", "src/lib.rs"}
        if name == "ground-fof-versioned":
            reviewed_files |= {"src/bin/driver.rs", "tests/driver_cli.rs"}
        if len(expected) != len(declared["files"]) or expected != reviewed_files:
            raise ValueError("FOF crate file policy differs from the reviewed inventory")
        for relative in expected:
            path = Path(relative)
            if path.is_absolute() or ".." in path.parts or not path.parts:
                raise ValueError("Unsafe FOF source policy path")
        found = set()
        for directory, dirs, files in os.walk(crate, followlinks=False):
            check()
            parent = Path(directory)
            for child in dirs[:]:
                target = parent / child
                relative = target.relative_to(crate).as_posix()
                if not stat.S_ISDIR(target.lstat().st_mode):
                    raise ValueError("FOF directory is a symlink or non-directory")
                if relative == "target":
                    dirs.remove(child)
                elif not any(value.startswith(relative + "/") for value in expected):
                    raise ValueError("Unlisted FOF source directory")
            for child in files:
                check()
                path = parent / child
                relative = path.relative_to(crate).as_posix()
                if relative not in expected or not stat.S_ISREG(path.lstat().st_mode):
                    raise ValueError("Unlisted or nonregular FOF source")
                found.add(relative)
        if found != expected:
            raise ValueError("Missing FOF source")
        for filename, key in (("Cargo.toml", "manifest"), ("Cargo.lock", "lock")):
            if tomllib.loads((crate / filename).read_text()) != declared[key]:
                raise ValueError("FOF Cargo graph differs: " + name + "/" + filename)
        graph(name, declared["manifest"], declared["lock"])
        result.extend(crate / relative for relative in sorted(found))
    return result, OLD | LEAVES | version8
