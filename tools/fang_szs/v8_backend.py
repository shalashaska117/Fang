"""Compact content pins for the Aeneas backend packages used by lean-v8.

A package digest covers every file except .git metadata, Lake configuration
caches and the downloaded Aeneas release archive. Each row is the path, kind,
size, SHA-256 and, for symlinks, the link text. Permission bits are ignored.

Three digests are pinned per package. The exact digest covers every such file.
The content digest leaves out Lake's .hash files. The fetch digest leaves out
all Lake build records (BUILD_RECORDS), which embed absolute build paths and
command lines; every source, .olean, .ilean, .c, .so and binary stays in it.
Per-kind digests let a failed check name the file kinds that differ.
"""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import hashlib
import json
import os
from pathlib import Path
import stat

PINS = "tools/v8_szs/backend-pins.json"
AENEAS_EXCLUDED = frozenset({".lake/lean-build-aeneas-x86_64-unknown-linux-gnu.tar.gz"})
AENEAS_SUBDIR = "backends/lean"
BUILD_RECORDS = (".hash", ".trace", ".setup.json", ".rsp")


def excluded(relative):
    return relative in AENEAS_EXCLUDED or relative.startswith(".lake/config/")


def lake_hash_file(relative):
    """Lake's cached artifact hashes. Lake rewrites them when it rehashes an unchanged artifact."""
    return relative.endswith(".hash")


def build_record(relative):
    """Lake build records: cached hashes, traces, setup files and linker response files."""
    return relative.endswith(BUILD_RECORDS)


def file_kind(relative):
    name = relative.rsplit("/", 1)[-1]
    return name.split(".", 1)[1] if "." in name else "(none)"


def _kept(relative, content, fetch):
    return not (excluded(relative) or (content and lake_hash_file(relative)) or (fetch and build_record(relative)))


def package_digest(rows, *, content=False, fetch=False):
    """Exact digest; content=True leaves out .hash files; fetch=True leaves out all build records."""
    hasher = hashlib.sha256()
    for relative in sorted(rows):
        if not _kept(relative, content, fetch):
            continue
        record = rows[relative]
        hasher.update("\0".join((relative, record["kind"], str(record["size"]), record["sha256"],
                                 record.get("target", ""))).encode("utf-8") + b"\n")
    return hasher.hexdigest()


def kind_digests(rows):
    """Exact digest and file count per file kind (the basename after its first dot)."""
    groups = {}
    for relative in rows:
        if not excluded(relative):
            groups.setdefault(file_kind(relative), {})[relative] = rows[relative]
    return {kind: {"files": len(group), "digest": package_digest(group)} for kind, group in sorted(groups.items())}


def _file_hash(path, check):
    hasher, size = hashlib.sha256(), 0
    with open(path, "rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            check()
            hasher.update(block)
            size += len(block)
    return hasher.hexdigest(), size


def scan(directory, check=lambda: None):
    """Inventory one package directory with the same row fields as the pinned inventory."""
    directory = Path(directory).resolve(strict=True)
    rows = {}
    for current, dirs, files in os.walk(directory, followlinks=False):
        check()
        dirs[:] = sorted(name for name in dirs if name != ".git")
        for name in files:
            path = Path(current) / name
            relative = path.relative_to(directory).as_posix()
            if excluded(relative):
                continue
            mode = path.lstat().st_mode
            if stat.S_ISLNK(mode):
                resolved = path.resolve(strict=True)
                if not resolved.is_relative_to(directory) or not resolved.is_file():
                    raise ValueError(f"Backend symlink leaves its package: {path}")
                digest, size = _file_hash(resolved, check)
                rows[relative] = {"kind": "symlink", "target": os.readlink(path), "sha256": digest, "size": size}
            elif stat.S_ISREG(mode):
                digest, size = _file_hash(path, check)
                rows[relative] = {"kind": "file", "sha256": digest, "size": size}
            else:
                raise ValueError(f"Unsupported backend entry: {path}")
        for name in dirs:
            if (Path(current) / name).is_symlink():
                raise ValueError(f"Backend directory symlink: {Path(current) / name}")
    return rows


def load_pins(root):
    value = json.loads((Path(root) / PINS).read_text(encoding="utf-8"))
    if value.get("schema") != "fang-v8-backend-pins-v1":
        raise ValueError("Unexpected backend pin schema")
    return value


def package_directory(packages, name):
    return Path(packages) / name / AENEAS_SUBDIR if name == "aeneas" else Path(packages) / name


def differing_kinds(rows, pin):
    """File kinds whose files differ from the pin, split into build records and everything else."""
    actual, pinned = kind_digests(rows), pin["kinds"]
    kinds = sorted(kind for kind in set(actual) | set(pinned) if actual.get(kind) != pinned.get(kind))
    records = [kind for kind in kinds if ("." + kind).endswith(BUILD_RECORDS)]
    return [kind for kind in kinds if kind not in records], records


def check_packages(packages, pins, check=lambda: None, *, allow_additions=False, before=None, content=False, fetch=False):
    """Compare every package with its pin, or, after a build, with the rows seen before it.

    Without `before`, each package must match its pin: the exact digest, the
    content digest (`content`) or the fetch digest (`fetch`). A fetch check also
    names the file kinds that differ; any differing kind outside BUILD_RECORDS
    fails. With `before` (the rows returned by an earlier call), every earlier
    row must be unchanged except Lake .hash rewrites; new rows are allowed only
    when `allow_additions` is set, for build outputs.
    """
    result, rows_by_package, problems = {}, {}, []
    for name, pin in sorted(pins["packages"].items()):
        rows = scan(package_directory(packages, name), check)
        rows_by_package[name] = rows
        if before is None:
            if fetch:
                kept = [relative for relative in rows if _kept(relative, False, True)]
                other, records = differing_kinds(rows, pin)
                matches = (len(kept) == pin["fetch_files"] and package_digest(rows, fetch=True) == pin["fetch_digest"]
                           and not other)
                result[name] = {"fetch_files": len(kept), "fetch_digest": package_digest(rows, fetch=True),
                                "matches_fetch_pin": matches, "differing_kinds": other,
                                "differing_build_record_kinds": records,
                                "matches_exact_pin": len(rows) == pin["files"] and package_digest(rows) == pin["digest"]}
            elif content:
                kept = [relative for relative in rows if not lake_hash_file(relative)]
                matches = len(kept) == pin["content_files"] and package_digest(rows, content=True) == pin["content_digest"]
                result[name] = {"content_files": len(kept), "content_digest": package_digest(rows, content=True),
                                "matches_content_pin": matches, "exact_digest": package_digest(rows),
                                "matches_exact_pin": len(rows) == pin["files"] and package_digest(rows) == pin["digest"]}
            else:
                matches = len(rows) == pin["files"] and package_digest(rows) == pin["digest"]
                result[name] = {"files": len(rows), "digest": package_digest(rows), "matches_pin": matches}
            if not matches:
                problems.append(name)
        else:
            earlier = before[name]
            changed = sorted(key for key in earlier if rows.get(key) != earlier[key])
            # Lake may rewrite its cached artifact hashes; the artifacts themselves must not change.
            rehashed = [key for key in changed if key.endswith(".hash") and key in rows]
            changed = [key for key in changed if key not in rehashed]
            added = sorted(set(rows) - set(earlier))
            result[name] = {"files": len(rows), "changed_or_removed": len(changed), "rehashed": len(rehashed),
                            "added": len(added), "examples": (changed + rehashed + added)[:5]}
            if changed or (added and not allow_additions):
                problems.append(name)
    return result, rows_by_package, problems
