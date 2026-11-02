"""Full Lean toolchain content checks, including internal symlinks."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import hashlib
import os
from pathlib import Path
import stat


def metadata(value):
    return (value.st_dev, value.st_ino, value.st_mode, value.st_size,
            value.st_mtime_ns, value.st_ctime_ns)


def tree(root, check):
    result = {}
    def failure(error):
        raise error
    for directory, dirs, files in os.walk(root, followlinks=False, onerror=failure):
        dirs.sort()
        for name in sorted(dirs + files):
            check()
            path = Path(directory) / name
            result[path.relative_to(root).as_posix()] = metadata(path.lstat())
    return result


def stable_file(path, check):
    before = path.lstat()
    with os.fdopen(os.open(path, os.O_RDONLY | os.O_NOFOLLOW), "rb") as stream:
        opened = os.fstat(stream.fileno())
        if not stat.S_ISREG(opened.st_mode) or metadata(before) != metadata(opened):
            raise ValueError("Toolchain dependency replaced before hashing")
        hasher = hashlib.sha256()
        while block := stream.read(1 << 20):
            check()
            hasher.update(block)
        if metadata(opened) != metadata(os.fstat(stream.fileno())):
            raise ValueError("Toolchain dependency changed during hashing")
    if metadata(opened) != metadata(path.lstat()):
        raise ValueError("Toolchain dependency replaced during hashing")
    return {"size": opened.st_size, "sha256": hasher.hexdigest(), "mode": stat.S_IMODE(opened.st_mode)}


def verify(root, expected, check=lambda: None):
    root = Path(root)
    if not root.is_absolute() or root.is_symlink() or not root.is_dir():
        raise ValueError("Toolchain root must be an absolute real directory")
    root = root.resolve(strict=True)
    before, actual = tree(root, check), {}
    for relative, identity in sorted(before.items()):
        check()
        path = root / relative
        if stat.S_ISDIR(identity[2]):
            continue
        if stat.S_ISLNK(identity[2]):
            resolved = path.resolve(strict=True)
            if not resolved.is_relative_to(root) or not resolved.is_file():
                raise ValueError("Toolchain symlink escapes the recorded tree")
            record = {"kind": "symlink", "target": os.readlink(path),
                      "resolved": resolved.relative_to(root).as_posix(), **stable_file(resolved, check)}
            if path.resolve(strict=True) != resolved:
                raise ValueError("Toolchain symlink changed during hashing")
        elif stat.S_ISREG(identity[2]):
            record = {"kind": "file", **stable_file(path, check)}
        else:
            raise ValueError("Nonregular toolchain member")
        if identity != metadata(path.lstat()):
            raise ValueError("Toolchain changed during inventory")
        actual[relative] = record
    if tree(root, check) != before or actual != expected:
        raise ValueError("Installed Lean toolchain differs from its reviewed inventory")
