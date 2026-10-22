"""Copy replay artifacts while checking their byte identity."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import hashlib
import shutil


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def copy_checked(source, target):
    target.parent.mkdir(parents=True, exist_ok=True)
    before = sha(source)
    shutil.copyfile(source, target)
    if sha(target) != before or sha(source) != before:
        raise ValueError(f"Artifact changed during staging: {source}")
    return before

