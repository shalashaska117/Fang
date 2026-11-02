#!/usr/bin/env python3
"""Hash the installation's Lean trees and compare them with the installation record.

`record` writes the tree manifests when the kernel is installed; `verify`
recomputes them before and after a kernel run. A tree is a directory the
compiler reads: the toolchain, every directory on the recorded LEAN_PATH
and the helper objects. Every regular file below it is hashed; symbolic
links are recorded by target. Any added, removed or changed entry makes the
status `changed`.
"""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import stat
import sys

sys.dont_write_bytecode = True


def digest_file(path):
    hasher = hashlib.sha256()
    with open(path, 'rb') as stream:
        while block := stream.read(1 << 20):
            hasher.update(block)
    return hasher.hexdigest()


def tree(directory):
    """relative path -> sha256 of a regular file, or 'link:' + target for a symbolic link."""
    result = {}
    base = Path(directory)
    for current, folders, files in os.walk(base, followlinks=False):
        folders.sort()
        for name in sorted(files) + sorted(folder for folder in folders if os.path.islink(os.path.join(current, folder))):
            path = Path(current) / name
            relative = path.relative_to(base).as_posix()
            info = os.lstat(path)
            if stat.S_ISLNK(info.st_mode):
                result[relative] = 'link:' + os.readlink(path)
            elif stat.S_ISREG(info.st_mode):
                result[relative] = digest_file(path)
            else:
                result[relative] = 'special'
    return result


def summary(files):
    return hashlib.sha256(json.dumps(files, sort_keys=True).encode()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('record', 'verify'))
    parser.add_argument('--trees', type=Path, help='record: JSON object name -> directory')
    parser.add_argument('--installation', type=Path, help='verify: the installation record')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    started = datetime.now(timezone.utc).isoformat()
    if args.mode == 'record':
        directories = json.loads(args.trees.read_bytes())
        value = {}
        for name, directory in sorted(directories.items()):
            files = tree(directory)
            value[name] = {'directory': str(directory), 'files': len(files), 'sha256': summary(files), 'files_sha256': files}
        args.output.write_bytes((json.dumps(value, indent=2, sort_keys=True) + '\n').encode())
        print(json.dumps({name: (item['files'], item['sha256']) for name, item in value.items()}))
        return 0
    out = args.output
    out.mkdir(parents=True, exist_ok=False)
    data = args.installation.read_bytes()
    record = json.loads(data)
    recorded = json.loads(Path(record['trees']['path']).read_bytes())
    if hashlib.sha256(json.dumps(recorded, indent=2, sort_keys=True).encode() + b'\n').hexdigest() != record['trees']['sha256']:
        raise SystemExit('Tree record differs from the installation record')
    differences, totals = {}, {}
    for name, item in sorted(recorded.items()):
        files = tree(item['directory'])
        old = item['files_sha256']
        differences[name] = {'added': sorted(set(files) - set(old))[:50], 'removed': sorted(set(old) - set(files))[:50],
                             'changed': sorted(key for key in set(files) & set(old) if files[key] != old[key])[:50]}
        totals[name] = {'files': len(files), 'sha256': summary(files)}
    unchanged = all(not values for tree_differences in differences.values() for values in tree_differences.values())
    report = {'schema': 'fang-v8-kernel-trees-v1', 'status': 'unchanged' if unchanged else 'changed',
              'started_utc': started, 'finished_utc': datetime.now(timezone.utc).isoformat(),
              'installation_sha256': hashlib.sha256(data).hexdigest(), 'trees': totals, 'differences': differences}
    (out / 'manifest.json').write_bytes((json.dumps(report, indent=2, sort_keys=True) + '\n').encode())
    print(json.dumps({'status': report['status']}))
    return 0 if unchanged else 1


if __name__ == '__main__':
    raise SystemExit(main())
