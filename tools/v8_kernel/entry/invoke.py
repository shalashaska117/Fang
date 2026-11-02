#!/usr/bin/env python3
"""Run pinned capture buffers under the outer equality entry supervisor (entry revision 6)."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import hashlib
import json
import os
from pathlib import Path
import sys
import types

sys.dont_write_bytecode = True


def load(path, expected, name):
    data = path.read_bytes()
    if hashlib.sha256(data).hexdigest() != expected:
        raise ValueError('Captured helper changed: ' + str(path))
    module = types.ModuleType(name)
    module.__file__ = str(path)
    sys.modules[name] = module
    exec(compile(data, str(path), 'exec'), module.__dict__)
    return module


def main():
    capture, root, mode, *arguments = sys.argv[1:]
    capture, root = Path(capture), Path(root)
    policy = json.loads((capture / 'policy.json').read_bytes())
    if mode == 'inventory':
        # The tree manifests recorded at install replace the dependency inventory.
        relative = policy['inventory']['runner']
        helper = load(capture / relative, policy['files'][relative], 'captured_inventory')
        sys.argv = [str(capture / relative), 'verify', '--installation', str(capture / 'installation.json'),
                    '--output', *arguments]
    elif mode == 'check':
        relative = policy['entry_directory'] + '/check.py'
        helper = load(capture / relative, policy['files'][relative], 'captured_check')
        helper.SOURCE = capture / policy['generator_directory']
        helper.TOOLS_ROOT = capture
        native = capture.parent / 'proof-native'

        def workspace(**_):
            native.mkdir(exist_ok=False)
            return str(native)

        helper.tempfile.mkdtemp = workspace
        sys.argv = [str(capture / relative), *arguments]
    else:
        raise ValueError('Unknown captured child mode')
    return helper.main()


if __name__ == '__main__':
    raise SystemExit(main())
