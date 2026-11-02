#!/usr/bin/env python3
"""Give the stdin-reading version-8 producer the captured sealed input descriptor."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import os
import sys

if len(sys.argv) != 3:
    raise SystemExit(64)
with open(sys.argv[2], "rb", buffering=0) as source:
    os.dup2(source.fileno(), 0)
    os.execv(sys.argv[1], [sys.argv[1]])
