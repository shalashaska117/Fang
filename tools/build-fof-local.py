#!/usr/bin/env python3
"""Build the CNF command and the bounded ground-FOF command with TSTP output."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import importlib.util
from pathlib import Path

spec = importlib.util.spec_from_file_location("fang_local_build", Path(__file__).with_name("build-local.py"))
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)

if __name__ == "__main__":
    raise SystemExit(module.main(fof=True))
