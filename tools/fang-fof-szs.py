#!/usr/bin/env python3
"""Run the explicit mixed ground-FOF status profile."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
from pathlib import Path
import sys
sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent / "fof_szs"))
from main import main

if __name__ == "__main__":
    raise SystemExit(main())
