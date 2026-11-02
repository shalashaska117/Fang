#!/usr/bin/env python3
"""Fail if any promoted version-8 Rust or Lean source differs from its source map or receipt."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import argparse
import json
from pathlib import Path
import sys
import tomllib

sys.dont_write_bytecode = True
sys.path.insert(0, str(Path(__file__).resolve().parent))
from fang_szs import v8_dependencies as sources

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT, help="source tree to check (default: this checkout)")
    parser.add_argument("--receipts", action="store_true",
                        help="also check the maps against the receipt archives under evidence/")
    parser.add_argument("--skip-lean", action="store_true", help="check the Rust crates only")
    args = parser.parse_args()
    root = args.root.resolve()
    try:
        manifest = tomllib.loads((root / "Cargo.toml").read_text(encoding="utf-8"))
        rust_map = sources.load_map(root, sources.RUST_MAP, sources.RUST_SCHEMA)
        sources.check_workspace(root, manifest, rust_map)
        report = {"status": "passed", "rust_files": len(sources.rust_files(root))}
        if not args.skip_lean:
            report["lean_files"] = len(sources.lean_files(root))
        if args.receipts:
            report["rust_receipt_entries"] = sources.check_rust_receipts(root)
            if not args.skip_lean:
                report["lean_receipt_entries"] = sources.check_lean_receipts(root)
    except (OSError, ValueError, KeyError) as error:
        print(json.dumps({"status": "failed", "error": str(error)}))
        return 1
    print(json.dumps(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
