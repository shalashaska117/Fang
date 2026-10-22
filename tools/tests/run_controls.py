#!/usr/bin/env python3
"""Retain synthetic adapter controls without claiming native proof acceptance."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import argparse
import datetime
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import sys
import unittest


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    output = args.out.absolute()
    output.mkdir(parents=True, exist_ok=False)
    root = Path(__file__).resolve().parents[1]
    sources = sorted((root / "fang_szs").glob("*.py")) + sorted((root / "replay").glob("*.py")) + [root / "fang-szs.py", root / "fang-install.py", root / "build-local.py",
        Path(__file__).resolve(), Path(__file__).with_name("test_fang_szs.py")]
    pins = {str(path.relative_to(root)): digest(path) for path in sources}
    interpreter = Path(sys.executable).resolve()
    interpreter_sha = digest(interpreter)
    # Capture local executable sources before loading tests and adapter modules.
    import test_fang_szs as tests
    canonical = root.parent
    fixture_paths = [canonical / name for name in ("Cargo.toml", "Cargo.lock")]
    fixture_paths += [canonical / tests.CORE / name for name in sorted(tests.CORE_FILES)]
    fixture_pins = {path.relative_to(root.parent).as_posix(): digest(path) for path in fixture_paths}
    for path in sources:
        target = output / "sources" / path.relative_to(root)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, target)
    for path in fixture_paths:
        target = output / "fixture-sources" / path.relative_to(root.parent)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(path, target)
    tests.ProcessTests.artifact_root = output / "process-artifacts"
    tests.ProcessTests.artifact_root.mkdir()
    log = io.StringIO()
    suite = unittest.defaultTestLoader.loadTestsFromModule(tests)
    result = unittest.TextTestRunner(stream=log, verbosity=2).run(suite)
    (output / "controls.log").write_text(log.getvalue(), encoding="utf-8")
    unchanged = (pins == {str(path.relative_to(root)): digest(path) for path in sources}
        and fixture_pins == {path.relative_to(root.parent).as_posix(): digest(path) for path in fixture_paths}
        and digest(interpreter) == interpreter_sha)
    report = {"status": "passed" if result.wasSuccessful() and not result.skipped and unchanged else "failed",
        "finished_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), "python": sys.version,
        "python_path": str(interpreter), "python_sha256": interpreter_sha,
        "scope": "Synthetic process/protocol and installation identity controls; no Rust/Lean build, certificate acceptance or timing claim",
        "tests_run": result.testsRun, "skipped": result.skipped, "sources_sha256": pins,
        "fixture_sources_sha256": fixture_pins,
        "sources_unchanged": unchanged,
        "failures": [{"test": str(test), "trace": trace} for test, trace in result.failures],
        "errors": [{"test": str(test), "trace": trace} for test, trace in result.errors]}
    (output / "manifest.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: report[key] for key in ("status", "tests_run", "sources_unchanged")}))
    return int(report["status"] != "passed")


if __name__ == "__main__":
    os.environ["PYTHONDONTWRITEBYTECODE"] = "1"
    raise SystemExit(main())
