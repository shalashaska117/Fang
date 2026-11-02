#!/usr/bin/env python3
"""Fetch the pinned Aeneas backend for a clean lean-v8 build. Uses the network.

Clones Aeneas and every Lake package at the exact revisions in
lean-v8/lake-manifest.json, downloads the mathlib prebuilt cache, obtains the
Aeneas build (release archive or local build of Aeneas only), and checks every
package against tools/v8_szs/backend-pins.json. A missing or different mathlib
cache is an install error: mathlib is never built from source as a fallback.
Pass the resulting package directory to tools/build-v8-lean.py --packages,
which checks the pins again before and after the lean-v8 build. Both use the
fetch digest of each pin, which leaves out only Lake build records (.hash,
.trace, .setup.json, .rsp); a differing file of any other kind is an error that
names the package and the file kinds.
"""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import argparse
from datetime import datetime, timezone
import json
from pathlib import Path
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True
TOOLS = Path(__file__).resolve().parent
ROOT = TOOLS.parent
sys.path.insert(0, str(TOOLS))
from fang_szs import v8_backend
from fang_szs.supervisor import write_json

CACHE_ERROR = ("The mathlib prebuilt cache for revision {rev} could not be downloaded. Installation stopped; "
               "mathlib is not built from source.")
DIFFERS = "Installation stopped: {package} differs from the pinned inventory in file kinds: {kinds}."


def differences(result, problems):
    return " ".join(DIFFERS.format(package=name, kinds=", ".join(result[name]["differing_kinds"]) or "(file count)")
                    for name in problems)


def run(command, cwd, environment, record, timeout):
    done = subprocess.run(list(map(str, command)), cwd=cwd, env=environment, capture_output=True, timeout=timeout)
    record.append({"command": list(map(str, command)), "exit_code": done.returncode,
                   "stdout_tail": done.stdout.decode("utf-8", "replace")[-2000:],
                   "stderr_tail": done.stderr.decode("utf-8", "replace")[-2000:]})
    return done.returncode == 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, required=True, help="fresh directory; packages end in <work>/project/.lake/packages")
    parser.add_argument("--lean-toolchain", type=Path, required=True, help="pinned Lean 4.35.0 toolchain root")
    args = parser.parse_args()
    if sys.platform != "linux":
        parser.error("Run on Linux or WSL")
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    toolchain = args.lean_toolchain.resolve()
    lake = toolchain / "bin/lake"
    environment = {"PATH": f"{toolchain / 'bin'}:/usr/bin:/bin", "HOME": str(work / "home"), "LANG": "C.UTF-8",
                   "LC_ALL": "C.UTF-8", "LEAN_NUM_THREADS": "1"}
    (work / "home").mkdir()
    report = {"schema": "fang-v8-backend-fetch-v1", "status": "running", "started_utc": datetime.now(timezone.utc).isoformat(),
              "commands": []}
    commands = report["commands"]
    try:
        manifest = json.loads((ROOT / "lean-v8/lake-manifest.json").read_text(encoding="utf-8"))
        pins = v8_backend.load_pins(ROOT)
        project = work / "project"
        project.mkdir()
        for name in ("lakefile.toml", "lean-toolchain", "lake-manifest.json"):
            shutil.copyfile(ROOT / "lean-v8" / name, project / name)
        packages = project / ".lake/packages"
        packages.mkdir(parents=True)
        revisions = {entry["name"]: entry for entry in manifest["packages"]}
        if set(revisions) != set(pins["packages"]):
            raise ValueError("lake-manifest.json and backend-pins.json name different packages")
        for name, entry in sorted(revisions.items()):
            if entry["rev"] != pins["packages"][name]["rev"]:
                raise ValueError(f"Revision of {name} differs between the manifest and the pins")
            target = packages / name
            if not (run(["git", "clone", "-q", "--no-checkout", entry["url"], target], work, environment, commands, 3600)
                    and run(["git", "-C", target, "-c", "advice.detachedHead=false", "checkout", "-q", entry["rev"]],
                            work, environment, commands, 600)):
                raise ValueError(f"Could not fetch {name} at {entry['rev']}")
            done = subprocess.run(["git", "-C", str(target), "rev-parse", "HEAD"], capture_output=True, env=environment)
            if done.stdout.decode().strip() != entry["rev"]:
                raise ValueError(f"{name} is not at its pinned revision")
        if not run([lake, "-d", project, "exe", "cache", "get"], project, environment, commands, 7200):
            raise ValueError(CACHE_ERROR.format(rev=revisions["mathlib"]["rev"]))
        result, _, problems = v8_backend.check_packages(packages, {"packages": {"mathlib": pins["packages"]["mathlib"]}},
                                                         fetch=True)
        report["mathlib"] = result["mathlib"]
        if problems:
            raise ValueError(differences(result, problems) + " The mathlib cache is never replaced by a source build.")
        if not run([lake, "-d", project, "build", "Aeneas", "AeneasMeta"], project, environment, commands, 14400):
            raise ValueError("Aeneas could not be fetched or built at the pinned revision")
        result, _, problems = v8_backend.check_packages(packages, pins, fetch=True)
        report["packages"] = result
        if problems:
            raise ValueError(differences(result, problems))
        report.update(status="fetched-and-checked", packages_directory=str(packages))
    except (OSError, ValueError, subprocess.TimeoutExpired) as error:
        report.update(status="failed", error=str(error))
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    write_json(work / "fetch-manifest.json", report)
    print(json.dumps({key: report.get(key) for key in ("status", "packages_directory", "error")}))
    return int(report["status"] != "fetched-and-checked")


if __name__ == "__main__":
    raise SystemExit(main())
