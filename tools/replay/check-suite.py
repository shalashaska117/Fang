#!/usr/bin/env python3
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
"""Snapshot and check the std-only Lean checker and frontend proof sources."""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import tempfile
import time


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def process_tree_rss(pid: int) -> int:
    """Sum resident memory of a process and its current descendants, in KiB."""
    try:
        status = Path(f"/proc/{pid}/status").read_text()
        match = re.search(r"^VmRSS:\s+(\d+)\s+kB$", status, re.M)
        own = int(match.group(1)) if match else 0
        children = Path(f"/proc/{pid}/task/{pid}/children").read_text().split()
        return own + sum(process_tree_rss(int(child)) for child in children)
    except (FileNotFoundError, ProcessLookupError):
        return 0


def lean_code(text: str) -> str:
    """Discard nested comments and strings before checking source directives."""
    output: list[str] = []
    cursor = depth = 0
    string = False
    while cursor < len(text):
        pair = text[cursor:cursor + 2]
        character = text[cursor]
        if depth:
            if pair == "/-":
                depth += 1
                cursor += 2
            elif pair == "-/":
                depth -= 1
                cursor += 2
            else:
                output.append("\n" if character == "\n" else " ")
                cursor += 1
        elif string:
            if character == "\\":
                cursor += 2
            elif character == '"':
                string = False
                output.append(" ")
                cursor += 1
            else:
                output.append("\n" if character == "\n" else " ")
                cursor += 1
        elif pair == "/-":
            depth = 1
            cursor += 2
        elif pair == "--":
            end = text.find("\n", cursor)
            cursor = len(text) if end < 0 else end
        elif character == "'" and (literal := re.match(
                r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^'\\\r\n])'", text[cursor:])):
            output.append(" ")
            cursor += len(literal.group(0))
        elif character == '"':
            string = True
            output.append(" ")
            cursor += 1
        else:
            output.append(character)
            cursor += 1
    return "".join(output)


def main() -> int:
    arguments = argparse.ArgumentParser(description=__doc__)
    arguments.add_argument("root", type=Path)
    arguments.add_argument("lean", type=Path)
    arguments.add_argument("--out", type=Path, help="Fresh directory for local proof artifacts")
    arguments.add_argument("--timeout-seconds", type=int, default=120)
    arguments.add_argument("--memory-mib", type=int, default=2048)
    options = arguments.parse_args()
    if options.timeout_seconds <= 0 or options.memory_mib <= 0:
        arguments.error("resource limits must be positive")
    root, lean = options.root.resolve(), options.lean.resolve()
    stamp = dt.datetime.now(dt.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    run = options.out.resolve() if options.out else root / ".local" / "checks" / f"proof-suite-{stamp}"
    run.mkdir(parents=True, exist_ok=False)
    source = run / "project"
    source.mkdir(parents=True)
    (run / "logs").mkdir()
    native = Path(tempfile.mkdtemp(prefix=f"fang-checker-{stamp}-", dir="/var/tmp"))
    manifest: dict = {
        "status": "running", "suite": "std-only-checker-frontend",
        "source_root": str(root / "lean"), "native_project": str(native),
        "timeout_seconds_per_module": options.timeout_seconds,
        "lean_heap_limit_mib": options.memory_mib,
        "rss_limit_mib": options.memory_mib,
        "rss_monitor": "Sample summed process-tree RSS every 50 ms; kill the process group above the limit. GNU time independently records maximum RSS. Brief peaks between samples can escape the sampler.",
        "lean_threads": 1,
        "completed_modules": [], "axiom_audits": [], "module_resources": {},
        "limits": "Kernel checks cover stated Lean theorems. Compiling IO entrypoints does not run their native IO regressions; compiled #eval checks are not kernel instance proofs.",
    }
    manifest_path = run / "manifest.json"

    def record() -> None:
        manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")

    print(run, flush=True)
    record()
    try:
        paths = sorted((root / "lean" / "Fang").rglob("*.lean"))
        paths += sorted((root / "lean").glob("*.lean"))
        for path in paths:
            destination = source / path.relative_to(root / "lean")
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, destination)
        for name in ("lean-toolchain", "lakefile.toml", "check-local.sh"):
            shutil.copyfile(root / "lean" / name, source / name)
        shutil.copyfile(Path(__file__), run / "check-suite.py")
        manifest["toolchain"] = (source / "lean-toolchain").read_text().strip()
        version = subprocess.check_output([str(lean), "--version"], text=True).strip()
        manifest["lean_version"] = version
        manifest["lean_executable_sha256"] = digest(lean)
        expected = manifest["toolchain"].rsplit(":v", 1)[-1]
        if f"version {expected}," not in version:
            raise RuntimeError(f"Expected Lean {expected}, observed {version}")
        (run / "lean-version.txt").write_text(version + "\n")
        modules = {str(path.relative_to(source).with_suffix("")).replace(os.sep, "."): path
                   for path in sorted(source.rglob("*.lean"))}
        dependencies: dict[str, list[str]] = {}
        audit_count = 0
        for module, path in modules.items():
            code = lean_code(path.read_text())
            forbidden = re.search(r"\b(sorry|admit|axiom|native_decide)\b|\bdecide\s*\+\s*native\b|\bdebug\.skipKernelTC\b", code)
            if forbidden:
                raise RuntimeError(f"Forbidden proof construct in {module}: {forbidden.group(0)}")
            dependencies[module] = re.findall(r"^\s*(?:public\s+)?import\s+([\w.]+)", code, re.M)
            audit_count += len(re.findall(r"#print\s+axioms\s+", code))
        manifest["declared_axiom_audits"] = audit_count
        manifest["source_sha256"] = {str(path.relative_to(source)): digest(path)
                                      for path in sorted(source.rglob("*")) if path.is_file()}
        order: list[str] = []
        visiting: set[str] = set()
        visited: set[str] = set()
        external: set[str] = set()

        def visit(module: str) -> None:
            if module in visited:
                return
            if module not in modules:
                if module.split(".")[0] not in {"Init", "Std", "Lean"}:
                    raise RuntimeError(f"Non-standard or missing dependency: {module}")
                external.add(module)
                return
            if module in visiting:
                raise RuntimeError(f"Cyclic module dependency: {module}")
            visiting.add(module)
            for dependency in dependencies[module]:
                visit(dependency)
            visiting.remove(module)
            visited.add(module)
            order.append(module)

        for module in sorted(modules):
            visit(module)
        prefix = Path(subprocess.check_output([str(lean), "--print-prefix"], text=True).strip())
        manifest["standard_library_imports"] = {
            module: {"path": str(path), "sha256": digest(path)}
            for module in sorted(external)
            for path in [prefix / "lib" / "lean" / (module.replace(".", "/") + ".olean")]
        }
        manifest["module_order"] = order
        record()
        shutil.copytree(source, native, dirs_exist_ok=True)
        environment = os.environ.copy()
        environment["LEAN_PATH"] = str(native)
        start = time.monotonic()
        for module in order:
            relative = module.replace(".", "/")
            log = run / "logs" / f"{module}.log"
            command = ["/usr/bin/time", "-v", "timeout", str(options.timeout_seconds),
                       str(lean), "-j1", f"-M{options.memory_mib}", "--root", str(native), "-o", str(native / f"{relative}.olean"),
                       str(native / f"{relative}.lean")]
            peak_rss = 0
            memory_exceeded = False
            with log.open("w") as stream:
                process = subprocess.Popen(command, cwd=native, env=environment, stdout=stream,
                                           stderr=subprocess.STDOUT, start_new_session=True)
                while process.poll() is None:
                    peak_rss = max(peak_rss, process_tree_rss(process.pid))
                    if peak_rss > options.memory_mib * 1024:
                        memory_exceeded = True
                        os.killpg(process.pid, signal.SIGKILL)
                        break
                    time.sleep(0.05)
                return_code = process.wait()
            manifest["module_resources"][module] = {
                "sampled_process_tree_peak_rss_kib": peak_rss,
                "memory_limit_exceeded": memory_exceeded,
                "command": command,
            }
            if return_code or memory_exceeded:
                manifest.update(failed_module=module, exit_code=return_code)
                raise RuntimeError(f"Compilation failed: {module}; see {log}")
            output = log.read_text()
            maximum_rss = re.search(r"Maximum resident set size \(kbytes\):\s*(\d+)", output)
            if maximum_rss is None:
                raise RuntimeError(f"Missing GNU time memory measurement for {module}")
            measured_rss = int(maximum_rss.group(1))
            manifest["module_resources"][module]["gnu_time_maximum_rss_kib"] = measured_rss
            if measured_rss > options.memory_mib * 1024:
                raise RuntimeError(f"Measured RSS exceeds the limit for {module}: {measured_rss} KiB")
            if "sorryAx" in output:
                raise RuntimeError(f"Unexpected sorryAx in {module}")
            audits = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output, re.S)
            audits += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", output)]
            for name, raw in audits:
                axioms = sorted({item.strip() for item in raw.split(",") if item.strip()})
                unexpected = set(axioms) - {"propext", "Classical.choice", "Quot.sound"}
                if unexpected:
                    raise RuntimeError(f"Unexpected assumptions for {name}: {unexpected}")
                manifest["axiom_audits"].append({"declaration": name, "axioms": axioms, "module": module})
            manifest["completed_modules"].append(module)
            record()
        if len(manifest["axiom_audits"]) != audit_count:
            raise RuntimeError("Printed axiom-audit count differs from source commands")
        for relative, expected_hash in manifest["source_sha256"].items():
            if digest(source / relative) != expected_hash or digest(native / relative) != expected_hash:
                raise RuntimeError(f"Snapshot source changed: {relative}")
        manifest["build_output_sha256"] = {str(path.relative_to(native)): digest(path)
                                           for path in sorted(native.rglob("*.olean"))}
        manifest.update(status="passed", elapsed_seconds=round(time.monotonic() - start, 3))
        record()
        print(json.dumps({"status": "passed", "modules": len(order),
                          "audits": audit_count, "run": str(run)}), flush=True)
        return 0
    except Exception as error:
        manifest.update(status="failed", error=str(error))
        record()
        print(str(error), flush=True)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
