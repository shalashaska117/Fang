#!/usr/bin/env python3
"""Rebuild original-byte instance proofs on native storage under one resource gate.

Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import re
import shutil
import signal
import subprocess
import sys
import tempfile
import threading
import time

from axiom_audit import audit_axioms
import source_witness
from replay_storage_probe import copy_checked, sha


def process_tree_rss(pid):
    """Sum resident pages for the driver and its current descendants (KiB)."""
    try:
        status = Path(f"/proc/{pid}/status").read_text()
        match = re.search(r"^VmRSS:\s+(\d+)\s+kB$", status, re.M)
        own = int(match.group(1)) if match else 0
        children = Path(f"/proc/{pid}/task/{pid}/children").read_text().split()
        return own + sum(process_tree_rss(int(child)) for child in children)
    except (FileNotFoundError, ProcessLookupError):
        return 0


def read_timing(path):
    """GNU time may be killed with its child before it writes any record."""
    if not path.exists():
        return None, "missing"
    lines = path.read_text().splitlines()
    if not lines:
        return None, "empty"
    for line in reversed(lines):
        if re.fullmatch(r"[0-9]+(?:\.[0-9]+)? [0-9]+", line.strip()):
            return int(line.split()[1]), "recorded"
    return None, "malformed"


def run_phase(command, folder, label, deadline, environment, required=(), memory_limit_kib=2097152):
    timing = folder / (label + ".time")
    command = ["/usr/bin/time", "-f", "%e %M", "-o", str(timing)] + command
    started = time.monotonic()
    remaining = deadline - started
    if remaining <= 0:
        return {"label": label, "passed": False, "timeout": True, "not_started": True,
                "classification": "timeout", "timing_status": "not-started"}
    process = subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True, start_new_session=True, env=environment)
    monitor_done = threading.Event()
    sampled = {"peak": process_tree_rss(os.getpid()), "exceeded": False}

    def kill_group():
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass

    def monitor():
        while not monitor_done.wait(0.02):
            sampled["peak"] = max(sampled["peak"], process_tree_rss(os.getpid()))
            if sampled["peak"] > memory_limit_kib:
                sampled["exceeded"] = True
                kill_group()
                return

    watcher = threading.Thread(target=monitor, daemon=True)
    watcher.start()
    timed_out = False
    try:
        stdout, stderr = process.communicate(timeout=remaining)
    except subprocess.TimeoutExpired:
        timed_out = True
        kill_group()
        stdout, stderr = process.communicate()
    finally:
        monitor_done.set()
        watcher.join()
    (folder / (label + ".stdout")).write_text(stdout)
    (folder / (label + ".stderr")).write_text(stderr)
    peak, timing_status = read_timing(timing)
    reports, error = {}, None
    if required:
        try:
            reports = audit_axioms(stdout, required)
        except ValueError as exception:
            error = str(exception)
    if sampled["exceeded"] or (peak is not None and peak > memory_limit_kib):
        classification = "memory-limit"
    elif timed_out:
        classification = "timeout"
    elif process.returncode != 0:
        classification = "process-failure"
    elif error is not None:
        classification = "audit-failure"
    elif peak is None:
        classification = "missing-timing"
    else:
        classification = "passed"
    return {"label": label, "command": command, "elapsed_seconds": time.monotonic() - started,
        "exit_code": process.returncode, "timeout": timed_out, "peak_rss_kib": peak,
        "timing_status": timing_status, "classification": classification,
        "sampled_driver_and_process_tree_peak_rss_kib": sampled["peak"],
        "memory_limit_exceeded": sampled["exceeded"], "memory_limit_kib": memory_limit_kib,
        "axiom_reports": reports, "audit_error": error,
        "passed": classification == "passed"}


def main():
    cli = argparse.ArgumentParser()
    cli.add_argument("--corpus", required=True, type=Path)
    cli.add_argument("--out", required=True, type=Path)
    cli.add_argument("--lean", required=True)
    cli.add_argument("--checker", required=True, type=Path)
    cli.add_argument("--cases", nargs="+")
    cli.add_argument("--decompose-all", action="store_true",
                     help="Use kernel-checked decoder decomposition for every selected case")
    args = cli.parse_args()
    root = Path(__file__).resolve().parents[2]
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=False)
    native = Path(tempfile.mkdtemp(prefix="fang-native-source-replay-", dir="/var/tmp"))
    source_manifest = json.loads((args.corpus / "manifest.json").read_text())
    corpus = {row["id"]: row for row in source_manifest["records"]
              if row["kind"] in ("accepted-refutation", "corpus-replay")}
    ids = args.cases if args.cases else list(corpus)
    manifest = {
        "scope": "Fresh decoder, original-byte witness and fixed linking kernel proofs",
        "general_parser_correctness": "Separate proof suite; this campaign checks per-instance grammar witnesses",
        "limits": {"aggregate_seconds_per_instance": 60, "peak_rss_kib": 2097152},
        "lean_threads": 1,
        "decoder_decomposition": "all-selected-cases" if args.decompose_all else "original-replay-failures",
        "memory_measurement": "Maximum of GNU time child peak, driver high-water RSS and summed driver/process-tree RSS sampled every 20 ms. The sampler kills the child process group above 2 GiB; brief peaks between samples can escape it. Shared pages are counted for each process.",
        "native_staging": str(native), "completed": False, "records": [],
        "corpus_manifest_sha256": sha(args.corpus / "manifest.json"),
        "lean_version": subprocess.check_output([args.lean, "--version"], text=True).strip(),
        "lean_executable_sha256": sha(Path(args.lean)),
        "sources": {path.name: sha(path) for path in (Path(__file__), Path(source_witness.__file__),
            Path(__file__).with_name("axiom_audit.py"), Path(__file__).with_name("replay_storage_probe.py"),
            Path(__file__).with_name("decomposed_replay_probe.py"))},
        "timing_boundary": "Starts before per-instance file copy and embedding; includes export, witness generation, decomposition, every instance compilation and fixed linking audit. Shared artifacts and executable staged once; evidence archival follows timing.",
    }
    runner_sources = output / "runner-sources"
    runner_sources.mkdir()
    for filename, expected in manifest["sources"].items():
        source = Path(__file__).with_name(filename)
        actual = copy_checked(source, runner_sources / filename)
        if actual != expected:
            raise ValueError(f"Runner source changed during snapshot: {filename}")
    manifest["runner_source_snapshot"] = str(runner_sources)
    setup_start = time.monotonic()
    shared = root / "lean/.lake/build/lib/lean"
    manifest["shared_olean_sha256"] = {
        str(path.relative_to(shared)): copy_checked(path, native / "shared" / path.relative_to(shared))
        for path in sorted(shared.rglob("*.olean"))
    }
    manifest["checker_sha256"] = copy_checked(args.checker, native / "fang-check")
    (native / "fang-check").chmod(0o700)
    manifest["setup_staging_seconds"] = time.monotonic() - setup_start
    manifest["shared_compilation"] = "Reuses pinned shared libraries; original build costs are recorded in the source-witness and decoder campaigns, separately from instance timings. No instance .olean is reused."

    def save():
        manifest["failures"] = [row["id"] for row in manifest["records"] if not row["passed"]]
        manifest["distinct_source_bytes"] = len({row["input_sha256"] for row in manifest["records"]})
        (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")

    run = run_phase

    for name in ids:
        original = corpus[name]
        case = native / name
        case.mkdir()
        started = time.monotonic()
        deadline = started + 60
        record = {"id": name, "phases": [], "passed": False}
        env = os.environ | {"LEAN_PATH": f"{case}:{native / 'shared'}"}
        for filename, field, original_key in (("input.p", "input_sha256", "input_sha256"),
            ("proof.fang", "certificate_sha256", "proof_sha256")):
            record[field] = copy_checked(args.corpus / name / filename, case / filename)
            if record[field] != original[original_key]:
                raise ValueError(f"Original corpus hash mismatch: {name}/{filename}")
        record["phases"].append(run([str(native / "fang-check"), "--emit-replay", str(case / "input.p"),
            str(case / "proof.fang")], case, "export", deadline, env))
        if record["phases"][-1]["passed"]:
            shutil.copyfile(case / "export.stdout", case / "Replay.lean")
            (case / "Source.lean").write_text(source_witness.generate(case), encoding="utf-8")
            recovered = args.decompose_all or original.get("replay", {}).get("status") != "passed"
            if recovered:
                record["phases"].append(run([sys.executable, str(runner_sources / "decomposed_replay_probe.py"),
                    str(case / "Replay.lean"), "--out", str(case / "decomposed"), "--lake", args.lean,
                    "--grouped", "--full", "--emit-only"], case, "decompose", deadline, env))
                if record["phases"][-1]["passed"]:
                    modules = json.loads((case / "decomposed/emitted.json").read_text())["modules"]
                    for module in modules:
                        shutil.copyfile(case / "decomposed" / (module + ".lean"), case / (module + ".lean"))
                else:
                    modules = []
                replay_module = "CompleteReplay"
            else:
                modules, replay_module = ["Replay"], "Replay"
            if all(phase["passed"] for phase in record["phases"]):
                for module in ["Source"] + modules:
                    phase = run([args.lean, "-j1", "-M", "2048", "--root", str(case), "-o",
                        str(case / (module + ".olean")), str(case / (module + ".lean"))],
                        case, module, deadline, env)
                    record["phases"].append(phase)
                    if not phase["passed"]:
                        break
            if all(phase["passed"] for phase in record["phases"]):
                source = (case / "input.p").read_bytes()
                proof = (case / "proof.fang").read_bytes()
                link = ("import Source\nimport " + replay_module + "\n\n"
                    "set_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n\n"
                    "theorem exact_original_bytes_unsat : ¬ Fang.Source.Grammar.BytesSatisfiable "
                    + source_witness.lean_list([str(byte) for byte in source])
                    + " := Fang.SourceInstance.original_input_unsat\n\n"
                    "theorem exact_source_decodes : Fang.decodeProblem " + source_witness.quote(source.decode("ascii"))
                    + " = .ok Fang.SourceInstance.problem := Fang.InstanceReplay.source_decodes\n\n"
                    "theorem exact_certificate_decodes : Fang.decodeCertificate " + source_witness.quote(proof.decode("ascii"))
                    + " = .ok Fang.SourceInstance.certificate := Fang.InstanceReplay.certificate_decodes\n\n"
                    "#print axioms exact_original_bytes_unsat\n#print axioms exact_source_decodes\n"
                    "#print axioms exact_certificate_decodes\n")
                (case / "Link.lean").write_text(link, encoding="utf-8")
                record["phases"].append(run([args.lean, "-j1", "-M", "2048", "--root", str(case), "-o",
                    str(case / "Link.olean"), str(case / "Link.lean")], case, "Link", deadline, env,
                    ["exact_original_bytes_unsat", "exact_source_decodes", "exact_certificate_decodes"]))
        record["aggregate_seconds"] = time.monotonic() - started
        record["driver_peak_rss_kib"] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
        record["peak_rss_kib"] = max(record["driver_peak_rss_kib"],
            max((max(phase.get("peak_rss_kib") or 0,
                     phase.get("sampled_driver_and_process_tree_peak_rss_kib") or 0)
                 for phase in record["phases"]), default=0))
        record["passed"] = record["aggregate_seconds"] <= 60 and all(phase["passed"] for phase in record["phases"]) \
            and record["phases"][-1]["label"] == "Link" and record["peak_rss_kib"] <= 2097152
        evidence = output / name
        evidence.mkdir()
        for path in sorted(case.iterdir()):
            if path.is_file() and path.suffix != ".olean":
                copy_checked(path, evidence / path.name)
        record["proof_source_sha256"] = {path.name: sha(path) for path in sorted(case.glob("*.lean"))}
        record["generated_olean_sha256"] = {path.name: sha(path) for path in sorted(case.glob("*.olean"))}
        manifest["records"].append(record)
        save()
        print(json.dumps({key: record[key] for key in ("id", "passed", "aggregate_seconds", "peak_rss_kib")}), flush=True)
    manifest["completed"] = True
    save()
    raise SystemExit(bool(manifest["failures"]))


if __name__ == "__main__":
    main()
