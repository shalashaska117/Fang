#!/usr/bin/env python3
"""Check original-byte refutations through the general source soundness theorem.

Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
"""
import argparse
import json
import os
from pathlib import Path
import resource
import shutil
import subprocess
import sys
import tempfile
import time

from native_source_replay import run_phase
from replay_storage_probe import copy_checked, sha
from source_witness import quote


def fixed_audit(module, source, certificate):
    """Only fixed theorem templates and independently read literal bytes enter the audit."""
    if module not in ("Replay", "CompleteReplay"):
        raise ValueError("Unexpected replay module")
    byte_list = "[" + ", ".join(map(str, source)) + "]"
    source_literal = quote(source.decode("ascii"))
    certificate_literal = quote(certificate.decode("ascii"))
    source_characters = "[" + ", ".join(repr(chr(byte)) for byte in source) + "]"
    return (
        f"import {module}\nimport Fang.SourceAscii\n\n"
        "set_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n\n"
        "theorem exact_input_value : Fang.InstanceReplay.originalInput = " + source_literal
        + " := by rfl\n\n"
        "theorem exact_certificate_value : Fang.InstanceReplay.originalCertificate = " + certificate_literal
        + " := by rfl\n\n"
        "theorem exact_input_bytes : Fang.Source.Grammar.spelling " + source_literal + " = "
        + byte_list + " := by\n"
        "  change Fang.Source.Grammar.spelling (String.ofList " + source_characters + ") = _\n"
        "  rw [Fang.Source.Grammar.spelling_ofList_ascii _ (by decide +kernel)]\n"
        "  rfl\n\n"
        "theorem exact_original_bytes_unsat : ¬ Fang.Source.Grammar.BytesSatisfiable "
        + byte_list + " := by\n"
        "  have proved : ¬ Fang.Source.Grammar.BytesSatisfiable\n"
        "      (Fang.Source.Grammar.spelling Fang.InstanceReplay.originalInput) :=\n"
        "    Fang.InstanceReplay.original_input_unsat\n"
        "  simpa only [exact_input_value, exact_input_bytes] using proved\n\n"
        "theorem exact_source_decodes : Fang.decodeProblem " + source_literal
        + " = .ok Fang.InstanceReplay.problem := by\n"
        "  rw [← exact_input_value]\n  exact Fang.InstanceReplay.source_decodes\n\n"
        "theorem exact_certificate_decodes : Fang.decodeCertificate " + certificate_literal
        + " = .ok Fang.InstanceReplay.certificate := by\n"
        "  rw [← exact_certificate_value]\n  exact Fang.InstanceReplay.certificate_decodes\n\n"
        "theorem exact_checker_acceptance : Fang.check (Fang.preprocess Fang.InstanceReplay.problem) "
        "Fang.InstanceReplay.certificate = true := Fang.InstanceReplay.accepted\n\n"
        "#print axioms exact_original_bytes_unsat\n#print axioms exact_source_decodes\n"
        "#print axioms exact_certificate_decodes\n#print axioms exact_checker_acceptance\n"
    )


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--corpus", required=True, type=Path)
    cli.add_argument("--proof-suite", required=True, type=Path)
    cli.add_argument("--out", required=True, type=Path)
    cli.add_argument("--lean", required=True, type=Path)
    cli.add_argument("--cases", nargs="+")
    cli.add_argument("--monolithic", action="store_true")
    args = cli.parse_args()
    root = Path(__file__).resolve().parents[2]
    output = args.out.resolve()
    output.mkdir(parents=True, exist_ok=False)
    native = Path(tempfile.mkdtemp(prefix="fang-generic-source-replay-", dir="/var/tmp"))
    suite = json.loads(args.proof_suite.read_text())
    if suite["status"] != "passed" or "Fang.FrontendSoundness" not in suite["completed_modules"]:
        raise ValueError("A completed source-soundness suite is required")
    if sha(args.lean) != suite["lean_executable_sha256"]:
        raise ValueError("Lean executable differs from the checked suite")
    corpus_manifest = json.loads((args.corpus / "manifest.json").read_text())
    corpus = {row["id"]: row for row in corpus_manifest["records"]
              if row["kind"] in ("accepted-refutation", "corpus-replay")}
    ids = args.cases if args.cases else list(corpus)
    if any(name not in corpus or not name.replace("-", "").replace("_", "").isalnum() for name in ids):
        raise ValueError("Unknown or invalid corpus case ID")
    manifest = {
        "scope": "Original-byte UNSAT via general Lean decoder soundness, exact decoder computations and checker acceptance",
        "source_acceptance_completeness": (
            "Fang.FrontendComplete is included in the selected shared proof suite; this replay uses successful-decoding soundness"
            if "Fang.FrontendComplete" in suite["completed_modules"] else
            "Not included in the selected shared proof suite; this replay uses successful-decoding soundness"
        ),
        "compiled_execution": "Exporter and compiler execution remain distinct from the resulting kernel proof",
        "limits": {"aggregate_seconds_per_instance": 60, "peak_rss_kib": 2097152},
        "lean_threads": 1, "completed": False, "records": [],
        "native_staging": str(native), "proof_suite": str(args.proof_suite.resolve()),
        "proof_suite_sha256": sha(args.proof_suite), "shared_proof_build_seconds": suite["elapsed_seconds"],
        "corpus_manifest_sha256": sha(args.corpus / "manifest.json"),
        "lean_executable_sha256": sha(args.lean), "lean_version": suite["lean_version"],
        "decoder_decomposition": "monolithic" if args.monolithic else "all-selected-cases",
        "timing_boundary": "Starts before each input/certificate copy; includes export, decomposition, every instance compilation and fixed audit. Shared library staging and exporter build are separate. Evidence archival follows instance timing.",
        "memory_measurement": "Maximum of GNU time process RSS, driver high-water RSS and summed driver/process-tree RSS sampled every 20 ms. The sampler kills the child group above 2 GiB; brief peaks between samples can escape it. Shared pages are counted per process.",
    }
    runners = output / "runner-sources"
    runners.mkdir()
    names = (Path(__file__).name, "native_source_replay.py", "axiom_audit.py", "replay_storage_probe.py",
             "source_witness.py", "decomposed_replay_probe.py")
    manifest["runner_sha256"] = {name: copy_checked(Path(__file__).with_name(name), runners / name) for name in names}
    setup = time.monotonic()
    checked_root = Path(suite["native_project"])
    manifest["shared_olean_sha256"] = {}
    for relative, expected in suite["build_output_sha256"].items():
        if not relative.endswith(".olean"):
            continue
        actual = copy_checked(checked_root / relative, native / "shared" / relative)
        if actual != expected:
            raise ValueError(f"Checked library changed: {relative}")
        manifest["shared_olean_sha256"][relative] = actual
    manifest["shared_staging_seconds"] = time.monotonic() - setup

    # Build the current fixed exporter from a frozen minimal source snapshot.
    builder = native / "exporter"
    builder.mkdir()
    exporter_sources = ["Main.lean", "lakefile.toml", "lean-toolchain"] + [f"Fang/{name}.lean" for name in
        ("Logic", "Input", "Checker", "CertificateInput", "Replay", "BoundedInput")]
    source_archive = output / "exporter-source"
    manifest["exporter_source_sha256"] = {}
    for relative in exporter_sources:
        actual = copy_checked(root / "lean" / relative, builder / relative)
        if relative.endswith(".lean") and relative not in ("Main.lean", "Fang/Replay.lean"):
            if actual != suite["source_sha256"][relative]:
                raise ValueError(f"Exporter dependency differs from soundness suite: {relative}")
        copy_checked(builder / relative, source_archive / relative)
        manifest["exporter_source_sha256"][relative] = actual
    env = os.environ | {"PATH": str(args.lean.parent) + ":" + os.environ["PATH"], "LEAN_NUM_THREADS": "1"}
    build_start = time.monotonic()
    build = subprocess.run([str(args.lean.with_name("lake")), "build", "fang-check"], cwd=builder,
                           env=env, capture_output=True, timeout=120)
    (output / "exporter-build.stdout").write_bytes(build.stdout)
    (output / "exporter-build.stderr").write_bytes(build.stderr)
    manifest["exporter_build_seconds"] = time.monotonic() - build_start
    manifest["exporter_build_exit_code"] = build.returncode
    if build.returncode:
        (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
        raise RuntimeError("Exporter build failed")
    checker = builder / ".lake/build/bin/fang-check"
    manifest["exporter_sha256"] = copy_checked(checker, output / "fang-check")

    def save():
        manifest["failures"] = [row["id"] for row in manifest["records"] if not row["passed"]]
        manifest["distinct_source_bytes"] = len({row["input_sha256"] for row in manifest["records"]})
        (output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")

    save()
    for name in ids:
        original = corpus[name]
        case = native / name
        case.mkdir()
        start = time.monotonic()
        deadline = start + 60
        record = {"id": name, "phases": [], "passed": False}
        environment = env | {"LEAN_PATH": f"{case}:{native / 'shared'}"}
        for filename, field, original_key in (("input.p", "input_sha256", "input_sha256"),
            ("proof.fang", "certificate_sha256", "proof_sha256")):
            record[field] = copy_checked(args.corpus / name / filename, case / filename)
            if record[field] != original[original_key]:
                raise ValueError(f"Corpus hash mismatch: {name}/{filename}")
        phases = record["phases"]
        phases.append(run_phase([str(checker), "--emit-replay", str(case / "input.p"), str(case / "proof.fang")],
                                case, "export", deadline, environment))
        if phases[-1]["passed"]:
            shutil.copyfile(case / "export.stdout", case / "Replay.lean")
            if args.monolithic:
                modules, final_module = ["Replay"], "Replay"
            else:
                phases.append(run_phase([sys.executable, str(runners / "decomposed_replay_probe.py"),
                    str(case / "Replay.lean"), "--out", str(case / "decomposed"), "--lake", str(args.lean),
                    "--grouped", "--full", "--emit-only"], case, "decompose", deadline, environment))
                modules = json.loads((case / "decomposed/emitted.json").read_text())["modules"] if phases[-1]["passed"] else []
                for module in modules:
                    if not module.isalnum():
                        raise ValueError("Invalid generated module name")
                    shutil.copyfile(case / "decomposed" / (module + ".lean"), case / (module + ".lean"))
                final_module = "CompleteReplay"
            if all(phase["passed"] for phase in phases):
                for module in modules:
                    phases.append(run_phase([str(args.lean), "-j1", "-M2048", "--root", str(case), "-o",
                        str(case / (module + ".olean")), str(case / (module + ".lean"))],
                        case, module, deadline, environment))
                    if not phases[-1]["passed"]:
                        break
            if all(phase["passed"] for phase in phases):
                audit = fixed_audit(final_module, (case / "input.p").read_bytes(), (case / "proof.fang").read_bytes())
                (case / "Audit.lean").write_text(audit, encoding="utf-8")
                phases.append(run_phase([str(args.lean), "-j1", "-M2048", "--root", str(case), "-o",
                    str(case / "Audit.olean"), str(case / "Audit.lean")], case, "Audit", deadline, environment,
                    ["exact_original_bytes_unsat", "exact_source_decodes", "exact_certificate_decodes", "exact_checker_acceptance"]))
        record["aggregate_seconds"] = time.monotonic() - start
        record["peak_rss_kib"] = max(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
            max((max(phase.get("peak_rss_kib") or 0, phase.get("sampled_driver_and_process_tree_peak_rss_kib") or 0)
                 for phase in phases), default=0))
        record["passed"] = record["aggregate_seconds"] <= 60 and record["peak_rss_kib"] <= 2097152 \
            and all(phase["passed"] for phase in phases) and phases[-1]["label"] == "Audit"
        record["proof_source_sha256"] = {path.name: sha(path) for path in sorted(case.glob("*.lean"))}
        record["generated_olean_sha256"] = {path.name: sha(path) for path in sorted(case.glob("*.olean"))}
        evidence = output / name
        evidence.mkdir()
        for path in sorted(case.iterdir()):
            if path.is_file() and path.suffix != ".olean":
                copy_checked(path, evidence / path.name)
        manifest["records"].append(record)
        save()
        print(json.dumps({key: record[key] for key in ("id", "passed", "aggregate_seconds", "peak_rss_kib")}), flush=True)
    manifest["completed"] = True
    save()
    return int(bool(manifest["failures"]))


if __name__ == "__main__":
    raise SystemExit(main())
