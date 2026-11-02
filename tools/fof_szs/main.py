#!/usr/bin/env python3
"""Bounded ground-FOF search/check adapter with an optional pinned TSTP exporter."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
from dataclasses import asdict
from pathlib import Path
import sys
import time

sys.dont_write_bytecode = True
import capability
import protocol
sys.path.insert(0, str(capability.ROOT / "tools"))
from fang_szs.app import emit_status, terminal_checkpoint
from fang_szs import cli
from fang_szs.supervisor import EXIT, Failure, Limits, Snapshot, Supervisor, read_regular, write_json
from fang_szs.tstp import read_solution, solution_output
import fof_tstp


def arguments(argv, *, public=False):
    return cli.arguments(argv, public=public, capability_bytes=capability.MAX_BYTES)


def pipeline(args, supervisor, manifest, root):
    raw_config = read_regular(args.capability, 32 << 20, supervisor.check)
    config = capability.strict_json(raw_config.decode("utf-8"))
    capability.verify(config, supervisor.check)
    if args.check not in config["profiles"]:
        raise Failure("Inappropriate", "Requested checking profile is not installed; no fallback was performed", "capability")
    if args.output not in config["outputs"]:
        raise Failure("Inappropriate", "Requested output capability is not installed", "capability")
    (root / "capability.json").write_bytes(raw_config)
    manifest["capability_sha256"] = __import__("hashlib").sha256(raw_config).hexdigest()
    manifest["capability"] = config
    source = Snapshot(root / "input.p", read_regular(args.input, args.max_input_bytes, supervisor.check))
    certificate = None
    manifest["input"] = {"bytes": len(source.data), "sha256": source.sha256,
                         "identity": "sealed memfd and retained disk bytes"}
    manifest["problem_id"] = "fang_" + source.sha256[:24]
    try:
        supervisor.memory()
        candidate = root / "search/candidate.fang"
        command = [config["engine"]["path"], source.argument, "--proof", str(candidate),
            "--max-steps", str(args.max_steps), "--max-clauses", str(args.max_clauses),
            "--max-operations", str(args.max_operations)]
        process, stdout, stderr = supervisor.run("search", command, root / "search", root, (source.fd,))
        source.verify(supervisor.check)
        status, reason = protocol.engine_outcome(process, stdout, stderr, source.data)
        if status != "candidate":
            if candidate.exists() or candidate.is_symlink():
                raise Failure("Error", "Noncandidate driver left a certificate", "search")
            return status, reason
        certificate = Snapshot(root / "proof.fang", read_regular(candidate, args.max_certificate_bytes, supervisor.check))
        manifest["certificate"] = {"bytes": len(certificate.data), "sha256": certificate.sha256,
                                   "version": 2, "preprocessing": "ground-fof-distributive-v1"}
        process, stdout, stderr = supervisor.run("checker", [config["checker"]["path"],
            source.argument, certificate.argument], root / "checker", root, (source.fd, certificate.fd))
        protocol.checker_acceptance(process, stdout, stderr)
        manifest["compiled_check"] = {"accepted": True, "kernel_instance": False,
            "scope": "Pinned original-byte v2 checker execution; compilation/runtime trusted"}
        if args.check == "kernel":
            import kernel_replay
            manifest["kernel_storage"] = {}
            manifest["kernel_check"] = kernel_replay.verify(supervisor, config, root, source,
                                                           certificate, manifest["kernel_storage"])
        if args.output == "tstp":
            manifest["solution"] = fof_tstp.export_solution(supervisor, config, root, source,
                                                           certificate, args.max_solution_bytes)
        source.verify(supervisor.check)
        certificate.verify(supervisor.check)
        if read_regular(candidate, args.max_certificate_bytes, supervisor.check) != certificate.data:
            raise Failure("Error", "Candidate certificate changed after capture", "checker")
        capability.verify(config, supervisor.check)
        supervisor.tree_bytes(root)
        supervisor.check("checked")
        reason = ("Fresh exact-byte Lean kernel replay accepted the captured version-2 pair" if args.check == "kernel"
                  else "Compiled original-byte version-2 checker accepted the captured pair")
        return "Unsatisfiable", reason
    finally:
        if certificate is not None:
            certificate.close()
        source.close()


def output_bytes(manifest, status, solution=b""):
    boundary = "fresh exact-byte kernel replay required" if manifest["profile"] == "kernel" else "compilation/runtime trusted"
    data = (f"% Fang experimental ground-FOF profile: {manifest['profile']}; {boundary}\n"
            f"% SZS status {status} for {manifest['problem_id']}\n").encode("ascii")
    if status == "Unsatisfiable" and manifest["output"] == "tstp":
        data += solution_output(solution, manifest["problem_id"])
    return data


def main(argv=None, *, public=False):
    started = time.monotonic()
    supervisor, root = None, None
    owns_run = False
    solution = b""
    manifest = {"schema": "fang-ground-fof-run-v1", "state": "starting", "profile": "kernel",
        "output": "status", "problem_id": "fang_unavailable", "language": capability.LANGUAGE,
        "scope": "Ground-FOF original-byte UNSAT with optional compiled TSTP output; no SAT or search-completeness claim"}
    try:
        args = arguments(argv, public=public)
        manifest.update(profile=args.check, output=args.output)
        if sys.platform != "linux":
            raise Failure("Error", "This adapter requires Linux/WSL")
        limits = Limits(args.wall_seconds, args.memory_mib, args.max_input_bytes,
                        args.max_certificate_bytes, args.max_log_bytes, args.max_artifact_bytes)
        supervisor = Supervisor(limits, started)
        root = args.artifacts.absolute()
        root.mkdir(mode=0o700, parents=True)
        owns_run = True
        manifest.update(state="running", limits=asdict(limits),
            engine_limits={name: getattr(args, name) for name in ("max_steps", "max_clauses", "max_operations")},
            resource_method="One total monotonic deadline; 20ms sampled adapter/owned-descendant RSS, not address-space enforcement",
            kernel_gate="Default kernel requires an explicit v2 capability; no fallback")
        write_json(root / "manifest.json", manifest)
        cli.announce_artifacts(args, root, supervisor, emit_status)
        status, reason = pipeline(args, supervisor, manifest, root)
        if status == "Unsatisfiable" and args.output == "tstp":
            solution = read_solution(root, manifest["solution"], supervisor.check)
        supervisor.check()
        stage = "complete"
    except Failure as error:
        status, reason, stage = error.status, error.reason, error.stage
    except Exception as error:
        status, reason, stage = "Error", str(error), "adapter"
    manifest.update(state="finished", status=status, exit_code=EXIT[status], reason=reason, stage=stage,
        elapsed_before_status_seconds=time.monotonic() - started,
        processes=supervisor.records if supervisor else [],
        peak_adapter_tree_rss_kib=supervisor.peak_kib if supervisor else None,
        output_delivery={"state": "pending", "closing_marker_delivered": False})
    if supervisor is not None and status == "Unsatisfiable":
        try:
            supervisor.memory()
            supervisor.check("output-preparation")
        except Failure as error:
            status = error.status
            manifest.update(status=status, exit_code=EXIT[status], reason=error.reason, stage=error.stage)
    if owns_run:
        status = terminal_checkpoint(root / "manifest.json", manifest, supervisor)
    output = output_bytes(manifest, status, solution)
    try:
        deadline = supervisor.deadline if supervisor and status == "Unsatisfiable" else time.monotonic() + 0.15
        cancelled = (lambda: supervisor.cancelled) if supervisor and status == "Unsatisfiable" else None
        if not emit_status(output, deadline, cancelled=cancelled):
            raise Failure("Timeout", "Caller did not accept status before deadline", "status-output")
        manifest["output_delivery"] = {"state": "written", "bytes": len(output),
            "sha256": __import__("hashlib").sha256(output).hexdigest(),
            "closing_marker_delivered": status == "Unsatisfiable" and manifest["output"] == "tstp",
            "scope": "Written to caller descriptor; downstream consumption is not acknowledged"}
    except Failure as error:
        status = error.status
        manifest.update(status=status, exit_code=EXIT[status], reason=error.reason, stage=error.stage)
        manifest["output_delivery"]["state"] = "incomplete"
    except OSError as error:
        status = "Error"
        manifest.update(status=status, exit_code=EXIT[status], reason=str(error), stage="status-output")
        manifest["output_delivery"]["state"] = "incomplete"
    if owns_run:
        status = terminal_checkpoint(root / "manifest.json", manifest,
                                     supervisor if status == "Unsatisfiable" else None)
    if supervisor:
        supervisor.close()
    return EXIT[status]


if __name__ == "__main__":
    raise SystemExit(main())
