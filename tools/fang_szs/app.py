"""Local ATP command with explicit checking and bounded TSTP output."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import argparse
from dataclasses import asdict
import fcntl
import math
import os
from pathlib import Path
import resource
import select
import sys
import time
from . import kernel
from .installation import digest_file, verify_installation, verify_running_adapter
from .protocol import checker_acceptance, engine_outcome
from .tstp import export_solution, read_solution, solution_output
from .supervisor import EXIT, Failure, Limits, Snapshot, Supervisor, read_regular, strict_json, write_json


class Parser(argparse.ArgumentParser):
    def error(self, message):
        raise Failure("Error", "Invalid adapter arguments: " + message)


def arguments(argv):
    parser = Parser(description="Local Linux/WSL Fang CNF prover. Kernel replay is the default; no SAT result.")
    parser.add_argument("input", type=Path)
    parser.add_argument("--installation", required=True, type=Path)
    parser.add_argument("--artifacts", required=True, type=Path)
    parser.add_argument("--check", choices=("kernel", "compiled"), default="kernel")
    parser.add_argument("--output", choices=("status", "tstp"), default="status")
    parser.add_argument("--max-solution-bytes", type=int, default=16 << 20)
    parser.add_argument("--wall-seconds", type=float, default=60)
    parser.add_argument("--memory-mib", type=int, default=2048)
    parser.add_argument("--max-steps", type=int, default=100_000)
    parser.add_argument("--max-clauses", type=int, default=1_000)
    parser.add_argument("--max-operations", type=int, default=5_000_000)
    parser.add_argument("--max-input-bytes", type=int, default=1 << 20)
    parser.add_argument("--max-certificate-bytes", type=int, default=64 << 20)
    parser.add_argument("--max-log-bytes", type=int, default=4 << 20)
    parser.add_argument("--max-artifact-bytes", type=int, default=256 << 20)
    args = parser.parse_args(argv)
    if not math.isfinite(args.wall_seconds) or not 0.25 <= args.wall_seconds <= 86400:
        parser.error("wall-seconds must be finite and between 0.25 and 86400")
    if not 16 <= args.memory_mib <= 1 << 20:
        parser.error("memory-mib must be between 16 and 1048576")
    for name in ("max_steps", "max_clauses", "max_operations", "max_input_bytes", "max_certificate_bytes", "max_log_bytes", "max_artifact_bytes"):
        value = getattr(args, name)
        if not 0 <= value <= (1 << 63) - 1:
            parser.error(name + " is outside the supported nonnegative range")
    if not 0 <= args.max_solution_bytes <= 16 << 20:
        parser.error("max-solution-bytes must be between 0 and 16777216")
    return args


def run_pipeline(args, supervisor, manifest, run_root):
    check = supervisor.check
    installation_bytes = read_regular(args.installation, 32 << 20, check)
    config = strict_json(installation_bytes.decode("utf-8"))
    verify_installation(config, check)
    verify_running_adapter(config, check)
    if args.output == "tstp" and "exporter" not in config:
        raise Failure("Error", "This installation has no pinned TSTP exporter")
    manifest["installation"] = config
    manifest["installation_sha256"] = __import__("hashlib").sha256(installation_bytes).hexdigest()
    (run_root / "installation.json").write_bytes(installation_bytes)
    source = Snapshot(run_root / "input.p", read_regular(args.input, supervisor.limits.input_bytes, check))
    certificate = None
    manifest["input"] = {"caller_path": str(args.input.absolute()), "bytes": len(source.data), "sha256": source.sha256,
        "child_identity": "Linux sealed memfd; disk copy retained and checked"}
    manifest["problem_id"] = "fang_" + source.sha256[:24]
    try:
        supervisor.memory()
        candidate_path = run_root / "search/candidate.fang"
        command = [config["engine"]["path"], source.argument, "--proof", str(candidate_path),
            "--max-steps", str(args.max_steps), "--max-clauses", str(args.max_clauses),
            "--max-operations", str(args.max_operations)]
        process, stdout, stderr = supervisor.run("search", command, run_root / "search", run_root, (source.fd,))
        source.verify(check)
        status, reason = engine_outcome(process, stdout, stderr, source.data)
        if status != "candidate":
            if candidate_path.exists() or candidate_path.is_symlink():
                raise Failure("Error", "Engine left a certificate for a noncandidate outcome", "search")
            return status, reason
        certificate = Snapshot(run_root / "proof.fang",
            read_regular(candidate_path, supervisor.limits.certificate_bytes, check))
        manifest["certificate"] = {"bytes": len(certificate.data), "sha256": certificate.sha256,
            "child_identity": "Linux sealed memfd; exact engine bytes retained"}
        process, stdout, stderr = supervisor.run("checker", [config["checker"]["path"],
            source.argument, certificate.argument], run_root / "checker", run_root, (source.fd, certificate.fd))
        checker_acceptance(process, stdout, stderr)
        source.verify(check)
        certificate.verify(check)
        if read_regular(candidate_path, supervisor.limits.certificate_bytes, check) != certificate.data:
            raise Failure("Error", "Engine certificate changed after capture", "checker")
        manifest["compiled_check"] = {"accepted": True, "kernel_instance": False}
        if args.check == "kernel":
            manifest["kernel_storage"] = {}
            manifest["kernel_check"] = kernel.verify(supervisor, config, run_root, source, certificate,
                manifest["kernel_storage"])
        if args.output == "tstp":
            manifest["solution"] = export_solution(supervisor, config, run_root, source,
                certificate, args.max_solution_bytes)
        verify_installation(config, check)
        verify_running_adapter(config, check)
        source.verify(check)
        certificate.verify(check)
        supervisor.tree_bytes(run_root)
        check()
        return "Unsatisfiable", "Selected checking profile accepted the exact captured problem"
    finally:
        if certificate is not None:
            certificate.close()
        source.close()


def terminal_checkpoint(path, manifest, supervisor):
    """An unsaved terminal record can never authorize positive output."""
    status = manifest["status"]
    try:
        write_json(path, manifest)
        if supervisor is not None and status == "Unsatisfiable":
            supervisor.check(reserve=0)
    except Failure as error:
        status = error.status
        manifest.update(status=status, exit_code=EXIT[status], reason=error.reason, stage="finalization")
        try:
            write_json(path, manifest)
        except (OSError, ValueError, TypeError) as retry_error:
            manifest["checkpoint_error"] = str(retry_error)
    except (OSError, ValueError, TypeError) as error:
        status = "Error"
        manifest.update(status=status, exit_code=EXIT[status], stage="finalization",
            reason="Could not save the terminal artifact record", checkpoint_error=str(error))
    return status


def emit_status(data, deadline, descriptor=1, cancelled=None):
    """Do not wait indefinitely for a caller that has stopped reading output."""
    flags = fcntl.fcntl(descriptor, fcntl.F_GETFL)
    try:
        fcntl.fcntl(descriptor, fcntl.F_SETFL, flags | os.O_NONBLOCK)
        remaining = memoryview(data)
        while remaining:
            if cancelled is not None and cancelled():
                raise Failure("Forced", "External cancellation", "status-output")
            budget = deadline - time.monotonic()
            if budget <= 0:
                return False
            if not select.select([], [descriptor], [], min(budget, 0.05))[1]:
                continue
            try:
                written = os.write(descriptor, remaining)
            except BlockingIOError:
                continue
            remaining = remaining[written:]
        return True
    finally:
        fcntl.fcntl(descriptor, fcntl.F_SETFL, flags)


def output_bytes(manifest, status, solution):
    data = (f"% Fang checking profile: {manifest['profile']}\n"
            f"% SZS status {status} for {manifest['problem_id']}\n").encode("ascii")
    if status == "Unsatisfiable" and manifest["output"] == "tstp":
        data += solution_output(solution, manifest["problem_id"])
    return data


def main(argv=None):
    started = time.monotonic()
    cpu_started = resource.getrusage(resource.RUSAGE_SELF)
    supervisor, run_root, args = None, None, None
    solution = b""
    manifest = {"schema": "fang-local-run-v2", "state": "starting", "problem_id": "fang_unavailable",
        "profile": "kernel", "output": "status",
        "scope": "Strict equality-free CNF; no SAT, calculus-completeness or whole-Rust proof claim"}
    try:
        args = arguments(argv)
        manifest["profile"] = args.check
        manifest["output"] = args.output
        manifest["max_solution_bytes"] = args.max_solution_bytes
        if sys.platform != "linux":
            raise Failure("Error", "This adapter requires Linux/WSL")
        limits = Limits(args.wall_seconds, args.memory_mib, args.max_input_bytes,
            args.max_certificate_bytes, args.max_log_bytes, args.max_artifact_bytes)
        supervisor = Supervisor(limits, started)
        run_root = args.artifacts.absolute()
        # A stale run is never overwritten, even when its manifest says failed.
        run_root.mkdir(mode=0o700, parents=True)
        manifest["limits"] = asdict(limits)
        manifest["engine_limits"] = {name: getattr(args, name) for name in ("max_steps", "max_clauses", "max_operations")}
        manifest["resource_method"] = "20ms sampled RSS sums adapter and owned descendants; may miss brief peaks. This is not an address-space cap. Whole monotonic deadline includes capture and selected checking. Cleanup/finalization costs are retained."
        manifest["adapter_source_sha256"] = {path.name: digest_file(path, supervisor.check)
            for path in sorted(Path(__file__).parent.glob("*.py"))}
        manifest["state"] = "running"
        write_json(run_root / "manifest.json", manifest)
        status, reason = run_pipeline(args, supervisor, manifest, run_root)
        if status == "Unsatisfiable" and args.output == "tstp":
            solution = read_solution(run_root, manifest["solution"], supervisor.check)
        supervisor.check()
        stage = "complete"
    except Failure as error:
        status, reason, stage = error.status, error.reason, error.stage
    except Exception as error:
        status, reason, stage = "Error", f"Adapter input, installation or I/O failure: {error}", "adapter"
    cpu_finished = resource.getrusage(resource.RUSAGE_SELF)
    manifest.update({"state": "finished", "status": status, "exit_code": EXIT[status], "reason": reason, "stage": stage,
        "elapsed_before_status_seconds": time.monotonic() - started,
        "adapter_user_seconds": cpu_finished.ru_utime - cpu_started.ru_utime,
        "adapter_system_seconds": cpu_finished.ru_stime - cpu_started.ru_stime,
        "children_user_seconds": sum(record.get("children_user_seconds", 0) for record in supervisor.records) if supervisor else 0,
        "children_system_seconds": sum(record.get("children_system_seconds", 0) for record in supervisor.records) if supervisor else 0,
        "processes": supervisor.records if supervisor else [],
        "peak_adapter_tree_rss_kib": supervisor.peak_kib if supervisor else None})
    manifest["output_delivery"] = {"state": "pending", "closing_marker_delivered": False}
    output = output_bytes(manifest, status, solution)
    if supervisor is not None and status == "Unsatisfiable":
        try:
            supervisor.memory()
            supervisor.check("output-preparation")
        except Failure as error:
            status = error.status
            manifest.update(status=status, exit_code=EXIT[status], reason=error.reason,
                stage="output-preparation")
            output = output_bytes(manifest, status, b"")
        manifest["peak_adapter_tree_rss_kib"] = supervisor.peak_kib
    # Stale directories are deliberately left untouched. Only a directory with
    # this invocation's initial manifest may receive the terminal checkpoint.
    owns_run = run_root is not None and "limits" in manifest
    if owns_run:
        saved_status = terminal_checkpoint(run_root / "manifest.json", manifest, supervisor)
        if saved_status != status:
            status = saved_status
            output = output_bytes(manifest, status, b"")
    try:
        deadline = supervisor.deadline if supervisor is not None and status == "Unsatisfiable" else time.monotonic() + 0.15
        cancelled = (lambda: supervisor.cancelled) if supervisor is not None and status == "Unsatisfiable" else None
        if not emit_status(output, deadline, cancelled=cancelled):
            manifest.update(status="Timeout", exit_code=EXIT["Timeout"], stage="status-output",
                reason="Caller did not accept final output before the deadline")
            manifest["output_delivery"]["state"] = "incomplete"
            if owns_run:
                terminal_checkpoint(run_root / "manifest.json", manifest, None)
            if supervisor is not None:
                supervisor.close()
            return EXIT["Timeout"]
    except Failure as error:
        manifest.update(status=error.status, exit_code=EXIT[error.status], stage=error.stage,
            reason=error.reason)
        manifest["output_delivery"]["state"] = "incomplete"
        if owns_run:
            terminal_checkpoint(run_root / "manifest.json", manifest, None)
        if supervisor is not None:
            supervisor.close()
        return EXIT[error.status]
    except (OSError, BrokenPipeError) as error:
        manifest.update(status="Error", exit_code=EXIT["Error"], stage="status-output",
            reason="Caller output failed: " + str(error))
        manifest["output_delivery"]["state"] = "incomplete"
        if owns_run:
            terminal_checkpoint(run_root / "manifest.json", manifest, None)
        if supervisor is not None:
            supervisor.close()
        return EXIT["Error"]
    manifest["output_delivery"] = {"state": "written", "bytes": len(output),
        "sha256": __import__("hashlib").sha256(output).hexdigest(),
        "closing_marker_delivered": status == "Unsatisfiable" and manifest["output"] == "tstp",
        "elapsed_seconds": time.monotonic() - started,
        "scope": "Written to the caller descriptor; downstream storage/consumption is not acknowledged"}
    if owns_run:
        status = terminal_checkpoint(run_root / "manifest.json", manifest, supervisor)
    if supervisor is not None:
        supervisor.close()
    return EXIT[status]
