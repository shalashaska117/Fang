"""Shared arguments for the installed command and explicit local adapters."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import argparse
import math
from pathlib import Path
import sys
import uuid

from .supervisor import Failure


class Parser(argparse.ArgumentParser):
    def error(self, message):
        raise Failure("Error", "Invalid adapter arguments: " + message)


def arguments(argv, *, public=False, capability_bytes=None):
    """Parse without creating files; preserve each adapter's existing limits."""
    fof = capability_bytes is not None
    scope = ("equality-free CNF and ground FOF axioms" if fof else "strict equality-free CNF")
    parser = Parser(prog="fang" if public else None,
        description=f"Fang theorem prover for {scope} on Linux/WSL. "
                    "Kernel replay is the default. Unsupported syntax is rejected; no SAT result is reported.",
        epilog="Compiled checking trusts compiler/runtime execution. Kernel checking also requires a fresh exact-input Lean proof.")
    parser.add_argument("input", type=Path, help="TPTP problem file to read and capture")
    configuration = "capability" if fof else "installation"
    parser.add_argument("--" + configuration, required=not public, type=Path,
        help=f"override the pinned {configuration} JSON file supplied by the installed launcher")
    parser.add_argument("--artifacts", required=not public, type=Path,
        help=("new directory for input, certificate, logs and manifest; must not exist "
              "(default: a fresh UUID directory under .local/runs in the current directory)" if public else
              "new directory for input, certificate, logs and manifest; required and must not exist"))
    parser.add_argument("--check", choices=("kernel", "compiled"), default="kernel",
        help="verification profile: fresh Lean kernel replay or compiled checker execution (default: %(default)s)")
    parser.add_argument("--output", choices=("status", "tstp"), default="status",
        help="SZS status only, or status plus a checked TSTP refutation when supported (default: %(default)s)")
    parser.add_argument("--max-solution-bytes", type=int, default=16 << 20,
        help="maximum TSTP solution bytes, from 0 to 16777216 (default: %(default)s)")
    parser.add_argument("--wall-seconds", type=float, default=60,
        help="total command deadline in seconds, from 0.25 to 86400 (default: %(default)s)")
    parser.add_argument("--memory-mib", type=int, default=2048,
        help="sampled memory limit for adapter and owned processes, in MiB, from 16 to 1048576 (default: %(default)s)")
    numeric = (
        ("steps", 100_000, "maximum search steps"),
        ("clauses", 1_000, "maximum clauses retained by search"),
        ("operations", 5_000_000, "maximum structural search operations"),
        ("input-bytes", capability_bytes if fof else 1 << 20, "maximum captured input bytes"),
        ("certificate-bytes", capability_bytes if fof else 64 << 20, "maximum captured certificate bytes"),
        ("log-bytes", 4 << 20, "maximum bytes per child output stream"),
        ("artifact-bytes", 256 << 20, "maximum retained run artifact bytes"),
    )
    for name, value, description in numeric:
        cap = f"; checker hard cap: {capability_bytes} bytes" if fof and name in ("input-bytes", "certificate-bytes") else ""
        parser.add_argument("--max-" + name, type=int, default=value,
            help=description + cap + " (default: %(default)s)")
    supplied = list(sys.argv[1:] if argv is None else argv)
    if public and supplied == ["help"]:
        supplied = ["--help"]
    args = parser.parse_args(supplied)
    if getattr(args, configuration) is None:
        parser.error("--" + configuration + " must be supplied by the installed launcher or explicitly")
    if not math.isfinite(args.wall_seconds) or not 0.25 <= args.wall_seconds <= 86400:
        parser.error("wall-seconds must be finite and between 0.25 and 86400")
    if not 16 <= args.memory_mib <= 1 << 20:
        parser.error("memory-mib outside supported range" if fof else "memory-mib must be between 16 and 1048576")
    for name, _, _ in numeric:
        attribute = "max_" + name.replace("-", "_")
        if not 0 <= getattr(args, attribute) <= (1 << 63) - 1:
            parser.error("Invalid nonnegative limit: " + name.replace("-", "_") if fof else
                         attribute + " is outside the supported nonnegative range")
    if fof and (args.max_input_bytes > capability_bytes or args.max_certificate_bytes > capability_bytes):
        parser.error("The actual FOF checker accepts at most 1 MiB each of source and certificate")
    if not 0 <= args.max_solution_bytes <= 16 << 20:
        parser.error("max-solution-bytes must be between zero and 16 MiB" if fof else
                     "max-solution-bytes must be between 0 and 16777216")
    args.auto_artifacts = args.artifacts is None
    if args.auto_artifacts:
        args.artifacts = Path.cwd() / ".local" / "runs" / uuid.uuid4().hex
    return args


def announce_artifacts(args, root, supervisor, emit):
    """Report an automatically created directory under the same deadline."""
    if not args.auto_artifacts:
        return
    message = ("Fang artifacts: " + str(root) + "\n").encode("utf-8", errors="backslashreplace")
    if not emit(message, supervisor.deadline, descriptor=2, cancelled=lambda: supervisor.cancelled):
        raise Failure("Timeout", "Caller did not accept artifact location before the deadline", "artifact-output")
