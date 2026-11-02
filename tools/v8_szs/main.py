"""Version-8 command: expanded TPTP input, Rust producer, compiled original-byte checker, SZS status.

Axiom-only single files go to the fast version-8 checker. Axiom-only inputs with include directives, distinct
objects or annotations go to the bundle producer and checker (bundle.py), and with --output tstp to the bundle
exporter after the checker accepted. Inputs with any role other than axiom, conjectures
included, go to the signed bundle producer and checker (signed.py), and with --output tstp, when the conjecture
exporter is installed, the proved conjectures of a single file get one document each. The run manifest and the first output line
record which path ran; the second line names the checking mode.

Without --check the compiled checker decides (capability.DEFAULT_CHECK; docs/USAGE.md describes both modes).
--check kernel is opt-in and refused below capability.KERNEL_MINIMUMS.
"""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import argparse
from dataclasses import asdict
import hashlib
import math
import os
import re
from pathlib import Path
import sys
import time
import uuid

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
if str(HERE.parent) not in sys.path:
    sys.path.insert(0, str(HERE.parent))
if str(HERE) not in sys.path:
    sys.path.insert(0, str(HERE))
import bundle
import capability
import protocol
import signed
from fang_szs import cli
from fang_szs.app import emit_status
from fang_szs.supervisor import (EXIT, Failure, Limits, Snapshot, Supervisor, child_environment, read_regular,
                                 strict_json, write_json)

# Theorem is the signed path's positive status; it exits 0 like Unsatisfiable.
EXITS = dict(EXIT, Theorem=0)
POSITIVE = ("Unsatisfiable", "Theorem")

PROFILES = ("v8", "cnf", "ground-fof")
KERNEL_FLAGS = " ".join(f"{option} {minimum}" for option, _, minimum in capability.KERNEL_MINIMUMS)
KERNEL_BELOW = ("--check kernel needs at least " + KERNEL_FLAGS + "; rerun with those flags, or without --check "
                "for the compiled checker (the default). No fallback was performed.")
KERNEL_UNAVAILABLE = ("Kernel replay is not installed in this package; rerun without --check for the compiled "
                      "checker (the default; trusts the Lean compiler and runtime). No fallback was performed.")
KERNEL_SINGLE_ONLY = ("Kernel replay covers single-file axiom input; rerun without --check for the compiled checker "
                      "(the default). No fallback was performed.")
KERNEL_TSTP = ("TSTP output is not available with --check kernel; rerun with --output status, or without --check. "
               "No fallback was performed.")
# The kernel entry's exit codes (tools/v8_kernel/entry/main.py contract): only 0 with KernelChecked is a result.
KERNEL_EXITS = {0: "KernelChecked", 2: "Usage", 3: "Rejected", 4: "ReviewPending", 5: "ResourceOut", 6: "Error",
                7: "Timeout", 8: "MemoryOut", 9: "Forced"}
KERNEL_STATUS = {"ResourceOut": "ResourceOut", "Timeout": "Timeout", "MemoryOut": "MemoryOut"}
MODES = {"compiled": "checked by the compiled Lean checker", "kernel": "kernel replay requested"}
TRUST = {"compiled": "compiler and runtime trusted", "kernel": "Lean kernel trusted"}
TSTP_UNAVAILABLE = ("TSTP output is not installed for version-8 input; rerun with --output status. "
                    "No fallback was performed.")
# The exporter stops this long before the command deadline, so its time-out cannot cancel an accepted result.
EXPORT_RESERVE_SECONDS = 1.0
DOCUMENT = re.compile(rb"(?:[ -~]*\n)+")
PATHS = {"single": "single file", "bundle": "bundle (include directives, distinct objects or annotations)",
         "signed": "signed bundle (conjectures or other non-axiom roles)"}


class Parser(argparse.ArgumentParser):
    def error(self, message):
        raise Failure("Error", "Invalid command arguments: " + message)


def build_parser(public):
    parser = Parser(prog="fang" if public else None,
        description="Fang theorem prover for TPTP CNF and FOF axioms with equality (version-8 pipeline) on Linux/WSL. "
                    "A Rust search writes a candidate certificate; only acceptance by the independent checker "
                    "gives a result. Unsupported input is rejected; no SAT result is reported.",
        epilog="Profiles: v8 (default) handles every input. --profile cnf and --profile ground-fof run the older "
               "restricted CNF and ground-FOF commands of an earlier installation, with their own options (see "
               "fang --profile cnf --help); they are available only when that installation was linked. There is no "
               "retry or fallback between profiles, and the older profiles keep their own defaults. For v8 input "
               "the default check is compiled: only the compiled Lean checker can accept a result, and the Lean "
               "compiler and runtime are trusted. --check kernel is opt-in, needs at least " + KERNEL_FLAGS
               + ", and is not installed yet. Every run names its checking mode in a comment line before the status. "
               "--output tstp prints a CNF refutation after the checker accepted, for single files and, when "
               "the bundle exporter is installed, for bundles. Inputs with annotations, include directives or distinct "
               "objects use the bundle checker; includes resolve relative to the including file, then the TPTP "
               "root. Inputs with conjectures or other non-axiom roles use the signed checker: Theorem needs an "
               "accepted certificate for every selected conjecture. The limits cover the whole command.")
    parser.add_argument("input", type=Path, help="TPTP problem file to read and capture")
    parser.add_argument("--profile", choices=PROFILES, default="v8",
        help="pipeline: v8, or an older profile chosen explicitly (default: %(default)s)")
    parser.add_argument("--capability", required=not public, type=Path,
        help="override the pinned capability JSON file supplied by the installed launcher")
    parser.add_argument("--artifacts", required=not public, type=Path,
        help=("new directory for input, certificate, logs and manifest; must not exist "
              "(default: a fresh UUID directory under .local/runs in the current directory)"))
    parser.add_argument("--tptp-root", type=Path, default=os.environ.get("TPTP") or None,
        help="directory for include files not found next to the input (default: the TPTP environment variable)")
    parser.add_argument("--check", choices=("kernel", "compiled"), default=None,
        help="verification mode: the compiled checker or per-input kernel replay (default: "
             + capability.DEFAULT_CHECK + ", which trusts the Lean compiler and runtime; kernel needs at least "
             + KERNEL_FLAGS + " and is not installed yet)")
    parser.add_argument("--output", choices=("status", "tstp"), default="status",
        help="SZS status only, or status plus a TSTP refutation (default: %(default)s; single files, bundles and, when "
             "installed, proved conjectures of a single file)")
    parser.add_argument("--max-solution-bytes", type=int, default=16 << 20,
        help="maximum TSTP document bytes, from 0 to 16777216 (default: %(default)s)")
    parser.add_argument("--self-check", action="store_true",
        help="hash every installed file and adapter source against the installation, then exit; no input is read")
    parser.add_argument("--wall-seconds", type=float, default=60,
        help="total command deadline in seconds, from 0.25 to 86400 (default: %(default)s)")
    parser.add_argument("--memory-mib", type=int, default=2048,
        help="sampled memory limit for the adapter and its processes, in MiB, from 16 to 1048576 (default: %(default)s)")
    for name, value, description in (
            ("input-bytes", capability.MAX_BYTES, "maximum captured input bytes; checker hard cap 1048576"),
            ("certificate-bytes", capability.MAX_BYTES, "maximum captured certificate bytes; checker hard cap 1048576"),
            ("log-bytes", 4 << 20, "maximum bytes per child output stream"),
            ("artifact-bytes", 256 << 20, "maximum retained run artifact bytes")):
        parser.add_argument("--max-" + name, type=int, default=value, help=description + " (default: %(default)s)")
    return parser


def arguments(argv, *, public=False):
    supplied = list(sys.argv[1:] if argv is None else argv)
    if public and supplied == ["help"]:
        supplied = ["--help"]
    parser = build_parser(public)
    args = parser.parse_args(supplied)
    if args.profile != "v8":
        parser.error("--profile " + args.profile + " is dispatched by the fang launcher, not by the v8 adapter")
    if args.capability is None:
        parser.error("--capability must be supplied by the installed launcher or explicitly")
    if not math.isfinite(args.wall_seconds) or not 0.25 <= args.wall_seconds <= 86400:
        parser.error("wall-seconds must be finite and between 0.25 and 86400")
    if not 16 <= args.memory_mib <= 1 << 20:
        parser.error("memory-mib must be between 16 and 1048576")
    if not 0 <= args.max_solution_bytes <= 16 << 20:
        parser.error("max-solution-bytes must be between 0 and 16777216")
    for name, maximum in (("input_bytes", capability.MAX_BYTES), ("certificate_bytes", capability.MAX_BYTES),
                          ("log_bytes", (1 << 63) - 1), ("artifact_bytes", (1 << 63) - 1)):
        if not 0 <= getattr(args, "max_" + name) <= maximum:
            parser.error("max-" + name.replace("_", "-") + " is outside the supported range")
    args.check_source = "explicit" if args.check is not None else "default"
    if args.check is None:
        args.check = capability.DEFAULT_CHECK
    args.auto_artifacts = args.artifacts is None
    if args.auto_artifacts:
        args.artifacts = Path.cwd() / ".local" / "runs" / uuid.uuid4().hex
    return args


def requested_features(args):
    """Refuse kernel checking before any input is read: below its minimum limits, or when this installation has no
    kernel mode, or with TSTP output. Other TSTP refusals come after routing, before search.
    """
    if args.check == "kernel":
        if any(getattr(args, name) < minimum for _, name, minimum in capability.KERNEL_MINIMUMS):
            raise Failure("Inappropriate", KERNEL_BELOW, "capability")
        try:
            installed = strict_json(read_regular(args.capability, 32 << 20).decode("utf-8")).get("kernel")
        except (OSError, ValueError, Failure):
            installed = None
        if installed is None:
            raise Failure("Inappropriate", KERNEL_UNAVAILABLE, "capability")
        if args.output == "tstp":
            raise Failure("Inappropriate", KERNEL_TSTP, "capability")


def load_capability(args, supervisor):
    data = read_regular(args.capability, 32 << 20, supervisor.check)
    config = strict_json(data.decode("utf-8"))
    capability.check_fields(config)
    return config, hashlib.sha256(data).hexdigest()


def verified(config, route, args, supervisor, manifest):
    """Hash what this route will execute, before it runs; see capability.PER_RUN."""
    identities = capability.verify_run(config, capability.run_records(config, route, args.output == "tstp",
                                                                      args.check == "kernel"), supervisor.check)
    manifest["verified_before_run"] = sorted(identities)
    return identities


def pipeline(args, supervisor, manifest, root):
    config, config_sha = load_capability(args, supervisor)
    manifest["capability"] = config
    manifest["capability_sha256"] = config_sha
    source = Snapshot(root / "input.p", read_regular(args.input, args.max_input_bytes, supervisor.check))
    certificate = None
    manifest["input"] = {"caller_path": str(args.input.absolute()), "bytes": len(source.data), "sha256": source.sha256,
                         "child_identity": "Linux sealed memfd; disk copy retained and checked"}
    manifest["problem_id"] = "fang_" + source.sha256[:24]
    try:
        tptp_root = None if args.tptp_root is None else args.tptp_root.absolute()
        files = [("base", args.input.absolute().name, None, source.data)]
        if bundle.needs_bundle(source.data):
            total = [len(source.data)]

            def read(location):
                data = read_regular(location, signed.FILE_BYTES, supervisor.check)
                total[0] += len(data)
                if total[0] > signed.TOTAL_BYTES:
                    raise Failure("ResourceOut", "Bundle total byte limit exceeded", "bundle-discovery")
                return data
            files = signed.discover(args.input.absolute().name, source.data, args.input.absolute().parent, tptp_root, read)
        route = signed.route(files, bundle.needs_bundle(source.data))
        manifest["path"] = route
        bundle_tstp = config["tstp"] is not None and "bundle_exporter" in config["tstp"]
        goal_tstp = config["tstp"] is not None and "goal_exporter" in config["tstp"]
        if args.output == "tstp" and (config["tstp"] is None or (route == "signed" and not goal_tstp)
                                      or (route == "bundle" and not bundle_tstp)):
            raise Failure("Inappropriate", {"single": TSTP_UNAVAILABLE, "bundle": bundle.TSTP_UNAVAILABLE,
                                            "signed": signed.TSTP_UNAVAILABLE}[route], "capability")
        if args.check == "kernel" and (route != "single" or config["kernel"] is None):
            raise Failure("Inappropriate", KERNEL_SINGLE_ONLY if config["kernel"] is not None else KERNEL_UNAVAILABLE,
                          "capability")
        if route == "signed":
            if config["signed"] is None:
                raise Failure("Inappropriate", signed.NOT_INSTALLED, "capability")
            identities = verified(config, route, args, supervisor, manifest)
            return signed_pipeline(args, supervisor, manifest, root, config, source, files, identities)
        if route == "bundle":
            if config["bundle"] is None:
                raise Failure("Inappropriate", bundle.NOT_INSTALLED, "capability")
            identities = verified(config, route, args, supervisor, manifest)
            return bundle_pipeline(args, supervisor, manifest, root, config, source, identities)
        identities = verified(config, route, args, supervisor, manifest)
        environment = child_environment() | {"LEAN_NUM_THREADS": "1"}
        wrapper = HERE / "exec_stdin.py"
        stage, stdout, stderr = supervisor.run("search",
            [config["python"]["path"], "-I", "-B", str(wrapper), config["engine"]["path"], source.argument],
            root / "search", root, (source.fd,), environment=environment, stdout_limit=args.max_certificate_bytes)
        source.verify(supervisor.check)
        try:
            status, reason = protocol.engine_outcome(stage, stdout, stderr, source.data)
        except ValueError as error:
            raise Failure("Error", str(error), "search") from error
        manifest["producer_outcome"] = status
        if status != "candidate":
            return status, reason
        certificate = Snapshot(root / "proof.fang", stdout)
        manifest["certificate"] = {"bytes": len(stdout), "sha256": certificate.sha256, "version": 8,
                                   "preprocessing": capability.LANGUAGE, "accepted": False}
        if args.check == "kernel":
            status, reason = kernel_check(supervisor, manifest, root, config, source, certificate, environment)
            capability.check_identities(identities, supervisor.check)
            supervisor.memory()
            supervisor.tree_bytes(root)
            supervisor.check("checked")
            manifest["certificate"]["accepted"] = True
            return status, reason
        stage, output, diagnostic = supervisor.run("checker",
            [config["checker"]["path"], source.argument, certificate.argument],
            root / "checker", root, (source.fd, certificate.fd), environment=environment)
        try:
            outcome = protocol.checker_outcome(stage, output, diagnostic)
        except ValueError as error:
            raise Failure("Error", str(error), "checker") from error
        manifest["compiled_check"] = {"outcome": outcome, "accepted": outcome == "accepted", "kernel_instance": False,
                                      "trust": "Lean compiler, runtime and operating system"}
        status, reason = protocol.checked_status(outcome)
        if status != "Unsatisfiable":
            raise Failure(status, reason, "checker")
        source.verify(supervisor.check)
        certificate.verify(supervisor.check)
        if read_regular(root / "search/stdout", args.max_certificate_bytes, supervisor.check) != certificate.data:
            raise Failure("Error", "Captured producer certificate changed", "checker")
        if args.output == "tstp":
            export_document(args, supervisor, manifest, root,
                            [config["tstp"]["exporter"]["path"], source.argument, certificate.argument,
                             args.input.absolute().name], (source.fd, certificate.fd), environment)
        capability.check_identities(identities, supervisor.check)
        supervisor.memory()
        supervisor.tree_bytes(root)
        supervisor.check("checked")
        manifest["certificate"]["accepted"] = True
        # Axiom-only input: no conjecture is selected and the one inputs certificate was accepted.
        return protocol.task_status(0, 1), reason
    finally:
        if certificate is not None:
            certificate.close()
        source.close()


def kernel_check(supervisor, manifest, root, config, source, certificate, environment):
    """Kernel mode: the witness tool suggests values, the kernel entry checks every one in Lean.

    Only exit 0 with status KernelChecked gives a result; ResourceOut, Timeout and MemoryOut keep their names, and
    every other outcome, ReviewPending included, is an Error and never a result.
    """
    kernel = config["kernel"]
    stage, witness, diagnostic = supervisor.run("witness", [kernel["witness"]["path"], source.argument, certificate.argument],
                                                root / "witness", root, (source.fd, certificate.fd), environment=environment,
                                                stdout_limit=16 << 20)
    try:
        value = strict_json(witness.decode("ascii"))
        valid = (stage["exit_code"] == 0 and not diagnostic and value.get("schema") == "fang-equality-kernel-witness-1"
                 and value.get("source_hex") == source.data.hex() and value.get("certificate_hex") == certificate.data.hex())
    except (UnicodeDecodeError, ValueError):
        valid = False
    if not valid:
        raise Failure("Error", "The kernel witness tool failed or described other files", "witness")
    witness_path = root / "witness.json"
    with witness_path.open("xb") as stream:
        stream.write(witness)
    source.verify(supervisor.check)
    certificate.verify(supervisor.check)
    output_root = Path(kernel["output_root"])
    # The entry refuses an existing directory; run directories of different runs may share a name.
    out = output_root / f"{root.name}-{uuid.uuid4().hex}"
    stage, stdout, stderr = supervisor.run("kernel", [config["python"]["path"], "-I", "-B", kernel["entry"]["path"],
                                                      "--input", str(root / "input.p"), "--certificate",
                                                      str(root / "proof.fang"), "--witness", str(witness_path),
                                                      "--out", str(out)],
                                           root / "kernel", root, environment=environment)
    code = stage["exit_code"]
    try:
        line = strict_json(stdout.decode("ascii"))
    except (UnicodeDecodeError, ValueError):
        line = {}
    record = {"exit_code": code, "status": line.get("status"), "error": line.get("error"), "out": str(out),
              "expected": KERNEL_EXITS.get(code)}
    kernel_manifest = out / "manifest.json"
    if kernel_manifest.is_file():
        record["manifest_sha256"] = hashlib.sha256(kernel_manifest.read_bytes()).hexdigest()
    manifest["kernel_check"] = record
    if code == 0 and line.get("status") == "KernelChecked" and line.get("manifest") == str(kernel_manifest):
        record["accepted"] = True
        return protocol.task_status(0, 1), "Lean kernel replay checked the exact captured pair (KernelChecked)"
    status = KERNEL_STATUS.get(KERNEL_EXITS.get(code))
    if status is not None and line.get("status") == KERNEL_EXITS[code]:
        raise Failure(status, "Kernel replay stopped: " + KERNEL_EXITS[code], "kernel")
    raise Failure("Error", f"Kernel replay gave no result ({KERNEL_EXITS.get(code, 'exit ' + str(code))})", "kernel")


def export_document(args, supervisor, manifest, root, command, descriptors, environment, label="export",
                    solution="solution.p"):
    """Print the TSTP document of what the checker has accepted, or record why there is none.

    `command` runs the single-file exporter on the sealed pair, the bundle exporter on the certificate and the
    sealed bundle files, the same arguments the bundle checker accepted, or the conjecture exporter on the sealed
    file, the accepted goal certificate and the goal index. The status stays what the checker decided whatever
    happens here: an export error, an invalid document, a resource stop or a time-out only removes the document.
    """
    name = args.input.absolute().name
    saved = supervisor.deadline
    supervisor.deadline = saved - EXPORT_RESERVE_SECONDS
    record = {"file_name": name}
    manifest["export"] = record
    try:
        stage, stdout, stderr = supervisor.run(label, command, root / label, root, descriptors,
                                               environment=environment, stdout_limit=args.max_solution_bytes)
    except Failure as error:
        if error.status not in ("Timeout", "MemoryOut", "ResourceOut"):
            raise
        record.update(state="resource", detail=error.status)
        manifest["export_note"] = "TSTP export stopped at a resource limit (" + error.status + "); no document printed"
        return
    finally:
        supervisor.deadline = saved
    record["exit_code"] = stage["exit_code"]
    if stage["exit_code"] == 0 and not stderr and DOCUMENT.fullmatch(stdout):
        path = root / solution
        with path.open("xb") as stream:
            stream.write(stdout)
        record.update(state="document", bytes=len(stdout), sha256=__import__("hashlib").sha256(stdout).hexdigest(),
                      path=str(path))
        return
    first = (stderr.decode("ascii", "replace").strip().splitlines() or ["no diagnostic"])[0][:200]
    record.update(state="failed", diagnostic=first)
    manifest["export_note"] = f"TSTP export failed (exit {stage['exit_code']}: {first}); no document printed"


def export_goal_documents(args, supervisor, manifest, root, exporter, source, certificates, environment):
    """One document per proved conjecture, in index order, from its accepted certificate.

    Any export that gives no document removes them all, with its note; the Theorem status stays.
    """
    records = []
    for index, certificate in enumerate(certificates):
        export_document(args, supervisor, manifest, root,
                        [exporter, source.argument, certificate.argument, str(index), args.input.absolute().name],
                        (source.fd, certificate.fd), environment, f"export-goal-{index}", f"solution-goal-{index}.p")
        records.append(dict(manifest["export"], goal=index))
        if manifest["export"].get("state") != "document":
            manifest["export"] = {"file_name": args.input.absolute().name, "state": manifest["export"].get("state"),
                                  "goals": records}
            return
    manifest["export"] = {"file_name": args.input.absolute().name, "state": "documents", "documents": records}


def bundle_pipeline(args, supervisor, manifest, root, config, source, identities):
    """Producer reads the bundle; every listed file is then read once, sealed, hashed and passed to the checker."""
    environment = child_environment() | {"LEAN_NUM_THREADS": "1"}
    tptp_root = None if args.tptp_root is None else args.tptp_root.absolute()
    manifest["tptp_root"] = None if tptp_root is None else str(tptp_root)
    command = [config["bundle"]["producer"]["path"], str(args.input.absolute())]
    if tptp_root is not None:
        command += ["--tptp-root", str(tptp_root)]
    stage, stdout, stderr = supervisor.run("search", command, root / "search", root, environment=environment,
                                           stdout_limit=args.max_certificate_bytes)
    source.verify(supervisor.check)
    try:
        status, detail = bundle.producer_outcome(stage, stdout, stderr)
        places = bundle.locate(detail, args.input, tptp_root) if status == "candidate" else None
    except ValueError as error:
        raise Failure("Error", str(error), "search") from error
    manifest["producer_outcome"] = status
    if status != "candidate":
        return status, detail
    snapshots, certificate = [], None
    try:
        files, total = [], 0
        for index, (root_name, path, location) in enumerate(places):
            data = source.data if index == 0 else read_regular(location, bundle.FILE_BYTES, supervisor.check)
            total += len(data)
            if len(data) > bundle.FILE_BYTES or total > bundle.TOTAL_BYTES:
                raise Failure("ResourceOut", "Bundle file or total byte limit exceeded", "bundle-capture")
            snapshot = source if index == 0 else Snapshot(root / f"bundle-{index}.p", data)
            if index:
                snapshots.append(snapshot)
            files.append((root_name, path, snapshot))
        captured = bundle.digest([(root_name, path, snapshot.data) for root_name, path, snapshot in files])
        manifest["bundle"] = {
            "files": [{"index": index, "root": root_name, "path": path, "read_from": str(location),
                       "bytes": len(snapshot.data), "sha256": snapshot.sha256}
                      for index, ((root_name, path, snapshot), (_, _, location)) in enumerate(zip(files, places))],
            "producer_digest": detail["bundle_sha256"], "captured_digest": captured,
            "digests_equal": captured == detail["bundle_sha256"],
            "declarations": detail["declarations"], "objects": detail["objects"]}
        certificate = Snapshot(root / "proof.fang", stdout)
        manifest["certificate"] = {"bytes": len(stdout), "sha256": certificate.sha256, "version": 8,
                                   "preprocessing": capability.LANGUAGE, "accepted": False}
        arguments = [item for root_name, path, snapshot in files for item in (root_name, path, snapshot.argument)]
        descriptors = tuple(snapshot.fd for _, _, snapshot in files) + (certificate.fd,)
        stage, output, diagnostic = supervisor.run("checker",
            [config["bundle"]["checker"]["path"], certificate.argument, *arguments],
            root / "checker", root, descriptors, environment=environment)
        try:
            outcome = bundle.checker_outcome(stage, output, diagnostic)
        except ValueError as error:
            raise Failure("Error", str(error), "checker") from error
        manifest["compiled_check"] = {"outcome": outcome, "accepted": outcome == "accepted", "kernel_instance": False,
                                      "checker": "bundle", "trust": "Lean compiler, runtime and operating system"}
        status, reason = protocol.checked_status(outcome)
        if status != "Unsatisfiable":
            raise Failure(status, reason.replace("version-8", "bundle"), "checker")
        for _, _, snapshot in files:
            snapshot.verify(supervisor.check)
        certificate.verify(supervisor.check)
        if read_regular(root / "search/stdout", args.max_certificate_bytes, supervisor.check) != certificate.data:
            raise Failure("Error", "Captured producer certificate changed", "checker")
        if args.output == "tstp":
            # Only after the bundle checker accepted these sealed files and this certificate.
            export_document(args, supervisor, manifest, root,
                            [config["tstp"]["bundle_exporter"]["path"], certificate.argument, *arguments], descriptors,
                            environment)
        capability.check_identities(identities, supervisor.check)
        supervisor.memory()
        supervisor.tree_bytes(root)
        supervisor.check("checked")
        manifest["certificate"]["accepted"] = True
        return protocol.task_status(0, 1), "The native bundle checker accepted the exact captured files and certificate"
    finally:
        for snapshot in snapshots:
            snapshot.close()
        if certificate is not None:
            certificate.close()


def signed_pipeline(args, supervisor, manifest, root, config, source, files, identities):
    """Signed tasks over the sealed bundle; statuses follow docs/DESIGN.md, "Status rules for conjectures".

    Every file is sealed and hashed once and passed as ROOT PATH FILE triples to
    every producer and checker run. The checker's own --goals listing decides the
    tasks; the whole command's limits cover all of them, and each task gets what
    remains. Running out before every task is accepted gives ResourceOut.
    """
    environment = child_environment() | {"LEAN_NUM_THREADS": "1"}
    snapshots, certificates = [], []
    try:
        sealed = []
        for index, (root_name, path, location, data) in enumerate(files):
            snapshot = source if index == 0 else Snapshot(root / f"signed-{index}.p", data)
            if index:
                snapshots.append(snapshot)
            sealed.append((root_name, path, location, snapshot))
        triples = [item for root_name, path, _, snapshot in sealed for item in (root_name, path, snapshot.argument)]
        descriptors = tuple(snapshot.fd for _, _, _, snapshot in sealed)
        record = {"files": [{"index": index, "root": root_name, "path": path,
                             "read_from": str(location if location is not None else args.input.absolute()),
                             "bytes": len(snapshot.data), "sha256": snapshot.sha256}
                            for index, (root_name, path, location, snapshot) in enumerate(sealed)], "tasks": []}
        manifest["signed"] = record
        checker, producer = config["signed"]["checker"]["path"], config["signed"]["producer"]["path"]
        stage, output, diagnostic = supervisor.run("goals", [checker, "--goals", *triples], root / "goals", root,
                                                   descriptors, environment=environment)
        try:
            status, listed = signed.listing(stage, output, diagnostic)
        except ValueError as error:
            raise Failure("Error", str(error), "goals") from error
        if status != "listed":
            return status, "The signed checker rejected the bundle while listing goals: " + diagnostic.decode("ascii", "replace").strip()
        record["listing"] = [list(item) for item in listed]
        tasks = list(range(len(listed))) or ["inputs"]
        outcomes = []
        for task in tasks:
            label = "inputs" if task == "inputs" else f"goal-{task}"
            selection = ["--inputs"] if task == "inputs" else ["--goal", str(task)]
            stage, stdout, stderr = supervisor.run("produce-" + label, [producer, *selection, *triples],
                                                   root / ("produce-" + label), root, descriptors,
                                                   environment=environment, stdout_limit=args.max_certificate_bytes)
            try:
                produced = signed.producer_outcome(stage, stdout, stderr)
            except ValueError as error:
                raise Failure("Error", str(error), "produce-" + label) from error
            entry = {"task": label, "producer": produced}
            record["tasks"].append(entry)
            if produced != "candidate":
                outcomes.append(produced)
                break
            certificate = Snapshot(root / f"proof-{label}.fang", stdout)
            certificates.append(certificate)
            entry["certificate_sha256"] = certificate.sha256
            stage, output, diagnostic = supervisor.run("check-" + label,
                [checker, *selection[:1], *selection[1:], certificate.argument, *triples],
                root / ("check-" + label), root, descriptors + (certificate.fd,), environment=environment)
            try:
                result = signed.accepted(stage, output, diagnostic, task)
                if result is None:
                    result = signed.rejection(stage["exit_code"], output, diagnostic)
            except ValueError as error:
                raise Failure("Error", str(error), "check-" + label) from error
            entry["checker"] = list(result) if isinstance(result, tuple) else result
            outcomes.append(result)
            if not isinstance(result, (tuple, bool)):
                break
        status = signed.final_status(listed, outcomes)
        record["status_rule"] = "docs/DESIGN.md, Status rules for conjectures"
        if status in ("Theorem", "Unsatisfiable"):
            for _, _, _, snapshot in sealed:
                snapshot.verify(supervisor.check)
            for certificate in certificates:
                certificate.verify(supervisor.check)
            if args.output == "tstp":
                # Only after the signed checker accepted every listed conjecture of these sealed files.
                if status == "Theorem" and len(sealed) == 1 and len(certificates) == len(listed):
                    export_goal_documents(args, supervisor, manifest, root, config["tstp"]["goal_exporter"]["path"],
                                          source, certificates, environment)
                else:
                    manifest["export"] = {"file_name": args.input.absolute().name, "state": "not-covered"}
                    manifest["export_note"] = GOAL_TSTP_SCOPE
            capability.check_identities(identities, supervisor.check)
            supervisor.memory()
            supervisor.tree_bytes(root)
            supervisor.check("checked")
            return status, ("The signed checker accepted a certificate for every listed conjecture" if status == "Theorem"
                            else "No conjecture is selected and the signed checker accepted the inputs certificate")
        return status, "Not every signed task was accepted: " + ", ".join(map(str, outcomes))
    except Failure as error:
        if error.status in ("Timeout", "MemoryOut"):
            raise Failure("ResourceOut", "The command limits ran out before every signed task was accepted ("
                          + error.status + ")", error.stage) from error
        raise
    finally:
        for snapshot in snapshots + certificates:
            snapshot.close()


def checkpoint(path, manifest, supervisor):
    """fang_szs.app.terminal_checkpoint for both positive statuses: an unsaved record never authorizes a result."""
    status = manifest["status"]
    try:
        write_json(path, manifest)
        if supervisor is not None and status in POSITIVE:
            supervisor.check(reserve=0)
    except Failure as error:
        status = error.status
        manifest.update(status=status, exit_code=EXITS[status], reason=error.reason, stage="finalization")
        try:
            write_json(path, manifest)
        except (OSError, ValueError, TypeError) as retry_error:
            manifest["checkpoint_error"] = str(retry_error)
    except (OSError, ValueError, TypeError) as error:
        status = "Error"
        manifest.update(status=status, exit_code=EXITS[status], stage="finalization",
                        reason="Could not save the terminal artifact record", checkpoint_error=str(error))
    return status


GOAL_TSTP_SCOPE = ("TSTP output for inputs with conjectures covers proved conjectures of a single file without "
                   "include directives; no document printed")


def output_bytes(manifest, status, document=b""):
    path = PATHS.get(manifest.get("path"), "not chosen")
    check = manifest["check"]
    chosen = "default mode" if manifest.get("check_source") == "default" else "--check " + check
    lines = [f"% Fang profile: v8, {path}", f"% fang: {MODES[check]} ({chosen}; {TRUST[check]})"]
    if manifest.get("stage") == "capability":
        lines.append("% Fang: " + manifest["reason"])
    lines.append(f"% SZS status {status} for {manifest['problem_id']}")
    output = ("\n".join(lines) + "\n").encode("ascii", errors="replace")
    documents = document if isinstance(document, list) else [document] if document else []
    if status in POSITIVE and documents:
        # One block per document; with several conjectures, one per conjecture in index order.
        name = manifest["export"]["file_name"]
        for text in documents:
            output += (f"% SZS output start CNFRefutation for {name}\n".encode("ascii", errors="replace") + text
                       + f"% SZS output end CNFRefutation for {name}\n".encode("ascii", errors="replace"))
    return output


def read_document(manifest, args, supervisor):
    """The exported document bytes (a list of them for conjectures), checked against the run record, or b"" with a note."""
    record = manifest.get("export", {})
    if record.get("state") not in ("document", "documents"):
        return b""
    try:
        rows = record["documents"] if record["state"] == "documents" else [record]
        texts = [read_regular(Path(row["path"]), args.max_solution_bytes, supervisor.check) for row in rows]
        if all(hashlib.sha256(data).hexdigest() == row["sha256"] for data, row in zip(texts, rows)):
            return texts if record["state"] == "documents" else texts[0]
    except Failure:
        pass
    record["state"] = "unreadable"
    manifest["export_note"] = "TSTP document could not be read back; no document printed"
    return b""


def self_check(supplied):
    """Full verification of the installation, as at install time."""
    try:
        index = supplied.index("--capability")
        config = strict_json(read_regular(Path(supplied[index + 1]), 32 << 20).decode("utf-8"))
        count = capability.verify(config)
    except (IndexError, OSError, ValueError, Failure) as error:
        print("% Fang self-check failed: " + str(getattr(error, "reason", error)))
        return EXITS["Error"]
    print(f"% Fang self-check: {count} pinned files and adapter sources match the installation")
    return 0


def main(argv=None, *, public=False):
    supplied = list(sys.argv[1:] if argv is None else argv)
    if "--self-check" in supplied:
        return self_check(supplied)
    started = time.monotonic()
    supervisor, root, owns_run = None, None, False
    manifest = {"schema": "fang-v8-run-v1", "state": "starting", "check": capability.DEFAULT_CHECK,
                "check_source": "default", "output": "status",
                "problem_id": "fang_unavailable", "language": capability.LANGUAGE,
                "scope": "Expanded TPTP CNF/FOF axioms with equality; no SAT, conjecture or search-completeness claim"}
    try:
        args = arguments(argv, public=public)
        manifest.update(check=args.check, check_source=args.check_source, output=args.output)
        if sys.platform != "linux":
            raise Failure("Error", "This command requires Linux/WSL")
        requested_features(args)
        limits = Limits(args.wall_seconds, args.memory_mib, args.max_input_bytes,
                        args.max_certificate_bytes, args.max_log_bytes, args.max_artifact_bytes)
        supervisor = Supervisor(limits, started)
        root = args.artifacts.absolute()
        root.mkdir(mode=0o700, parents=True)
        owns_run = True
        manifest.update(state="running", limits=asdict(limits),
            resource_method="One monotonic deadline; sampled adapter and owned-descendant RSS, not an address-space cap",
            engine_limits="Producer defaults of the accepted v8 producer; no search-limit flag")
        write_json(root / "manifest.json", manifest)
        cli.announce_artifacts(args, root, supervisor, emit_status)
        status, reason = pipeline(args, supervisor, manifest, root)
        supervisor.check()
        stage = "complete"
    except Failure as error:
        status, reason, stage = error.status, error.reason, error.stage
    except Exception as error:
        status, reason, stage = "Error", f"Adapter input, installation or I/O failure: {error}", "adapter"
    manifest.update(state="finished", status=status, exit_code=EXITS[status], reason=reason, stage=stage,
        elapsed_before_status_seconds=time.monotonic() - started,
        processes=supervisor.records if supervisor else [],
        peak_adapter_tree_rss_kib=supervisor.peak_kib if supervisor else None,
        output_delivery={"state": "pending"})
    document = read_document(manifest, args, supervisor) if status in POSITIVE and supervisor else b""
    output = output_bytes(manifest, status, document)
    if supervisor is not None and status in POSITIVE:
        try:
            supervisor.memory()
            supervisor.check("output-preparation")
        except Failure as error:
            status = error.status
            manifest.update(status=status, exit_code=EXITS[status], reason=error.reason, stage=error.stage)
            output = output_bytes(manifest, status)
    if owns_run:
        saved = checkpoint(root / "manifest.json", manifest, supervisor)
        if saved != status:
            status = saved
            output = output_bytes(manifest, status)
    try:
        deadline = supervisor.deadline if supervisor and status in POSITIVE else time.monotonic() + 0.15
        cancelled = (lambda: supervisor.cancelled) if supervisor and status in POSITIVE else None
        if not emit_status(output, deadline, cancelled=cancelled):
            raise Failure("Timeout", "Caller did not accept status before the deadline", "status-output")
        manifest["output_delivery"] = {"state": "written", "bytes": len(output),
                                       "sha256": hashlib.sha256(output).hexdigest(), "document": bool(document)}
        if status in POSITIVE and manifest.get("export_note"):
            try:
                sys.stderr.write("fang: " + manifest["export_note"] + "\n")
                sys.stderr.flush()
            except OSError:
                pass
    except Failure as error:
        status = error.status
        manifest.update(status=status, exit_code=EXITS[status], reason=error.reason, stage=error.stage)
        manifest["output_delivery"]["state"] = "incomplete"
    except OSError as error:
        status = "Error"
        manifest.update(status=status, exit_code=EXITS[status], reason=str(error), stage="status-output")
        manifest["output_delivery"]["state"] = "incomplete"
    if owns_run:
        status = checkpoint(root / "manifest.json", manifest, supervisor if status in POSITIVE else None)
    if supervisor:
        supervisor.close()
    return EXITS[status]


if __name__ == "__main__":
    raise SystemExit(main())
