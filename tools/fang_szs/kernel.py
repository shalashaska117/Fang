"""One internal replay hook; source and certificate cannot choose proof commands."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import importlib
import os
from pathlib import Path
import sys
from .installation import HELPERS, digest_file
from .protocol import completed_contract, exact_axioms, fixed_replay
from .storage import KernelWorkspace
from .supervisor import Failure, child_environment, read_regular, strict_json


def existing_helpers(config):
    folder = Path(config["source_root"]) / "tools/replay"
    for name in HELPERS:
        relative = "tools/replay/" + name
        if digest_file(folder / name) != config["source_sha256"][relative]:
            raise Failure("Error", "Fixed replay helper changed", "kernel")
    # Import only installation-pinned repository helpers, never child artifacts.
    sys.path.insert(0, str(folder))
    try:
        replay = importlib.import_module("generic_source_replay")
        audit = importlib.import_module("axiom_audit")
    finally:
        sys.path.pop(0)
    for module in (replay, audit):
        if Path(module.__file__).resolve().parent != folder.resolve():
            raise Failure("Error", "Fixed replay helper resolved outside the installation", "kernel")
    return replay, audit


def verify(supervisor, config, run_root, source, certificate, storage_report):
    """Fresh decomposed proof and fixed audit; no precomputed instance artifacts."""
    source.verify(supervisor.check)
    certificate.verify(supervisor.check)
    process, stdout, stderr = supervisor.run("export", [config["checker"]["path"], "--emit-replay",
        source.argument, certificate.argument], run_root / "export", run_root, (source.fd, certificate.fd))
    if completed_contract(process) != 0 or stderr:
        raise Failure("Error", "Replay exporter failed", "export")
    replay = fixed_replay(stdout, source.data, certificate.data)
    workspace = KernelWorkspace(supervisor, run_root, storage_report)
    try:
        workspace.stage_library(config)
        result = verify_native(supervisor, config, workspace, source, certificate, replay)
        workspace.verify_library()
        expected_archive = {"kernel/decomposed/" + name + ".lean": digest
            for name, digest in result["module_source_sha256"].items()}
        expected_archive.update({"kernel/input.p": source.sha256, "kernel/proof.fang": certificate.sha256})
        workspace.archive(expected_archive)
        workspace.cleanup()
        supervisor.check("kernel-archived")
        return result
    except Exception as error:
        workspace.retain_failure(error)
        raise


def verify_native(supervisor, config, workspace, source, certificate, replay):
    run_root = workspace.native
    project = run_root / "kernel"
    project.mkdir(mode=0o700)
    (project / "Replay.lean").write_text(replay, encoding="utf-8")
    for name, captured in (("input.p", source), ("proof.fang", certificate)):
        (project / name).write_bytes(captured.data)
        (project / name).chmod(0o400)
    helpers, audited_parser = existing_helpers(config)
    generator = Path(config["source_root"]) / "tools/replay/decomposed_replay_probe.py"
    modules_root = project / "decomposed"
    process, stdout, stderr = supervisor.run("decompose", [config["python"]["path"], str(generator),
        str(project / "Replay.lean"), "--out", str(modules_root), "--lake", config["lean"]["path"],
        "--full", "--grouped", "--emit-only"], run_root / "decompose", run_root)
    if completed_contract(process) != 0 or stdout or stderr:
        raise Failure("Error", "Fixed replay decomposition failed", "decompose")
    emitted = strict_json(read_regular(modules_root / "emitted.json", 4 << 20, supervisor.check).decode("utf-8"))
    modules = emitted.get("modules")
    expected_modules = ["ReplayDefs", "CertificateCharacters", "LexerProofs", "CertificateTokens",
        "NodeProofs", "CertificateDecoded", "SourceCharacters", "SourceLexer", "SourceDecoded",
        "CertificateAccepted", "CompleteReplay"]
    if modules != expected_modules:
        raise Failure("Error", "Unexpected generated module inventory", "decompose")
    if modules[0] != "ReplayDefs" or modules[-1] != "CompleteReplay" or emitted.get("generator_sha256") != config["source_sha256"]["tools/replay/decomposed_replay_probe.py"]:
        raise Failure("Error", "Decomposition identity or endpoints differ", "decompose")
    if {path.name for path in modules_root.iterdir()} != {name + ".lean" for name in modules} | {"emitted.json"}:
        raise Failure("Error", "Decomposer emitted unexpected or precomputed files", "decompose")
    for name, captured in (("input.p", source), ("proof.fang", certificate)):
        if read_regular(project / name, len(captured.data), supervisor.check) != captured.data:
            raise Failure("Error", "Decomposer changed captured bytes", "decompose")
    audit_source = helpers.fixed_audit("CompleteReplay", source.data, certificate.data)
    (modules_root / "Audit.lean").write_text(audit_source, encoding="utf-8")
    environment = child_environment() | {"LEAN_PATH": str(modules_root) + ":" + str(workspace.library)}
    results = {}
    source_hashes = {name: digest_file(modules_root / (name + ".lean"), supervisor.check) for name in [*modules, "Audit"]}
    for name in [*modules, "Audit"]:
        process, stdout, stderr = supervisor.run("kernel-" + name.lower(),
            [config["lean"]["path"], "-j1", "-M", str(supervisor.limits.memory_mib),
             "--root", str(modules_root), "-o", str(modules_root / (name + ".olean")), str(modules_root / (name + ".lean"))],
            run_root / ("kernel-" + name.lower()), run_root, environment=environment)
        if completed_contract(process) != 0 or stderr:
            raise Failure("Error", "Kernel replay or fixed audit failed", "kernel-" + name.lower())
        if not (modules_root / (name + ".olean")).is_file():
            raise Failure("Error", "Kernel compiler did not write its module", "kernel-" + name.lower())
        if name == "Audit":
            try:
                results = exact_axioms(stdout.decode("utf-8"), audited_parser)
            except ValueError as error:
                raise Failure("Error", str(error), "audit") from error
    source.verify(supervisor.check)
    certificate.verify(supervisor.check)
    if source_hashes != {name: digest_file(modules_root / (name + ".lean"), supervisor.check) for name in [*modules, "Audit"]}:
        raise Failure("Error", "Generated proof source changed during compilation", "kernel")
    return {"hook": "fixed-decomposed-v2", "audited_theorems": results, "modules": modules,
        "module_source_sha256": source_hashes, "fixed_audit_sha256": source_hashes["Audit"],
        "scope": "Fresh original-byte kernel instance; no SAT or search-completeness proof"}
