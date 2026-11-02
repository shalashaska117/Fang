"""Fresh original-byte kernel replay under the adapter's shared deadline."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import hashlib
import importlib.util
from pathlib import Path
import sys

import capability
import protocol
from fang_szs.storage import KernelWorkspace
from fang_szs.supervisor import Failure, child_environment, read_regular

MODULES = ("FofInstanceData", "FofInstanceInput", "FofInstanceCertificate", "FofInstanceProof")
AUDIT = "FofInstanceAudit"
AUDITS = frozenset("Fang.FOFKernelAudit." + name for name in (
    "exact_original_bytes_unsat", "exact_input_bytes", "exact_certificate_bytes",
    "exact_certificate_decodes", "exact_acceptance"))


def load_helper(path, name):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


def exact_audits(output, auditor):
    text = output.decode("utf-8")
    reports = list(auditor.REPORT.finditer(text))
    if len(reports) != len(AUDITS) or auditor.REPORT.sub("", text).strip():
        raise ValueError("Fixed kernel audit report inventory differs")
    values = auditor.audit_axioms(text, AUDITS)
    if set(values) != AUDITS:
        raise ValueError("Fixed kernel audit theorem set differs")
    return values


def verify(supervisor, config, root, source, certificate, storage):
    kernel = config["kernel"]
    bounds = capability.KERNEL_LIMITS
    if len(source.data) > bounds["input_bytes"] or len(certificate.data) > bounds["certificate_bytes"]:
        raise Failure("ResourceOut", "Captured pair exceeds this kernel replay profile's byte cap", "kernel")
    workspace = KernelWorkspace(supervisor, root, storage)
    try:
        workspace.stage_library({"proof_library": kernel["library"]})
        helpers, modules = workspace.native / "helpers", workspace.native / "modules"
        helpers.mkdir()
        modules.mkdir()
        for name, pin in kernel["helpers"].items():
            workspace.copy_file(Path(pin["path"]), helpers / name, pin["sha256"])
        emitter = capability.HERE / "emit_replay.py"
        workspace.copy_file(emitter, helpers / "emit_replay.py", config["runtime_source_sha256"][str(emitter)])
        source.verify(supervisor.check)
        certificate.verify(supervisor.check)
        process, stdout, stderr = supervisor.run("kernel-generate",
            [config["python"]["path"], str(helpers / "emit_replay.py"), str(helpers),
             source.argument, certificate.argument, str(modules)], workspace.native / "generate",
            workspace.native, (source.fd, certificate.fd))
        code = protocol.normal_exit(process)
        if code == 5 and not stdout and stderr == b"ResourceLimit: kernel replay profile bound exceeded\n":
            raise Failure("ResourceOut", "Kernel replay profile bound exceeded", "kernel-generate")
        if code or stdout or stderr:
            raise Failure("Error", "Kernel witness generator failed", "kernel-generate")
        emitted = capability.strict_json(read_regular(modules / "emitted.json", 4096, supervisor.check).decode("utf-8"))
        if set(emitted) != {"modules", "input_bytes", "certificate_bytes", "certificate_nodes"} or emitted["modules"] != list(MODULES):
            raise Failure("Error", "Generated module inventory differs", "kernel-generate")
        if (emitted["input_bytes"] != len(source.data) or emitted["certificate_bytes"] != len(certificate.data)
                or type(emitted["certificate_nodes"]) is not int or not 0 <= emitted["certificate_nodes"] <= bounds["certificate_nodes"]):
            raise Failure("Error", "Generated replay metadata differs", "kernel-generate")
        if {p.name for p in modules.iterdir()} != {name + ".lean" for name in MODULES} | {"emitted.json"}:
            raise Failure("Error", "Unexpected generated artifact", "kernel-generate")
        generator = load_helper(helpers / "generate.py", "fang_fof_pinned_generator")
        auditor = load_helper(helpers / "axiom_audit.py", "fang_fof_pinned_auditor")
        # This audit is constructed separately from the captured pair, not read
        # from child output or supplied with the candidate certificate.
        (modules / (AUDIT + ".lean")).write_text(generator.audit_source(source.data, certificate.data), encoding="utf-8", newline="\n")
        source_hashes, generated_bytes = {}, 0
        for name in (*MODULES, AUDIT):
            data = read_regular(modules / (name + ".lean"), bounds["generated_bytes"], supervisor.check)
            generated_bytes += len(data)
            source_hashes[name] = hashlib.sha256(data).hexdigest()
        if generated_bytes > bounds["generated_bytes"]:
            raise Failure("ResourceOut", "Generated replay exceeds the profile byte cap", "kernel-generate")
        environment = child_environment() | {"LEAN_PATH": str(modules) + ":" + str(workspace.library), "LEAN_NUM_THREADS": "1"}
        results = None
        for name in (*MODULES, AUDIT):
            stage = "kernel-" + name.lower()
            command = [config["python"]["path"], "-c",
                "import os,sys; os.chdir(sys.argv[1]); os.execv(sys.argv[2],sys.argv[2:])",
                str(modules), kernel["lean"]["path"], "-j1", "-M" + str(min(2048, supervisor.limits.memory_mib)),
                "-o", str(modules / (name + ".olean")), str(modules / (name + ".lean"))]
            process, stdout, stderr = supervisor.run(stage, command, workspace.native / stage,
                                                     workspace.native, environment=environment)
            if protocol.normal_exit(process) != 0 or stderr:
                raise Failure("Error", "Fresh kernel replay did not pass", stage)
            if name == AUDIT:
                results = exact_audits(stdout, auditor)
            elif stdout:
                raise Failure("Error", "Unexpected kernel diagnostic", stage)
            if not (modules / (name + ".olean")).is_file():
                raise Failure("Error", "Kernel module artifact missing", stage)
        expected = {"modules/" + name + ".lean": digest for name, digest in source_hashes.items()}
        for name, pin in kernel["helpers"].items():
            expected["helpers/" + name] = pin["sha256"]
        expected["helpers/emit_replay.py"] = config["runtime_source_sha256"][str(emitter)]
        source.verify(supervisor.check)
        certificate.verify(supervisor.check)
        workspace.verify_library()
        workspace.archive(expected)
        workspace.cleanup()
        supervisor.check("kernel-archived")
        return {"profile": capability.KERNEL_PROFILE, "audited_theorems": results,
            "module_source_sha256": source_hashes, "certificate_nodes": emitted["certificate_nodes"],
            "fresh_instance": True, "source_sha256": source.sha256, "certificate_sha256": certificate.sha256,
            "scope": "Fresh exact-byte Lean kernel instance; compiled execution and direct Rust verification remain separate"}
    except Exception as error:
        workspace.retain_failure(error)
        raise
