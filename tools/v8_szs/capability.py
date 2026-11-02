"""The installed version-8 capability: pinned engine, checker, interpreter, adapter sources and provenance.

Absent optional sections mean the feature is not installed. The adapter rejects
such requests before search; later work adds the section without changing the
rest of the schema. The `bundle` section, when present, pins the bundle producer
and checker for axiom-only inputs with include directives, distinct objects or annotations;
the `signed` section pins the signed bundle producer and checker for inputs
with roles other than axiom; the `tstp` section pins the single-file TSTP
exporter and, when installed, the bundle exporter (`bundle_exporter`) and the
conjecture exporter (`goal_exporter`). Every binary is built from the repository
at install time.

`provenance` pins the installation's copies of the source maps, the audit list,
the backend pins and the build manifests. The maps name the receipts every
source came from, as data; installation reads no receipt.

Verification is split by when it runs (PER_RUN, also written into every
capability): `verify` hashes every pinned file and is used at install time and
by `fang --self-check`; a run hashes only what it will execute (`verify_run`)
and afterwards compares those files' identities (`check_identities`).

`default_check` records the checking mode a run uses when `--check` is not
given: the compiled checker (docs/USAGE.md). Kernel replay is opt-in and needs
at least KERNEL_MINIMUMS.
"""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import hashlib
import os
from pathlib import Path
import stat

SCHEMA = "fang-v8-capability-v6"
LANGUAGE = "expanded-fof-equality-skolem-distributive-v1"
MAX_BYTES = 1 << 20
DEFAULT_CHECK = "compiled"
# Limits that --check kernel needs, as (option, argument attribute, minimum).
KERNEL_MINIMUMS = (("--wall-seconds", "wall_seconds", 600), ("--memory-mib", "memory_mib", 4096),
                   ("--max-artifact-bytes", "max_artifact_bytes", 1 << 30))
HERE = Path(__file__).resolve().parent
# Features an installation may lack; None means not installed in this capability.
OPTIONAL = ()
REQUIRED = {"schema", "language", "certificate_version", "max_input_bytes", "max_certificate_bytes",
            "engine", "checker", "python", "runtime_source_sha256", "provenance", "bundle", "signed", "tstp",
            "per_run_verification", "default_check", "kernel"}
# The kernel section: the witness binary, the kernel entry and its installation record, and the run root.
KERNEL_FIELDS = {"witness", "entry", "installation", "output_root"}
PER_RUN = {
    "before_execution": "SHA-256 of the Python interpreter, every adapter source and the binaries of the chosen path "
                        "(single file: engine and checker, plus the exporter when TSTP is requested; with --check "
                        "kernel, engine, witness, kernel entry and its installation record instead of the checker; "
                        "bundle: bundle producer and checker, plus the bundle exporter when TSTP is requested; signed: "
                        "signed producer and checker), each before it runs.",
    "after_execution": "Before a positive status, each file hashed before execution must keep its device, inode, "
                       "size, mtime_ns and ctime_ns. ctime cannot be set by a user, so an in-place rewrite that "
                       "restores mtime is still seen.",
    "not_per_run": "Provenance records and the binaries of paths the run does not take. A change to them cannot affect the "
                   "run's result; it is found when that path runs, by fang --self-check, or at install time.",
    "full": "Install time and fang --self-check hash every pinned file and every adapter source.",
    "why": "Hashes detect artifact changes; they do not prove correct execution, and artifact identity is trusted "
           "(docs/DESIGN.md). Hashing the seven installed binaries twice per run cost several seconds without "
           "covering anything the run executes beyond the files listed above.",
}


def _hash_descriptor(descriptor, path, check, limit):
    info = os.fstat(descriptor)
    if not stat.S_ISREG(info.st_mode) or info.st_size > limit:
        raise ValueError("Pinned dependency is not a bounded regular file: " + str(path))
    hasher, remaining = hashlib.sha256(), limit + 1
    while remaining:
        check()
        data = os.read(descriptor, min(1 << 20, remaining))
        if not data:
            return hasher.hexdigest(), info
        hasher.update(data)
        remaining -= len(data)
    raise ValueError("Pinned dependency grew beyond its bound: " + str(path))


def digest(path, check=lambda: None, limit=512 << 20):
    descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
    try:
        return _hash_descriptor(descriptor, path, check, limit)[0]
    finally:
        os.close(descriptor)


def identity(info):
    return [info.st_dev, info.st_ino, info.st_size, info.st_mtime_ns, info.st_ctime_ns]


def runtime_sources():
    """Adapter sources that run in-process; the installation pins each one."""
    return sorted([*HERE.glob("*.py"), *(HERE.parent / "fang_szs").glob("*.py")])


def pinned_records(config):
    yield config["engine"]
    yield config["checker"]
    yield config["python"]
    yield from config["provenance"]
    for name in ("bundle", "signed"):
        if config[name] is not None:
            yield config[name]["producer"]
            yield config[name]["checker"]
    if config["tstp"] is not None:
        yield config["tstp"]["exporter"]
        if "bundle_exporter" in config["tstp"]:
            yield config["tstp"]["bundle_exporter"]
        if "goal_exporter" in config["tstp"]:
            yield config["tstp"]["goal_exporter"]
    if config["kernel"] is not None:
        yield config["kernel"]["witness"]
        yield config["kernel"]["entry"]
        yield config["kernel"]["installation"]


def run_records(config, route, tstp=False, kernel=False):
    """The pinned binaries that a run on `route` executes."""
    if route == "single" and kernel:
        return [config["engine"], config["kernel"]["witness"], config["kernel"]["entry"], config["kernel"]["installation"]]
    if route == "single":
        return [config["engine"], config["checker"]] + ([config["tstp"]["exporter"]] if tstp else [])
    if route == "bundle" and tstp:
        return [config["bundle"]["producer"], config["bundle"]["checker"], config["tstp"]["bundle_exporter"]]
    if route == "signed" and tstp:
        return [config["signed"]["producer"], config["signed"]["checker"], config["tstp"]["goal_exporter"]]
    return [config[route]["producer"], config[route]["checker"]]


def check_fields(config):
    """Schema and structure only; no file is read."""
    if set(config) != REQUIRED:
        raise ValueError("Unexpected version-8 capability fields")
    if (config["schema"] != SCHEMA or config["language"] != LANGUAGE or config["certificate_version"] != 8
            or config["max_input_bytes"] != MAX_BYTES or config["max_certificate_bytes"] != MAX_BYTES
            or config["per_run_verification"] != PER_RUN or config["default_check"] != DEFAULT_CHECK):
        raise ValueError("Unsupported version-8 capability")
    if config["kernel"] is not None and (not isinstance(config["kernel"], dict) or set(config["kernel"]) != KERNEL_FIELDS
                                         or not isinstance(config["kernel"]["output_root"], str)):
        raise ValueError("Unexpected kernel capability fields")
    for name in ("bundle", "signed"):
        if config[name] is not None and set(config[name]) != {"producer", "checker"}:
            raise ValueError("Unexpected " + name + " capability fields")
    if config["tstp"] is not None and not {"exporter"} <= set(config["tstp"]) <= {"exporter", "bundle_exporter", "goal_exporter"}:
        raise ValueError("Unexpected tstp capability fields")
    if any(set(record) != {"path", "sha256"} for record in pinned_records(config)):
        raise ValueError("Unexpected pinned record fields")


def verify(config, check=lambda: None):
    """Full verification: every pinned file and every adapter source (install time and fang --self-check)."""
    check_fields(config)
    for record in pinned_records(config):
        if digest(record["path"], check) != record["sha256"]:
            raise ValueError("Pinned version-8 dependency changed: " + str(record.get("path")))
    actual = {str(path): digest(path, check) for path in runtime_sources()}
    if actual != config["runtime_source_sha256"]:
        raise ValueError("Running version-8 adapter sources differ from the installation")
    return sum(1 for _ in pinned_records(config)) + len(actual)


def verify_run(config, records, check=lambda: None):
    """Hash what this run executes before it runs; return each file's identity at the moment it was hashed."""
    expected = [(record["path"], record["sha256"]) for record in [config["python"], *records]]
    expected += list(config["runtime_source_sha256"].items())
    if sorted(config["runtime_source_sha256"]) != sorted(str(path) for path in runtime_sources()):
        raise ValueError("Running version-8 adapter sources differ from the installation")
    identities = {}
    for path, pin in expected:
        descriptor = os.open(path, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK)
        try:
            value, info = _hash_descriptor(descriptor, path, check, 512 << 20)
            if value != pin or identity(os.fstat(descriptor)) != identity(info):
                raise ValueError("Pinned version-8 dependency changed: " + str(path))
        finally:
            os.close(descriptor)
        identities[str(path)] = identity(info)
    return identities


def check_identities(identities, check=lambda: None):
    """After execution: every file hashed before the run must still be the same inode, unmodified."""
    for path, expected in identities.items():
        check()
        if identity(os.stat(path, follow_symlinks=False)) != expected:
            raise ValueError("Executed version-8 dependency changed during the run: " + path)
