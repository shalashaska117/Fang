"""Create/check local experimental capability pins; no implicit build or install."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import argparse
import hashlib
import json
from pathlib import Path
import stat
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
SCHEMA = "fang-ground-fof-capability-v1"
KERNEL_SCHEMA = "fang-ground-fof-capability-v2"
TSTP_SCHEMA = "fang-ground-fof-tstp-capability-v2"
KERNEL_PROFILE = "exact-v2-ground-fof-replay-v1"
KERNEL_LIMITS = {"input_bytes": 4096, "certificate_bytes": 65536,
                 "certificate_nodes": 100, "generated_bytes": 16 << 20}
LANGUAGE = "mixed-cnf-ground-fof-v1"
ENVELOPE = "fang-proof-2/ground-fof-distributive-v1"
MAX_BYTES = 1 << 20


def digest(path, check=lambda: None):
    path = Path(path)
    check()
    if not stat.S_ISREG(path.lstat().st_mode):
        raise ValueError("Pin must identify a regular file: " + str(path))
    result = hashlib.sha256()
    with path.open("rb") as stream:
        while block := stream.read(65536):
            check()
            result.update(block)
    return result.hexdigest()


def strict_json(data):
    def pairs(items):
        value = {}
        for key, item in items:
            if key in value:
                raise ValueError("Duplicate capability field")
            value[key] = item
        return value
    return json.loads(data, object_pairs_hook=pairs,
        parse_constant=lambda value: (_ for _ in ()).throw(ValueError("Nonfinite JSON value")))


def record(path):
    path = Path(path).absolute()
    return {"path": str(path), "sha256": digest(path)}


def inventory(root, check=lambda: None):
    root = Path(root)
    if not root.is_dir() or root.is_symlink():
        raise ValueError("Library must be a real directory")
    result = {}
    for path in sorted(root.rglob("*")):
        check()
        if path.is_symlink():
            raise ValueError("Library contains a symlink")
        if path.is_file():
            result[path.relative_to(root).as_posix()] = digest(path, check)
        elif not path.is_dir():
            raise ValueError("Library contains a nonregular member")
    return result


def runtime_sources():
    return sorted([*HERE.glob("*.py"), *(ROOT / "tools/fang_szs").glob("*.py")])


def verify(config, check=lambda: None):
    keys = {"schema", "language", "certificate", "profiles", "outputs", "max_input_bytes",
            "max_certificate_bytes", "engine", "checker", "python", "proof_library",
            "runtime_source_sha256", "dependency_source_sha256", "receipts"}
    exporting = config.get("schema") == TSTP_SCHEMA
    kernel = config.get("schema") in (KERNEL_SCHEMA, TSTP_SCHEMA)
    if kernel:
        keys.add("kernel")
    if exporting:
        keys.add("exporter")
    if set(config) != keys or config["schema"] not in (SCHEMA, KERNEL_SCHEMA, TSTP_SCHEMA) or config["language"] != LANGUAGE or config["certificate"] != ENVELOPE:
        raise ValueError("Unsupported FOF capability schema")
    if config["profiles"] != (["kernel", "compiled"] if kernel else ["compiled"]) or config["outputs"] != (["status", "tstp"] if exporting else ["status"]):
        raise ValueError("Unimplemented checking/output capability")
    if config["max_input_bytes"] != MAX_BYTES or config["max_certificate_bytes"] != MAX_BYTES:
        raise ValueError("Capability differs from the actual checker byte limits")
    for name in ("engine", "checker", "python"):
        pin = config[name]
        if set(pin) != {"path", "sha256"} or not Path(pin["path"]).is_absolute() or digest(pin["path"], check) != pin["sha256"]:
            raise ValueError("Executable pin changed: " + name)
    if digest(Path(sys.executable).resolve(), check) != config["python"]["sha256"]:
        raise ValueError("Running Python differs from capability")
    expected = {str(p): digest(p, check) for p in runtime_sources()}
    if expected != config["runtime_source_sha256"]:
        raise ValueError("Running adapter/shared helper source changed")
    sources = config["dependency_source_sha256"]
    if not isinstance(sources, dict) or not sources:
        raise ValueError("Missing reviewed dependency source closure")
    for path, value in sources.items():
        if not Path(path).is_absolute() or digest(path, check) != value:
            raise ValueError("Dependency source changed: " + path)
    library = config["proof_library"]
    if set(library) != {"path", "files_sha256"} or not Path(library["path"]).is_absolute() or inventory(library["path"], check) != library["files_sha256"]:
        raise ValueError("Checked library inventory changed")
    for name in ("Fang/FOF/VersionedCheck.olean", "Fang/FOF/FOFByteSemantics.olean", "Fang/FOF/FofCertificateInput.olean"):
        if name not in library["files_sha256"]:
            raise ValueError("Required checked FOF module missing: " + name)
    if not isinstance(config["receipts"], list) or not config["receipts"]:
        raise ValueError("Missing build/proof receipt pins")
    for pin in config["receipts"]:
        if set(pin) != {"path", "sha256"} or not Path(pin["path"]).is_absolute() or digest(pin["path"], check) != pin["sha256"]:
            raise ValueError("Build/proof receipt changed")
    if kernel:
        verify_kernel(config["kernel"], check)
    if exporting:
        build = verify_exporter(config["exporter"], check)
        if (config["dependency_source_sha256"] != config["exporter"]["sources_sha256"]
                or config["proof_library"]["files_sha256"] != build["library_sha256"]
                or config["python"] != build.get("python")):
            raise ValueError("Exporter and checker source/library linkage differs")
        verify_portable_links(config, build)


def verify_portable_links(config, build):
    """Bind every executing checker path to the same completed source build."""
    receipt = config["exporter"]["build_receipt"]
    installed = Path(receipt["path"]).parent
    info = build["fof"]["toolchain"]
    for key, binary in (("engine", "fang-ground-fof-driver"), ("checker", "fang-fof-check")):
        expected = {"path": str(installed / "bin" / binary),
                    "sha256": build["fof"]["binaries_sha256"][binary]}
        if config[key] != expected:
            raise ValueError("Executing FOF binary differs from its build: " + key)
    library = {"path": str(installed / "proof-library"), "files_sha256": build["library_sha256"]}
    kernel = config["kernel"]
    if (config["proof_library"] != library or kernel["library"] != library
            or kernel["receipt"] != receipt or config["receipts"] != [receipt]):
        raise ValueError("Kernel library/receipt differs from its build")
    expected_helpers = {name: {
        "path": str(installed / "source/tools/replay" / filename),
        "sha256": build["source_sha256"]["tools/replay/" + filename]}
        for name, filename in (("generate.py", "fof_replay.py"),
                               ("source_witness.py", "source_witness.py"),
                               ("axiom_audit.py", "axiom_audit.py"))}
    expected_tree = {"path": info["path"], "inventory": {
        "path": info["inventory"], "sha256": info["inventory_sha256"]}, "receipt": receipt}
    expected_lean = {"path": str(Path(info["path"]) / "bin/lean"), "sha256": info["lean_sha256"]}
    if (kernel["helpers"] != expected_helpers or kernel["toolchain"] != expected_tree
            or kernel["lean"] != expected_lean or info.get("verified_before_and_after") is not True):
        raise ValueError("Kernel helpers/toolchain differ from their build")


def verify_exporter(exporter, check=lambda: None):
    if set(exporter) != {"path", "sha256", "sources_sha256", "proof_receipt", "build_receipt"}:
        raise ValueError("Unsupported exporter capability")
    if not Path(exporter["path"]).is_absolute() or digest(exporter["path"], check) != exporter["sha256"]:
        raise ValueError("Exporter executable changed")
    for name in ("proof_receipt", "build_receipt"):
        pin = exporter[name]
        if set(pin) != {"path", "sha256"} or not Path(pin["path"]).is_absolute() or digest(pin["path"], check) != pin["sha256"]:
            raise ValueError("Exporter receipt changed: " + name)
    proof = strict_json(Path(exporter["proof_receipt"]["path"]).read_text())
    build = strict_json(Path(exporter["build_receipt"]["path"]).read_text())
    installation = Path(exporter["build_receipt"]["path"]).parent
    if (proof.get("status") != "passed" or build.get("status") != "built-and-checked"
            or build.get("proof_suite_sha256") != exporter["proof_receipt"]["sha256"]
            or build.get("proof_suite") != exporter["proof_receipt"]["path"]
            or exporter["path"] != str(installation / "bin/fang-fof-tstp-export")
            or build.get("fof", {}).get("binaries_sha256", {}).get("fang-fof-tstp-export") != exporter["sha256"]
            or build.get("library_sha256") != proof.get("build_output_sha256")):
        raise ValueError("Exporter source/build/proof linkage differs")
    required = "Fang.FofTstpExport.RenderProof.decoded_render_checked_text"
    matching = [row for row in proof.get("axiom_audits", [])
                if row.get("module") == "Fang.FOF.TSTP.Audit" and row.get("declaration") == required]
    if (len(matching) != 1 or not set(matching[0].get("axioms", [])) <= {"propext", "Classical.choice", "Quot.sound"}
            or build["fof"].get("exporter", {}).get("theorem") != required):
        raise ValueError("Exporter proof lacks its connected text theorem")
    sources = exporter["sources_sha256"]
    source_root = installation / "source"
    relative_sources = build.get("source_sha256", {})
    if (not relative_sources or any(Path(name).is_absolute() or ".." in Path(name).parts
                                   for name in relative_sources)):
        raise ValueError("Invalid built source inventory")
    expected = {str(source_root / name): value for name, value in relative_sources.items()}
    required_sources = {"lean/Fang/FOF/TstpExport.lean", "lean/FofTstpMain.lean",
                        "lean/Fang/BoundedInput.lean", "proofs/fof-tstp/CheckedText.lean",
                        "proofs/fof-tstp/Audit.lean", "tools/fof_proof_inventory.json"}
    if sources != expected or not required_sources <= relative_sources.keys():
        raise ValueError("Exporter source closure differs")
    for path, value in sources.items():
        if not Path(path).is_absolute() or digest(path, check) != value:
            raise ValueError("Exporter source changed: " + path)
    # Every compiled Lean source must match the same captured source package.
    checked_sources = {}
    for name, value in relative_sources.items():
        if name.startswith("lean/") and (name.endswith(".lean") or name in
                {"lean/lean-toolchain", "lean/lakefile.toml", "lean/check-local.sh"}):
            target = name.removeprefix("lean/")
        elif name.startswith("proofs/fof-tstp/") and name.endswith(".lean"):
            target = "Fang/FOF/TSTP/" + name.removeprefix("proofs/fof-tstp/")
        elif name.startswith("proofs/tstp/") and name.endswith(".lean"):
            target = name.removeprefix("proofs/tstp/")
        else:
            continue
        if target in checked_sources:
            raise ValueError("Duplicate checked proof module")
        checked_sources[target] = value
    if proof.get("source_sha256") != checked_sources:
        raise ValueError("Checked proof sources differ from the build")
    if (relative_sources["tools/fof_proof_inventory.json"]
            != build["fof"]["exporter"].get("inventory_sha256")):
        raise ValueError("Required exporter proof inventory changed")
    import fof_tstp_setup
    fof_tstp_setup.check_proofs(source_root, proof)
    return build


def verify_kernel(kernel, check=lambda: None):
    if set(kernel) != {"profile", "lean", "library", "helpers", "limits", "receipt", "toolchain"} or kernel["profile"] != KERNEL_PROFILE:
        raise ValueError("Unsupported kernel capability")
    if kernel["limits"] != KERNEL_LIMITS:
        raise ValueError("Kernel replay bounds differ")
    for name in ("lean", "receipt"):
        pin = kernel[name]
        if set(pin) != {"path", "sha256"} or not Path(pin["path"]).is_absolute() or digest(pin["path"], check) != pin["sha256"]:
            raise ValueError("Kernel pin changed: " + name)
    helpers = kernel["helpers"]
    if set(helpers) != {"generate.py", "source_witness.py", "axiom_audit.py"}:
        raise ValueError("Kernel helper inventory differs")
    for name, pin in helpers.items():
        if set(pin) != {"path", "sha256"} or not Path(pin["path"]).is_absolute() or digest(pin["path"], check) != pin["sha256"]:
            raise ValueError("Kernel helper changed: " + name)
    library = kernel["library"]
    if set(library) != {"path", "files_sha256"} or not Path(library["path"]).is_absolute() or inventory(library["path"], check) != library["files_sha256"]:
        raise ValueError("Kernel library inventory changed")
    if not {"Fang/FOF/Replay.olean", "Fang/FOF/VersionedCheck.olean", "Fang/FOF/FOFByteSemantics.olean"} <= library["files_sha256"].keys():
        raise ValueError("Kernel library lacks the required checked modules")
    tree = kernel["toolchain"]
    if set(tree) != {"path", "inventory", "receipt"} or Path(tree["path"]) != Path(kernel["lean"]["path"]).parent.parent:
        raise ValueError("Toolchain root differs from Lean's installed sysroot")
    for name in ("inventory", "receipt"):
        pin = tree[name]
        if set(pin) != {"path", "sha256"} or not Path(pin["path"]).is_absolute() or digest(pin["path"], check) != pin["sha256"]:
            raise ValueError("Toolchain inventory/receipt pin changed")
    import toolchain
    expected = strict_json(Path(tree["inventory"]["path"]).read_text())
    toolchain.verify(tree["path"], expected, check)


def kernel_from_receipt(path, toolchain_inventory, toolchain_receipt):
    """Pin the retained helper/library bytes of a reviewed generic replay run."""
    receipt = strict_json(Path(path).read_text())
    if (receipt.get("status") != "passed" or receipt.get("accepted_instances") != 12
            or receipt.get("rejected_replays") != 6 or receipt.get("audits") != 60):
        raise ValueError("Generic replay receipt does not satisfy its declared gate")
    native = Path(receipt["native_workspace_retained"])
    tools = receipt["input_helper_tool_sha256"]
    lean = [name for name in tools if Path(name).name == "lean"]
    if len(lean) != 1:
        raise ValueError("Generic replay receipt lacks one Lean executable")
    helpers = {}
    for name in ("generate.py", "source_witness.py", "axiom_audit.py"):
        matches = [digest for path, digest in tools.items() if Path(path).name == name]
        if len(matches) != 1:
            raise ValueError("Generic replay receipt has ambiguous helper pins")
        helpers[name] = {"path": str(native / "helpers" / name), "sha256": matches[0]}
    result = {"profile": KERNEL_PROFILE, "limits": dict(KERNEL_LIMITS),
        "lean": {"path": lean[0], "sha256": tools[lean[0]]}, "helpers": helpers,
        "library": {"path": str(native / "library"), "files_sha256": receipt["library_sha256"]},
        "receipt": record(path), "toolchain": {"path": str(Path(lean[0]).parent.parent),
            "inventory": record(toolchain_inventory), "receipt": record(toolchain_receipt)}}
    verify_kernel(result)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("engine", "checker", "library", "out"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--receipt", type=Path, action="append", required=True)
    parser.add_argument("--source", type=Path, action="append", required=True,
                        help="Exact reviewed dependency source; repeat for the full closure")
    parser.add_argument("--kernel-receipt", type=Path,
                        help="Reviewed generic replay receipt; enables the explicit v2 kernel capability")
    parser.add_argument("--toolchain-inventory", type=Path)
    parser.add_argument("--toolchain-receipt", type=Path)
    args = parser.parse_args()
    config = {"schema": SCHEMA, "language": LANGUAGE, "certificate": ENVELOPE,
        "profiles": ["compiled"], "outputs": ["status"], "max_input_bytes": MAX_BYTES,
        "max_certificate_bytes": MAX_BYTES, "engine": record(args.engine), "checker": record(args.checker),
        "python": record(Path(sys.executable).resolve()),
        "proof_library": {"path": str(args.library.absolute()), "files_sha256": inventory(args.library)},
        "runtime_source_sha256": {str(p): digest(p) for p in runtime_sources()},
        "dependency_source_sha256": {str(p.absolute()): digest(p) for p in args.source},
        "receipts": [record(path) for path in args.receipt]}
    if args.kernel_receipt:
        if not args.toolchain_inventory or not args.toolchain_receipt:
            parser.error("Kernel capability requires the reviewed full toolchain inventory and receipt")
        config.update(schema=KERNEL_SCHEMA, profiles=["kernel", "compiled"],
                      kernel=kernel_from_receipt(args.kernel_receipt, args.toolchain_inventory, args.toolchain_receipt))
    verify(config)
    with args.out.open("x", encoding="utf-8") as stream:
        json.dump(config, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"status": "pinned", "capability": str(args.out), "sha256": digest(args.out)}))


if __name__ == "__main__":
    main()
