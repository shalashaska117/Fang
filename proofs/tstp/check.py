#!/usr/bin/env python3
"""Replay the complete TSTP text proof from source against a fresh installation."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tempfile

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
ROOT = Path(__file__).resolve().parents[2]

# This ordered source map is the release recipe. No historical evidence is read.
MODULES = [
    'lean/TstpExport.lean',
    'proofs/tstp/Acceptance.lean',
    'proofs/tstp/Rows.lean',
    'proofs/tstp/SourceLink.lean',
    'proofs/tstp/Trace.lean',
    'proofs/tstp/BuilderLoop.lean',
    'proofs/tstp/Witness.lean',
    'proofs/tstp/Process.lean',
    'proofs/tstp/Invariant.lean',
    'proofs/tstp/Names.lean',
    'proofs/tstp/Freshness.lean',
    'proofs/tstp/DerivedState.lean',
    'proofs/tstp/DerivedProcess.lean',
    'proofs/tstp/Derivation.lean',
    'proofs/tstp/Origins.lean',
    'proofs/tstp/Pruning.lean',
    'proofs/tstp/Leaves.lean',
    'proofs/tstp/ExportProvenance.lean',
    'proofs/tstp/QuotedAtom.lean',
    'proofs/tstp/TermRendering.lean',
    'proofs/tstp/VariableNames.lean',
    'proofs/tstp/TermParsing.lean',
    'proofs/tstp/LiteralParsing.lean',
    'proofs/tstp/ClauseParsing.lean',
    'proofs/tstp/AnnotationGrammar.lean',
    'proofs/tstp/WitnessMetadata.lean',
    'proofs/tstp/SourceMetadata.lean',
    'proofs/tstp/AnnotatedRows.lean',
    'proofs/tstp/NamedSemantics.lean',
    'proofs/tstp/ActualComposition.lean',
    'proofs/tstp/ProvenanceComposition.lean',
    'proofs/tstp/Controls.lean',
    'proofs/tstp/Audit.lean',
    'proofs/tstp/LeafText.lean',
    'proofs/tstp/AnnotationLexer.lean',
    'proofs/tstp/AnnotationParser.lean',
    'proofs/tstp/AnnotationMembership.lean',
    'proofs/tstp/BodyPrefix.lean',
    'proofs/tstp/SourceLexerBridge.lean',
    'proofs/tstp/BodyBridge.lean',
    'proofs/tstp/RowUniqueness.lean',
    'proofs/tstp/SequenceUniqueness.lean',
    'proofs/tstp/BridgeAudit.lean',
    'proofs/tstp/FinalComposition.lean',
    'proofs/tstp/FinalAudit.lean',
]
TEXT_AUDITS = {"Fang.TstpText." + name for name in (
    "quote_grammar", "decodeQuoted_correct", "QuotedAtom.functional", "quote_roundtrip",
    "quote_utf8_roundtrip", "quote_injective", "symbol_correspondence", "term_correspondence",
    "terms_correspondence", "literal_correspondence", "variable_name_valid", "variable_name_grammar",
    "variable_name_injective", "TermBytesParse.unique", "term_byte_correspondence",
    "LiteralBytesParse.unique", "literal_byte_correspondence", "ClauseBytesParse.unique",
    "clause_byte_correspondence", "natural_spelling", "NaturalSpelling.functional",
    "witness_term_correspondence", "witness_terms_correspondence", "witness_correspondence",
    "source_correspondence", "SourceMeaning.record", "row_correspondence", "render_correspondence",
    "NamedTerm.eval", "NamedTerms.eval", "NamedLiteral.holds", "NamedClause.valid",
    "render_derivation_valid", "render_original_models", "rendered_final_false",
    "built_render_original_models", "export_text_correspondence", "export_traced_rows")}
CONTROLS = {"Fang.TstpText.Controls." + name for name in (
    "escaped_quote_and_slash", "empty_label_rejected", "newline_label_rejected",
    "nonascii_label_rejected", "bare_quote_rejected", "unknown_escape_rejected",
    "ordered_nested_term", "wrong_arity_rejected")}
BRIDGE_AUDITS = {"Fang.TstpText." + name for name in (
    "source_lexeme", "source_tokenization", "SourcePrefix.head", "body_prefix", "clause_prefix",
    "ParsedRow.unique", "AnnotatedRowText.prefix", "AnnotatedRowText.prefix_unique",
    "AnnotatedRowText.functional", "ParsedRows.unique", "printed_rows_parse", "printed_rows_unique",
    "correspondence_printed_rows")}
FINAL_AUDITS = {"Fang.TstpText." + name for name in (
    "rows_original_semantics", "rows_with_leaves", "export_complete_text")}
AUDITS = {"Audit": TEXT_AUDITS | CONTROLS, "BridgeAudit": BRIDGE_AUDITS, "FinalAudit": FINAL_AUDITS}


def digest(path):
    if path.is_symlink() or not path.is_file() or path.stat().st_size > 64 << 20:
        raise ValueError("Expected bounded regular file: " + str(path))
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--installation", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    if sys.platform != "linux":
        parser.error("Use Linux or WSL")
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=False)
    native = Path(tempfile.mkdtemp(prefix="fang-tstp-release-proofs-", dir="/var/tmp"))
    source = native / "source"
    source.mkdir()
    installation = args.installation.resolve()
    config = json.loads(installation.read_text())
    lean = Path(config["lean"]["path"])
    inputs = [ROOT / relative for relative in MODULES]
    helpers = [ROOT / "tools/fang_szs" / name for name in
               ("__init__.py", "supervisor.py", "installation.py", "dependencies.py")]
    helpers.append(ROOT / "tools/replay/axiom_audit.py")
    pins = {str(p): digest(p) for p in [installation, lean, Path(sys.executable).resolve(),
                                      Path(__file__), *inputs, *helpers]}
    captured_helpers = native / "helpers"
    (captured_helpers / "fang_szs").mkdir(parents=True)
    for path in helpers:
        destination = captured_helpers / ("fang_szs" if path.parent.name == "fang_szs" else "") / path.name
        shutil.copyfile(path, destination)
        if digest(destination) != pins[str(path)]:
            raise ValueError("Captured helper differs before import: " + path.name)
    for path in inputs:
        destination = source / path.name
        shutil.copyfile(path, destination)
        if digest(destination) != pins[str(path)]:
            raise ValueError("Source changed during capture: " + path.name)
    sys.path.insert(0, str(captured_helpers))
    from fang_szs.installation import verify_installation
    from fang_szs.supervisor import Limits, Supervisor, child_environment
    from axiom_audit import audit_axioms
    supervisor = Supervisor(Limits(wall_seconds=300, memory_mib=4096,
                                   artifact_bytes=256 << 20, log_bytes=4 << 20))
    manifest = {"status": "running", "started_utc": datetime.now(timezone.utc).isoformat(),
        "scope": "Actual export, original leaves, ordered typed derivation, exact metadata, unique full-row and row-list parsing, original-model validity and final false clause; Lean definitions only.",
        "historical_evidence_required": False,
        "module_source_order": [str(p.relative_to(ROOT)) for p in inputs],
        "fixed_audit_sets": {k: sorted(v) for k, v in AUDITS.items()},
        "python_version": sys.version, "helpers_captured_before_import": True,
        "native_workspace": str(native), "native_workspace_retained": True,
        "input_helper_tool_sha256": pins, "stages": supervisor.records,
        "limits": {"whole_pipeline_wall_seconds": 300, "sampled_tree_rss_mib": 4096,
                   "artifact_bytes": 256 << 20, "per_stream_log_bytes": 4 << 20}}
    (out / "launch.json").write_text(json.dumps(manifest, indent=2) + "\n")
    try:
        verify_installation(config, supervisor.check)
        manifest["installation_verified_before"] = True
        env = child_environment()
        env.update(LEAN_PATH=str(source) + ":" + config["proof_library"]["path"], LEAN_NUM_THREADS="1")
        for module_path in MODULES:
            name = Path(module_path).stem
            command = ["/bin/sh", "-c", 'cd "$1" && shift && exec "$@"', "fang-tstp-release-proof",
                       str(source), str(lean), "-o", str(source / (name + ".olean")),
                       str(source / (name + ".lean"))]
            record, stdout, stderr = supervisor.run(name, command, native / name, native, environment=env)
            if record["classification"] != "completed" or record["exit_code"] != 0 or stderr:
                raise ValueError("Lean module failed: " + name)
            if name in AUDITS:
                audits = audit_axioms(stdout.decode(), AUDITS[name])
                if audits.keys() != AUDITS[name]:
                    raise ValueError("Unexpected fixed audit declaration set: " + name)
                manifest.setdefault("axiom_audits", {})[name] = audits
        if set(manifest.get("axiom_audits", {})) != set(AUDITS):
            raise ValueError("Missing fixed audit stage")
        verify_installation(config, supervisor.check)
        manifest["installation_verified_after"] = True
        if any(digest(Path(p)) != value for p, value in pins.items()):
            raise ValueError("Source, helper, installation or executable changed")
        if any(digest(source / p.name) != pins[str(p)] for p in inputs):
            raise ValueError("Captured source changed")
        for path in helpers:
            captured = captured_helpers / ("fang_szs" if path.parent.name == "fang_szs" else "") / path.name
            if digest(captured) != pins[str(path)]:
                raise ValueError("Captured helper changed")
        count = sum(len(names) for names in AUDITS.values())
        manifest.update(status="passed", modules=len(MODULES), theorem_audits=count,
                        general_theorems=count - len(CONTROLS), kernel_controls=len(CONTROLS))
    except Exception as error:
        manifest.update(status="failed", error=f"{type(error).__name__}: {error}")
    finally:
        supervisor.close()
        manifest["finished_utc"] = datetime.now(timezone.utc).isoformat()
        try:
            native_hashes = {p.relative_to(native).as_posix(): digest(p)
                             for p in sorted(native.rglob("*")) if p.is_file()}
            shutil.copytree(native, out / "run")
            archived = {p.relative_to(out / "run").as_posix(): digest(p)
                        for p in sorted((out / "run").rglob("*")) if p.is_file()}
            if native_hashes != archived:
                raise ValueError("Archive differs from native workspace")
            manifest.update(artifacts_sha256=archived, archive_hashes_verified=True)
        except Exception as error:
            manifest.update(status="failed", archive_error=str(error))
        shutil.copyfile(__file__, out / "check.py")
        (out / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: manifest.get(k) for k in ("status", "modules", "theorem_audits", "error")}))
    return int(manifest["status"] != "passed")


if __name__ == "__main__":
    raise SystemExit(main())
