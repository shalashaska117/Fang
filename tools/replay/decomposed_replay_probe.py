#!/usr/bin/env python3
"""Check cached lexer/node equations for the unchanged certificate decoder."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time
from source_witness import quote

parser = argparse.ArgumentParser()
parser.add_argument("source", type=Path)
parser.add_argument("--out", required=True, type=Path)
parser.add_argument("--lake", required=True)
parser.add_argument("--grouped", action="store_true")
parser.add_argument("--full", action="store_true")
parser.add_argument("--emit-only", action="store_true", help="Write proof sources without compiling or claiming verification")
args = parser.parse_args()
started = time.monotonic()
generator_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
root = Path(__file__).resolve().parents[2]
output = args.out.resolve()
output.mkdir(parents=True, exist_ok=False)
original = args.source.read_text()
proof = (args.source.parent / "proof.fang").read_bytes().decode("ascii")
source_text = (args.source.parent / "input.p").read_bytes().decode("ascii")
definition = original.split("theorem source_decodes", 1)[0].replace(
    "import Fang.CertificateInput", "import Fang.DecoderComposition")
matches = list(re.finditer(r"[A-Za-z0-9_$-]+|[(),.|~]", proof))
tokens = [(match.group(), match.start()) for match in matches]
assert len(proof) == len(proof.encode("ascii"))
assert re.sub(r"[A-Za-z0-9_$-]+|[(),.|~]|[ \t\n\r\f\v]", "", proof) == ""
starts = []
depth = 0
for index, (token, _) in enumerate(tokens):
    if token == "(":
        if depth == 1:
            starts.append(index)
        depth += 1
    elif token == ")":
        depth -= 1
assert tokens[starts[-1] + 1][0] == "final"

def token_source(items):
    return "[" + ", ".join("{ text := " + json.dumps(text) + ", offset := " + str(offset) + " }"
                           for text, offset in items) + "]"

def state_source(index):
    return "({ tokens := " + token_source(tokens[index:]) + ", endOffset := " + str(len(proof)) + " } : Frontend.State)"

def chars_source(text):
    return "[" + ", ".join(repr(char) for char in text) + "]"

options = "\nnamespace Fang.InstanceReplay\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\nset_option cbv.maxSteps 10000000\n\n"
ending = "\nend Fang.InstanceReplay\n"
modules = [("ReplayDefs", definition + ending)]
# These equations use the library's checked string theory. The generator's
# literal and character-list construction still have to agree in the kernel.
def character_equations(label, text, include_size_lemma=False):
    literal, characters = quote(text), chars_source(text)
    result = (f"@[cbv_eval] theorem {label}_characters : String.toList {literal} = {characters} := by\n"
              "  exact String.toList_ofList\n")
    if include_size_lemma:
        result += """theorem size_ofList (characters : List Char) :
    (String.ofList characters).utf8ByteSize = (characters.map Char.utf8Size).sum := by
  induction characters with
  | nil => rfl
  | cons c cs ih =>
    change (String.ofList ([c] ++ cs)).utf8ByteSize = _
    rw [String.ofList_append, String.utf8ByteSize_append,
      ← String.singleton_eq_ofList, String.utf8ByteSize_singleton, ih]
    rfl
"""
    result += (f"@[cbv_eval] theorem {label}_size : {literal}.utf8ByteSize = {len(text)} := by\n"
               f"  change (String.ofList {characters}).utf8ByteSize = {len(text)}\n"
               "  rw [size_ofList]\n  decide +kernel\n"
               f"#print axioms {label}_size\n#print axioms {label}_characters\n")
    return result

modules.append(("CertificateCharacters", "import ReplayDefs\n" + options
                + character_equations("certificate", proof, True) + ending))
previous = "CertificateCharacters"
# A suffix theorem is reusable only after the kernel has checked its equation.
# The generator's lexing and state construction are never assumed correct.
boundaries = [0] + [tokens[index][1] for index in starts]
boundaries = sorted(set(boundaries))
lexer_bodies = []
for number, offset in reversed(list(enumerate(boundaries))):
    prefix = proof[:offset]
    consumed_steps = len(re.findall(r"[A-Za-z0-9_$-]+|[(),.|~]|[ \t\n\r\f\v]", prefix))
    remaining_tokens = [(text, position) for text, position in tokens if position >= offset]
    name = f"Lexer{number}"
    theorem = f"lex_suffix_{number}"
    body = (f"@[cbv_eval] theorem {theorem} : Frontend.lexAux {len(proof) + 1 - consumed_steps} "
            + f"{chars_source(proof[offset:])} {offset} = .ok "
            + token_source(remaining_tokens) + " := by cbv\n"
            + f"#print axioms {theorem}\n")
    if args.grouped:
        lexer_bodies.append(body)
    else:
        modules.append((name, f"import {previous}\n" + options + body + ending))
        previous = name
if args.grouped:
    modules.append(("LexerProofs", f"import {previous}\n" + options + "\n".join(lexer_bodies) + ending))
    previous = "LexerProofs"

body = ("@[cbv_eval] theorem certificate_tokenizes : Frontend.tokenize " + quote(proof) + " = .ok "
        + token_source(tokens) + " :=\n  tokenize_of_characters _ _ _ certificate_characters "
        + "(by decide +kernel) lex_suffix_0\n#print axioms certificate_tokenizes\n")
modules.append(("CertificateTokens", f"import {previous}\n" + options + body + ending))
previous = "CertificateTokens"
end_state = state_source(len(tokens) - 1)
node_bodies = []
for number, token_index in reversed(list(enumerate(starts))):
    name = f"Node{number}"
    theorem = f"node_suffix_{number}"
    body = (f"@[cbv_eval] theorem {theorem} : CertificateInput.nodes {len(tokens) + 1 - number} {number} "
            + state_source(token_index) + f" = .ok ((certificate.steps.drop {number}, certificate.final), "
            + end_state + ") := by cbv\n" + f"#print axioms {theorem}\n")
    if args.grouped:
        node_bodies.append(body)
    else:
        modules.append((name, f"import {previous}\n" + options + body + ending))
        previous = name
if args.grouped:
    modules.append(("NodeProofs", f"import {previous}\n" + options + "\n".join(node_bodies) + ending))
    previous = "NodeProofs"
body = ("theorem certificate_decodes : decodeCertificate originalCertificate = .ok certificate :=\n"
        "  decodeCertificate_of_tokens _ _ _ { tokens := [], endOffset := " + str(len(proof))
        + " } certificate_tokenizes (by cbv)\n"
        "#print axioms certificate_decodes\n")
modules.append(("CertificateDecoded", f"import {previous}\n" + options + body + ending))
if args.full:
    source_proof = "theorem source_decodes" + original.split("theorem source_decodes", 1)[1].split(
        "theorem certificate_decodes", 1)[0]
    accepted_proof = "theorem accepted" + original.split("theorem accepted", 1)[1]
    modules.append(("SourceCharacters", "import CertificateDecoded\n" + options
                    + character_equations("source", source_text) + ending))
    token_pattern = r"[A-Za-z0-9_$-]+|[(),.|~]"
    source_matches = list(re.finditer(token_pattern, source_text))
    source_tokens = [(match.group(), match.start()) for match in source_matches]
    assert re.sub(token_pattern + r"|[ \t\n\r\f\v]", "", source_text) == ""
    source_boundaries = sorted({0, *(offset for token, offset in source_tokens if token == "cnf")})
    source_lexer = []
    for number, offset in reversed(list(enumerate(source_boundaries))):
        steps = len(re.findall(token_pattern + r"|[ \t\n\r\f\v]", source_text[:offset]))
        remaining = [(text, position) for text, position in source_tokens if position >= offset]
        source_lexer.append(
            f"@[cbv_eval] theorem source_lex_{number} : Frontend.lexAux {len(source_text) + 1 - steps} "
            + chars_source(source_text[offset:]) + f" {offset} = .ok " + token_source(remaining)
            + f" := by cbv\n#print axioms source_lex_{number}\n")
    source_lexer.append(
        "@[cbv_eval] theorem source_tokenizes : Frontend.tokenize " + quote(source_text)
        + " = .ok " + token_source(source_tokens) + " :=\n"
        "  tokenize_of_characters _ _ _ source_characters (by decide +kernel) source_lex_0\n"
        "#print axioms source_tokenizes\n")
    modules.append(("SourceLexer", "import SourceCharacters\n" + options + "\n".join(source_lexer) + ending))
    modules.append(("SourceDecoded", "import SourceLexer\n" + options + source_proof
                    + "#print axioms source_decodes\n" + ending))
    accepted, consequences = accepted_proof.split("theorem parsed_ast_unsat", 1)
    modules.append(("CertificateAccepted", "import SourceDecoded\n" + options + accepted
                    + "#print axioms accepted\n" + ending))
    modules.append(("CompleteReplay", "import CertificateAccepted\n" + options
                    + "theorem parsed_ast_unsat" + consequences))
if args.emit_only:
    for name, contents in modules:
        (output / (name + ".lean")).write_text(contents)
    (output / "emitted.json").write_text(json.dumps({
        "scope": "Untrusted generated proof sources; no compilation performed",
        "generator_sha256": generator_hash,
        "modules": [name for name, _ in modules],
    }, indent=2) + "\n")
    raise SystemExit(0)
records = []
for name, contents in modules:
    path = output / (name + ".lean")
    path.write_text(contents)
    timing = output / (name + ".time")
    command = ["/usr/bin/time", "-f", "%e %M", "-o", str(timing), args.lake,
               "env", "lean", "-M", "2048", "--root", str(output),
               "-o", str(path.with_suffix(".olean")), str(path)]
    phase_start = time.monotonic()
    process = subprocess.Popen(command, cwd=root / "lean", stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, text=True, start_new_session=True,
                               env=os.environ | {"LEAN_PATH": str(output)})
    try:
        stdout, stderr = process.communicate(timeout=max(0.01, 60 - (phase_start - started)))
        code = process.returncode
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        stdout, stderr = process.communicate()
        code = -1
    (output / (name + ".stdout")).write_text(stdout)
    (output / (name + ".stderr")).write_text(stderr)
    peak = 0
    if timing.exists():
        last = timing.read_text().splitlines()[-1:]
        if last and len(last[0].split()) == 2:
            peak = int(last[0].split()[1])
    record = {"module": name, "exit_code": code, "command": command,
              "elapsed_seconds": time.monotonic() - phase_start, "peak_rss_kib": peak,
              "axiom_report_has_no_sorry": "sorryAx" not in stdout,
              "source_sha256": hashlib.sha256(contents.encode()).hexdigest()}
    records.append(record)
    print(json.dumps({key: record[key] for key in ("module", "exit_code", "elapsed_seconds", "peak_rss_kib")}), flush=True)
    if code or peak > 2 * 1024 * 1024 or "sorryAx" in stdout:
        break
elapsed = time.monotonic() - started
manifest = {"scope": "Decoder computations and AST theorem; declarative grammar remains unproved"
            if args.full else "Certificate decoder decomposition only; source semantics unchanged",
            "source": str(args.source), "elapsed_seconds": elapsed,
            "generator_sha256": generator_hash,
            "input_sha256": hashlib.sha256((args.source.parent / "input.p").read_bytes()).hexdigest(),
            "certificate_sha256": hashlib.sha256((args.source.parent / "proof.fang").read_bytes()).hexdigest(),
            "limits": {"total_seconds": 60, "peak_rss_kib": 2 * 1024 * 1024},
            "expected_modules": len(modules), "records": records,
            "passed": len(records) == len(modules) and elapsed <= 60 and all(
                r["exit_code"] == 0 and r["peak_rss_kib"] <= 2 * 1024 * 1024 and
                r["axiom_report_has_no_sorry"] for r in records)}
(output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
print(json.dumps({"passed": manifest["passed"], "elapsed_seconds": elapsed}), flush=True)
