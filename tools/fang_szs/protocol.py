"""Versioned contracts for the unchanged Fang CLI and fixed replay exporter."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import json
import re
from .supervisor import Failure


ACCEPTED = b"accepted-refutation (compiled checker; no per-instance kernel replay performed)\n"
REQUIRED_AUDITS = frozenset({"exact_original_bytes_unsat", "exact_source_decodes",
    "exact_certificate_decodes", "exact_checker_acceptance"})
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
UNSUPPORTED = frozenset({"interpreted symbols and $true are unsupported",
    "token is outside the supported TPTP CNF fragment", "only cnf statements are supported",
    "only the axiom role is supported", "TPTP annotations are unsupported"})
INVALID = frozenset({"uppercase character in a lowercase identifier",
    "input must contain ASCII bytes only", "invalid character", "inconsistent symbol arity",
    "expected a lowercase identifier", "expected a term", "duplicate clause name",
    "only cnf statements are supported", *(f"expected '{char}'" for char in "(),.")})
ESTABLISHED_INPUT_ERROR = frozenset({"inconsistent symbol arity", "duplicate clause name"})


def completed_contract(process):
    code = process.get("exit_code")
    if type(code) is not int or process.get("classification") != ("completed" if code == 0 else "nonzero-exit") or code < 0:
        raise Failure("Error", "Child did not satisfy its normal-exit contract", process.get("stage", "child"))
    return code


def engine_outcome(process, stdout, stderr, source=None):
    code = completed_contract(process)
    stage = "search"
    if code == 0 and stdout == b"candidate-refutation\n" and re.fullmatch(
        rb"[1-9][0-9]* recorded search nodes; serialized proof keeps only refutation dependencies; independent checking required\n", stderr):
        return "candidate", "Rust candidate requires independent checking"
    if code == 2 and stdout == b"unknown\n" and re.fullmatch(
        rb"queue exhausted after [0-9]+ clauses and [0-9]+ inference attempts\n", stderr):
        return "GaveUp", "Search exhausted its queue without a certified result"
    if not stdout:
        match = re.fullmatch(rb"(InvalidInput|Unsupported) at byte ([0-9]+): ([^\r\n]+)\n", stderr)
        if match:
            message = match[3].decode("ascii", errors="strict")
            if code == 4 and match[1] == b"Unsupported" and message in UNSUPPORTED:
                return "Inappropriate", message
            if code == 3 and match[1] == b"InvalidInput" and message in INVALID:
                offset = int(match[2])
                if message == "invalid character" and source is not None and offset < len(source):
                    byte = source[offset]
                    if byte == 127 or (byte < 32 and byte not in b"\t\n\v\f\r"):
                        return "InputError", "Invalid control byte in the declared ASCII syntax"
                return ("InputError" if message in ESTABLISHED_INPUT_ERROR else "Inappropriate"), message
        if code == 5 and re.fullmatch(rb"ResourceLimit: [\x20-\x7e]+\n", stderr):
            return "ResourceOut", stderr[:-1].decode("ascii")
    raise Failure("Error", "Malformed, unrecognized or failed engine contract", stage)


def checker_acceptance(process, stdout, stderr):
    if completed_contract(process) != 0 or stdout != ACCEPTED or stderr:
        raise Failure("Error", "Independent compiled checker did not accept the captured certificate", "checker")


def exact_axioms(text, audited_parser):
    """Reuse the existing parser, then enforce one exact report per theorem."""
    reports = audited_parser.audit_axioms(text, REQUIRED_AUDITS)
    matches = list(audited_parser.REPORT.finditer(text))
    if len(matches) != len(REQUIRED_AUDITS) or {match.group("name") for match in matches} != REQUIRED_AUDITS:
        raise Failure("Error", "Extra or duplicate fixed-audit report", "audit")
    remainder, end = [], 0
    for match in matches:
        remainder.append(text[end:match.start()])
        end = match.end()
    remainder.append(text[end:])
    if "".join(remainder).strip():
        raise Failure("Error", "Unexpected fixed-audit output", "audit")
    if set(reports) != REQUIRED_AUDITS or any(set(value) - ALLOWED_AXIOMS for value in reports.values()):
        raise Failure("Error", "Fixed-audit theorem or axiom set differs", "audit")
    return reports


HEADER = """/-
Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
The kernel checks exact decoder computations and checker acceptance, then
applies general source soundness to the original input byte value.
The compiled exporter is untrusted. Source acceptance completeness is separate.
-/
import Fang.CertificateInput
import Fang.FrontendSoundness
import Lean.Elab.Tactic.Cbv

namespace Fang.InstanceReplay

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option cbv.maxSteps 10000000

"""
FOOTER = """theorem source_decodes : decodeProblem originalInput = .ok problem := by cbv

theorem certificate_decodes : decodeCertificate originalCertificate = .ok certificate := by cbv

theorem accepted : check (preprocess problem) certificate = true := by decide +kernel

theorem parsed_ast_unsat : ¬ Satisfiable problem :=
  check_preprocessed_sound problem certificate accepted

theorem original_input_unsat : ¬ Source.Grammar.BytesSatisfiable
    (Source.Grammar.spelling originalInput) :=
  decoded_refutation_unsat source_decodes certificate accepted

#print axioms source_decodes
#print axioms certificate_decodes
#print axioms accepted
#print axioms parsed_ast_unsat
#print axioms original_input_unsat

end Fang.InstanceReplay
"""


def quote(data):
    value = data.decode("ascii")
    return '"' + "".join("\\u000c" if char == "\f" else "\\u0008" if char == "\b"
        else json.dumps(char, ensure_ascii=True)[1:-1] for char in value) + '"'


def literal_value(text):
    """Accept only Lean's ordinary ASCII string escapes, never an expression."""
    if len(text) < 2 or text[0] != '"' or text[-1] != '"':
        raise Failure("Error", "Exporter string is not a string literal", "export")
    result, index = [], 1
    escapes = {'n': '\n', 'r': '\r', 't': '\t', '\\': '\\', '"': '"', '0': '\0'}
    while index < len(text) - 1:
        char = text[index]
        index += 1
        if char == "\\":
            if index >= len(text) - 1:
                raise Failure("Error", "Incomplete exporter escape", "export")
            escape = text[index]
            index += 1
            if escape in escapes:
                char = escapes[escape]
            elif escape in ("u", "x"):
                width = 4 if escape == "u" else 2
                digits = text[index:index + width]
                if len(digits) != width or not re.fullmatch(r"[0-9A-Fa-f]+", digits):
                    raise Failure("Error", "Invalid exporter escape", "export")
                char, index = chr(int(digits, 16)), index + width
            else:
                raise Failure("Error", "Unsupported exporter escape", "export")
        elif char == '"' or ord(char) < 32:
            raise Failure("Error", "Invalid raw exporter string character", "export")
        if ord(char) > 127:
            raise Failure("Error", "Exporter string changed the ASCII source boundary", "export")
        result.append(char)
    return "".join(result).encode("ascii")


DATA_TOKEN = re.compile(r"\s+|Certificate\.mk|\.(?:var|app|input|factor|resolve)\b|positive\b|atom\b|pred\b|args\b|true\b|false\b|[0-9]+|:=|[\[\](){},]")


def fixed_replay(exported, source, certificate):
    """Validate the exporter template and retain constructor-only AST data."""
    text = exported.decode("utf-8")
    if not text.startswith(HEADER) or not text.endswith(FOOTER):
        raise Failure("Error", "Exporter imports or proof template differs", "export")
    body = text[len(HEADER):-len(FOOTER)]
    pattern = r"def originalInput : String := ([^\n]+)\n\ndef originalCertificate : String := ([^\n]+)\n\ndef problem : Problem := (.*?)\n\ndef certificate : Certificate := (.*?)\n\n"
    match = re.fullmatch(pattern, body, re.DOTALL)
    if match is None or literal_value(match[1]) != source or literal_value(match[2]) != certificate:
        raise Failure("Error", "Exporter did not embed the captured input and certificate", "export")
    for expression in (match[3], match[4]):
        cursor = 0
        while cursor < len(expression):
            token = DATA_TOKEN.match(expression, cursor)
            if token is None:
                raise Failure("Error", "Exporter contains non-constructor data", "export")
            cursor = token.end()
    return (HEADER + "def originalInput : String := " + quote(source) + "\n\n"
        + "def originalCertificate : String := " + quote(certificate) + "\n\n"
        + "def problem : Problem := " + match[3] + "\n\n"
        + "def certificate : Certificate := " + match[4] + "\n\n" + FOOTER)
