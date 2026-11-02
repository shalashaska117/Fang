"""Version-8 process contracts and SZS mapping. Only exact checker acceptance authorizes a result.

Derived from the accepted version-7 command protocol. The producer prints its
typed adapter errors with the `adapter:` prefix; the variants are the same.
"""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import json
import re

ACCEPTED = b"accepted-original-expanded-equality (native checker; compiler/runtime trusted)\n"
CANDIDATE = b"candidate-certificate: unchecked original input\n"
HEADER = b"(fang-proof 8\n  (preprocessing expanded-fof-equality-skolem-distributive-v1)\n"
TEXT = rb'"(?:[^"\\\r\n]|\\.)*"'
INPUT = rb"Error \{ kind: (InvalidInput|Unsupported|ResourceLimit), offset: (None|Some\(([0-9]+)\)), message: (" + TEXT + rb") \}"
RESOURCE = rb'Resource\("[^"\\\r\n]+"\)'
CORE_CAP = rb"(FormulaDepth|FormulaNodes|TermDepth|InputTermNodes|Clauses|LiteralsPerClause|Literals|StoredNodes|Operations|Arithmetic|Binders)"
PREPROCESSING_RESOURCES = (
    RESOURCE,
    rb"Skolem\(Resource\((Declarations|Functions|SkolemSymbols|Operations|StoredNodes|TermDepth)\)\)",
    rb"Skolem\(Core\(Resource\(" + CORE_CAP + rb"\)\)\)",
    rb"Removal\(Resource\((FormulaDepth|Operations|OutputNodes)\)\)",
    rb"Clausification\(Resource\((FormulaDepth|FormulaNodes|TermDepth|InputTermNodes|Clauses|LiteralsPerClause|Literals|StoredNodes|Operations|Arithmetic)\)\)",
)
ADAPTER_RESOURCES = [
    RESOURCE,
    rb"(Encoding|Conversion)\((PredicateLimit|SymbolId|LiteralLimit)\)",
    rb"Search\(" + RESOURCE + rb"\)",
    rb"Search\(Search\(" + RESOURCE + rb"\)\)",
    rb"Search\(Search\(Unification\(Error \{ kind: ResourceLimit, offset: None, message: " + TEXT + rb" \}\)\)\)",
    rb"Search\(Search\(Reconstruction\((Depth|Literals|Bindings|OutputNodes|Operations)\)\)\)",
    rb"Search\(Search\(Paramodulation\(Resource\((Operations|OutputNodes|Literals|Arithmetic)\)\)\)\)",
    rb"Search\(Search\(Paramodulation\(Input\((Depth|Literals|Bindings|OutputNodes|Operations)\)\)\)\)",
    rb"Search\(Search\(Paramodulation\(Occurrence\((Depth|OutputNodes|Operations)\)\)\)\)",
] + [rb"Preprocessing\(" + pattern + rb"\)" for pattern in PREPROCESSING_RESOURCES]
INPUT_STATUS = {b"InvalidInput": "InputError", b"Unsupported": "Inappropriate", b"ResourceLimit": "ResourceOut"}


def normal(record):
    code = record.get("exit_code")
    if type(code) is not int or code < 0 or record.get("classification") != (
            "completed" if code == 0 else "nonzero-exit"):
        raise ValueError("Child did not complete its declared exit contract")
    return code


def engine_outcome(record, stdout, stderr, source):
    """Map the producer's exit code and streams; a candidate is never a result."""
    code = normal(record)
    if code == 0 and stdout.startswith(HEADER) and stderr == CANDIDATE:
        return "candidate", "Original-byte checking is required"
    if stdout:
        raise ValueError("Noncandidate or malformed producer emitted certificate bytes")
    if code == 2 and re.fullmatch(rb"unknown: processed=[0-9]+ attempted=[0-9]+\n", stderr):
        return "GaveUp", "Search stopped without a certified result"
    if code == 3:
        match = re.fullmatch(rb"adapter: Input\(" + INPUT + rb"\)\n", stderr)
        if match:
            if match[3] is not None and int(match[3]) > len(source):
                raise ValueError("Diagnostic offset exceeds captured input")
            message = json.loads(match[4].decode("ascii"))
            if not isinstance(message, str) or any(ord(char) < 32 or ord(char) > 126 for char in message):
                raise ValueError("Malformed producer diagnostic")
            return INPUT_STATUS[match[1]], message
        if any(re.fullmatch(rb"adapter: " + pattern + rb"\n", stderr) for pattern in ADAPTER_RESOURCES):
            return "ResourceOut", "Preprocessing or search reached a structural resource bound"
    if code == 4 and re.fullmatch(rb"serialization: " + RESOURCE + rb"\n", stderr):
        return "ResourceOut", "Serialization reached a structural resource bound"
    raise ValueError("Unrecognized or failed version-8 producer contract")


def checker_outcome(record, stdout, stderr):
    """Classify the native checker; only `accepted` can lead to a result."""
    code = normal(record)
    if code == 0 and stdout == ACCEPTED and not stderr:
        return "accepted"
    if stdout:
        raise ValueError("Rejected or malformed checker result emitted acceptance output")
    if code == 1 and re.fullmatch(rb"logical-rejection: Fang\.Equality\.TraceError\.((inputIndex|parentIndex) [0-9]+|inferenceWitness|claimedClause|finalIndex|finalNotEmpty)\n", stderr):
        return "logical-rejection"
    if code == 6 and stderr == b"signature-rejection\n":
        return "signature-rejection"
    if code == 3 and re.fullmatch(rb"certificate: (invalid-certificate|invalid-syntax|unsupported): [ -~]+\n", stderr):
        return "certificate-rejection"
    resources = (
        rb"resource\.(bytes\.(input|certificate)|replay\.(skolem|skolem-core|removal|clausification))",
        rb"resource\.replay\.input:[0-9]+",
        rb"resource\.replay\.(width|conversion-width): [ -~]+",
        rb"replay\.(reservation|conversion)\.(predicate-limit|symbol-width|literal-limit)",
        rb"(certificate|replay\.(transport-input|preprocessing-input)): resource-exhaustion[ -~]*",
    )
    if code == 4 and any(re.fullmatch(pattern + rb"\n", stderr) for pattern in resources):
        return "resource"
    rejected = (
        rb"replay\.input\.(invalid|unsupported):[0-9]+",
        rb"replay\.(transport-input|preprocessing-input): [ -~]+",
        rb"replay\.nonliteral",
        rb"replay\.(reservation|conversion)\.(unknown-predicate|predicate-arity|reserved-arity)",
        rb"replay\.(missing-function-arity|missing-predicate-arity|skolem-invalid|skolem-unsupported|residual-existential|clausification-invalid)",
        rb"invalid-utf8\.(input|certificate)",
        rb"(invalid-nul|unsupported-non-ascii)\.(input|certificate):[0-9]+",
    )
    if code == 2 and any(re.fullmatch(pattern + rb"\n", stderr) for pattern in rejected):
        return "input-or-replay-rejection"
    if code == 5 and re.fullmatch(rb"(replay\.(input\.internal:[0-9]+|transport-runtime-effect|transport-divergence|runtime-effect|divergence|clause-block-count)|internal-byte-roundtrip\.(input|certificate))\n", stderr):
        return "internal-replay-failure"
    if code == 74 and re.fullmatch(rb"io-error: [ -~]+\n(?:  [ -~]+\n)*", stderr):
        return "io-failure"
    raise ValueError("Unrecognized or failed version-8 checker contract")


def checked_status(outcome):
    """Status after a producer candidate; a rejection is an error, never a result."""
    if outcome == "accepted":
        return "Unsatisfiable", "The native version-8 checker accepted the exact captured pair"
    if outcome == "resource":
        return "ResourceOut", "The native checker reached its declared resource bound"
    return "Error", "The original-byte checker rejected the producer candidate: " + outcome


def task_status(conjectures, accepted):
    """Status rule for the signed per-conjecture path, kept here for when it is installed.

    `conjectures` is the number of selected conjectures and `accepted` the number
    of conjecture indices (or, with none selected, the inputs task) whose
    certificate was accepted. The axiom-only path calls this with zero
    conjectures. Satisfiable and CounterSatisfiable are never produced.
    """
    if conjectures > 0:
        return "Theorem" if accepted == conjectures else "GaveUp"
    return "Unsatisfiable" if accepted == 1 else "GaveUp"
