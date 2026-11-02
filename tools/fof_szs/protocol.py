"""Exact experimental driver/checker contracts; no fallback between languages."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import re

ACCEPTED = b"accepted-original-ground-fof (compiled checker; compiler/runtime trusted)\n"
UNSUPPORTED = frozenset({"interpreted symbols are unsupported", "NAND and NOR are unsupported",
    "token is outside the supported CNF/ground FOF fragment", "$true is unsupported in CNF",
    "formula connectives are unsupported in CNF", "only CNF and ground FOF statements are supported",
    "only the axiom role is supported", "TPTP annotations are unsupported"})
INVALID = frozenset({"uppercase character in a lowercase identifier", "input must contain ASCII bytes only",
    "invalid character", "inconsistent symbol arity", "expected a lowercase identifier", "expected a term",
    "free variables are invalid in ground FOF", "expected a ground formula", "duplicate statement name",
    "only CNF and ground FOF statements are supported", *(f"expected '{c}'" for c in "(),.")})


def normal_exit(record):
    code = record.get("exit_code")
    if type(code) is not int or code < 0 or record.get("classification") != (
            "completed" if code == 0 else "nonzero-exit"):
        raise ValueError("Child did not complete its declared exit contract")
    return code


def engine_outcome(record, stdout, stderr, source):
    code = normal_exit(record)
    if code == 0 and stdout == b"candidate-refutation\n" and re.fullmatch(
            rb"[1-9][0-9]* recorded search nodes; serialized proof keeps only refutation dependencies; independent checking required\n", stderr):
        return "candidate", "Candidate requires independent original-byte checking"
    if code == 2 and stdout == b"unknown\n" and re.fullmatch(
            rb"queue exhausted after [0-9]+ clauses and [0-9]+ inference attempts\n", stderr):
        return "GaveUp", "Search exhausted its queue without a certified result"
    if not stdout:
        match = re.fullmatch(rb"(InvalidInput|Unsupported) at byte ([0-9]+): ([^\r\n]+)\n", stderr)
        if match:
            message = match[3].decode("ascii")
            if int(match[2]) > len(source):
                raise ValueError("Driver diagnostic offset exceeds captured input")
            if code == 3 and match[1] == b"InvalidInput" and message in INVALID:
                return "InputError", message
            if code == 4 and match[1] == b"Unsupported" and message in UNSUPPORTED:
                return "Inappropriate", message
        if code == 5 and re.fullmatch(rb"ResourceLimit: [\x20-\x7e]+\n", stderr):
            return "ResourceOut", stderr[:-1].decode("ascii")
    raise ValueError("Malformed, unrecognized or failed FOF driver contract")


def checker_acceptance(record, stdout, stderr):
    if normal_exit(record) != 0 or stdout != ACCEPTED or stderr:
        raise ValueError("Pinned original-byte version-2 checker did not accept")
