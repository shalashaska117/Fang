#!/usr/bin/env python3
"""Audit reports emitted by a fixed Lean audit module after importing a proof.

Do not trust reports printed by an untrusted generated proof module itself.
The fixed audit module must also check the theorem's expected type and input.
"""

# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.

import argparse
import json
from pathlib import Path
import re

ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
REPORT = re.compile(
    r"'(?P<name>[^'\n]+)'\s+(?:depends on axioms:\s*\[(?P<axioms>[^\]]*)\]"
    r"|(?P<none>does not depend on any axioms))",
    re.MULTILINE,
)


def audit_axioms(output: str, required_theorems) -> dict[str, list[str]]:
    """Fail closed on missing reports or any dependency outside the allowlist."""
    required = set(required_theorems)
    if not required:
        raise ValueError("At least one theorem must be required by the audit")
    if "sorryAx" in output:
        raise ValueError("Lean audit contains sorryAx")
    reports = {}
    for match in REPORT.finditer(output):
        names = set() if match.group("none") else {
            name.strip() for name in match.group("axioms").split(",") if name.strip()
        }
        unexpected = names - ALLOWED_AXIOMS
        if unexpected:
            raise ValueError(f"Unexpected axioms for {match.group('name')}: {sorted(unexpected)}")
        theorem = match.group("name")
        value = sorted(names)
        if theorem in reports and reports[theorem] != value:
            raise ValueError(f"Conflicting axiom reports for {theorem}")
        reports[theorem] = value
    missing = required - reports.keys()
    if missing:
        raise ValueError(f"Missing Lean theorem audits: {sorted(missing)}")
    return reports


def self_test():
    cases = [
        ("'T' depends on axioms: [propext,\n Classical.choice, Quot.sound]", ["T"], True),
        ("'T' does not depend on any axioms", ["T"], True),
        ("'T' depends on axioms: []", ["T"], True),
        ("'T' depends on axioms: [Trusted.unsound]", ["T"], False),
        ("'T' depends on axioms: [sorryAx]", ["T"], False),
        ("'Other' does not depend on any axioms", ["T"], False),
        ("'T' depends on axioms: [propext]\n'T' depends on axioms: []", ["T"], False),
        ("'T' depends on axioms: [propext", ["T"], False),
        ("", [], False),
    ]
    for index, (output, required, expected) in enumerate(cases):
        try:
            audit_axioms(output, required)
            accepted = True
        except ValueError:
            accepted = False
        if accepted != expected:
            raise AssertionError(f"Axiom audit control {index} failed")
    return {"controls": len(cases), "status": "passed", "scope": "report parser only"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("log", type=Path, nargs="?")
    parser.add_argument("theorems", nargs="*")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        print(json.dumps(self_test()))
    else:
        if args.log is None:
            parser.error("log and required theorem names are required")
        print(json.dumps(audit_axioms(args.log.read_text(), args.theorems), indent=2))
