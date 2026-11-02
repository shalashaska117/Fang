"""Bundle path: inputs with include directives, distinct objects or annotations.

The bundle producer reads the top-level file and its includes itself (relative
to the input file, then the TPTP root) and reports the bundle's files in order.
The adapter then reads every listed file once, seals it, hashes it into the run
manifest and passes exactly those bytes to the bundle checker. Only the
checker's acceptance gives a result. The routing test is untrusted: both paths
are sound for the inputs they accept.
"""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import struct

import protocol
import signed

ACCEPTED = b"accepted-original-bundle-equality (native checker; compiler/runtime trusted)\n"
CANDIDATE = b"candidate-certificate: unchecked bundle input\n"
FILE_BYTES = 1 << 20
TOTAL_BYTES = 4 << 20
INCLUDE = re.compile(rb"(?<![A-Za-z0-9_$])include\s*\(")
CAPTURE = re.compile(rb"capture: (InvalidInput|Unsupported|ResourceLimit) ([A-Za-z]+) file=(?:None|Some\([0-9]+\)) "
                     rb"offset=(?:None|Some\([0-9]+\))\n")
NOT_INSTALLED = ("Inputs with include directives, distinct objects or annotations need the bundle checker, which is not "
                 "installed here. No other path was tried.")
TSTP_UNAVAILABLE = ("TSTP output for bundles needs the bundle exporter, which is not installed here; rerun "
                    "with --output status. No fallback was performed.")


def needs_bundle(data):
    """Route by features of the input, before anything runs: a double quote or an include directive anywhere,
    comments included, or a statement with an annotation (more than three arguments), which the single-file
    decoder does not read and the bundle path does. The test is untrusted: a wrong route only gives the other path's
    own checked answer or rejection, never a fallback."""
    if b'"' in data or INCLUDE.search(data) is not None:
        return True
    return any(statement.keyword in (b"fof", b"cnf") and len(statement.arguments) > 3
               for statement in signed.statements(data))


def valid_path(text):
    path = PurePosixPath(text)
    return (bool(text) and not path.is_absolute() and "\\" not in text and str(path) == text
            and all(part not in ("", ".", "..") for part in path.parts))


def _bundle_info(line):
    info = json.loads(line.decode("ascii"))
    if (not isinstance(info, dict) or set(info) != {"bundle_sha256", "files", "declarations", "objects"}
            or not re.fullmatch(r"[0-9a-f]{64}", str(info["bundle_sha256"])) or not isinstance(info["files"], list)
            or not info["files"] or any(not isinstance(item, list) or len(item) != 2 or item[0] not in ("base", "tptp")
                                        or not isinstance(item[1], str) or not valid_path(item[1])
                                        for item in info["files"])
            or info["files"][0][0] != "base" or "/" in info["files"][0][1]
            or len({tuple(item) for item in info["files"]}) != len(info["files"])):
        raise ValueError("Malformed bundle producer file list")
    return info


def producer_outcome(record, stdout, stderr):
    """Map the bundle producer's streams; a candidate is never a result."""
    code = protocol.normal(record)
    if code in (0, 2):
        first, _, rest = stderr.partition(b"\n")
        info = _bundle_info(first)
        if code == 0 and stdout.startswith(protocol.HEADER) and rest == CANDIDATE:
            return "candidate", info
        if code == 2 and not stdout and re.fullmatch(rb"unknown: processed=[0-9]+ attempted=[0-9]+\n", rest):
            return "GaveUp", "Search stopped without a certified result"
        raise ValueError("Malformed bundle producer outcome")
    if stdout:
        raise ValueError("Noncandidate bundle producer emitted certificate bytes")
    if code == 3:
        match = CAPTURE.fullmatch(stderr)
        if match:
            return protocol.INPUT_STATUS[match[1]], "Bundle capture: " + match[2].decode("ascii")
        match = re.fullmatch(rb"adapter: Input\(" + protocol.INPUT + rb"\)\n", stderr)
        if match:
            return protocol.INPUT_STATUS[match[1]], json.loads(match[4].decode("ascii"))
        if any(re.fullmatch(rb"adapter: " + pattern + rb"\n", stderr) for pattern in protocol.ADAPTER_RESOURCES):
            return "ResourceOut", "Preprocessing or search reached a structural resource bound"
    if code == 4 and re.fullmatch(rb"serialization: " + protocol.RESOURCE + rb"\n", stderr):
        return "ResourceOut", "Serialization reached a structural resource bound"
    raise ValueError("Unrecognized or failed bundle producer contract")


def checker_outcome(record, stdout, stderr):
    """Classify the native bundle checker; only `accepted` can lead to a result."""
    code = protocol.normal(record)
    if code == 0 and stdout == ACCEPTED and not stderr:
        return "accepted"
    if stdout or not re.fullmatch(rb"[ -~]+\n(?:  [ -~]+\n)*", stderr):
        raise ValueError("Rejected or malformed bundle checker result")
    if code == 4 and re.match(rb"(resource\.|replay\.(reservation|conversion)\.(predicate-limit|symbol-width|literal-limit)\n"
                              rb"|(certificate|replay\.(transport-input|preprocessing-input)): resource-exhaustion)", stderr):
        return "resource"
    names = {1: "logical-rejection", 2: "input-or-bundle-rejection", 3: "certificate-rejection",
             5: "internal-replay-failure", 6: "signature-rejection", 74: "io-failure"}
    if code in names:
        return names[code]
    raise ValueError("Unrecognized or failed bundle checker contract")


def digest(files):
    """The producer's bundle digest over (root, path, bytes) in bundle order."""
    data = bytearray(b"fang-tptp-bundle-v1\0")
    data += struct.pack(">Q", len(files))
    for root, path, content in files:
        data.append(0 if root == "base" else 1)
        components = path.split("/")
        data += struct.pack(">Q", len(components))
        for component in components:
            data += struct.pack(">Q", len(component)) + component.encode()
        data += struct.pack(">Q", len(content)) + content
    return hashlib.sha256(bytes(data)).hexdigest()


def locate(info, input_path, tptp_root):
    """Where each listed file is read from: the input's directory for base, the TPTP root for tptp."""
    input_path = Path(input_path).absolute()
    if info["files"][0] != ["base", input_path.name]:
        raise ValueError("Bundle producer did not start from the captured input")
    places = []
    for root, path in info["files"]:
        if root == "tptp" and tptp_root is None:
            raise ValueError("Bundle needs a TPTP root that was not given")
        base = input_path.parent if root == "base" else Path(tptp_root).absolute()
        places.append((root, path, base / path))
    return places
