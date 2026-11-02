"""Signed path: inputs with any role other than axiom, over plain files or include bundles.

The checker and the producer both take the bundle as ROOT PATH FILE triples, so
the adapter finds the include closure itself, in the order the bundle checker
requires: depth-first first reach from the top-level file, each include path
resolved next to the including file within its root, then under the TPTP root.
The search for files and the routing test are untrusted: a wrong file list is
rejected by the checker, and every path is sound for the inputs it accepts.

Status rules: docs/DESIGN.md, section "Status rules for conjectures". The
checker's own `--goals` listing decides; see `final_status`.
"""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
from pathlib import Path
import re
import stat

import protocol

FILE_BYTES = 1 << 20
TOTAL_BYTES = 4 << 20
WORD = re.compile(rb"[a-z][A-Za-z0-9_]*")
LISTING = re.compile(rb"goals ([0-9]+)\n((?:goal [0-9]+ item [0-9]+ [0-9]+\n)*)")
LISTED = re.compile(rb"goal ([0-9]+) item ([0-9]+) ([0-9]+)\n")
GOAL = re.compile(rb"accepted-goal ([0-9]+) item ([0-9]+) ([0-9]+) \(native checker; compiler/runtime trusted\)\n")
INPUTS = b"accepted-inputs-unsatisfiable (native checker; compiler/runtime trusted)\n"
CANDIDATE = b"candidate-certificate: unchecked signed bundle task\n"
NOT_INSTALLED = ("Inputs with roles other than axiom need the signed bundle checker, which is not installed here. "
                 "No other path was tried.")
TSTP_UNAVAILABLE = ("TSTP output is not yet available for inputs with conjectures or other non-axiom roles; rerun with "
                    "--output status. No fallback was performed.")


class Statement:
    def __init__(self, keyword, arguments):
        self.keyword, self.arguments = keyword, arguments

    @property
    def role(self):
        if self.keyword in (b"fof", b"cnf") and len(self.arguments) >= 2:
            return self.arguments[1].strip().decode("ascii", "replace")
        return None

    @property
    def include(self):
        if self.keyword != b"include" or not self.arguments:
            return None
        text = self.arguments[0].strip()
        if len(text) < 2 or text[:1] != b"'" or text[-1:] != b"'":
            return None
        body, value, index = text[1:-1], bytearray(), 0
        while index < len(body):
            if body[index] == 0x5C and index + 1 < len(body) and body[index + 1] in b"\\'":
                value.append(body[index + 1])
                index += 2
            else:
                value.append(body[index])
                index += 1
        return bytes(value).decode("ascii", "replace")


def _skip_layout(data, index):
    while index < len(data):
        if data[index] in b" \t\r\n\x0b\x0c":
            index += 1
        elif data[index:index + 1] == b"%":
            end = data.find(b"\n", index)
            index = len(data) if end < 0 else end + 1
        elif data[index:index + 2] == b"/*":
            end = data.find(b"*/", index + 2)
            index = len(data) if end < 0 else end + 2
        else:
            break
    return index


def _quoted(data, index):
    quote, index = data[index], index + 1
    while index < len(data):
        if data[index] == 0x5C:
            index += 2
        elif data[index] == quote:
            return index + 1
        else:
            index += 1
    return len(data)


def statements(data):
    """Top-level statements with their arguments split at depth one; stops at the first unreadable byte."""
    result, index = [], 0
    while True:
        index = _skip_layout(data, index)
        match = WORD.match(data, index)
        if match is None:
            return result
        keyword, index = match.group(), _skip_layout(data, match.end())
        if data[index:index + 1] != b"(":
            return result
        depth, index, arguments, current = 1, index + 1, [], bytearray()
        while index < len(data) and depth:
            byte = data[index]
            if byte in b"'\"":
                end = _quoted(data, index)
                current += data[index:end]
                index = end
                continue
            if data[index:index + 1] == b"%" or data[index:index + 2] == b"/*":
                index = _skip_layout(data, index)
                current += b" "
                continue
            if byte in b"([":
                depth += 1
            elif byte in b")]":
                depth -= 1
                if depth == 0:
                    arguments.append(bytes(current))
                    index += 1
                    break
            elif byte == ord(",") and depth == 1:
                arguments.append(bytes(current))
                current = bytearray()
                index += 1
                continue
            current.append(byte)
            index += 1
        if depth:
            return result
        result.append(Statement(keyword, arguments))
        index = _skip_layout(data, index)
        if data[index:index + 1] != b".":
            return result
        index += 1


def components(path):
    """The bundle's include path rules: relative, 1 to 64 components, no '.', '..', empty, backslash, colon or NUL."""
    if not path or len(path) > 4096 or path.startswith("/") or any(char in path for char in "\\:\0"):
        return None
    parts = path.split("/")
    if len(parts) > 64 or any(part in ("", ".", "..") for part in parts):
        return None
    return parts


def _location(root_directory, parts):
    """A regular file reached through real directories, or None, as the bundle capture checks it."""
    if root_directory is None:
        return None
    path = Path(root_directory)
    for position, part in enumerate(parts):
        path = path / part
        try:
            info = path.lstat()
        except (FileNotFoundError, NotADirectoryError):
            return None
        if stat.S_ISLNK(info.st_mode):
            return None
        last = position + 1 == len(parts)
        if (not last and not stat.S_ISDIR(info.st_mode)) or (last and not stat.S_ISREG(info.st_mode)):
            return None
    return path


def discover(top_name, top_bytes, base_directory, tptp_root, read):
    """Bundle files in first-reach order as [(root, path, location, bytes)]; stops early on a problem the checker reports."""
    files = [("base", (top_name,), None, top_bytes)]
    index, finished = {("base", (top_name,)): 0}, set()
    roots = {"base": base_directory, "tptp": tptp_root}

    def visit(position, stack):
        for statement in statements(files[position][3]):
            path = statement.include
            if statement.keyword != b"include":
                continue
            parts = components(path) if path is not None else None
            if parts is None:
                return False
            root, key = files[position][0], files[position][1]
            child = None
            for candidate in ((root, tuple(key[:-1]) + tuple(parts)), ("tptp", tuple(parts))):
                if candidate in index:
                    child = index[candidate]
                    break
                location = _location(roots[candidate[0]], candidate[1])
                if location is not None:
                    data = read(location)
                    index[candidate] = len(files)
                    files.append((candidate[0], candidate[1], location, data))
                    child = index[candidate]
                    break
            if child is None or child in stack:
                return False
            if child not in finished and not visit(child, stack + [child]):
                return False
        finished.add(position)
        return True

    visit(0, [0])
    return [(root, "/".join(key), location, data) for root, key, location, data in files]


def roles(files):
    return [statement.role for _, _, _, data in files for statement in statements(data) if statement.role is not None]


def route(files, plain_bundle):
    """signed for any role other than axiom; bundle for axiom-only inputs with includes or objects; else single."""
    if any(role != "axiom" for role in roles(files)):
        return "signed"
    return "bundle" if len(files) > 1 or plain_bundle else "single"


def listing(record, stdout, stderr):
    """The checker's own selected-conjecture listing, or the status its rejection gives."""
    code = protocol.normal(record)
    if code == 0 and not stderr:
        match = LISTING.fullmatch(stdout)
        if match:
            items = [(int(index), int(file), int(statement)) for index, file, statement in LISTED.findall(match[2])]
            if len(items) == int(match[1]) and [row[0] for row in items] == list(range(len(items))):
                return "listed", [(file, statement) for _, file, statement in items]
        raise ValueError("Malformed signed checker goal listing")
    return rejection(code, stdout, stderr, reading=True), None


def rejection(code, stdout, stderr, *, reading=False):
    """Status for a checker rejection. Only input reading can give an input status; a task rejection is an error."""
    if stdout or not re.fullmatch(rb"[ -~]+\n(?:  [ -~]+\n)*", stderr):
        raise ValueError("Malformed signed checker rejection")
    if code == 4 and re.match(rb"(resource\.|replay\.(reservation|conversion)\.(predicate-limit|symbol-width|literal-limit)\n"
                              rb"|(certificate|replay\.[a-z-]+): resource-exhaustion)", stderr):
        return "ResourceOut"
    if reading and code == 2:
        if re.fullmatch(rb"(bundle\.frame|replay\.input)\.unsupported:[0-9]+\n", stderr):
            return "Inappropriate"
        # A selected conjecture together with a selected negated conjecture is unsupported (status rules above).
        if stderr == b"bundle.mixed-goal-modes\n":
            return "Inappropriate"
        if re.fullmatch(rb"(bundle\.frame\.invalid:[0-9]+|bundle\.include\.(missing|cycle)|"
                        rb"bundle\.selection\.(missing|ambiguous)|replay\.input\.invalid:[0-9]+|"
                        rb"invalid-utf8\.input|(invalid-nul|unsupported-non-ascii)\.input:[0-9]+)\n", stderr):
            return "InputError"
    if code in (1, 2, 3, 5, 6, 74):
        return "Error"
    raise ValueError("Unrecognized signed checker contract")


def accepted(record, stdout, stderr, task):
    """The item an accepted goal printed, True for accepted inputs, or None for a rejection."""
    code = protocol.normal(record)
    if code == 0 and not stderr:
        if task == "inputs" and stdout == INPUTS:
            return True
        match = GOAL.fullmatch(stdout)
        if task != "inputs" and match and int(match[1]) == task:
            return int(match[2]), int(match[3])
        raise ValueError("Malformed signed checker acceptance")
    return None


def producer_outcome(record, stdout, stderr):
    """Candidate, GaveUp, ResourceOut, Inappropriate or Error for one producer task; never a result."""
    code = protocol.normal(record)
    if code == 0 and stdout.startswith(protocol.HEADER) and stderr == CANDIDATE:
        return "candidate"
    if stdout:
        raise ValueError("Noncandidate signed producer emitted certificate bytes")
    if code == 2 and re.fullmatch(rb"unknown: processed=[0-9]+ attempted=[0-9]+\n", stderr):
        return "GaveUp"
    if code == 1 and re.fullmatch(rb"error: [a-z-]+ [ -~]*\n", stderr):
        kind = stderr.split()[1]
        if kind == b"modes":
            # Mixed goal modes are unsupported (status rules above); the checker's listing refuses them first.
            return "Inappropriate"
        if kind in (b"resource", b"width") or b"Resource(" in stderr or b"ResourceLimit" in stderr:
            return "ResourceOut"
        return "Error"
    raise ValueError("Unrecognized signed producer contract")


def final_status(listed, outcomes):
    """docs/DESIGN.md, "Status rules for conjectures".

    Theorem only if the checker listed at least one selected conjecture and every
    listed index was accepted printing its listed item; Unsatisfiable only if it
    listed none and the inputs task was accepted. `outcomes` holds, per task in
    order, the acceptance (item or True) or the first non-accepting status, and
    stops at that status. A partial set of accepted goals is never reported.
    """
    if outcomes and not isinstance(outcomes[-1], (tuple, bool)):
        return outcomes[-1]
    if listed:
        if len(outcomes) == len(listed) and all(outcome == item for outcome, item in zip(outcomes, listed)):
            return protocol.task_status(len(listed), len(outcomes))
        return "Error"
    if outcomes == [True]:
        return protocol.task_status(0, 1)
    return "Error"
