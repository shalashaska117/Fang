"""Check the version-8 crates and Lean modules against their source maps.

The maps record, for every promoted file, the receipt it came from, its hash and
its notice. The working tree must match the maps exactly; with receipts present,
the maps are also checked against the receipt archives.
"""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import bisect
import hashlib
import json
import os
from pathlib import Path
import re
import stat
import tomllib

RUST_MAP = "tools/v8_szs/rust-sources.json"
LEAN_MAP = "tools/v8_szs/lean-sources.json"
RUST_SCHEMA = "fang-v8-rust-source-map-v1"
LEAN_SCHEMA = "fang-v8-lean-source-map-v1"
GROUND = ("crates/ground-fof-core", "crates/ground-fof-frontend", "crates/ground-fof-search", "crates/ground-fof-versioned")
# Trees whose crates must not resolve to the root workspace: research, evidence and installation snapshots.
OUTSIDE = (".local", "evidence", "experiments", "verification")
IMPORT = re.compile(r"(?:public )?import ([A-Za-z0-9_. ]+)")


def _regular(path, check):
    check()
    if not stat.S_ISREG(Path(path).lstat().st_mode):
        raise ValueError(f"Expected a regular file: {path}")


def digest(path, check=lambda: None):
    _regular(path, check)
    hasher = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1 << 20), b""):
            check()
            hasher.update(block)
    return hasher.hexdigest()


def load_map(root, relative, schema, check=lambda: None):
    path = Path(root) / relative
    _regular(path, check)
    value = json.loads(path.read_text(encoding="utf-8"))
    if value.get("schema") != schema:
        raise ValueError(f"Unexpected source map schema: {relative}")
    return value


def crate_names(root, check=lambda: None):
    """Directory names under crates/ that belong to the version-8 workspace."""
    source_map = load_map(root, RUST_MAP, RUST_SCHEMA, check)
    return frozenset(Path(name).name for name in source_map["crates"])


def _listed_tree(directory, check, skip=("target",)):
    found = set()
    for current, dirs, files in os.walk(directory, followlinks=False):
        check()
        parent = Path(current)
        for child in list(dirs):
            path = parent / child
            relative = path.relative_to(directory).as_posix()
            if relative in skip:
                dirs.remove(child)
            elif not stat.S_ISDIR(path.lstat().st_mode):
                raise ValueError(f"Source directory is not a real directory: {path}")
        for child in files:
            path = parent / child
            if not stat.S_ISREG(path.lstat().st_mode):
                raise ValueError(f"Source file is not regular: {path}")
            found.add(path.relative_to(directory).as_posix())
    return found


def apply_rewrites(original, rewrites, edits=(), includes=()):
    """Rebuild a moved file from its receipt bytes, recorded line edits, path strings and include paths.

    Line edits are the one recorded package rename (the renamed package line, its kept library name, and dependents
    naming it with `package =`); each replaces exactly the recorded receipt line. Path rewrites change a Cargo.toml
    `path = "..."` string, and include rewrites the path of an `include_str!` in a crate test.
    """
    lines = original.decode("utf-8").split("\n")
    for edit in edits:
        if lines[edit["line"] - 1] != edit["from"]:
            raise ValueError("Recorded line edit does not match the receipt bytes")
        lines[edit["line"] - 1] = edit["to"]
    for rewrite in rewrites:
        line = lines[rewrite["line"] - 1]
        needle = f'path = "{rewrite["from"]}"'
        if line.count(needle) != 1:
            raise ValueError("Recorded path rewrite does not match the receipt bytes")
        lines[rewrite["line"] - 1] = line.replace(needle, f'path = "{rewrite["to"]}"')
    for rewrite in includes:
        line = lines[rewrite["line"] - 1]
        needle = f'include_str!("{rewrite["from"]}")'
        if line.count(needle) != 1:
            raise ValueError("Recorded include rewrite does not match the receipt bytes")
        lines[rewrite["line"] - 1] = line.replace(needle, f'include_str!("{rewrite["to"]}")')
    return "\n".join(lines).encode("utf-8")


# Line comment, block comment opener and closer, by file suffix; Lean and Rust nest block comments, TOML has none.
COMMENT_SYNTAX = {".lean": ("--", "/-", "-/"), ".rs": ("//", "/*", "*/"), ".toml": ("#", None, None)}
# Characters after an opener that make a doc or module comment; the view keeps them, so a plain comment cannot
# become a documentation comment unnoticed.
COMMENT_KINDS = {".lean": ("", "-!"), ".rs": ("/!", "*!"), ".toml": ("", "")}
_CHARACTER = re.compile(r"'(?:\\[^'\n]{1,10}|[^\\'\n])'")
_RAW_STRING = re.compile(r'b?r(#*)"')


def _string_end(text, start, suffix, view):
    """Index just past the string literal whose opening quote is at `start`, keeping it whole in `view`."""
    position = start + 1
    interpolated = suffix == ".lean" and start > 0 and text[start - 1] == "!"
    while position < len(text):
        character = text[position]
        if character == "\\":
            position += 2
        elif character == '"':
            view.append(text[start:position + 1])
            return position + 1
        elif interpolated and character == "{":
            inner = []
            position = _scan(text, position + 1, suffix, inner, interpolation=True) + 1
        else:
            position += 1
    raise ValueError("Unclosed string literal")


def _scan(text, position, suffix, view, interpolation=False, spans=None):
    """Append the code view of `text` from `position` to `view`, and each comment's (start, end) to `spans`.

    Return the end of the text, or with `interpolation` the index of the brace that closes the interpolated code.
    """
    spans = [] if spans is None else spans
    line, opener, closer = COMMENT_SYNTAX[suffix]
    line_kinds, block_kinds = COMMENT_KINDS[suffix]
    braces = 0
    while position < len(text):
        character = text[position]
        if interpolation and character == "{":
            braces += 1
        elif interpolation and character == "}":
            if braces == 0:
                return position
            braces -= 1
        if text.startswith(line, position):
            kind = text[position + 2:position + 3]
            end = text.find("\n", position)
            end = len(text) if end < 0 else end
            view.append(line + (kind if kind and kind in line_kinds else ""))
            spans.append((position, end))
            position = end
            continue
        if opener and text.startswith(opener, position):
            kind = text[position + 2:position + 3]
            kind = kind if kind and kind in block_kinds and not text.startswith(closer, position + 2) else ""
            view.append(opener + kind)
            start = position
            depth, position = 1, position + 2 + len(kind)
            while depth:
                if position >= len(text):
                    raise ValueError("Unclosed block comment")
                if text.startswith(opener, position):
                    depth, position = depth + 1, position + 2
                elif text.startswith(closer, position):
                    depth, position = depth - 1, position + 2
                else:
                    if text[position] == "\n":
                        view.append("\n")
                    position += 1
            view.append(closer)
            spans.append((start, position))
            continue
        previous = text[position - 1] if position else ""
        raw = _RAW_STRING.match(text, position) if character in "br" and suffix != ".toml" else None
        if raw and not (previous.isalnum() or previous == "_"):
            terminator = '"' + raw[1]
            end = text.find(terminator, raw.end())
            if end < 0:
                raise ValueError("Unclosed raw string literal")
            view.append(text[position:end + len(terminator)])
            position = end + len(terminator)
            continue
        if character == '"':
            position = _string_end(text, position, suffix, view)
            continue
        if character == "'" and suffix == ".toml":
            # A TOML literal string: no escapes, one line.
            end = text.find("'", position + 1)
            if end < 0 or "\n" in text[position:end]:
                raise ValueError("Unclosed literal string")
            view.append(text[position:end + 1])
            position = end + 1
            continue
        if character == "'":
            literal = _CHARACTER.match(text, position)
            if literal and not (suffix == ".lean" and (previous.isalnum() or previous in "_'!?")):
                view.append(literal[0])
                position = literal.end()
                continue
        if suffix == ".lean" and character == "\u00ab":
            end = text.find("\u00bb", position)
            if end < 0:
                raise ValueError("Unclosed escaped identifier")
            view.append(text[position:end + 1])
            position = end + 1
            continue
        view.append(character)
        position += 1
    if interpolation:
        raise ValueError("Unclosed interpolation")
    return position


def code_view(text, suffix):
    """`text` with every comment body removed; delimiters, comment kinds, line breaks, strings and code are kept."""
    view = []
    _scan(text, 0, suffix, view)
    return "".join(view)


def code_view_sha256(text, suffix):
    return hashlib.sha256(code_view(text, suffix).encode("utf-8")).hexdigest()


def _line_sha256(line):
    return hashlib.sha256(line.encode("utf-8")).hexdigest()


def apply_comment_rewrite(original, rewrite, suffix):
    """Development check: apply a recorded comment rewrite to the reviewed bytes.

    The reviewed file must have the recorded code view, and each edited line the recorded hash of its old text.
    """
    text = original.decode("utf-8")
    if code_view_sha256(text, suffix) != rewrite["code_view_sha256"]:
        raise ValueError("Recorded code view differs from the reviewed bytes")
    lines = text.split("\n")
    for edit in rewrite["edits"]:
        number = edit["line"]
        if (not 1 <= number <= len(lines) or "\n" in edit["to"]
                or _line_sha256(lines[number - 1]) != edit["from_sha256"]):
            raise ValueError("Recorded comment edit does not match the reviewed bytes")
        lines[number - 1] = edit["to"]
    return "\n".join(lines).encode("utf-8")


def check_comment_rewrite(current, rewrite, suffix):
    """Install-time check of a recorded comment rewrite; it needs none of the replaced text.

    Each recorded line must hold its recorded text and lie inside comments, and the file's code view (comment bodies
    removed) must hash to the reviewed file's, so the edits changed comment text only and opened or closed no comment.
    The development check (`apply_comment_rewrite` on the receipt archive) shows that only these lines changed.
    """
    text = current.decode("utf-8")
    view, spans = [], []
    _scan(text, 0, suffix, view, spans=spans)
    if hashlib.sha256("".join(view).encode("utf-8")).hexdigest() != rewrite["code_view_sha256"]:
        raise ValueError("Code differs from the reviewed file beyond comment text")
    edits = rewrite["edits"]
    numbers = [edit["line"] for edit in edits]
    if not edits or len(set(numbers)) != len(numbers):
        raise ValueError("Comment edits must name distinct lines")
    lines = text.split("\n")
    offsets = [0]
    for line in lines:
        offsets.append(offsets[-1] + len(line) + 1)
    starts = [span[0] for span in spans]
    for edit in edits:
        number = edit["line"]
        if (not 1 <= number <= len(lines) or lines[number - 1] != edit["to"]
                or _line_sha256(edit["to"]) == edit["from_sha256"]):
            raise ValueError("Recorded comment edit does not match the file")
        for offset, character in enumerate(edit["to"], offsets[number - 1]):
            index = bisect.bisect_right(starts, offset) - 1
            if not character.isspace() and (index < 0 or offset >= spans[index][1]):
                raise ValueError("Recorded comment edit lies outside comments")


def check_workspace(root, manifest, source_map, check=lambda: None):
    """The root workspace table and lockfile must be the reviewed ones."""
    expected = source_map["workspace"]
    workspace = manifest.get("workspace")
    if workspace != {"members": expected["members"], "exclude": expected["exclude"]}:
        raise ValueError("Unreviewed root workspace table")
    members = ["crates/fang-predicate-index"] + [name for name, crate in source_map["crates"].items()
                                                 if crate["workspace"] == "member"]
    excluded = (list(GROUND) + [name for name, crate in source_map["crates"].items() if crate["workspace"] != "member"]
                + list(OUTSIDE))
    if sorted(members) != sorted(expected["members"]) or sorted(excluded) != sorted(expected["exclude"]):
        raise ValueError("Workspace roles differ from the source map")
    if digest(Path(root) / "Cargo.lock", check) != expected["lock_sha256"]:
        raise ValueError("Unreviewed workspace lockfile")


def rust_files(root, check=lambda: None):
    """Return every moved crate file after checking the exact inventory and hashes."""
    root = Path(root)
    source_map = load_map(root, RUST_MAP, RUST_SCHEMA, check)
    listed = {}
    for name in source_map["files"]:
        crate = next((crate for crate in source_map["crates"] if name.startswith(crate + "/")), None)
        if crate is None:
            raise ValueError(f"Source map file outside its crates: {name}")
        listed.setdefault(crate, set()).add(name[len(crate) + 1:])
    result = []
    for crate in source_map["crates"]:
        directory = root / crate
        if not stat.S_ISDIR(directory.lstat().st_mode):
            raise ValueError(f"Missing moved crate: {crate}")
        if _listed_tree(directory, check) != listed.get(crate, set()):
            raise ValueError(f"Moved crate inventory differs from the source map: {crate}")
        for relative in sorted(listed[crate]):
            path = directory / relative
            entry = source_map["files"][crate + "/" + relative]
            if digest(path, check) != entry["sha256"]:
                raise ValueError(f"Moved file differs from its receipt: {crate}/{relative}")
            if "comment_rewrite" in entry:
                _check_recorded_comments(path, entry, check)
            for rewrite in entry.get("include_rewrites", []):
                check_rust_include(root, path, rewrite, check)
            result.append(path)
    for name, entry in source_map["path_targets"].items():
        if digest(root / name, check) != entry["sha256"]:
            raise ValueError(f"Path target differs from the receipt the crates were built with: {name}")
        if "comment_rewrite" in entry:
            _check_recorded_comments(root / name, entry, check)
    # Data files a crate reads at build or test time from outside its directory (recorded with their reason).
    for name, entry in source_map.get("data_files", {}).items():
        if digest(root / name, check) != entry["sha256"]:
            raise ValueError(f"Crate data file differs from the source map: {name}")
        if "same_as" in entry and digest(root / entry["same_as"], check) != entry["sha256"]:
            raise ValueError(f"Crate data file differs from {entry['same_as']}: {name}")
        if "comment_rewrite" in entry:
            _check_recorded_comments(root / name, entry, check)
        result.append(root / name)
    # The lean-v8 files that crate tests read through recorded include rewrites; callers copy them with the crates.
    targets = sorted({rewrite["target"] for entry in source_map["files"].values()
                      for rewrite in entry.get("include_rewrites", [])})
    result += [root / target for target in targets]
    return result


def check_rust_include(root, path, rewrite, check=lambda: None):
    """A rewritten include must read the recorded lean-v8 file itself."""
    check()
    line = path.read_text(encoding="utf-8").split("\n")[rewrite["line"] - 1]
    target = os.path.normpath(os.path.join(os.path.dirname(os.path.relpath(path, root)), rewrite["to"]))
    if (line.count(f'include_str!("{rewrite["to"]}")') != 1 or Path(target).as_posix() != rewrite["target"]
            or not rewrite["target"].startswith("lean-v8/")):
        raise ValueError(f"Include does not read its recorded lean-v8 file: {path}")
    _regular(root / rewrite["target"], check)


def _check_recorded_comments(path, entry, check):
    """A crate file with recorded comment edits differs from its other recorded rewrites only in comment text.

    The recorded code view is that of the receipt bytes after the path, line and include rewrites, so a manifest with
    path rewrites can also carry comment edits; the receipt check applies the rewrites first, then the comment edits.
    """
    check()
    check_comment_rewrite(path.read_bytes(), entry["comment_rewrite"], path.suffix)


def check_rust_receipts(root, check=lambda: None):
    """Development-tree check: the map itself agrees with the receipt archives."""
    root = Path(root)
    source_map = load_map(root, RUST_MAP, RUST_SCHEMA, check)
    manifests = {}
    for name, receipt in source_map["receipts"].items():
        path = root / receipt["manifest"]
        if digest(path, check) != receipt["sha256"]:
            raise ValueError(f"Receipt pin differs: {name}")
        manifests[name] = json.loads(path.read_text(encoding="utf-8"))
        if manifests[name]["status"] != "passed":
            raise ValueError(f"Receipt did not pass: {name}")
    lean_map = load_map(root, LEAN_MAP, LEAN_SCHEMA, check)
    entries = list(source_map["files"].items()) + list(source_map["path_targets"].items())
    for name, entry in entries:
        manifest = manifests[entry["receipt"]]
        receipt = source_map["receipts"][entry["receipt"]]
        archived = (root / receipt["manifest"]).parent / receipt.get("archive", "run/source") / entry["original"]
        expected = entry.get("original_sha256", entry["sha256"])
        if (manifest[receipt.get("source_table", "source_sha256")].get(entry["original"]) != expected
                or manifest["artifacts_sha256"].get("source/" + entry["original"]) != expected
                or digest(archived, check) != expected):
            raise ValueError(f"Source map differs from the receipt: {name}")
        rebuilt = apply_rewrites(archived.read_bytes(), entry.get("path_rewrites", []), entry.get("line_edits", []),
                                 entry.get("include_rewrites", []))
        for rewrite in entry.get("include_rewrites", []):
            # The receipt tested the include against the same reviewed bytes the lean-v8 file has.
            source = Path(os.path.normpath(os.path.join(os.path.dirname(entry["original"]), rewrite["from"])))
            tested = manifest[receipt.get("source_table", "source_sha256")].get(source.as_posix())
            reviewed = lean_map["files"].get(rewrite["target"][len("lean-v8/"):], {})
            if tested is None or tested != reviewed.get("original_sha256", reviewed.get("sha256")):
                raise ValueError(f"Rewritten include reads other bytes than the receipt tested: {name}")
        if "comment_rewrite" in entry:
            rebuilt = apply_comment_rewrite(rebuilt, entry["comment_rewrite"], Path(name).suffix)
        if hashlib.sha256(rebuilt).hexdigest() != entry["sha256"]:
            raise ValueError(f"Moved file is not the receipt bytes with the recorded path strings: {name}")
    for name, entry in source_map.get("data_files", {}).items():
        manifest = manifests[entry["receipt"]]
        receipt = source_map["receipts"][entry["receipt"]]
        archived = (root / receipt["manifest"]).parent / receipt.get("archive", "run/source") / entry["original"]
        expected = entry.get("original_sha256", entry["sha256"])
        rebuilt = archived.read_bytes()
        if "comment_rewrite" in entry:
            rebuilt = apply_comment_rewrite(rebuilt, entry["comment_rewrite"], Path(name).suffix)
        if (manifest[receipt.get("source_table", "source_sha256")].get(entry["original"]) != expected
                or digest(archived, check) != expected or hashlib.sha256(rebuilt).hexdigest() != entry["sha256"]):
            raise ValueError(f"Crate data file differs from its receipt: {name}")
    for name, entry in source_map["not_moved"].items():
        table = source_map["receipts"][entry["receipt"]].get("source_table", "source_sha256")
        if manifests[entry["receipt"]][table].get(name) != entry["sha256"]:
            raise ValueError(f"Unmoved receipt file differs: {name}")
    return len(entries)


def lean_files(root, check=lambda: None):
    """Return every lean-v8 source after checking the exact inventory and hashes."""
    root = Path(root)
    source_map = load_map(root, LEAN_MAP, LEAN_SCHEMA, check)
    project = root / source_map["project"]
    expected = set(source_map["files"])
    if _listed_tree(project, check, skip=(".lake", "build")) != expected:
        raise ValueError("lean-v8 inventory differs from the source map")
    for relative, entry in sorted(source_map["files"].items()):
        if digest(project / relative, check) != entry["sha256"]:
            raise ValueError(f"lean-v8 file differs from the source map: {relative}")
    check_adaptations(project, source_map, check)
    check_left_out(project, source_map, check)
    return [project / relative for relative in sorted(expected)]


def check_left_out(project, source_map, check=lambda: None):
    """Gate modules recorded as left out (superseded native mains) are absent, and no lean-v8 module imports them."""
    left_out = {}
    for gate in source_map["gates"].values():
        for relative, reason in gate.get("left_out", {}).items():
            if not reason or not relative.endswith(".lean"):
                raise ValueError(f"Left-out module without a reason: {relative}")
            left_out[relative[:-len(".lean")].replace("/", ".")] = relative
    staged = {relative[:-len(".lean")].replace("/", ".")
              for relative in source_map["files"] if relative.endswith(".lean")}
    if set(left_out) & staged or any((project / relative).exists() for relative in left_out.values()):
        raise ValueError("A left-out module is staged in lean-v8")
    for relative in sorted(source_map["files"]):
        check()
        if relative.endswith(".lean"):
            text = (project / relative).read_text(encoding="utf-8")
            if {token for _, match in _imports(text) for token in match[1].split()} & set(left_out):
                raise ValueError(f"Module imports a left-out module: {relative}")


def _imports(text):
    return [(number, match) for number, line in enumerate(text.split("\n"), 1)
            for match in [IMPORT.fullmatch(line)] if match]


def _gate_renames(source_map):
    """Renames recorded for one gate only, by gate name."""
    return {name: gate.get("module_renames", {}) for name, gate in source_map.get("gates", {}).items()}


def check_adaptations(project, source_map, check=lambda: None):
    """The only differences from the gate sources are the recorded module renames, their import lines and comment edits.

    `module_renames` apply to every gate; a gate's own `module_renames` apply to the modules of that gate only,
    because another gate keeps a different module under the old name.
    """
    renames = source_map.get("module_renames", {})
    scoped = _gate_renames(source_map)
    lowered = [relative.lower() for relative in source_map["files"]]
    if len(set(lowered)) != len(lowered):
        raise ValueError("lean-v8 has paths that differ only in letter case")
    for relative, entry in sorted(source_map["files"].items()):
        check()
        if not relative.endswith(".lean"):
            continue
        adaptation = entry.get("adaptation")
        text = (project / relative).read_bytes().decode("utf-8")
        imported = {token for _, match in _imports(text) for token in match[1].split()}
        if imported & set(renames):
            raise ValueError(f"Import of a renamed module remains: {relative}")
        owners = {entry.get("receipt")} | set(entry.get("also_in", []))
        for gate, gate_renames in scoped.items():
            if gate in owners and imported & set(gate_renames):
                raise ValueError(f"Import of a module renamed in {gate} remains: {relative}")
            if gate not in owners and imported & set(gate_renames.values()):
                raise ValueError(f"Import of a module renamed only in {gate}: {relative}")
        own = dict(renames)
        if entry.get("receipt") in scoped and not entry.get("also_in"):
            own |= scoped[entry["receipt"]]
        if adaptation is not None and adaptation["kind"] == "comment-rewrite":
            if relative != entry["original"]:
                raise ValueError(f"Comment rewrite of a moved module: {relative}")
            check_comment_rewrite((project / relative).read_bytes(), adaptation, ".lean")
            continue
        if adaptation is None:
            # A pinned source names its working-tree origin, not an archived path.
            moved = relative != entry.get("original", relative) and entry.get("origin") != "pinned-source"
            if moved or "original_sha256" in entry or imported & set(own.values()):
                raise ValueError(f"Unrecorded adaptation: {relative}")
            continue
        old, new = adaptation["from"], adaptation["to"]
        if own.get(old) != new:
            raise ValueError(f"Adaptation names an unrecorded rename: {relative}")
        if adaptation["kind"] == "module-rename":
            if (relative != new.replace(".", "/") + ".lean" or entry["original"] != old.replace(".", "/") + ".lean"
                    or "original_sha256" in entry):
                raise ValueError(f"Renamed module is not a path-only move: {relative}")
        elif adaptation["kind"] == "import-rename":
            lines = text.split("\n")
            for number, match in _imports(text):
                tokens = match[1].split(" ")
                if (new in tokens) != (number in adaptation["lines"]):
                    raise ValueError(f"Import lines differ from the recorded adaptation: {relative}")
                if new in tokens:
                    lines[number - 1] = lines[number - 1][:match.start(1)] + " ".join(old if t == new else t for t in tokens)
            if (relative != entry["original"]
                    or hashlib.sha256("\n".join(lines).encode("utf-8")).hexdigest() != entry["original_sha256"]):
                raise ValueError(f"Module differs from the gate beyond the recorded import lines: {relative}")
        else:
            raise ValueError(f"Unknown adaptation kind: {relative}")


def check_lean_receipts(root, check=lambda: None):
    """Development-tree check: every module equals its gate's source table and archive, and the audit list its gates."""
    root = Path(root)
    source_map = load_map(root, LEAN_MAP, LEAN_SCHEMA, check)
    checked = 0
    manifests = {}
    for name, receipt in source_map["receipts"].items():
        if digest(root / receipt["manifest"], check) != receipt["sha256"]:
            raise ValueError(f"Receipt pin differs: {name}")
        manifests[name] = json.loads((root / receipt["manifest"]).read_text(encoding="utf-8"))
    gates = {name: manifests[name] for name in source_map["gates"]}
    for name, gate in gates.items():
        covered = {entry["original"] for entry in source_map["files"].values()
                   if (entry["origin"].endswith("-gate") and entry.get("receipt") == name)
                   or name in entry.get("also_in", [])}
        left_out = set(source_map["gates"][name].get("left_out", {}))
        if covered & left_out or covered | left_out != set(gate["source_sha256"]):
            raise ValueError(f"lean-v8 modules are not exactly the module set of {name}")
    for relative, entry in source_map["files"].items():
        if entry["origin"] == "product":
            continue
        original = entry.get("original_sha256", entry["sha256"])
        if entry["origin"] == "pinned-source":
            # Not archived by any gate; the working-tree file, when present, must still have the pinned bytes.
            if (root / entry["original"]).exists() and digest(root / entry["original"], check) != original:
                raise ValueError(f"Pinned source changed in the working tree: {relative}")
            checked += 1
            continue
        manifest = manifests[entry["receipt"]]
        archived = (root / source_map["receipts"][entry["receipt"]]["manifest"]).parent / "run/source" / entry["original"]
        recorded = (manifest["source_sha256"].get(entry["original"]) if entry["origin"].endswith("-gate")
                    else manifest["capture_sha256"].get("source/" + entry["original"]))
        moved = entry.get("adaptation", {}).get("kind") == "module-rename"
        if (relative != entry["original"] and not moved) or not (
                original == recorded == digest(archived, check)
                == manifest["artifacts_sha256"]["source/" + entry["original"]]):
            raise ValueError(f"Lean source differs from its receipt: {relative}")
        if entry.get("adaptation", {}).get("kind") == "comment-rewrite":
            rebuilt = apply_comment_rewrite(archived.read_bytes(), entry["adaptation"], ".lean")
            if hashlib.sha256(rebuilt).hexdigest() != entry["sha256"]:
                raise ValueError(f"Module is not its receipt bytes with the recorded comment edits: {relative}")
        for name in entry.get("also_in", []):
            if gates[name]["source_sha256"].get(entry["original"]) != original:
                raise ValueError(f"Shared module differs in {name}: {relative}")
        checked += 1
    audits = json.loads((root / source_map["project"] / "audits.json").read_text(encoding="utf-8"))
    expected = {}
    for name, gate in gates.items():
        for theorem in gate[source_map["gates"][name].get("audit_key", "fixed_audit_set")]:
            expected.setdefault(theorem, sorted(gate["axiom_audits"][theorem]))
    if {theorem: row["axioms"] for theorem, row in audits["names"].items()} != expected:
        raise ValueError("Fixed audit list differs from the gates")
    if any(audits["roots"][name] != entry["library_roots"] for name, entry in source_map["gates"].items()):
        raise ValueError("Audit roots differ from the gate roots")
    for name, executable in source_map["executables"].items():
        renames = dict(source_map.get("module_renames", {}))
        renames |= source_map["gates"].get(executable.get("gate"), {}).get("module_renames", {})
        renamed = {new: old for old, new in renames.items()}
        closure = sorted(renamed.get(module, module) for module in executable["closure"])
        if "build_receipt" in executable:
            if closure != sorted(manifests[executable["build_receipt"]]["module_order"]):
                raise ValueError(f"{name} closure differs from its native build")
        elif executable.get("closure_source") == "gate":
            # No native build of this closure exists; every module must belong to the executable's gate.
            table = gates[executable["gate"]]["source_sha256"]
            if not {module.replace(".", "/") + ".lean" for module in closure} <= set(table):
                raise ValueError(f"{name} closure leaves its gate")
    return checked
