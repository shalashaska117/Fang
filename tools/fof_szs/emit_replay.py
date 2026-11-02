"""Bounded child for untrusted FOF witnesses; this command never authorizes UNSAT."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True


def main():
    helpers, source, certificate, destination = map(Path, sys.argv[1:])
    sys.path.insert(0, str(helpers))
    from generate import generate, ReplayLimit
    from source_witness import certificate_source
    try:
        replay = generate(source.read_bytes(), certificate.read_bytes(), certificate_source)
        for name, contents in replay.modules:
            (destination / (name + ".lean")).write_text(contents, encoding="utf-8", newline="\n")
        (destination / "emitted.json").write_text(json.dumps({
            "modules": [name for name, _ in replay.modules],
            "input_bytes": replay.input_bytes, "certificate_bytes": replay.certificate_bytes,
            "certificate_nodes": replay.certificate_nodes}) + "\n")
        return 0
    except ReplayLimit:
        sys.stderr.write("ResourceLimit: kernel replay profile bound exceeded\n")
        return 5


if __name__ == "__main__":
    raise SystemExit(main())
