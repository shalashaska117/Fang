"""Capture complete ground-FOF TSTP output before reporting a checked result."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
# Adapted from Fang's accepted tools/fang_szs/tstp.py protocol boundary.
from fang_szs.supervisor import Failure, Snapshot


def validate_output(data, check=lambda: None):
    """Transport guard only; the checked exporter establishes the row semantics."""
    if not data or not data.endswith(b"\n") or any(c > 127 for c in data):
        raise Failure("Error", "Exporter returned empty, truncated or non-ASCII text", "exporter")
    rows = data.splitlines(keepends=True)
    for row in rows:
        check()
        if not row.startswith((b"cnf('", b"fof('")) or not row.endswith(b").\n") or b"%" in row or b"\r" in row:
            raise Failure("Error", "Exporter violated its row-only output protocol", "exporter")
    if not rows[-1].startswith(b"cnf('") or b",($false)," not in rows[-1]:
        raise Failure("Error", "Exporter did not end with an empty clause", "exporter")
    return len(rows)


def export_solution(supervisor, config, root, source, certificate, byte_limit):
    if len(source.data) > 1 << 20 or len(certificate.data) > 1 << 20:
        raise Failure("ResourceOut", "TSTP export accepts at most 1 MiB each of input and certificate", "exporter")
    record, stdout, stderr = supervisor.run("exporter", [config["exporter"]["path"],
        source.argument, certificate.argument, "input.p"], root / "exporter", root,
        (source.fd, certificate.fd), stdout_limit=byte_limit)
    if record["exit_code"] == 2 and not stdout and stderr in (
            b"resource-exhaustion: export supports at most 1000 certificate nodes\n",
            b"resource-exhaustion: TSTP output exceeds 16 MiB\n"):
        raise Failure("ResourceOut", stderr.decode("ascii").strip(), "exporter")
    if record["exit_code"] != 0 or record["classification"] != "completed" or stderr:
        raise Failure("Error", "Pinned FOF TSTP exporter did not return a clean success", "exporter")
    count = validate_output(stdout, supervisor.check)
    source.verify(supervisor.check)
    certificate.verify(supervisor.check)
    snapshot = Snapshot(root / "solution.tstp", stdout)
    try:
        snapshot.verify(supervisor.check)
        return {"path": "solution.tstp", "bytes": len(stdout), "sha256": snapshot.sha256,
            "rows": count, "source_label": "input.p", "execution": "compiled-exporter",
            "per_instance_kernel_check_of_printed_bytes": False,
            "scope": "Checked ground-FOF exporter correspondence plus trusted compilation/runtime; the kernel profile proves the original input/certificate pair"}
    finally:
        snapshot.close()
