"""Capture a pinned compiled export before emitting any positive SZS output."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
from .supervisor import Failure, Snapshot, digest_bytes, read_regular


def validate_output(data, check=lambda: None):
    """Protocol guard only. Grammar/semantics come from the checked exporter."""
    if not data or not data.endswith(b"\n") or any(c > 127 for c in data):
        raise Failure("Error", "Exporter returned empty, truncated or non-ASCII text", "exporter")
    rows = data.splitlines(keepends=True)
    for row in rows:
        check()
        if not row.startswith(b"cnf('") or not row.endswith(b").\n") or b"%" in row or b"\r" in row:
            raise Failure("Error", "Exporter violated its row-only output protocol", "exporter")
    if b",($false)," not in rows[-1]:
        raise Failure("Error", "Exporter did not end with an empty clause", "exporter")
    return len(rows)


def export_solution(supervisor, config, root, source, certificate, byte_limit):
    # The proved exporter has a separate, smaller input/certificate boundary.
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
        raise Failure("Error", "Pinned TSTP exporter did not return a clean success", "exporter")
    count = validate_output(stdout, supervisor.check)
    source.verify(supervisor.check)
    certificate.verify(supervisor.check)
    snapshot = Snapshot(root / "solution.tstp", stdout)
    try:
        snapshot.verify(supervisor.check)
        return {"path": "solution.tstp", "bytes": len(stdout), "sha256": snapshot.sha256,
            "rows": count, "source_label": "input.p", "execution": "compiled-exporter",
            "per_instance_kernel_check_of_printed_bytes": False,
            "scope": "General exporter correspondence proofs plus trusted compilation/runtime; kernel profile checks the original input and internal certificate"}
    finally:
        snapshot.close()


def read_solution(root, record, check):
    data = read_regular(root / "solution.tstp", record["bytes"], check)
    if len(data) != record["bytes"] or digest_bytes(data) != record["sha256"]:
        raise Failure("Error", "Captured solution changed before output", "exporter")
    return data


def solution_output(data, problem_id):
    return (b"% Fang TSTP execution: compiled exporter; printed bytes are not a per-instance kernel theorem\n"
        + f"% SZS output start CNFRefutation for {problem_id}\n".encode("ascii")
        + data + f"% SZS output end CNFRefutation for {problem_id}\n".encode("ascii"))
