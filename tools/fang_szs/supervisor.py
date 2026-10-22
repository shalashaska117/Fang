"""Bounded Linux children under one deadline; no background service."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
from dataclasses import dataclass
import ctypes
import fcntl
import hashlib
import json
import os
from pathlib import Path
import resource
import signal
import stat
import subprocess
import time


EXIT = {"Unsatisfiable": 0, "GaveUp": 2, "Unknown": 2, "InputError": 3,
        "Inappropriate": 4, "ResourceOut": 5, "Error": 6, "Timeout": 7,
        "MemoryOut": 8, "Forced": 9}


class Failure(Exception):
    def __init__(self, status, reason, stage="adapter"):
        super().__init__(reason)
        self.status, self.reason, self.stage = status, reason, stage


def digest_bytes(data):
    return hashlib.sha256(data).hexdigest()


def strict_json(text):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError("Duplicate JSON field")
            result[key] = value
        return result
    return json.loads(text, object_pairs_hook=pairs,
        parse_constant=lambda value: (_ for _ in ()).throw(ValueError("Nonfinite JSON number")))


def write_json(path, value):
    temporary = path.with_name(path.name + ".new")
    with temporary.open("x", encoding="utf-8") as stream:
        json.dump(value, stream, indent=2, sort_keys=True, allow_nan=False)
        stream.write("\n")
    os.replace(temporary, path)


def read_regular(path, limit, check=lambda: None):
    """Read one regular inode, at most limit+1 bytes; never wait on a FIFO."""
    flags = os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK
    descriptor = os.open(path, flags)
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise Failure("Error", "A required artifact is not a regular file")
        pieces, length = [], 0
        while length <= limit:
            check()
            part = os.read(descriptor, min(65536, limit + 1 - length))
            if not part:
                break
            pieces.append(part)
            length += len(part)
        if length > limit:
            raise Failure("ResourceOut", "Declared byte limit exceeded")
        return b"".join(pieces)
    finally:
        os.close(descriptor)


class Snapshot:
    """Disk evidence plus a sealed Linux descriptor supplied to every child."""
    def __init__(self, path, data):
        self.path, self.data, self.sha256 = path, data, digest_bytes(data)
        with path.open("xb") as stream:
            stream.write(data)
        path.chmod(0o400)
        self.fd = os.memfd_create("fang-captured-data", os.MFD_ALLOW_SEALING)
        view = memoryview(data)
        while view:
            written = os.write(self.fd, view)
            view = view[written:]
        fcntl.fcntl(self.fd, fcntl.F_ADD_SEALS,
            fcntl.F_SEAL_WRITE | fcntl.F_SEAL_SHRINK | fcntl.F_SEAL_GROW | fcntl.F_SEAL_SEAL)
        self.argument = f"/proc/self/fd/{self.fd}"

    def verify(self, check=lambda: None):
        if read_regular(self.path, len(self.data), check) != self.data:
            raise Failure("Error", "Captured disk artifact changed")

    def close(self):
        os.close(self.fd)


@dataclass(frozen=True)
class Limits:
    wall_seconds: float = 60.0
    memory_mib: int = 2048
    input_bytes: int = 1 << 20
    certificate_bytes: int = 64 << 20
    log_bytes: int = 4 << 20
    artifact_bytes: int = 256 << 20
    poll_seconds: float = 0.02


def process_table():
    """PID -> (parent, group, start ticks, resident KiB), excluding reaped tasks."""
    result = {}
    page_kib = os.sysconf("SC_PAGE_SIZE") // 1024
    for entry in Path("/proc").iterdir():
        if not entry.name.isdecimal():
            continue
        try:
            text = (entry / "stat").read_text()
            fields = text[text.rfind(")") + 2:].split()
            result[int(entry.name)] = (int(fields[1]), int(fields[2]),
                int(fields[19]), int(fields[21]) * page_kib)
        except (FileNotFoundError, ProcessLookupError):
            continue
    return result


def descendants(table, parent):
    owned, frontier = set(), {parent}
    while frontier:
        next_level = {pid for pid, info in table.items() if info[0] in frontier} - owned
        owned |= next_level
        frontier = next_level
    return owned


def child_environment():
    """Deliberately exclude loader, Python and inherited Lean search overrides."""
    return {"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8", "LC_ALL": "C.UTF-8",
            "PYTHONDONTWRITEBYTECODE": "1"}


ENVIRONMENT_KEYS = frozenset({"PATH", "LANG", "LC_ALL", "LC_CTYPE", "HOME", "USER", "TMPDIR", "TMP", "TEMP", "XDG_CACHE_HOME",
    "RUSTUP_HOME", "CARGO_HOME", "RUSTUP_TOOLCHAIN", "CARGO_TARGET_DIR", "CARGO_NET_OFFLINE",
    "CARGO_BUILD_JOBS", "LEAN_PATH", "LEAN_NUM_THREADS", "PYTHONDONTWRITEBYTECODE"})


class Supervisor:
    def __init__(self, limits, started=None):
        self.limits = limits
        self.started = time.monotonic() if started is None else started
        self.deadline = self.started + limits.wall_seconds
        self.cancelled = False
        self.records = []
        self.peak_kib = 0
        self.additional_artifact_roots = []
        self.pid = os.getpid()
        self._old_handlers = {}
        # Orphaned grandchildren stay owned by this finite adapter invocation.
        if ctypes.CDLL(None, use_errno=True).prctl(36, 1, 0, 0, 0) != 0:
            raise OSError(ctypes.get_errno(), "Cannot enable child subreaper")
        for number in (signal.SIGINT, signal.SIGTERM):
            self._old_handlers[number] = signal.signal(number, self._cancel)

    def _cancel(self, _number, _frame):
        self.cancelled = True

    def close(self):
        for number, handler in self._old_handlers.items():
            signal.signal(number, handler)

    def check(self, stage="adapter", reserve=0.15):
        if self.cancelled:
            raise Failure("Forced", "External cancellation", stage)
        if time.monotonic() >= self.deadline - reserve:
            raise Failure("Timeout", "Whole-pipeline deadline reached", stage)

    def memory(self, table=None):
        table = process_table() if table is None else table
        total = sum(table[pid][3] for pid in descendants(table, self.pid) | {self.pid}
                    if pid in table)
        self.peak_kib = max(self.peak_kib, total)
        if total > self.limits.memory_mib * 1024:
            raise Failure("MemoryOut", "Sampled adapter-plus-descendant RSS limit reached")
        return total

    def tree_bytes(self, directory):
        roots = list(dict.fromkeys([Path(directory), *self.additional_artifact_roots]))
        total, count, pending = 0, 0, roots.copy()
        while pending:
            self.check("artifact-scan")
            current = pending.pop()
            try:
                entries = os.scandir(current)
            except FileNotFoundError:
                if current in roots:
                    raise
                # Build tools can remove a queued temporary directory between
                # its parent's listing and this scan. Required reads stay strict.
                continue
            with entries:
                for entry in entries:
                    self.check("artifact-scan")
                    count += 1
                    if count > 100000:
                        raise Failure("ResourceOut", "Run artifact entry limit reached")
                    try:
                        info = entry.stat(follow_symlinks=False)
                    except FileNotFoundError:
                        # A disappearing temporary file contributes no retained
                        # bytes; all other I/O errors still stop the run.
                        continue
                    if stat.S_ISLNK(info.st_mode) or not (stat.S_ISDIR(info.st_mode) or stat.S_ISREG(info.st_mode)):
                        raise Failure("Error", "Child created a nonregular artifact")
                    if stat.S_ISDIR(info.st_mode):
                        pending.append(entry.path)
                    else:
                        total += info.st_size
                    if total > self.limits.artifact_bytes:
                        raise Failure("ResourceOut", "Aggregate run artifact byte limit reached")
        return total

    def cleanup(self, process):
        """Signal only this subreaper's owned descendants; preserve PID identity."""
        table = process_table()
        owned = {pid: table[pid][2] for pid in descendants(table, self.pid)}
        for pid, start in owned.items():
            current = process_table().get(pid)
            if current is not None and current[2] == start:
                try:
                    os.kill(pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
        process.wait()
        # Killing ancestors makes remaining descendants direct adopted children.
        cleanup_deadline = time.monotonic() + 1.0
        while True:
            table = process_table()
            remaining = descendants(table, self.pid)
            for pid in remaining:
                try:
                    os.kill(pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            try:
                while os.waitpid(-1, os.WNOHANG)[0]:
                    pass
            except ChildProcessError:
                pass
            if not descendants(process_table(), self.pid):
                return sorted(owned)
            if time.monotonic() >= cleanup_deadline:
                raise Failure("Error", "Owned descendants did not terminate during cleanup")
            time.sleep(0.005)

    def run(self, stage, command, directory, run_root, pass_fds=(), environment=None, *, stdout_limit=None):
        self.check(stage)
        stdout_limit = self.limits.log_bytes if stdout_limit is None else stdout_limit
        if type(stdout_limit) is not int or stdout_limit < 0:
            raise Failure("Error", "Invalid stdout byte limit", stage)
        stream_limits = {"stdout": stdout_limit, "stderr": self.limits.log_bytes}
        directory.mkdir(mode=0o700)
        stdout_path, stderr_path = directory / "stdout", directory / "stderr"
        started = time.monotonic()
        usage = resource.getrusage(resource.RUSAGE_CHILDREN)
        record = {"stage": stage, "command": list(map(str, command)), "started_seconds": started - self.started,
            "stdout": str(stdout_path.relative_to(run_root)), "stderr": str(stderr_path.relative_to(run_root)),
            "classification": "starting", "exit_code": None}
        record["stream_byte_limits"] = stream_limits
        self.records.append(record)
        process, failure = None, None
        log_identity = {}
        peak = 0
        try:
            with stdout_path.open("xb") as stdout, stderr_path.open("xb") as stderr:
                for name, stream in (("stdout", stdout), ("stderr", stderr)):
                    info = os.fstat(stream.fileno())
                    log_identity[name] = (info.st_dev, info.st_ino)
                env = child_environment() if environment is None else environment.copy()
                if set(env) - ENVIRONMENT_KEYS:
                    raise Failure("Error", "Child environment contains unapproved variables", stage)
                env["PYTHONDONTWRITEBYTECODE"] = "1"
                record["environment"] = env
                process = subprocess.Popen(list(map(str, command)), cwd=directory, env=env,
                    stdin=subprocess.DEVNULL, stdout=stdout, stderr=stderr,
                    pass_fds=tuple(pass_fds), start_new_session=True)
                record["pid"] = process.pid
                while True:
                    self.check(stage)
                    peak = max(peak, self.memory())
                    self.tree_bytes(run_root)
                    if stdout_path.stat().st_size > stdout_limit or stderr_path.stat().st_size > self.limits.log_bytes:
                        raise Failure("ResourceOut", "Child stdout/stderr byte limit reached", stage)
                    if process.poll() is not None:
                        break
                    time.sleep(min(self.limits.poll_seconds, max(0.001, self.deadline - time.monotonic())))
                record["exit_code"] = process.returncode
                if descendants(process_table(), self.pid):
                    raise Failure("Error", "Child exited with live descendants", stage)
                record["classification"] = "completed" if process.returncode == 0 else (
                    "signal" if process.returncode < 0 else "nonzero-exit")
        except Failure as error:
            failure = error
            record["classification"] = error.status
        except (OSError, ValueError) as error:
            failure = Failure("Error", f"Child launch or supervision failed: {error}", stage)
            record["classification"] = "Error"
        finally:
            if process is not None:
                try:
                    record["terminated_owned_pids"] = self.cleanup(process)
                except Failure as error:
                    failure = error
                    record["classification"] = "Error"
                record["exit_code"] = process.returncode
            record["elapsed_seconds"] = time.monotonic() - started
            record["peak_adapter_tree_rss_kib"] = peak
            after = resource.getrusage(resource.RUSAGE_CHILDREN)
            record["children_user_seconds"] = after.ru_utime - usage.ru_utime
            record["children_system_seconds"] = after.ru_stime - usage.ru_stime
            for name, path in (("stdout", stdout_path), ("stderr", stderr_path)):
                try:
                    info = path.lstat()
                except FileNotFoundError:
                    record[name + "_hash_status"] = "missing"
                    if process is not None:
                        failure = Failure("Error", "Child removed its log pathname", stage)
                        record["classification"] = "Error"
                    continue
                if not stat.S_ISREG(info.st_mode) or (info.st_dev, info.st_ino) != log_identity.get(name):
                    record[name + "_hash_status"] = "nonregular-or-replaced-path"
                    failure = Failure("Error", "Child replaced its log pathname", stage)
                    record["classification"] = "Error"
                    continue
                record[name + "_bytes"] = info.st_size
                # Oversized/sparse logs remain evidence, but cannot force an
                # unbounded hash after the supervisor has stopped the child.
                if info.st_size > stream_limits[name]:
                    record[name + "_hash_status"] = "skipped-over-log-limit"
                    failure = Failure("ResourceOut", "Child stdout/stderr byte limit reached", stage)
                    record["classification"] = "ResourceOut"
                elif self.cancelled or time.monotonic() >= self.deadline - 0.15:
                    record[name + "_hash_status"] = "skipped-after-deadline-or-cancellation"
                else:
                    hasher = hashlib.sha256()
                    descriptor = os.open(path, os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW)
                    try:
                        opened = os.fstat(descriptor)
                        if not stat.S_ISREG(opened.st_mode) or (opened.st_dev, opened.st_ino) != log_identity[name]:
                            failure = Failure("Error", "Log identity changed while opening", stage)
                            record["classification"] = "Error"
                            record[name + "_hash_status"] = "changed-while-opening"
                            continue
                        remaining = stream_limits[name] + 1
                        while remaining:
                            if self.cancelled or time.monotonic() >= self.deadline - 0.15:
                                record[name + "_hash_status"] = "incomplete-at-deadline-or-cancellation"
                                break
                            block = os.read(descriptor, min(65536, remaining))
                            if not block:
                                record[name + "_sha256"] = hasher.hexdigest()
                                record[name + "_hash_status"] = "complete"
                                break
                            hasher.update(block)
                            remaining -= len(block)
                        if remaining == 0:
                            failure = Failure("ResourceOut", "Log grew beyond its bound", stage)
                            record["classification"] = "ResourceOut"
                            record[name + "_hash_status"] = "grew-over-limit"
                    finally:
                        os.close(descriptor)
        if failure is not None:
            raise failure
        self.check(stage)
        return record, read_regular(stdout_path, stdout_limit, self.check), read_regular(stderr_path, self.limits.log_bytes, self.check)
