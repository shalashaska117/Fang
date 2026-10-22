"""Fresh native kernel files, checked archive, and explicit partial retention."""
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
import hashlib
from pathlib import Path
import stat
import tempfile
import time
from .supervisor import Failure, read_regular


class KernelWorkspace:
    def __init__(self, supervisor, public, report):
        self.supervisor, self.public, self.report = supervisor, public, report
        supervisor.check("kernel-staging")
        self.native = Path(tempfile.mkdtemp(prefix="fang-kernel-", dir="/var/tmp"))
        self.report.update(state="created", native_path=str(self.native), native_removed=False,
            archive_completed=False, cleanup_completed=False,
            retention="The newly created native path is recorded before initialization can fail.")
        identity = self.native.lstat()
        self.identity = (identity.st_dev, identity.st_ino)
        self.library = self.native / ".proof-library"
        self.started = time.monotonic()
        self.report.update(state="staging", native_path=str(self.native),
            archive_path=str(public), cache=False, archived_files_sha256={},
            accounting="Public and fresh native files share the artifact-byte and entry caps; the native checked-library copy is included. Staging, hashing, archive and cleanup consume the same pipeline deadline.")
        supervisor.additional_artifact_roots.extend([public, self.native])

    def verify_owned(self):
        identity = self.native.lstat()
        if not stat.S_ISDIR(identity.st_mode) or (identity.st_dev, identity.st_ino) != self.identity:
            raise Failure("Error", "Owned native kernel directory was replaced", "kernel-storage")

    def copy_file(self, source, destination, expected=None):
        supervisor = self.supervisor
        supervisor.check("kernel-copy")
        data = read_regular(source, supervisor.limits.artifact_bytes, supervisor.check)
        digest = hashlib.sha256(data).hexdigest()
        if expected is not None and digest != expected:
            raise Failure("Error", "Kernel staging or archive identity differs", "kernel-copy")
        destination.parent.mkdir(parents=True, exist_ok=True)
        with destination.open("xb") as stream:
            for offset in range(0, len(data), 65536):
                supervisor.check("kernel-copy")
                stream.write(data[offset:offset + 65536])
        supervisor.memory()
        supervisor.tree_bytes(self.public)
        copied = read_regular(destination, len(data), supervisor.check)
        if hashlib.sha256(copied).hexdigest() != digest:
            raise Failure("Error", "Archived kernel file differs from its source", "kernel-copy")
        return digest

    def stage_library(self, config):
        expected = config["proof_library"]["files_sha256"]
        source = Path(config["proof_library"]["path"])
        copied = {}
        for relative, digest in sorted(expected.items()):
            path = Path(relative)
            if path.is_absolute() or not path.parts or ".." in path.parts:
                raise Failure("Error", "Unsafe installed library member", "kernel-staging")
            copied[relative] = self.copy_file(source / path, self.library / path, digest)
        if copied != expected:
            raise Failure("Error", "Copied kernel library inventory differs", "kernel-staging")
        self.report.update(state="checking", library_files_sha256=copied,
            staging_seconds=time.monotonic() - self.started)

    def files(self, root):
        self.verify_owned()
        if not stat.S_ISDIR(root.lstat().st_mode):
            raise Failure("Error", "Native kernel inventory root is not a directory", "kernel-file-inventory")
        pending = [root]
        while pending:
            self.supervisor.check("kernel-file-inventory")
            self.verify_owned()
            current = pending.pop()
            for child in sorted(current.iterdir()):
                self.supervisor.check("kernel-file-inventory")
                mode = child.lstat().st_mode
                if stat.S_ISDIR(mode):
                    pending.append(child)
                elif stat.S_ISREG(mode):
                    yield child
                else:
                    raise Failure("Error", "Native kernel workspace contains a nonregular file", "kernel-file-inventory")

    def verify_library(self):
        actual = {path.relative_to(self.library).as_posix():
            hashlib.sha256(read_regular(path, self.supervisor.limits.artifact_bytes, self.supervisor.check)).hexdigest()
            for path in self.files(self.library)}
        if actual != self.report["library_files_sha256"]:
            raise Failure("Error", "Native checked library changed during kernel replay", "kernel-library")
        self.report["library_unchanged_after_checking"] = True

    def archive(self, expected=None):
        self.report["state"] = "archiving"
        archive_started = time.monotonic()
        for path in self.files(self.native):
            relative = path.relative_to(self.native)
            if relative.parts[0] == ".proof-library":
                continue
            digest = self.copy_file(path, self.public / relative, (expected or {}).get(relative.as_posix()))
            self.report["archived_files_sha256"][relative.as_posix()] = digest
        if any(self.report["archived_files_sha256"].get(name) != digest for name, digest in (expected or {}).items()):
            raise Failure("Error", "Required checked source was not archived", "kernel-archive")
        self.report.update(state="archived", archive_completed=True,
            archive_seconds=time.monotonic() - archive_started)

    def cleanup(self):
        # This tree was created by this invocation, never supplied by a caller.
        if not self.report["archive_completed"]:
            raise Failure("Error", "Native evidence cannot be removed before verified archival", "kernel-cleanup")
        if self.native.parent != Path("/var/tmp") or not self.native.name.startswith("fang-kernel-"):
            raise Failure("Error", "Native cleanup target differs", "kernel-cleanup")
        self.report["state"] = "cleaning"
        for path in self.files(self.native):
            self.supervisor.check("kernel-cleanup")
            path.unlink()
        directories, pending = [], [self.native]
        while pending:
            self.supervisor.check("kernel-cleanup")
            self.verify_owned()
            for path in pending.pop().iterdir():
                self.supervisor.check("kernel-cleanup")
                if not stat.S_ISDIR(path.lstat().st_mode):
                    raise Failure("Error", "Native cleanup found an unexpected entry", "kernel-cleanup")
                directories.append(path)
                pending.append(path)
        directories.sort(key=lambda path: len(path.parts), reverse=True)
        for path in directories:
            self.supervisor.check("kernel-cleanup")
            path.rmdir()
        self.supervisor.check("kernel-cleanup")
        self.native.rmdir()
        self.supervisor.additional_artifact_roots.remove(self.native)
        self.supervisor.additional_artifact_roots.remove(self.public)
        self.report.update(state="archived-and-removed", native_removed=True, cleanup_completed=True,
            total_storage_and_checking_seconds=time.monotonic() - self.started)

    def retain_failure(self, error):
        # Failure handling must not start a copy that can outlive an expired
        # deadline. The public terminal manifest records this exact owned path.
        if self.report["cleanup_completed"]:
            self.report.update(state="removed-before-terminal-failure", native_removed=True,
                failure=str(error), retention="Native files were already archived and removed; the final status still failed.")
            return
        try:
            identity = self.native.lstat()
        except FileNotFoundError:
            self.report.update(state="native-missing-after-failure", native_removed=False,
                failure=str(error), native_path_status="missing",
                retention="The native directory is missing without completed owned cleanup. No successful archive or cleanup is inferred from absence.")
            return
        if not stat.S_ISDIR(identity.st_mode) or (identity.st_dev, identity.st_ino) != self.identity:
            self.report.update(state="native-replaced-after-failure", native_removed=False,
                failure=str(error), native_path_status="replaced",
                retention="The native pathname no longer identifies the created directory. The replacement is not removed.")
            return
        retention = ("Verified public archive is complete; owned native cleanup did not finish."
            if self.report["archive_completed"] else
            "Partial native evidence remains at this path. Verified copyback was not completed within the original run.")
        self.report.update(state="retained-after-failure", native_removed=False,
            failure=str(error), retained_path=str(self.native),
            retention=retention + " No cache reuse or successful result is authorized.")
