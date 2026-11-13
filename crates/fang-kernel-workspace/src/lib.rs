// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Fresh native kernel files, a checked archive, and explicit partial retention: a port of
//! tools/fang_szs/storage.py `KernelWorkspace`. The report is the run record's `kernel_storage` object and is
//! passed to each step, since the record owns it; its keys, stage names and reasons are those of storage.py.
//!
//! Its own crate, so that the launcher's older profiles and kernel mode (revision 8) share it and kernel mode's
//! policy pins this crate rather than the whole launcher. Revision 8 uses it without `stage_library` and
//! `verify_library`; no `.proof-library` directory exists unless `stage_library` is called.
#![forbid(unsafe_code)]

use std::collections::BTreeMap;
use std::fs;
use std::io::Write;
use std::os::unix::fs::MetadataExt;
use std::path::{Component, Path, PathBuf};
use std::time::Instant;

use fang_json::{Number, Object, Value};
use fang_supervisor::{Failure, Fault, Status, Supervisor};

const CHUNK: usize = 65536;
/// The Python `supervisor.check` default reserve, in seconds.
const RESERVE: f64 = 0.15;

/// An Error failure at `stage`, as storage.py raised `Failure("Error", reason, stage)`.
fn error(reason: &str, stage: &str) -> Fault {
    Fault::Failure(Failure::new(Status::Error, reason, stage))
}

/// The Python `supervisor.check()` passed to bounded reads: stage "adapter", the default reserve.
fn check(supervisor: &Supervisor) -> Result<(), Failure> {
    supervisor.check("adapter", RESERVE)
}

fn float(value: f64) -> Value {
    Value::Number(Number::Float(value))
}

/// The owned native directory and its public archive root.
pub struct KernelWorkspace {
    native: PathBuf,
    identity: (u64, u64),
    library: PathBuf,
    public: PathBuf,
    started: Instant,
}

impl KernelWorkspace {
    /// Create `/var/tmp/fang-kernel-*`, record its path before anything else can fail, and add the public root
    /// and the native directory to the supervisor's artifact roots.
    pub fn create(
        supervisor: &mut Supervisor,
        public: &Path,
        report: &mut Object,
    ) -> Result<KernelWorkspace, Fault> {
        supervisor.check("kernel-staging", RESERVE)?;
        let native = fang_supervisor::make_temp_dir(Path::new("/var/tmp"), "fang-kernel-")?;
        report.set("state", "created");
        report.set("native_path", native.display().to_string());
        report.set("native_removed", false);
        report.set("archive_completed", false);
        report.set("cleanup_completed", false);
        report.set(
            "retention",
            "The newly created native path is recorded before initialization can fail.",
        );
        let metadata = fs::symlink_metadata(&native).map_err(Fault::at(&native))?;
        let workspace = KernelWorkspace {
            identity: (metadata.dev(), metadata.ino()),
            library: native.join(".proof-library"),
            native: native.clone(),
            public: public.to_path_buf(),
            started: Instant::now(),
        };
        report.set("state", "staging");
        report.set("native_path", native.display().to_string());
        report.set("archive_path", public.display().to_string());
        report.set("cache", false);
        report.set("archived_files_sha256", Value::Object(Object::new()));
        report.set(
            "accounting",
            "Public and fresh native files share the artifact-byte and entry caps; the native checked-library copy is included. Staging, hashing, archive and cleanup consume the same pipeline deadline.",
        );
        supervisor
            .additional_artifact_roots
            .push(public.to_path_buf());
        supervisor.additional_artifact_roots.push(native);
        Ok(workspace)
    }

    pub fn native(&self) -> &Path {
        &self.native
    }

    pub fn library(&self) -> &Path {
        &self.library
    }

    pub fn verify_owned(&self) -> Result<(), Fault> {
        match fs::symlink_metadata(&self.native) {
            Ok(metadata)
                if metadata.is_dir() && (metadata.dev(), metadata.ino()) == self.identity =>
            {
                Ok(())
            }
            _ => Err(error(
                "Owned native kernel directory was replaced",
                "kernel-storage",
            )),
        }
    }

    /// Copy one regular file under the artifact-byte limit, check its expected SHA-256 and re-read the copy.
    pub fn copy_file(
        &self,
        supervisor: &mut Supervisor,
        source: &Path,
        destination: &Path,
        expected: Option<&str>,
    ) -> Result<String, Fault> {
        supervisor.check("kernel-copy", RESERVE)?;
        let limit = supervisor.limits.artifact_bytes;
        let data = {
            let supervisor: &Supervisor = supervisor;
            fang_supervisor::read_regular(source, limit, &mut || check(supervisor))?
        };
        let digest = fang_hash::sha256_hex(&data);
        if expected.is_some_and(|expected| expected != digest) {
            return Err(error(
                "Kernel staging or archive identity differs",
                "kernel-copy",
            ));
        }
        if let Some(parent) = destination.parent() {
            fs::create_dir_all(parent).map_err(Fault::at(parent))?;
        }
        let mut stream = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(destination)
            .map_err(Fault::at(destination))?;
        for piece in data.chunks(CHUNK) {
            supervisor.check("kernel-copy", RESERVE)?;
            stream.write_all(piece).map_err(Fault::Os)?;
        }
        drop(stream);
        supervisor.memory()?;
        supervisor.tree_bytes(&self.public)?;
        let copied = {
            let supervisor: &Supervisor = supervisor;
            fang_supervisor::read_regular(destination, data.len() as u64, &mut || {
                check(supervisor)
            })?
        };
        if fang_hash::sha256_hex(&copied) != digest {
            return Err(error(
                "Archived kernel file differs from its source",
                "kernel-copy",
            ));
        }
        Ok(digest)
    }

    /// Copy a checked library, given as its `{path, files_sha256}` record, into `library()`.
    pub fn stage_library(
        &mut self,
        supervisor: &mut Supervisor,
        library: &Object,
        report: &mut Object,
    ) -> Result<(), Fault> {
        let unsafe_member = || error("Unsafe installed library member", "kernel-staging");
        let source = match library.get("path") {
            Some(Value::String(path)) => PathBuf::from(path),
            _ => return Err(unsafe_member()),
        };
        let Some(Value::Object(expected)) = library.get("files_sha256") else {
            return Err(error(
                "Copied kernel library inventory differs",
                "kernel-staging",
            ));
        };
        let mut sorted: BTreeMap<String, String> = BTreeMap::new();
        for (relative, digest) in expected.iter() {
            let Value::String(digest) = digest else {
                return Err(error(
                    "Copied kernel library inventory differs",
                    "kernel-staging",
                ));
            };
            sorted.insert(relative.to_string(), digest.clone());
        }
        let mut copied = Object::new();
        for (relative, digest) in &sorted {
            let path = Path::new(relative);
            if path.is_absolute()
                || path.components().next().is_none()
                || path
                    .components()
                    .any(|component| component == Component::ParentDir)
            {
                return Err(unsafe_member());
            }
            let digest = self.copy_file(
                supervisor,
                &source.join(path),
                &self.library.join(path),
                Some(digest),
            )?;
            copied.set(relative.as_str(), digest);
        }
        if copied.len() != sorted.len() {
            return Err(error(
                "Copied kernel library inventory differs",
                "kernel-staging",
            ));
        }
        report.set("state", "checking");
        report.set("library_files_sha256", Value::Object(copied));
        report.set(
            "staging_seconds",
            float(self.started.elapsed().as_secs_f64()),
        );
        Ok(())
    }

    /// The regular files under `root`, as storage.py `files` yields them: each directory's entries in sorted
    /// order, subdirectories later from a stack.
    fn files(&self, supervisor: &Supervisor, root: &Path) -> Result<Vec<PathBuf>, Fault> {
        self.verify_owned()?;
        let inventory = |reason: &str| error(reason, "kernel-file-inventory");
        if !fs::symlink_metadata(root)
            .map(|metadata| metadata.is_dir())
            .unwrap_or(false)
        {
            return Err(inventory("Native kernel inventory root is not a directory"));
        }
        let mut found = Vec::new();
        let mut pending = vec![root.to_path_buf()];
        while let Some(current) = pending.pop() {
            supervisor.check("kernel-file-inventory", RESERVE)?;
            self.verify_owned()?;
            let mut children: Vec<PathBuf> = fs::read_dir(&current)
                .map_err(Fault::at(&current))?
                .map(|entry| entry.map(|entry| entry.path()))
                .collect::<Result<_, _>>()
                .map_err(Fault::at(&current))?;
            children.sort();
            for child in children {
                supervisor.check("kernel-file-inventory", RESERVE)?;
                let metadata = fs::symlink_metadata(&child).map_err(Fault::at(&child))?;
                if metadata.is_dir() {
                    pending.push(child);
                } else if metadata.is_file() {
                    found.push(child);
                } else {
                    return Err(inventory(
                        "Native kernel workspace contains a nonregular file",
                    ));
                }
            }
        }
        Ok(found)
    }

    pub fn verify_library(
        &self,
        supervisor: &mut Supervisor,
        report: &mut Object,
    ) -> Result<(), Fault> {
        let limit = supervisor.limits.artifact_bytes;
        let supervisor: &Supervisor = supervisor;
        let mut actual = Object::new();
        for path in self.files(supervisor, &self.library)? {
            let data = fang_supervisor::read_regular(&path, limit, &mut || check(supervisor))?;
            let relative = path
                .strip_prefix(&self.library)
                .unwrap_or(&path)
                .to_string_lossy()
                .to_string();
            actual.set(relative.as_str(), fang_hash::sha256_hex(&data));
        }
        let same = match report.get("library_files_sha256") {
            Some(Value::Object(recorded)) => same_strings(recorded, &actual),
            _ => false,
        };
        if !same {
            return Err(error(
                "Native checked library changed during kernel replay",
                "kernel-library",
            ));
        }
        report.set("library_unchanged_after_checking", true);
        Ok(())
    }

    /// Copy every regular file except the checked-library copy to the public root; every `expected` entry
    /// (path relative to the native directory -> SHA-256) must be archived with that hash.
    pub fn archive(
        &self,
        supervisor: &mut Supervisor,
        expected: &BTreeMap<String, String>,
        report: &mut Object,
    ) -> Result<(), Fault> {
        report.set("state", "archiving");
        let archive_started = Instant::now();
        let files = self.files(supervisor, &self.native)?;
        let mut archived: BTreeMap<String, String> = BTreeMap::new();
        for path in files {
            let relative = path
                .strip_prefix(&self.native)
                .unwrap_or(&path)
                .to_path_buf();
            if relative.components().next() == Some(Component::Normal(".proof-library".as_ref())) {
                continue;
            }
            let name = relative.to_string_lossy().to_string();
            let digest = self.copy_file(
                supervisor,
                &path,
                &self.public.join(&relative),
                expected.get(&name).map(String::as_str),
            )?;
            if let Some(Value::Object(record)) = report.get_mut("archived_files_sha256") {
                record.set(name.as_str(), digest.clone());
            }
            archived.insert(name, digest);
        }
        if expected
            .iter()
            .any(|(name, digest)| archived.get(name) != Some(digest))
        {
            return Err(error(
                "Required checked source was not archived",
                "kernel-archive",
            ));
        }
        report.set("state", "archived");
        report.set("archive_completed", true);
        report.set(
            "archive_seconds",
            float(archive_started.elapsed().as_secs_f64()),
        );
        Ok(())
    }

    /// Remove the native directory after a verified archive. The workspace stays usable, so a later
    /// failure can still be recorded by `retain_failure`, as in storage.py.
    pub fn cleanup(&self, supervisor: &mut Supervisor, report: &mut Object) -> Result<(), Fault> {
        let cleanup = |reason: &str| error(reason, "kernel-cleanup");
        if !matches!(report.get("archive_completed"), Some(Value::Bool(true))) {
            return Err(cleanup(
                "Native evidence cannot be removed before verified archival",
            ));
        }
        let name_ok = self
            .native
            .file_name()
            .and_then(|name| name.to_str())
            .is_some_and(|name| name.starts_with("fang-kernel-"));
        if self.native.parent() != Some(Path::new("/var/tmp")) || !name_ok {
            return Err(cleanup("Native cleanup target differs"));
        }
        report.set("state", "cleaning");
        for path in self.files(supervisor, &self.native)? {
            supervisor.check("kernel-cleanup", RESERVE)?;
            fs::remove_file(&path).map_err(Fault::at(&path))?;
        }
        let mut directories = Vec::new();
        let mut pending = vec![self.native.clone()];
        while let Some(current) = pending.pop() {
            supervisor.check("kernel-cleanup", RESERVE)?;
            self.verify_owned()?;
            for entry in fs::read_dir(&current).map_err(Fault::at(&current))? {
                supervisor.check("kernel-cleanup", RESERVE)?;
                let path = entry.map_err(Fault::Os)?.path();
                if !fs::symlink_metadata(&path)
                    .map(|metadata| metadata.is_dir())
                    .unwrap_or(false)
                {
                    return Err(cleanup("Native cleanup found an unexpected entry"));
                }
                directories.push(path.clone());
                pending.push(path);
            }
        }
        directories.sort_by_key(|path| std::cmp::Reverse(path.components().count()));
        for path in &directories {
            supervisor.check("kernel-cleanup", RESERVE)?;
            fs::remove_dir(path).map_err(Fault::at(path))?;
        }
        supervisor.check("kernel-cleanup", RESERVE)?;
        fs::remove_dir(&self.native).map_err(Fault::at(&self.native))?;
        supervisor
            .additional_artifact_roots
            .retain(|root| root != &self.native);
        if let Some(position) = supervisor
            .additional_artifact_roots
            .iter()
            .position(|root| root == &self.public)
        {
            supervisor.additional_artifact_roots.remove(position);
        }
        report.set("state", "archived-and-removed");
        report.set("native_removed", true);
        report.set("cleanup_completed", true);
        report.set(
            "total_storage_and_checking_seconds",
            float(self.started.elapsed().as_secs_f64()),
        );
        Ok(())
    }

    /// Record what is left after a failure; never copies.
    pub fn retain_failure(&self, failure: &Fault, report: &mut Object) {
        if matches!(report.get("cleanup_completed"), Some(Value::Bool(true))) {
            report.set("state", "removed-before-terminal-failure");
            report.set("native_removed", true);
            report.set("failure", failure.python_str());
            report.set(
                "retention",
                "Native files were already archived and removed; the final status still failed.",
            );
            return;
        }
        let metadata = match fs::symlink_metadata(&self.native) {
            Ok(metadata) => metadata,
            Err(_) => {
                report.set("state", "native-missing-after-failure");
                report.set("native_removed", false);
                report.set("failure", failure.python_str());
                report.set("native_path_status", "missing");
                report.set(
                    "retention",
                    "The native directory is missing without completed owned cleanup. No successful archive or cleanup is inferred from absence.",
                );
                return;
            }
        };
        if !metadata.is_dir() || (metadata.dev(), metadata.ino()) != self.identity {
            report.set("state", "native-replaced-after-failure");
            report.set("native_removed", false);
            report.set("failure", failure.python_str());
            report.set("native_path_status", "replaced");
            report.set("retention", "The native pathname no longer identifies the created directory. The replacement is not removed.");
            return;
        }
        let retention = if matches!(report.get("archive_completed"), Some(Value::Bool(true))) {
            "Verified public archive is complete; owned native cleanup did not finish."
        } else {
            "Partial native evidence remains at this path. Verified copyback was not completed within the original run."
        };
        report.set("state", "retained-after-failure");
        report.set("native_removed", false);
        report.set("failure", failure.python_str());
        report.set("retained_path", self.native.display().to_string());
        report.set(
            "retention",
            format!("{retention} No cache reuse or successful result is authorized."),
        );
    }
}

fn same_strings(left: &Object, right: &Object) -> bool {
    left.len() == right.len()
        && left
            .iter()
            .all(|(key, value)| match (value, right.get(key)) {
                (Value::String(a), Some(Value::String(b))) => a == b,
                _ => false,
            })
}

#[cfg(test)]
mod tests {
    use super::*;
    use fang_supervisor::Limits;

    /// Directories a test created, removed when the test ends, whether it passed or not.
    struct Cleanup(Vec<PathBuf>);

    impl Drop for Cleanup {
        fn drop(&mut self) {
            for path in &self.0 {
                let _ = fs::remove_dir_all(path);
            }
        }
    }

    /// A fresh directory under /var/tmp holding the test's public root, as a run directory holds it.
    fn scratch(cleanup: &mut Cleanup) -> PathBuf {
        let base =
            fang_supervisor::make_temp_dir(Path::new("/var/tmp"), "fang-kernel-workspace-test-")
                .unwrap();
        cleanup.0.push(base.clone());
        fs::create_dir(base.join("public")).unwrap();
        base
    }

    fn create(
        supervisor: &mut Supervisor,
        base: &Path,
        report: &mut Object,
        cleanup: &mut Cleanup,
    ) -> KernelWorkspace {
        let workspace = KernelWorkspace::create(supervisor, &base.join("public"), report).unwrap();
        cleanup.0.push(workspace.native().to_path_buf());
        workspace
    }

    fn supervisor() -> Supervisor {
        Supervisor::new(Limits::default(), None).unwrap()
    }

    fn text<'a>(report: &'a Object, key: &str) -> &'a str {
        report.get(key).and_then(Value::as_str).unwrap_or_default()
    }

    const MODULE: &[u8] = b"theorem t : True := trivial\n";

    #[test]
    fn a_verified_archive_precedes_cleanup() {
        let mut cleanup = Cleanup(Vec::new());
        let (mut supervisor, mut report) = (supervisor(), Object::new());
        let base = scratch(&mut cleanup);
        let first = create(&mut supervisor, &base, &mut report, &mut cleanup);
        assert_eq!(text(&report, "state"), "staging");
        assert!(!first.library().exists());
        fs::create_dir(first.native().join("modules")).unwrap();
        fs::write(first.native().join("modules/A.lean"), MODULE).unwrap();
        let digest = fang_hash::sha256_hex(MODULE);
        let refused = first.cleanup(&mut supervisor, &mut report).unwrap_err();
        assert_eq!(
            refused.python_str(),
            "Native evidence cannot be removed before verified archival"
        );
        let wrong = BTreeMap::from([("modules/B.lean".to_string(), digest.clone())]);
        let missing = first
            .archive(&mut supervisor, &wrong, &mut report)
            .unwrap_err();
        assert_eq!(
            missing.python_str(),
            "Required checked source was not archived"
        );

        let mut report = Object::new();
        let base = scratch(&mut cleanup);
        let workspace = create(&mut supervisor, &base, &mut report, &mut cleanup);
        fs::create_dir(workspace.native().join("modules")).unwrap();
        fs::write(workspace.native().join("modules/A.lean"), MODULE).unwrap();
        let expected = BTreeMap::from([("modules/A.lean".to_string(), digest)]);
        workspace
            .archive(&mut supervisor, &expected, &mut report)
            .unwrap();
        assert_eq!(
            fs::read(base.join("public/modules/A.lean")).unwrap(),
            MODULE
        );
        workspace.cleanup(&mut supervisor, &mut report).unwrap();
        assert!(!workspace.native().exists());
        assert_eq!(text(&report, "state"), "archived-and-removed");
        workspace.retain_failure(&Fault::Value("late".into()), &mut report);
        assert_eq!(text(&report, "state"), "removed-before-terminal-failure");
    }

    #[test]
    fn a_failure_retains_the_native_directory() {
        let mut cleanup = Cleanup(Vec::new());
        let (mut supervisor, mut report) = (supervisor(), Object::new());
        let base = scratch(&mut cleanup);
        let workspace = create(&mut supervisor, &base, &mut report, &mut cleanup);
        fs::write(workspace.native().join("partial.lean"), "x").unwrap();
        workspace.retain_failure(&Fault::Value("stopped".into()), &mut report);
        assert_eq!(text(&report, "state"), "retained-after-failure");
        assert_eq!(text(&report, "failure"), "stopped");
        assert_eq!(
            text(&report, "retained_path"),
            workspace.native().display().to_string()
        );
        assert!(workspace.native().join("partial.lean").is_file());
        fs::remove_dir_all(workspace.native()).unwrap();
        workspace.retain_failure(&Fault::Value("stopped".into()), &mut report);
        assert_eq!(text(&report, "state"), "native-missing-after-failure");
    }

    #[test]
    fn the_library_copy_is_checked_before_and_after() {
        let mut cleanup = Cleanup(Vec::new());
        let base = scratch(&mut cleanup);
        let library = base.join("library");
        fs::create_dir_all(library.join("Fang")).unwrap();
        fs::write(library.join("Fang/A.olean"), "a").unwrap();
        let mut files = Object::new();
        files.set("Fang/A.olean", fang_hash::sha256_hex(b"a"));
        let mut record = Object::new();
        record.set("path", library.display().to_string());
        record.set("files_sha256", Value::Object(files));
        let (mut supervisor, mut report) = (supervisor(), Object::new());
        let mut workspace = create(&mut supervisor, &base, &mut report, &mut cleanup);
        workspace
            .stage_library(&mut supervisor, &record, &mut report)
            .unwrap();
        assert_eq!(text(&report, "state"), "checking");
        workspace
            .verify_library(&mut supervisor, &mut report)
            .unwrap();
        fs::write(workspace.library().join("Fang/A.olean"), "b").unwrap();
        let changed = workspace
            .verify_library(&mut supervisor, &mut report)
            .unwrap_err();
        assert_eq!(
            changed.python_str(),
            "Native checked library changed during kernel replay"
        );
        let mut unsafe_files = Object::new();
        unsafe_files.set("../A.olean", fang_hash::sha256_hex(b"a"));
        record.set("files_sha256", Value::Object(unsafe_files));
        let refused = workspace
            .stage_library(&mut supervisor, &record, &mut report)
            .unwrap_err();
        assert_eq!(refused.python_str(), "Unsafe installed library member");
    }
}
