// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The storage controls of tools/tests/test_fang_szs.py (`StorageTests`), on the Rust KernelWorkspace. Each
//! test is named after the Python test it replaces, without its `test_` prefix. Synthetic files only; these are
//! workspace controls, not proof acceptance evidence.

use std::collections::BTreeMap;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use fang_json::{Object, Value};
use fang_kernel_workspace::KernelWorkspace;
use fang_supervisor::{Fault, Limits, Status, Supervisor};

/// One test's public root, workspace and report. Drop removes what the test created, whether it passed or not.
struct Fixture {
    base: PathBuf,
    public: PathBuf,
    supervisor: Supervisor,
    report: Object,
    workspace: KernelWorkspace,
}

impl Fixture {
    /// `setUp`: a fresh public root and a workspace under a supervisor with a 10 s deadline.
    fn new() -> Fixture {
        let base =
            fang_supervisor::make_temp_dir(Path::new("/var/tmp"), "fang-storage-control-").unwrap();
        let public = base.join("public");
        fs::create_dir(&public).unwrap();
        let mut supervisor = Supervisor::new(
            Limits {
                wall_seconds: 10.0,
                ..Limits::default()
            },
            None,
        )
        .unwrap();
        let mut report = Object::new();
        let workspace = KernelWorkspace::create(&mut supervisor, &public, &mut report).unwrap();
        Fixture {
            base,
            public,
            supervisor,
            report,
            workspace,
        }
    }

    fn native(&self) -> PathBuf {
        self.workspace.native().to_path_buf()
    }

    /// A checked library of one file, as its `{path, files_sha256}` record.
    fn library(&self) -> Object {
        let source = self.base.join("library");
        fs::create_dir(&source).unwrap();
        fs::write(source.join("checked.olean"), b"checked library control").unwrap();
        let mut files = Object::new();
        files.set(
            "checked.olean",
            fang_hash::sha256_hex(b"checked library control"),
        );
        let mut record = Object::new();
        record.set("path", source.display().to_string());
        record.set("files_sha256", Value::Object(files));
        record
    }

    fn state(&self) -> &str {
        self.report
            .get("state")
            .and_then(Value::as_str)
            .unwrap_or_default()
    }

    fn flag(&self, key: &str) -> Option<bool> {
        self.report.get(key).and_then(Value::as_bool)
    }

    fn archive(&mut self, expected: &[(&str, &str)]) -> Result<(), Fault> {
        let expected: BTreeMap<String, String> = expected
            .iter()
            .map(|(name, digest)| (name.to_string(), digest.to_string()))
            .collect();
        self.workspace
            .archive(&mut self.supervisor, &expected, &mut self.report)
    }

    fn cleanup(&mut self) -> Result<(), Fault> {
        self.workspace
            .cleanup(&mut self.supervisor, &mut self.report)
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        let native = self.native();
        if let Ok(metadata) = fs::symlink_metadata(&native)
            && metadata.is_dir()
        {
            let _ = fs::set_permissions(&native, fs::Permissions::from_mode(0o700));
            let _ = fs::remove_dir_all(&native);
        }
        let _ = fs::remove_dir_all(&self.base);
    }
}

#[test]
fn copy_archive_and_owned_cleanup() {
    let mut fixture = Fixture::new();
    let library = fixture.library();
    fixture
        .workspace
        .stage_library(&mut fixture.supervisor, &library, &mut fixture.report)
        .unwrap();
    fs::create_dir(fixture.native().join("kernel")).unwrap();
    fs::write(
        fixture.native().join("kernel/Audit.lean"),
        b"fixed audit control",
    )
    .unwrap();
    fixture.archive(&[]).unwrap();
    fixture.cleanup().unwrap();
    assert_eq!(
        fs::read(fixture.public.join("kernel/Audit.lean")).unwrap(),
        b"fixed audit control"
    );
    assert!(!fixture.public.join(".proof-library").exists());
    assert_eq!(fixture.state(), "archived-and-removed");
    assert!(!fixture.native().exists());
    assert!(fixture.supervisor.additional_artifact_roots.is_empty());
}

#[test]
fn bad_library_pin_retains_failed_workspace() {
    let mut fixture = Fixture::new();
    let mut library = fixture.library();
    let mut files = Object::new();
    files.set("checked.olean", "0".repeat(64));
    library.set("files_sha256", Value::Object(files));
    let failure = fixture
        .workspace
        .stage_library(&mut fixture.supervisor, &library, &mut fixture.report)
        .unwrap_err();
    fixture
        .workspace
        .retain_failure(&failure, &mut fixture.report);
    assert_eq!(fixture.state(), "retained-after-failure");
    assert!(fixture.native().is_dir());
}

#[test]
fn changed_staged_library_is_rejected() {
    let mut fixture = Fixture::new();
    let library = fixture.library();
    fixture
        .workspace
        .stage_library(&mut fixture.supervisor, &library, &mut fixture.report)
        .unwrap();
    fs::write(
        fixture.workspace.library().join("checked.olean"),
        b"changed",
    )
    .unwrap();
    let failure = fixture
        .workspace
        .verify_library(&mut fixture.supervisor, &mut fixture.report)
        .unwrap_err();
    assert_eq!(failure.status(), Status::Error);
}

#[test]
fn archive_checks_previously_checked_source_hash() {
    let mut fixture = Fixture::new();
    fs::write(fixture.native().join("Audit.lean"), b"changed").unwrap();
    let zeros = "0".repeat(64);
    let failure = fixture.archive(&[("Audit.lean", &zeros)]).unwrap_err();
    assert_eq!(
        failure.python_str(),
        "Kernel staging or archive identity differs"
    );
    assert!(!fixture.public.join("Audit.lean").exists());
}

#[test]
fn public_and_native_bytes_share_one_cap() {
    let mut fixture = Fixture::new();
    fs::write(fixture.public.join("public-data"), b"123456").unwrap();
    fs::write(fixture.native().join("native-data"), b"abcdef").unwrap();
    fixture.supervisor.limits = Limits {
        artifact_bytes: 10,
        ..Limits::default()
    };
    let failure = fixture.supervisor.tree_bytes(&fixture.public).unwrap_err();
    assert_eq!(failure.status(), Status::ResourceOut);
}

#[test]
fn expired_archive_retains_native_evidence() {
    let mut fixture = Fixture::new();
    fs::write(fixture.native().join("proof-data"), b"keep").unwrap();
    fixture
        .supervisor
        .set_deadline(Instant::now().checked_sub(Duration::from_secs(1)).unwrap());
    let failure = fixture.archive(&[]).unwrap_err();
    fixture
        .workspace
        .retain_failure(&failure, &mut fixture.report);
    assert_eq!(failure.status(), Status::Timeout);
    assert_eq!(
        fs::read(fixture.native().join("proof-data")).unwrap(),
        b"keep"
    );
    assert_eq!(
        fixture.report.get("retained_path").and_then(Value::as_str),
        Some(fixture.native().display().to_string().as_str())
    );
}

#[test]
fn archive_does_not_overwrite_public_files() {
    let mut fixture = Fixture::new();
    fs::write(fixture.native().join("proof-data"), b"new").unwrap();
    fs::write(fixture.public.join("proof-data"), b"old").unwrap();
    let failure = fixture.archive(&[]).unwrap_err();
    assert!(
        matches!(&failure, Fault::OsAt(error, _) if error.kind() == std::io::ErrorKind::AlreadyExists),
        "{failure:?}"
    );
    assert_eq!(fs::read(fixture.public.join("proof-data")).unwrap(), b"old");
}

#[test]
fn changed_native_directory_identity_is_rejected() {
    // The Python control changed the recorded identity; here the directory itself is replaced at its path.
    let mut fixture = Fixture::new();
    fixture.archive(&[]).unwrap();
    let native = fixture.native();
    let moved = fixture.base.join("moved-native");
    fs::rename(&native, &moved).unwrap();
    fs::create_dir(&native).unwrap();
    let failure = fixture.cleanup().unwrap_err();
    assert_eq!(
        failure.python_str(),
        "Owned native kernel directory was replaced"
    );
    assert!(native.is_dir());
}

#[test]
fn symlink_in_workspace_is_rejected() {
    let mut fixture = Fixture::new();
    std::os::unix::fs::symlink(&fixture.public, fixture.native().join("link")).unwrap();
    let failure = fixture.archive(&[]).unwrap_err();
    assert_eq!(
        failure.python_str(),
        "Native kernel workspace contains a nonregular file"
    );
}

#[test]
fn failure_after_cleanup_does_not_claim_retained_native_files() {
    let mut fixture = Fixture::new();
    fixture.archive(&[]).unwrap();
    fixture.cleanup().unwrap();
    let failure = Fault::Failure(fang_supervisor::Failure::new(
        Status::Timeout,
        "final deadline",
        "adapter",
    ));
    fixture
        .workspace
        .retain_failure(&failure, &mut fixture.report);
    assert_eq!(fixture.state(), "removed-before-terminal-failure");
    assert_eq!(fixture.flag("native_removed"), Some(true));
}

#[test]
fn missing_native_directory_does_not_claim_archive_or_cleanup() {
    let mut fixture = Fixture::new();
    fs::remove_dir(fixture.native()).unwrap();
    let failure = Fault::Value("native path disappeared".into());
    fixture
        .workspace
        .retain_failure(&failure, &mut fixture.report);
    assert_eq!(fixture.state(), "native-missing-after-failure");
    assert_eq!(fixture.flag("archive_completed"), Some(false));
    assert_eq!(fixture.flag("cleanup_completed"), Some(false));
    assert_eq!(fixture.flag("native_removed"), Some(false));
}

#[test]
fn cleanup_failure_preserves_completed_archive_state() {
    // The Python control made unlink fail with a mock; here the native directory loses its write permission.
    let mut fixture = Fixture::new();
    fs::write(
        fixture.native().join("Audit.lean"),
        b"checked archive control",
    )
    .unwrap();
    fixture.archive(&[]).unwrap();
    fs::set_permissions(fixture.native(), fs::Permissions::from_mode(0o500)).unwrap();
    let failure = fixture.cleanup().unwrap_err();
    fs::set_permissions(fixture.native(), fs::Permissions::from_mode(0o700)).unwrap();
    assert!(
        matches!(&failure, Fault::OsAt(error, _) if error.kind() == std::io::ErrorKind::PermissionDenied),
        "{failure:?}"
    );
    fixture
        .workspace
        .retain_failure(&failure, &mut fixture.report);
    assert_eq!(fixture.flag("archive_completed"), Some(true));
    assert_eq!(fixture.flag("cleanup_completed"), Some(false));
    assert_eq!(fixture.state(), "retained-after-failure");
    assert_eq!(
        fs::read(fixture.public.join("Audit.lean")).unwrap(),
        b"checked archive control"
    );
}
