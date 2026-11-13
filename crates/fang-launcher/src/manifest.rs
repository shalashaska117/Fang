// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The run record: the run directory, the first record and the terminal checkpoint.
//!
//! A run directory is created by this invocation and never reused, so a stale run is never overwritten. The
//! terminal checkpoint keeps the rule that an unsaved record never authorizes a positive status.

use std::fs::DirBuilder;
use std::os::unix::fs::DirBuilderExt;
use std::path::Path;

use fang_json::{Object, Value};
use fang_supervisor::{Failure, Status, Supervisor};

/// Create the run directory with mode 0700, as Python's `mkdir(mode=0o700, parents=True)`: missing parents get
/// the default mode, only the run directory gets 0700, and the run directory must not exist yet.
pub fn create_run_root(root: &Path) -> std::io::Result<()> {
    if let Some(parent) = root.parent()
        && !parent.as_os_str().is_empty()
    {
        DirBuilder::new().recursive(true).create(parent)?;
    }
    DirBuilder::new().mode(0o700).create(root)
}

/// Write the first record of a run into `root/manifest.json`.
pub fn write_initial(root: &Path, manifest: &Object) -> std::io::Result<()> {
    fang_json::write_json(
        &root.join("manifest.json"),
        &Value::Object(manifest.clone()),
    )
}

/// The terminal checkpoint of a run.
///
/// The record is written; when its status is positive and a supervisor is given, the whole-run deadline is
/// checked with no reserve after the write. A failure of that check, or of the write, replaces the status:
/// with the check's status, or with Error when the record cannot be saved. Returns the status that stands.
/// `positive` says which statuses are results and `exit_code` maps a status to its exit code.
pub fn terminal_checkpoint(
    path: &Path,
    manifest: &mut Object,
    supervisor: Option<&Supervisor>,
    positive: &dyn Fn(&str) -> bool,
    exit_code: &dyn Fn(&str) -> i64,
) -> String {
    let deadline = supervisor.map(|supervisor| move || supervisor.check("adapter", 0.0));
    checkpoint_with(
        path,
        manifest,
        deadline
            .as_ref()
            .map(|check| check as &dyn Fn() -> Result<(), Failure>),
        positive,
        exit_code,
        &mut |path, value| fang_json::write_json(path, value),
    )
}

/// `terminal_checkpoint` with the deadline check and the record writer given, as the controls replace them.
fn checkpoint_with(
    path: &Path,
    manifest: &mut Object,
    deadline: Option<&dyn Fn() -> Result<(), Failure>>,
    positive: &dyn Fn(&str) -> bool,
    exit_code: &dyn Fn(&str) -> i64,
    write: &mut dyn FnMut(&Path, &Value) -> std::io::Result<()>,
) -> String {
    let status = match manifest.get("status") {
        Some(Value::String(status)) => status.clone(),
        _ => "Error".to_string(),
    };
    let written = write(path, &Value::Object(manifest.clone()));
    let checked: Result<(), Failure> = match (&written, deadline) {
        (Ok(()), Some(deadline)) if positive(&status) => deadline(),
        _ => Ok(()),
    };
    match (written, checked) {
        (Ok(()), Ok(())) => status,
        (Ok(()), Err(failure)) => {
            let status = failure.status.name().to_string();
            update(
                manifest,
                &status,
                exit_code(&status),
                &failure.reason,
                "finalization",
            );
            if let Err(retry) = write(path, &Value::Object(manifest.clone())) {
                manifest.set("checkpoint_error", Value::String(retry.to_string()));
            }
            status
        }
        (Err(error), _) => {
            let status = Status::Error.name().to_string();
            update(
                manifest,
                &status,
                exit_code(&status),
                "Could not save the terminal artifact record",
                "finalization",
            );
            manifest.set("checkpoint_error", Value::String(error.to_string()));
            status
        }
    }
}

/// Set the status fields of a record, as the Python `manifest.update(status=..., exit_code=..., reason=...,
/// stage=...)`.
pub fn update(manifest: &mut Object, status: &str, exit_code: i64, reason: &str, stage: &str) {
    manifest.set("status", Value::String(status.to_string()));
    manifest.set("exit_code", Value::from(exit_code));
    manifest.set("reason", Value::String(reason.to_string()));
    manifest.set("stage", Value::String(stage.to_string()));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn positive(status: &str) -> bool {
        status == "Unsatisfiable"
    }

    fn exit_code(status: &str) -> i64 {
        if positive(status) { 0 } else { 6 }
    }

    fn record() -> Object {
        let mut manifest = Object::new();
        manifest.set("status", "Unsatisfiable");
        manifest
    }

    /// test_fang_szs ProtocolTests.test_failed_terminal_write_cannot_report_success.
    #[test]
    fn failed_terminal_write_cannot_report_success() {
        let mut manifest = record();
        let mut write = |_: &Path, _: &Value| Err(std::io::Error::other("unwritable artifact"));
        let status = checkpoint_with(
            Path::new("unused"),
            &mut manifest,
            None,
            &positive,
            &exit_code,
            &mut write,
        );
        assert_eq!(status, "Error");
        assert_eq!(
            manifest.get("status").and_then(Value::as_str),
            Some("Error")
        );
        assert_eq!(
            manifest.get("checkpoint_error").and_then(Value::as_str),
            Some("unwritable artifact")
        );
    }

    /// test_fang_szs ProtocolTests.test_expired_success_with_failed_retry_still_reports_timeout.
    #[test]
    fn expired_success_with_failed_retry_still_reports_timeout() {
        let mut manifest = record();
        let mut writes = 0;
        let mut write = |_: &Path, _: &Value| {
            writes += 1;
            if writes == 1 {
                Ok(())
            } else {
                Err(std::io::Error::other("retry failed"))
            }
        };
        let expired = || Err(Failure::new(Status::Timeout, "expired", "adapter"));
        let status = checkpoint_with(
            Path::new("unused"),
            &mut manifest,
            Some(&expired),
            &positive,
            &exit_code,
            &mut write,
        );
        assert_eq!(status, "Timeout");
        assert_eq!(
            manifest.get("status").and_then(Value::as_str),
            Some("Timeout")
        );
        assert_eq!(
            manifest.get("checkpoint_error").and_then(Value::as_str),
            Some("retry failed")
        );
    }

    #[test]
    fn a_saved_success_within_the_deadline_stands() {
        let mut manifest = record();
        let mut write = |_: &Path, _: &Value| Ok(());
        let open = || Ok(());
        let status = checkpoint_with(
            Path::new("unused"),
            &mut manifest,
            Some(&open),
            &positive,
            &exit_code,
            &mut write,
        );
        assert_eq!(status, "Unsatisfiable");
        assert!(manifest.get("checkpoint_error").is_none());
    }
}
