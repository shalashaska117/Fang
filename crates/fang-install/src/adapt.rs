// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The installer's calls into fang-supervisor, fang-source-checks and fang-axiom-audit, in one place, so that
//! the build steps read like the Python they replace and an API change touches only this file.

use std::collections::BTreeMap;
use std::ffi::OsString;
use std::path::{Path, PathBuf};

use fang_json::Value;
use fang_supervisor::{Environment, Failure, Limits, Stage, StageOutput, Supervisor};

use crate::common::{Error, Result};

/// `supervisor.check()`: stage "adapter", reserve 0.15 s.
pub fn check(supervisor: &Supervisor) -> std::result::Result<(), Failure> {
    supervisor.check("adapter", 0.15)
}

/// `supervisor.check(stage)`.
pub fn check_stage(supervisor: &Supervisor, stage: &str) -> Result<()> {
    supervisor.check(stage, 0.15).map_err(Error::from)
}

/// `Supervisor(Limits(wall_seconds=..., memory_mib=..., log_bytes=..., artifact_bytes=...))`.
pub fn supervisor(
    wall_seconds: f64,
    memory_mib: u64,
    log_bytes: u64,
    artifact_bytes: u64,
) -> Result<Supervisor> {
    let limits = Limits {
        wall_seconds,
        memory_mib,
        log_bytes,
        artifact_bytes,
        ..Limits::default()
    };
    Supervisor::new(limits, None).map_err(Error::from)
}

/// A child environment from a map, keys in order; the supervisor refuses keys outside ENVIRONMENT_KEYS when it
/// runs, with Python's message.
pub fn environment(values: &BTreeMap<String, String>) -> Result<Environment> {
    let mut environment = Environment::new();
    for (key, value) in values {
        environment.set(key.clone(), value.clone());
    }
    Ok(environment)
}

/// `tempfile.mkdtemp(prefix=prefix, dir=parent)`.
pub fn make_temp_dir(parent: &Path, prefix: &str) -> Result<PathBuf> {
    fang_supervisor::make_temp_dir(parent, prefix).map_err(|fault| Error::Os {
        class: "OSError",
        message: fault.to_string(),
    })
}

/// One supervised stage: `supervisor.run(stage, command, directory, run_root, environment=..., stdout_limit=...)`,
/// with `cwd` where the Python wrapped the command to change directory.
pub struct StageCall<'a> {
    pub name: &'a str,
    pub command: Vec<String>,
    pub directory: PathBuf,
    pub run_root: &'a Path,
    pub environment: Option<&'a Environment>,
    pub stdout_limit: Option<u64>,
    pub cwd: Option<&'a Path>,
}

pub fn run(supervisor: &mut Supervisor, call: StageCall<'_>) -> Result<StageOutput> {
    let command: Vec<OsString> = call.command.iter().map(OsString::from).collect();
    let stage = Stage {
        name: call.name,
        command: &command,
        directory: &call.directory,
        run_root: call.run_root,
        environment: call.environment,
        stdin: None,
        stdout_limit: call.stdout_limit,
        cwd: call.cwd,
    };
    supervisor.run(&stage).map_err(Error::from)
}

/// The stage records as the manifests store them.
pub fn records(supervisor: &Supervisor) -> Value {
    Value::Array(
        supervisor
            .records
            .iter()
            .map(|record| record.to_json())
            .collect(),
    )
}

/// fang-source-checks' error as the Python exception it stands for; a Failure from `check` passes through.
fn source_error(error: fang_source_checks::Error) -> Error {
    use fang_source_checks::Error as Source;
    match error {
        Source::Failure(failure) => Error::Failure(failure),
        Source::Os(io, Some(path)) => crate::common::os_error(&io, &path),
        Source::Key(key) => Error::Key(crate::common::py_repr(&key)),
        other => Error::Value(other.to_string()),
    }
}

/// The lean-v8 source map's path and schema.
pub const LEAN_MAP: &str = fang_source_checks::v8::LEAN_MAP;
pub const LEAN_SCHEMA: &str = fang_source_checks::v8::LEAN_SCHEMA;
pub const RUST_MAP: &str = fang_source_checks::v8::RUST_MAP;
pub const RUST_SCHEMA: &str = fang_source_checks::v8::RUST_SCHEMA;
pub const PINS: &str = fang_source_checks::backend::PINS;
pub const AENEAS_SUBDIR: &str = fang_source_checks::backend::AENEAS_SUBDIR;

/// `sources.load_map(root, relative, schema, check)`.
pub fn load_map(
    root: &Path,
    relative: &str,
    schema: &str,
    supervisor: &Supervisor,
) -> Result<Value> {
    fang_source_checks::v8::load_map(root, relative, schema, &mut || check(supervisor))
        .map_err(source_error)
}

/// `sources.lean_files(root, check)`.
pub fn lean_files(root: &Path, supervisor: &Supervisor) -> Result<Vec<PathBuf>> {
    fang_source_checks::v8::lean_files(root, &mut || check(supervisor)).map_err(source_error)
}

/// `sources.digest(path)`: a regular file's SHA-256.
pub fn digest(path: &Path) -> Result<String> {
    fang_source_checks::v8::digest(path, &mut || Ok(())).map_err(source_error)
}

/// `sources.check_lean_receipts(root, check)`: the number of receipt entries checked.
pub fn check_lean_receipts(root: &Path, supervisor: &Supervisor) -> Result<u64> {
    fang_source_checks::v8::check_lean_receipts(root, &mut || check(supervisor))
        .map_err(source_error)
}

/// `v8_backend.load_pins(root)`.
pub fn load_pins(root: &Path) -> Result<Value> {
    fang_source_checks::backend::load_pins(root).map_err(source_error)
}

/// The rows of each package from an earlier `check_packages`.
pub type Rows = fang_source_checks::backend::Rows;

/// `v8_backend.check_packages(packages, pins, check, allow_additions=..., before=..., fetch=...)`.
pub fn check_packages(
    packages: &Path,
    pins: &Value,
    supervisor: Option<&Supervisor>,
    allow_additions: bool,
    before: Option<&Rows>,
    fetch: bool,
) -> Result<(Value, Rows, Vec<String>)> {
    let options = fang_source_checks::backend::CheckOptions {
        allow_additions,
        before,
        content: false,
        fetch,
    };
    let mut no_check = || Ok(());
    match supervisor {
        Some(supervisor) => fang_source_checks::backend::check_packages(
            packages,
            pins,
            &mut || check(supervisor),
            &options,
        ),
        None => {
            fang_source_checks::backend::check_packages(packages, pins, &mut no_check, &options)
        }
    }
    .map_err(source_error)
}

/// build-v8-lean.py's `parse_audit(text, names, recorded)`.
pub fn parse_build_audit(
    text: &str,
    names: &[String],
    recorded: &BTreeMap<String, Vec<String>>,
) -> Result<Vec<(String, Vec<String>)>> {
    let names: Vec<&str> = names.iter().map(String::as_str).collect();
    let recorded: Vec<(&str, Vec<String>)> = recorded
        .iter()
        .map(|(name, axioms)| (name.as_str(), axioms.clone()))
        .collect();
    fang_axiom_audit::parse_build_audit(text, &names, &recorded)
        .map_err(|error| Error::Value(error.0))
}

/// check-suite.py's audit lines: (declaration, sorted axioms) in report order.
pub fn check_suite_audit(text: &str, module: &str) -> Result<Vec<(String, Vec<String>)>> {
    fang_axiom_audit::check_suite_audit(text, module).map_err(|error| Error::Runtime(error.0))
}

/// The record's `exit_code`.
pub fn exit_code(output: &StageOutput) -> Option<i64> {
    output
        .record
        .to_json()
        .get("exit_code")
        .and_then(Value::as_i64)
}

/// `record["classification"] == "completed" and record["exit_code"] == 0`.
pub fn completed(output: &StageOutput) -> bool {
    output
        .record
        .to_json()
        .get("classification")
        .and_then(Value::as_str)
        == Some("completed")
        && exit_code(output) == Some(0)
}

/// `dependency_files(root, lambda: supervisor.check(stage))` of tools/fang_szs/dependencies.py.
pub fn dependency_files(root: &Path, supervisor: &Supervisor, stage: &str) -> Result<Vec<PathBuf>> {
    fang_source_checks::deps::dependency_files(root, &mut || supervisor.check(stage, 0.15))
        .map_err(source_error)
}

/// tools/fof_szs/toolchain.py, from worker-roles' port in the launcher, so that the capture here and the
/// launcher's run-time check are one copy.
pub mod toolchain {
    use std::collections::BTreeMap;
    use std::path::Path;

    use fang_json::Value;
    use fang_launcher::profile_ground_fof::toolchain as port;
    use fang_supervisor::{Failure, Supervisor};

    use crate::common::{Error, Result};

    pub use port::Metadata;

    pub fn tree(
        root: &Path,
        supervisor: &Supervisor,
        stage: &str,
    ) -> Result<BTreeMap<String, Metadata>> {
        port::tree(root, &mut || -> std::result::Result<(), Failure> {
            supervisor.check(stage, 0.15)
        })
        .map_err(Error::from)
    }

    pub fn stable_file(path: &Path, supervisor: &Supervisor, stage: &str) -> Result<Value> {
        port::stable_file(path, &mut || -> std::result::Result<(), Failure> {
            supervisor.check(stage, 0.15)
        })
        .map(Value::Object)
        .map_err(Error::from)
    }

    pub fn verify(
        root: &Path,
        expected: &Value,
        supervisor: &Supervisor,
        stage: &str,
    ) -> Result<()> {
        port::verify(
            root,
            expected,
            &mut || -> std::result::Result<(), Failure> { supervisor.check(stage, 0.15) },
        )
        .map_err(Error::from)
    }
}

/// fang-hash's chunked digest of a file, in the tagged text form the capability records (the tag comes from
/// fang-hash and follows its chunk size).
pub fn chunked(path: &Path) -> Result<String> {
    use fang_hash::HashFileError;
    match fang_hash::hash_file_chunked(
        path,
        fang_hash::DEFAULT_FILE_LIMIT,
        0,
        &mut || -> std::result::Result<(), Failure> { Ok(()) },
    ) {
        Ok((hex, _)) => Ok(fang_hash::chunked_text(&hex)),
        Err(HashFileError::Io(error)) => Err(crate::common::os_error(&error, path)),
        Err(HashFileError::Check(failure)) => Err(Error::Failure(failure)),
        Err(HashFileError::NotBounded) => Err(Error::Value(format!(
            "Not a regular file within the hash limit: {}",
            crate::common::text_of(path)
        ))),
        Err(HashFileError::Grew | HashFileError::Changed) => Err(Error::Value(format!(
            "File changed while it was hashed: {}",
            crate::common::text_of(path)
        ))),
    }
}

/// The descriptors this process inherited without close-on-exec, which its children inherit too (std cannot close
/// them), as fang-supervisor records them: `[{"fd": N, "target": "..."}]`. INTEGRATION.md item 9.
pub fn inherited_descriptors() -> Value {
    Value::Array(
        fang_supervisor::inherited_descriptors()
            .iter()
            .map(|descriptor| {
                crate::common::object(vec![
                    ("fd", i64::from(descriptor.fd).into()),
                    ("target", descriptor.target.as_str().into()),
                ])
            })
            .collect(),
    )
}
