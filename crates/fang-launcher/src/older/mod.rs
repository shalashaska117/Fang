// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Code the two older profiles share, and the internal stages they run as bounded children of the launcher.
//!
//! The shared pieces are ports of tools/fang_szs: the argument set (`cli`), the child contracts both
//! profiles' engines follow (`contract`) and the TSTP capture and framing (`tstp`), with the Forced path
//! (`forced`). The kernel workspace (storage.py) is the crate fang-kernel-workspace, which kernel mode shares.

use std::ffi::OsString;
use std::path::Path;
use std::process::ExitCode;

use fang_json::Value;
pub use fang_supervisor::Fault;
use fang_supervisor::{Environment, Failure, Stage, StageOutput, Status, Supervisor};

pub mod binaries;
pub mod cli;
pub mod contract;
pub mod forced;
pub mod tstp;

/// A checked library as both older profiles pin it: its directory and the SHA-256 of every file under it, by
/// relative path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Library {
    pub path: std::path::PathBuf,
    pub files_sha256: std::collections::BTreeMap<String, String>,
}

/// The marker the launcher binary is run with for an internal stage.
pub const INTERNAL: &str = "--fang-internal";

/// Run the internal stage `name` with `arguments`. Reached only through `--fang-internal NAME` as the first
/// argument of the binary; an unknown name is a usage error (exit 64).
pub fn internal(name: &str, arguments: Vec<String>) -> ExitCode {
    match name {
        "ground-fof-replay" => crate::profile_ground_fof::kernel::emit(&arguments),
        "cnf-decompose" => crate::profile_cnf::kernel::decompose(&arguments),
        _ => {
            eprintln!("fang: unknown internal stage {name}");
            ExitCode::from(64)
        }
    }
}

/// A failure with its status, reason and stage (a Python `Failure`).
pub fn failure(status: Status, reason: impl Into<String>, stage: impl Into<String>) -> Fault {
    Fault::Failure(Failure {
        status,
        reason: reason.into(),
        stage: stage.into(),
    })
}

/// An Error failure, the commonest kind.
pub fn error(reason: impl Into<String>, stage: impl Into<String>) -> Fault {
    failure(Status::Error, reason, stage)
}

/// A Python ValueError with this text.
pub fn value(reason: impl Into<String>) -> Fault {
    Fault::Value(reason.into())
}

/// Run one supervised child stage. `cwd` defaults to the stage directory, as in the Python supervisor.
#[allow(
    clippy::too_many_arguments,
    reason = "one parameter per argument of the Python supervisor.run"
)]
pub fn run_stage(
    supervisor: &mut Supervisor,
    name: &str,
    command: &[OsString],
    directory: &Path,
    run_root: &Path,
    environment: Option<&Environment>,
    stdout_limit: Option<u64>,
    cwd: Option<&Path>,
) -> Result<StageOutput, Fault> {
    supervisor.run(&Stage {
        name,
        command,
        directory,
        run_root,
        environment,
        stdin: None,
        stdout_limit,
        cwd,
    })
}

/// The Python `supervisor.check()`: stage "adapter", reserve 0.15 s.
pub fn check(supervisor: &Supervisor) -> Result<(), Failure> {
    supervisor.check("adapter", 0.15)
}

/// The launcher binary, for internal child stages.
pub fn launcher() -> Result<std::path::PathBuf, Fault> {
    std::env::current_exe().map_err(|error| {
        crate::older::error(format!("Cannot locate the launcher: {error}"), "adapter")
    })
}

/// The exit code and classification of a stage record, as the Python contract helpers read them.
pub fn exit_and_class(output: &StageOutput) -> (Option<i64>, String) {
    let record = output.record.to_json();
    let Value::Object(object) = record else {
        return (None, String::new());
    };
    let code = match object.get("exit_code") {
        Some(Value::Number(fang_json::Number::Integer(integer))) => integer.as_i64(),
        _ => None,
    };
    let class = match object.get("classification") {
        Some(Value::String(text)) => text.clone(),
        _ => String::new(),
    };
    (code, class)
}

/// `normal_exit` and `completed_contract` of the Python protocols: an integer exit code of at least zero
/// whose classification is `completed` for 0 and `nonzero-exit` otherwise. Returns the code, or None.
pub fn normal_code(output: &StageOutput) -> Option<i64> {
    match exit_and_class(output) {
        (Some(code), class)
            if code >= 0
                && class
                    == if code == 0 {
                        "completed"
                    } else {
                        "nonzero-exit"
                    } =>
        {
            Some(code)
        }
        _ => None,
    }
}

/// Python's `==` on JSON values: objects regardless of key order, an integer equal to a float of the same
/// value.
pub fn json_equal(left: &Value, right: &Value) -> bool {
    use fang_json::Number;
    fn number(value: &Number) -> Option<f64> {
        match value {
            Number::Integer(integer) => integer.as_i128().map(|value| value as f64),
            Number::Float(value) => Some(*value),
        }
    }
    match (left, right) {
        (Value::Null, Value::Null) => true,
        (Value::Bool(a), Value::Bool(b)) => a == b,
        (Value::String(a), Value::String(b)) => a == b,
        (Value::Number(Number::Integer(a)), Value::Number(Number::Integer(b))) => {
            a.as_i128() == b.as_i128()
        }
        (Value::Number(a), Value::Number(b)) => number(a).is_some() && number(a) == number(b),
        (Value::Array(a), Value::Array(b)) => {
            a.len() == b.len() && a.iter().zip(b).all(|(x, y)| json_equal(x, y))
        }
        (Value::Object(a), Value::Object(b)) => {
            a.len() == b.len()
                && a.iter()
                    .all(|(key, value)| b.get(key).is_some_and(|other| json_equal(value, other)))
        }
        _ => false,
    }
}

/// Lowercase hex of 32 random bytes from the kernel, as `uuid.uuid4().hex`.
pub fn fresh_hex() -> Result<String, Fault> {
    let token = fang_supervisor::fresh_token()?;
    Ok(token
        .chars()
        .filter(|character| *character != '-')
        .collect())
}

/// Python's `bytes.decode("utf-8")`, with the UnicodeDecodeError text as a ValueError on failure.
pub fn python_utf8(data: &[u8]) -> Result<&str, Fault> {
    let failure = match std::str::from_utf8(data) {
        Ok(text) => return Ok(text),
        Err(failure) => failure,
    };
    let start = failure.valid_up_to();
    let (end, reason) = match failure.error_len() {
        None => (data.len(), "unexpected end of data"),
        Some(1) if !matches!(data[start], 0xc2..=0xf4) => (start + 1, "invalid start byte"),
        Some(length) => (start + length, "invalid continuation byte"),
    };
    let place = if end - start == 1 {
        format!("byte 0x{:02x} in position {start}", data[start])
    } else {
        format!("bytes in position {start}-{}", end - 1)
    };
    Err(value(format!(
        "'utf-8' codec can't decode {place}: {reason}"
    )))
}

/// A path as Python prints `str(path)` encoded with `errors="backslashreplace"`: a byte that is not UTF-8
/// was decoded to a lone surrogate, which prints as `\udcXX`.
pub fn python_path_bytes(path: &Path) -> Vec<u8> {
    use std::os::unix::ffi::OsStrExt;
    let mut result = Vec::new();
    for chunk in path.as_os_str().as_bytes().utf8_chunks() {
        result.extend_from_slice(chunk.valid().as_bytes());
        for byte in chunk.invalid() {
            result.extend_from_slice(format!("\\udc{byte:02x}").as_bytes());
        }
    }
    result
}

/// The exit code of a status name, as `EXIT[status]`.
pub fn exit_code(status: &str) -> i64 {
    Status::from_name(status).map_or(6, |status| i64::from(status.exit_code()))
}

/// The run record's limits: `asdict(limits)`, with the wall limit as parsed (the integer default stays an
/// integer, as in Python).
pub fn limits_json(limits: &fang_supervisor::Limits, wall: &crate::cli::Parsed) -> Value {
    let mut value = limits.to_json();
    if let (Value::Object(object), crate::cli::Parsed::Int(seconds)) = (&mut value, wall) {
        object.set("wall_seconds", Value::from(*seconds));
    }
    value
}

/// The description of the captured input in the run record. Python's adapter sealed a memfd; the launcher
/// keeps a 0400 copy and checks it after every child.
pub const SNAPSHOT_IDENTITY: &str =
    "0400 disk snapshot, checked by identity and SHA-256 after each child";
