// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Helpers shared by the build steps. Each reproduces the Python call it replaces: the text of a refusal, the
//! metadata a copy keeps, the mode of a new directory, the UTC time format and the JSON writer.

use std::collections::BTreeMap;
use std::ffi::OsString;
use std::fs::{self, DirBuilder, File, FileTimes};
use std::io::{self, Read, Write};
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt, PermissionsExt};
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use fang_json::{DumpOptions, Object, ParseLimits, Value};
use fang_supervisor::Failure;

pub type Result<T> = std::result::Result<T, Error>;

/// A refusal or failure. `typed` gives Python's `f"{type(error).__name__}: {error}"`.
#[derive(Debug)]
pub enum Error {
    /// `ValueError`: `require` and the source, pin and audit checks.
    Value(String),
    /// `RuntimeError`: the proof suite.
    Runtime(String),
    /// The supervisor's `Failure`; its text is the reason.
    Failure(Failure),
    /// An `OSError` subclass, with Python's message.
    Os {
        class: &'static str,
        message: String,
    },
    /// `json.JSONDecodeError`, with CPython's message as fang-json gives it.
    Json(String),
    /// `subprocess.TimeoutExpired`.
    Timeout(String),
    /// `KeyError`; its text is the quoted key.
    Key(String),
}

impl Error {
    pub fn class(&self) -> &str {
        match self {
            Error::Value(_) => "ValueError",
            Error::Runtime(_) => "RuntimeError",
            Error::Failure(_) => "Failure",
            Error::Os { class, .. } => class,
            Error::Json(_) => "JSONDecodeError",
            Error::Timeout(_) => "TimeoutExpired",
            Error::Key(_) => "KeyError",
        }
    }

    /// `str(error)`.
    pub fn message(&self) -> String {
        match self {
            Error::Value(text)
            | Error::Runtime(text)
            | Error::Json(text)
            | Error::Timeout(text)
            | Error::Key(text) => text.clone(),
            Error::Failure(failure) => failure.reason.clone(),
            Error::Os { message, .. } => message.clone(),
        }
    }

    /// `f"{type(error).__name__}: {error}"`.
    pub fn typed(&self) -> String {
        format!("{}: {}", self.class(), self.message())
    }
}

impl From<Failure> for Error {
    fn from(failure: Failure) -> Error {
        Error::Failure(failure)
    }
}

/// The supervisor's fault as the Python exception it stands for.
impl From<fang_supervisor::Fault> for Error {
    fn from(fault: fang_supervisor::Fault) -> Error {
        use fang_supervisor::Fault;
        let message = fault.python_str();
        match fault {
            Fault::Failure(failure) => Error::Failure(failure),
            Fault::Value(text) => Error::Value(text),
            Fault::Os(error) | Fault::OsAt(error, _) => Error::Os {
                class: os_class(error.raw_os_error()),
                message,
            },
        }
    }
}

/// Python's `require(value, message)`: a `ValueError` when the condition fails.
pub fn require(condition: bool, message: impl AsRef<str>) -> Result<()> {
    if condition {
        Ok(())
    } else {
        Err(Error::Value(message.as_ref().to_string()))
    }
}

/// The `OSError` subclass Python raises for an errno.
fn os_class(code: Option<i32>) -> &'static str {
    match code {
        Some(1) | Some(13) => "PermissionError",
        Some(2) => "FileNotFoundError",
        Some(3) => "ProcessLookupError",
        Some(4) => "InterruptedError",
        Some(10) => "ChildProcessError",
        Some(11) | Some(114) | Some(115) => "BlockingIOError",
        Some(17) => "FileExistsError",
        Some(20) => "NotADirectoryError",
        Some(21) => "IsADirectoryError",
        Some(32) | Some(108) => "BrokenPipeError",
        Some(103) => "ConnectionAbortedError",
        Some(104) => "ConnectionResetError",
        Some(110) => "TimeoutError",
        Some(111) => "ConnectionRefusedError",
        _ => "OSError",
    }
}

/// Python's `repr` of a str: single quotes unless the text holds one and no double quote.
pub fn py_repr(text: &str) -> String {
    let quote = if text.contains('\'') && !text.contains('"') {
        '"'
    } else {
        '\''
    };
    let mut out = String::new();
    out.push(quote);
    for character in text.chars() {
        match character {
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if c == quote => {
                out.push('\\');
                out.push(c);
            }
            c if (c as u32) < 0x20 || c as u32 == 0x7f => {
                out.push_str(&format!("\\x{:02x}", c as u32))
            }
            c => out.push(c),
        }
    }
    out.push(quote);
    out
}

/// Python's `repr` of a list of str.
pub fn py_repr_list(items: &[String]) -> String {
    format!(
        "[{}]",
        items
            .iter()
            .map(|item| py_repr(item))
            .collect::<Vec<_>>()
            .join(", ")
    )
}

/// An `OSError` for one path, as Python words it: `[Errno 2] No such file or directory: '/x'`.
pub fn os_error(error: &io::Error, path: &Path) -> Error {
    let code = error.raw_os_error();
    let text = error.to_string();
    let message = match code {
        Some(number) => {
            let reason = text
                .strip_suffix(&format!(" (os error {number})"))
                .unwrap_or(&text);
            format!("[Errno {number}] {reason}: {}", py_repr(&text_of(path)))
        }
        None => text,
    };
    Error::Os {
        class: os_class(code),
        message,
    }
}

/// Attach the path an `io::Error` concerns.
pub trait At<T> {
    fn at(self, path: &Path) -> Result<T>;
}

impl<T> At<T> for io::Result<T> {
    fn at(self, path: &Path) -> Result<T> {
        self.map_err(|error| os_error(&error, path))
    }
}

/// `str(path)`. Paths here are UTF-8; anything else is shown as Rust's lossy text.
pub fn text_of(path: &Path) -> String {
    path.to_string_lossy().into_owned()
}

/// `Path.resolve()` (non-strict): the existing prefix with its links resolved, then the rest as written.
pub fn resolve(path: &Path) -> Result<PathBuf> {
    let absolute = std::path::absolute(path).at(path)?;
    let mut existing = absolute.clone();
    let mut rest = Vec::new();
    while fs::symlink_metadata(&existing).is_err() {
        match existing.file_name() {
            Some(name) => {
                rest.push(name.to_owned());
                existing.pop();
            }
            None => break,
        }
    }
    let mut result = fs::canonicalize(&existing).at(&existing)?;
    for name in rest.into_iter().rev() {
        result.push(name);
    }
    Ok(result)
}

/// `Path.mkdir(mode=mode, parents=parents, exist_ok=exist_ok)`: missing parents get the default mode.
pub fn mkdir(path: &Path, mode: u32, parents: bool, exist_ok: bool) -> Result<()> {
    match DirBuilder::new().mode(mode).create(path) {
        Ok(()) => Ok(()),
        Err(error) if parents && error.kind() == io::ErrorKind::NotFound => {
            if let Some(parent) = path.parent().filter(|parent| *parent != path) {
                mkdir(parent, 0o777, true, true)?;
            }
            mkdir(path, mode, false, exist_ok)
        }
        Err(error) => {
            if exist_ok && path.is_dir() {
                Ok(())
            } else {
                Err(os_error(&error, path))
            }
        }
    }
}

/// `Path.mkdir()` with the default mode.
pub fn mkdir_plain(path: &Path) -> Result<()> {
    mkdir(path, 0o777, false, false)
}

/// `shutil.copyfile`: the bytes only; the target is created or truncated under the umask.
pub fn copyfile(source: &Path, target: &Path) -> Result<()> {
    let mut input = File::open(source).at(source)?;
    let metadata = input.metadata().at(source)?;
    if !metadata.is_file() && !metadata.is_dir() {
        return Err(Error::Os {
            class: "SpecialFileError",
            message: format!("`{}` is a named pipe", text_of(source)),
        });
    }
    let mut output = File::create(target).at(target)?;
    io::copy(&mut input, &mut output).at(target)?;
    Ok(())
}

/// `shutil.copy2`: `copyfile`, then the access and modification times and the permission bits, in
/// copystat's order. Extended attributes are not copied (the trees here carry none).
pub fn copy2(source: &Path, target: &Path) -> Result<()> {
    copyfile(source, target)?;
    let metadata = fs::metadata(source).at(source)?;
    let times = FileTimes::new()
        .set_accessed(metadata.accessed().at(source)?)
        .set_modified(metadata.modified().at(source)?);
    File::options()
        .write(true)
        .open(target)
        .at(target)?
        .set_times(times)
        .at(target)?;
    fs::set_permissions(
        target,
        fs::Permissions::from_mode(metadata.permissions().mode() & 0o7777),
    )
    .at(target)?;
    Ok(())
}

/// `Path.write_bytes`.
pub fn write_bytes(path: &Path, data: &[u8]) -> Result<()> {
    File::create(path).at(path)?.write_all(data).at(path)
}

/// `open(path, "x")` followed by a write: refuses an existing path.
pub fn create_new(path: &Path, data: &[u8]) -> Result<()> {
    File::options()
        .write(true)
        .create_new(true)
        .mode(0o666)
        .open(path)
        .at(path)?
        .write_all(data)
        .at(path)
}

/// SHA-256 of a file's bytes, following links, as `hashlib.sha256(path.read_bytes())`.
pub fn sha256_file(path: &Path) -> Result<String> {
    let mut stream = File::open(path).at(path)?;
    let mut hasher = fang_hash::Hasher::new();
    let mut block = vec![0u8; 1 << 20];
    loop {
        let read = stream.read(&mut block).at(path)?;
        if read == 0 {
            break;
        }
        hasher.update(&block[..read]);
    }
    Ok(fang_hash::hex(&hasher.finish()))
}

/// `json.loads(path.read_text(encoding="utf-8"))`. Duplicate keys are refused, where Python kept the last.
pub fn read_json(path: &Path) -> Result<Value> {
    let data = fs::read(path).at(path)?;
    fang_json::parse(&data, &ParseLimits::default()).map_err(|error| Error::Json(error.to_string()))
}

/// `json.dumps(value)`: one line, keys in insertion order.
pub fn compact(value: &Value) -> String {
    fang_json::dumps(
        value,
        &DumpOptions {
            indent: None,
            sort_keys: false,
        },
    )
    .unwrap_or_default()
}

/// `supervisor.write_json`: indent 2, sorted keys, "\n", through `NAME.new` and a rename.
pub fn write_manifest(path: &Path, value: &Value) -> Result<()> {
    fang_json::write_json(path, value).at(path)
}

/// `open(path, "x")` with `json.dump(value, indent=2, sort_keys=True)` and "\n".
pub fn create_json(path: &Path, value: &Value) -> Result<()> {
    let text = fang_json::dumps_manifest(value).map_err(|error| Error::Value(error.0))?;
    create_new(path, format!("{text}\n").as_bytes())
}

/// An object from pairs in insertion order.
pub fn object(pairs: Vec<(&str, Value)>) -> Value {
    Value::Object(pairs.into_iter().collect::<Object>())
}

/// A JSON array of strings.
pub fn strings(items: &[String]) -> Value {
    Value::Array(
        items
            .iter()
            .map(|item| Value::from(item.as_str()))
            .collect(),
    )
}

/// `datetime.now(timezone.utc).isoformat()`.
pub fn utc_now() -> String {
    let since = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default();
    let (date, clock) = civil(since.as_secs());
    let micros = since.subsec_micros();
    if micros == 0 {
        format!("{date}T{clock}+00:00")
    } else {
        format!("{date}T{clock}.{micros:06}+00:00")
    }
}

/// `datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")`.
pub fn utc_stamp() -> String {
    let since = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default();
    let (date, clock) = civil(since.as_secs());
    format!("{}T{}Z", date.replace('-', ""), clock.replace(':', ""))
}

/// Date and time of day for seconds since the epoch, by the civil-from-days algorithm.
fn civil(seconds: u64) -> (String, String) {
    let days = (seconds / 86_400) as i64;
    let rest = seconds % 86_400;
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1_460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = doy - (153 * mp + 2) / 5 + 1;
    let month = if mp < 10 { mp + 3 } else { mp - 9 };
    let year = yoe + era * 400 + i64::from(month <= 2);
    (
        format!("{year:04}-{month:02}-{day:02}"),
        format!(
            "{:02}:{:02}:{:02}",
            rest / 3_600,
            rest % 3_600 / 60,
            rest % 60
        ),
    )
}

/// The result of a child run outside the supervisor.
pub struct Completed {
    /// Python's `returncode`: the exit code, or minus the signal number.
    pub returncode: i32,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}

fn returncode(status: std::process::ExitStatus) -> i32 {
    status
        .code()
        .unwrap_or_else(|| -status.signal().unwrap_or(0))
}

/// `subprocess.run(command, cwd=..., env=..., capture_output=True, timeout=...)`. `environment` None inherits
/// the caller's environment. On timeout the child is killed and Python's TimeoutExpired text is the error.
pub fn run_captured(
    command: &[String],
    cwd: Option<&Path>,
    environment: Option<&BTreeMap<String, String>>,
    timeout: Duration,
) -> Result<Completed> {
    run_child(command, cwd, environment, timeout, true)
}

/// `subprocess.run(command, timeout=...)` with inherited streams and environment.
pub fn run_inherited(command: &[String], timeout: Duration) -> Result<i32> {
    Ok(run_child(command, None, None, timeout, false)?.returncode)
}

fn run_child(
    command: &[String],
    cwd: Option<&Path>,
    environment: Option<&BTreeMap<String, String>>,
    timeout: Duration,
    capture: bool,
) -> Result<Completed> {
    let program = PathBuf::from(&command[0]);
    let mut builder = Command::new(&command[0]);
    builder.args(&command[1..]).stdin(Stdio::inherit());
    if let Some(directory) = cwd {
        builder.current_dir(directory);
    }
    if let Some(environment) = environment {
        builder.env_clear().envs(
            environment
                .iter()
                .map(|(key, value)| (OsString::from(key), OsString::from(value))),
        );
    }
    // The guard marker belongs only to this worker. A nested guarded executable
    // must enter through its outer process and create its own worker group.
    // Remove it after an explicit environment too, while preserving all other variables.
    builder.env_remove(fang_supervisor::guard::MARKER);
    if capture {
        builder
            .stdin(Stdio::null())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped());
    }
    let mut child = builder.spawn().at(&program)?;
    let readers = if capture {
        let mut out = child.stdout.take().expect("piped stdout");
        let mut err = child.stderr.take().expect("piped stderr");
        Some((
            thread::spawn(move || drain(&mut out)),
            thread::spawn(move || drain(&mut err)),
        ))
    } else {
        None
    };
    let started = Instant::now();
    let status = loop {
        if let Some(status) = child.try_wait().at(&program)? {
            break status;
        }
        if started.elapsed() >= timeout {
            let _ = child.kill();
            let _ = child.wait();
            return Err(Error::Timeout(format!(
                "Command '{}' timed out after {} seconds",
                py_repr_list(command),
                timeout.as_secs()
            )));
        }
        thread::sleep(Duration::from_millis(20).min(timeout.saturating_sub(started.elapsed())));
    };
    let (stdout, stderr) = match readers {
        Some((out, err)) => (
            out.join().unwrap_or_default(),
            err.join().unwrap_or_default(),
        ),
        None => (Vec::new(), Vec::new()),
    };
    Ok(Completed {
        returncode: returncode(status),
        stdout,
        stderr,
    })
}

fn drain(stream: &mut impl Read) -> Vec<u8> {
    let mut data = Vec::new();
    let _ = stream.read_to_end(&mut data);
    data
}

/// The last `count` characters of `bytes.decode("utf-8", "replace")`, as Python's `[-count:]`.
pub fn tail_text(bytes: &[u8], count: usize) -> String {
    let text = String::from_utf8_lossy(bytes);
    let total = text.chars().count();
    text.chars().skip(total.saturating_sub(count)).collect()
}

/// Command-line options in argparse's long form (`--name VALUE`, `--name=VALUE`, `--flag`) and positionals.
/// Abbreviated option names, which argparse accepts, are refused.
pub struct Arguments {
    pub values: BTreeMap<String, Vec<String>>,
    pub positional: Vec<String>,
}

impl Arguments {
    /// Parse `arguments` given the options that take a value and the flags. An error is argparse's exit 2.
    pub fn parse(
        arguments: &[String],
        valued: &[&str],
        flags: &[&str],
    ) -> std::result::Result<Arguments, String> {
        let mut values: BTreeMap<String, Vec<String>> = BTreeMap::new();
        let mut positional = Vec::new();
        let mut index = 0;
        while index < arguments.len() {
            let item = &arguments[index];
            index += 1;
            if let Some(body) = item.strip_prefix("--") {
                let (name, inline) = match body.split_once('=') {
                    Some((name, value)) => (name, Some(value.to_string())),
                    None => (body, None),
                };
                if flags.contains(&name) && inline.is_none() {
                    values
                        .entry(name.to_string())
                        .or_default()
                        .push(String::new());
                } else if valued.contains(&name) {
                    let value = match inline {
                        Some(value) => value,
                        None if index < arguments.len() => {
                            index += 1;
                            arguments[index - 1].clone()
                        }
                        None => return Err(format!("argument --{name}: expected one argument")),
                    };
                    values.entry(name.to_string()).or_default().push(value);
                } else {
                    return Err(format!("unrecognized arguments: {item}"));
                }
            } else {
                positional.push(item.clone());
            }
        }
        Ok(Arguments { values, positional })
    }

    /// The last value of an option, as argparse keeps the last.
    pub fn value(&self, name: &str) -> Option<&str> {
        self.values
            .get(name)
            .and_then(|values| values.last())
            .map(String::as_str)
    }

    pub fn path(&self, name: &str) -> Option<PathBuf> {
        self.value(name).map(PathBuf::from)
    }

    pub fn flag(&self, name: &str) -> bool {
        self.values.contains_key(name)
    }
}

/// argparse's error exit: usage and message on stderr, status 2.
pub fn usage_error(program: &str, usage: &str, message: &str) -> i32 {
    eprintln!("usage: {program} {usage}");
    eprintln!("{program}: error: {message}");
    2
}
