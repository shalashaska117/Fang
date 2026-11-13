// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! read_regular, strict_json, write_json, Snapshot, and fresh names.

use std::fs::OpenOptions;
use std::io::{Read, Write};
use std::os::unix::fs::{OpenOptionsExt, PermissionsExt};
use std::path::{Path, PathBuf};

use fang_hash::{Identity, open_regular, sha256_hex};
use fang_json::{ParseLimits, Value};

use crate::status::{Failure, Status};

/// What Python raised: a Failure with its own status, an OSError, or a ValueError.
/// The launcher reports the last two as Error with "Adapter input, installation or I/O failure: ...".
#[derive(Debug)]
pub enum Fault {
    Failure(Failure),
    Os(std::io::Error),
    /// An OSError that names its file, as Python's does: "[Errno 2] ...: '/path'".
    OsAt(std::io::Error, PathBuf),
    Value(String),
}

/// strerror(3) text of an OS error: Rust's Display without its " (os error N)" suffix.
fn strerror(error: &std::io::Error) -> String {
    let text = error.to_string();
    match error.raw_os_error() {
        Some(code) => text
            .strip_suffix(&format!(" (os error {code})"))
            .unwrap_or(&text)
            .to_owned(),
        None => text,
    }
}

impl Fault {
    pub fn status(&self) -> Status {
        match self {
            Fault::Failure(failure) => failure.status,
            Fault::Os(_) | Fault::OsAt(..) | Fault::Value(_) => Status::Error,
        }
    }

    /// Python's `str(error)` for the exception this stands for.
    pub fn python_str(&self) -> String {
        match self {
            Fault::Failure(failure) => failure.reason.clone(),
            Fault::Value(text) => text.clone(),
            Fault::Os(error) => match error.raw_os_error() {
                Some(code) => format!("[Errno {code}] {}", strerror(error)),
                None => error.to_string(),
            },
            Fault::OsAt(error, path) => match error.raw_os_error() {
                Some(code) => format!(
                    "[Errno {code}] {}: {}",
                    strerror(error),
                    fang_json::python_repr_str(&path.to_string_lossy())
                ),
                None => error.to_string(),
            },
        }
    }

    /// The reason the launcher records: the Failure's own, or the adapter-failure text.
    pub fn reason(&self) -> String {
        match self {
            Fault::Failure(failure) => failure.reason.clone(),
            other => format!(
                "Adapter input, installation or I/O failure: {}",
                other.python_str()
            ),
        }
    }

    /// An OS error with the file it concerns.
    pub fn at(path: &Path) -> impl FnOnce(std::io::Error) -> Fault + '_ {
        move |error| Fault::OsAt(error, path.to_path_buf())
    }
}

impl From<Failure> for Fault {
    fn from(failure: Failure) -> Fault {
        Fault::Failure(failure)
    }
}

impl From<std::io::Error> for Fault {
    fn from(error: std::io::Error) -> Fault {
        Fault::Os(error)
    }
}

impl std::fmt::Display for Fault {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.python_str())
    }
}

impl std::error::Error for Fault {}

/// Read one regular inode, at most `limit` + 1 bytes; never wait on a FIFO (supervisor.read_regular).
pub fn read_regular(
    path: &Path,
    limit: u64,
    check: &mut dyn FnMut() -> Result<(), Failure>,
) -> Result<Vec<u8>, Fault> {
    let (mut file, _) = match open_regular(path) {
        Ok(opened) => opened,
        Err(error) if error.kind() == std::io::ErrorKind::InvalidInput => {
            return Err(Failure::adapter(
                Status::Error,
                "A required artifact is not a regular file",
            )
            .into());
        }
        Err(error) => return Err(Fault::OsAt(error, path.to_path_buf())),
    };
    let mut data = Vec::new();
    let mut block = vec![0u8; 65536];
    while (data.len() as u64) <= limit {
        check()?;
        let want = (limit + 1 - data.len() as u64).min(65536) as usize;
        let read = file.read(&mut block[..want])?;
        if read == 0 {
            break;
        }
        data.extend_from_slice(&block[..read]);
    }
    if data.len() as u64 > limit {
        return Err(Failure::adapter(Status::ResourceOut, "Declared byte limit exceeded").into());
    }
    Ok(data)
}

/// supervisor.strict_json: duplicate fields and NaN or Infinity are refused with Python's texts.
pub fn strict_json(bytes: &[u8]) -> Result<Value, Fault> {
    let limits = ParseLimits {
        max_bytes: usize::MAX,
        max_depth: 1 << 16,
    };
    fang_json::parse(bytes, &limits).map_err(|error| Fault::Value(error.python_message(bytes)))
}

/// supervisor.write_json: `name.new` created exclusively, then renamed over `path`.
pub fn write_json(path: &Path, value: &Value) -> Result<(), Fault> {
    match fang_json::write_json(path, value) {
        Ok(()) => Ok(()),
        Err(error) if error.kind() == std::io::ErrorKind::InvalidData => {
            Err(Fault::Value(error.to_string()))
        }
        Err(error) => {
            let mut temporary = path.as_os_str().to_os_string();
            temporary.push(".new");
            Err(Fault::OsAt(error, PathBuf::from(temporary)))
        }
    }
}

/// A captured input: a read-only copy that children read, checked by identity and hash.
/// Python's sealed memfd has no std counterpart; the coordinator's rule replaces it.
#[derive(Clone, Debug)]
pub struct Snapshot {
    pub path: PathBuf,
    pub sha256: String,
    pub identity: Identity,
    pub data: Vec<u8>,
}

impl Snapshot {
    /// Create `path` exclusively, write `data`, sync, make it 0400, and record its identity and SHA-256.
    pub fn create(path: &Path, data: &[u8]) -> Result<Snapshot, Fault> {
        let mut stream = OpenOptions::new()
            .write(true)
            .create_new(true)
            .mode(0o600)
            .open(path)
            .map_err(Fault::at(path))?;
        stream.write_all(data)?;
        stream.sync_all()?;
        drop(stream);
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o400))?;
        let identity = Identity::of_path(path)?;
        Ok(Snapshot {
            path: path.to_path_buf(),
            sha256: sha256_hex(data),
            identity,
            data: data.to_vec(),
        })
    }

    /// The argument a child is given in place of /proc/self/fd/N.
    pub fn argument(&self) -> &Path {
        &self.path
    }

    /// The same inode, unchanged in size and times, with the same bytes.
    pub fn verify(&self, check: &mut dyn FnMut() -> Result<(), Failure>) -> Result<(), Fault> {
        let changed = || {
            Fault::Failure(Failure::adapter(
                Status::Error,
                "Captured disk artifact changed",
            ))
        };
        match Identity::of_path(&self.path) {
            Ok(identity) if identity == self.identity => {}
            _ => return Err(changed()),
        }
        let data =
            read_regular(&self.path, self.data.len() as u64, check).map_err(
                |fault| match fault {
                    Fault::Failure(failure) if failure.status == Status::ResourceOut => changed(),
                    other => other,
                },
            )?;
        if data != self.data {
            return Err(changed());
        }
        Ok(())
    }
}

/// A random token, from /proc/sys/kernel/random/uuid, in place of uuid4().hex.
pub fn fresh_token() -> Result<String, Fault> {
    let text = std::fs::read_to_string("/proc/sys/kernel/random/uuid")?;
    Ok(text.trim().replace('-', ""))
}

/// tempfile.mkdtemp: a new 0700 directory `parent/prefix<random>`.
pub fn make_temp_dir(parent: &Path, prefix: &str) -> Result<PathBuf, Fault> {
    use std::os::unix::fs::DirBuilderExt;
    for _ in 0..100 {
        let token = fresh_token()?;
        let path = parent.join(format!("{prefix}{}", &token[..8]));
        match std::fs::DirBuilder::new().mode(0o700).create(&path) {
            Ok(()) => return Ok(path),
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(error.into()),
        }
    }
    Err(Fault::Os(std::io::Error::new(
        std::io::ErrorKind::AlreadyExists,
        "No usable temporary directory name",
    )))
}
