// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! File, JSON and TOML helpers shared by the checks, with Python's error texts.

use std::collections::BTreeSet;
use std::io::Read;
use std::path::{Path, PathBuf};

use fang_json::{Object, ParseLimits, Value};
use fang_supervisor::Failure;

use crate::error::Error;

pub type Check<'a> = &'a mut dyn FnMut() -> Result<(), Failure>;

pub fn display(path: &Path) -> String {
    path.to_string_lossy().into_owned()
}

pub fn os_error(path: &Path) -> impl FnOnce(std::io::Error) -> Error + '_ {
    move |error| Error::Os(error, Some(path.to_path_buf()))
}

pub fn lstat(path: &Path) -> Result<std::fs::Metadata, Error> {
    std::fs::symlink_metadata(path).map_err(os_error(path))
}

/// `Path.resolve(strict=True)`: CPython 3.14's posixpath.realpath, component by component, so
/// that a failure names the same path as Python's: the first missing component, the target a
/// dangling link points to, the file that has components after it (ENOTDIR), or the link that
/// closes a loop (ELOOP).
pub fn resolve_strict(path: &Path) -> Result<PathBuf, Error> {
    enum Part {
        Name(String),
        /// A link whose target has been walked: its resolution is the current path.
        Resolved(String),
    }
    let filename = path.to_string_lossy().into_owned();
    let mut path = if filename.starts_with('/') {
        "/".to_owned()
    } else {
        std::env::current_dir()
            .map_err(|error| Error::Os(error, None))?
            .to_string_lossy()
            .into_owned()
    };
    let mut rest: Vec<Part> = filename
        .split('/')
        .rev()
        .map(|name| Part::Name(name.to_owned()))
        .collect();
    let mut seen: std::collections::HashMap<String, Option<String>> =
        std::collections::HashMap::new();
    let os_at = |error: std::io::Error, at: &str| Error::Os(error, Some(PathBuf::from(at)));
    while let Some(part) = rest.pop() {
        let name = match part {
            Part::Resolved(link) => {
                seen.insert(link, Some(path.clone()));
                continue;
            }
            Part::Name(name) => name,
        };
        if name.is_empty() || name == "." {
            continue;
        }
        if name == ".." {
            path = match path.rfind('/') {
                Some(index) if index > 0 => path[..index].to_owned(),
                _ => "/".to_owned(),
            };
            continue;
        }
        let newpath = if path == "/" {
            format!("/{name}")
        } else {
            format!("{path}/{name}")
        };
        let metadata =
            std::fs::symlink_metadata(&newpath).map_err(|error| os_at(error, &newpath))?;
        if !metadata.file_type().is_symlink() {
            let more = rest.iter().any(|part| matches!(part, Part::Name(_)));
            if more && !metadata.is_dir() {
                return Err(os_at(std::io::Error::from_raw_os_error(20), &newpath));
            }
            path = newpath;
            continue;
        }
        if let Some(resolved) = seen.get(&newpath) {
            if let Some(resolved) = resolved {
                path = resolved.clone();
                continue;
            }
            // Python calls os.stat(newpath) here to raise ELOOP.
            std::fs::metadata(&newpath).map_err(|error| os_at(error, &newpath))?;
            path = newpath;
            continue;
        }
        let target = std::fs::read_link(&newpath)
            .map_err(|error| os_at(error, &newpath))?
            .to_string_lossy()
            .into_owned();
        seen.insert(newpath.clone(), None);
        rest.push(Part::Resolved(newpath));
        rest.extend(
            target
                .split('/')
                .rev()
                .map(|name| Part::Name(name.to_owned())),
        );
        if target.starts_with('/') {
            path = "/".to_owned();
        }
    }
    Ok(PathBuf::from(path))
}

/// `_regular`: check, then the path itself (not followed) must be a regular file.
pub fn regular(path: &Path, check: Check<'_>) -> Result<(), Error> {
    check()?;
    if !lstat(path)?.file_type().is_file() {
        return Err(Error::value(format!(
            "Expected a regular file: {}",
            display(path)
        )));
    }
    Ok(())
}

/// `digest`: the SHA-256 of a regular file, read in 1 MiB blocks with a check after each block.
pub fn digest(path: &Path, check: Check<'_>) -> Result<String, Error> {
    regular(path, check)?;
    let mut file = std::fs::File::open(path).map_err(os_error(path))?;
    let mut hasher = fang_hash::Hasher::new();
    let mut block = vec![0u8; 1 << 20];
    loop {
        let read = file.read(&mut block).map_err(os_error(path))?;
        if read == 0 {
            break;
        }
        check()?;
        hasher.update(&block[..read]);
    }
    Ok(fang_hash::hex(&hasher.finish()))
}

pub fn sha256_hex(data: &[u8]) -> String {
    fang_hash::sha256_hex(data)
}

pub fn read_bytes(path: &Path) -> Result<Vec<u8>, Error> {
    std::fs::read(path).map_err(os_error(path))
}

/// `data.decode("utf-8")`. The error carries the text of CPython's UnicodeDecodeError: the
/// first maximal invalid subpart, which `Utf8Error` reports the same way.
pub fn decode(data: &[u8]) -> Result<&str, Error> {
    std::str::from_utf8(data).map_err(|error| {
        let start = error.valid_up_to();
        let (end, reason) = match error.error_len() {
            None => (data.len(), "unexpected end of data"),
            Some(length) if (0xC2..=0xF4).contains(&data[start]) => {
                (start + length, "invalid continuation byte")
            }
            Some(length) => (start + length, "invalid start byte"),
        };
        Error::Value(if end == start + 1 {
            format!(
                "'utf-8' codec can't decode byte 0x{:02x} in position {start}: {reason}",
                data[start]
            )
        } else {
            format!(
                "'utf-8' codec can't decode bytes in position {start}-{}: {reason}",
                end - 1
            )
        })
    })
}

/// `path.read_bytes().decode("utf-8")`.
pub fn read_decoded(path: &Path) -> Result<String, Error> {
    Ok(decode(&read_bytes(path)?)?.to_owned())
}

/// `path.read_text(encoding="utf-8")`: decoded, with universal newlines ("\r\n" and "\r" read
/// as "\n").
pub fn read_text(path: &Path) -> Result<String, Error> {
    let text = read_decoded(path)?;
    Ok(if text.contains('\r') {
        text.replace("\r\n", "\n").replace('\r', "\n")
    } else {
        text
    })
}

/// `json.loads(path.read_text(encoding="utf-8"))`.
pub fn read_json(path: &Path) -> Result<Value, Error> {
    let text = read_text(path)?;
    if text.starts_with('\u{feff}') {
        return Err(Error::value(
            "Unexpected UTF-8 BOM (decode using utf-8-sig): line 1 column 1 (char 0)",
        ));
    }
    let limits = ParseLimits {
        max_bytes: usize::MAX,
        max_depth: 10_000,
    };
    fang_json::parse(text.as_bytes(), &limits)
        .map_err(|error| Error::Value(error.python_message(text.as_bytes())))
}

/// `tomllib.loads(path.read_text())`.
pub fn read_toml(path: &Path) -> Result<Value, Error> {
    let text = read_text(path)?;
    fang_toml::parse(&text).map_err(|error| Error::Value(error.to_string()))
}

/// `value[key]` on an object: KeyError when absent.
pub fn get<'v>(value: &'v Value, key: &str) -> Result<&'v Value, Error> {
    object(value)?
        .get(key)
        .ok_or_else(|| Error::Key(key.to_owned()))
}

pub fn object(value: &Value) -> Result<&Object, Error> {
    value
        .as_object()
        .ok_or_else(|| Error::value("Expected a JSON object"))
}

pub fn text(value: &Value) -> Result<&str, Error> {
    value
        .as_str()
        .ok_or_else(|| Error::value("Expected a JSON string"))
}

pub fn integer(value: &Value) -> Result<i64, Error> {
    value
        .as_i64()
        .ok_or_else(|| Error::value("Expected a JSON integer"))
}

pub fn array(value: &Value) -> Result<&Vec<Value>, Error> {
    value
        .as_array()
        .ok_or_else(|| Error::value("Expected a JSON array"))
}

/// `value.get(key)` returning None when absent.
pub fn optional<'v>(value: &'v Value, key: &str) -> Option<&'v Value> {
    value.as_object().and_then(|object| object.get(key))
}

/// `value.get(key, {})` iterated as an object.
pub fn entries<'v>(value: &'v Value, key: &str) -> Vec<(&'v str, &'v Value)> {
    optional(value, key)
        .and_then(Value::as_object)
        .map(|object| object.iter().collect())
        .unwrap_or_default()
}

/// `os.path.normpath` for a relative POSIX path.
pub fn normpath(path: &str) -> String {
    let absolute = path.starts_with('/');
    let mut parts: Vec<&str> = Vec::new();
    for part in path.split('/') {
        match part {
            "" | "." => {}
            ".." => {
                if parts.last().is_some_and(|last| *last != "..") {
                    parts.pop();
                } else if !absolute {
                    parts.push("..");
                }
            }
            other => parts.push(other),
        }
    }
    let joined = parts.join("/");
    if absolute {
        format!("/{joined}")
    } else if joined.is_empty() {
        ".".to_owned()
    } else {
        joined
    }
}

/// `os.path.dirname` for a POSIX path.
pub fn dirname(path: &str) -> &str {
    match path.rfind('/') {
        Some(0) => "/",
        Some(index) => path[..index].trim_end_matches('/'),
        None => "",
    }
}

/// `os.path.join(a, b)` for POSIX paths.
pub fn join(left: &str, right: &str) -> String {
    if right.starts_with('/') || left.is_empty() {
        right.to_owned()
    } else if left.ends_with('/') {
        format!("{left}{right}")
    } else {
        format!("{left}/{right}")
    }
}

/// `_listed_tree`: every regular file under `directory` by relative POSIX path, skipping the
/// named relative directories; a symlink or other non-directory among the directories, or a
/// non-regular file, is an error, as os.walk with followlinks=False reports them.
pub fn listed_tree(
    directory: &Path,
    check: Check<'_>,
    skip: &[&str],
) -> Result<BTreeSet<String>, Error> {
    let mut found = BTreeSet::new();
    let mut pending: Vec<PathBuf> = vec![directory.to_path_buf()];
    while let Some(current) = pending.pop() {
        check()?;
        let entries = match std::fs::read_dir(&current) {
            Ok(entries) => entries,
            Err(_) if current != directory => continue,
            Err(error) => return Err(Error::Os(error, Some(current))),
        };
        for entry in entries {
            let entry = entry.map_err(os_error(&current))?;
            let path = entry.path();
            let relative = relative_posix(&path, directory);
            // os.walk lists an entry among the directories when it is one, following symlinks.
            let is_directory = std::fs::metadata(&path)
                .map(|metadata| metadata.is_dir())
                .unwrap_or(false);
            let metadata = lstat(&path)?;
            if is_directory {
                if skip.contains(&relative.as_str()) {
                    continue;
                }
                if !metadata.file_type().is_dir() {
                    return Err(Error::value(format!(
                        "Source directory is not a real directory: {}",
                        display(&path)
                    )));
                }
                pending.push(path);
            } else {
                if !metadata.file_type().is_file() {
                    return Err(Error::value(format!(
                        "Source file is not regular: {}",
                        display(&path)
                    )));
                }
                found.insert(relative);
            }
        }
    }
    Ok(found)
}

pub fn relative_posix(path: &Path, base: &Path) -> String {
    path.strip_prefix(base)
        .map(|relative| {
            relative
                .components()
                .map(|part| part.as_os_str().to_string_lossy())
                .collect::<Vec<_>>()
                .join("/")
        })
        .unwrap_or_else(|_| display(path))
}
