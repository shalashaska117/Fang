// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Full Lean toolchain content checks, including internal symlinks: a port of tools/fof_szs/toolchain.py.
//! Public, because the installer captures the same inventory with these functions; the error texts are
//! toolchain.py's, at stage "adapter" where the Python ValueError ended.

use std::collections::BTreeMap;
use std::fs;
use std::io::Read;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};

use fang_json::{Object, Value};
use fang_supervisor::{Failure, Fault};

use crate::older::error;

/// `metadata` of toolchain.py: (st_dev, st_ino, st_mode, st_size, st_mtime_ns, st_ctime_ns).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Metadata {
    pub dev: u64,
    pub ino: u64,
    pub mode: u32,
    pub size: u64,
    pub mtime_ns: i128,
    pub ctime_ns: i128,
}

impl Metadata {
    pub fn of(metadata: &fs::Metadata) -> Metadata {
        Metadata {
            dev: metadata.dev(),
            ino: metadata.ino(),
            mode: metadata.mode(),
            size: metadata.size(),
            mtime_ns: i128::from(metadata.mtime()) * 1_000_000_000
                + i128::from(metadata.mtime_nsec()),
            ctime_ns: i128::from(metadata.ctime()) * 1_000_000_000
                + i128::from(metadata.ctime_nsec()),
        }
    }
    fn is_dir(&self) -> bool {
        self.mode & 0o170000 == 0o040000
    }
    fn is_link(&self) -> bool {
        self.mode & 0o170000 == 0o120000
    }
    fn is_file(&self) -> bool {
        self.mode & 0o170000 == 0o100000
    }
}

fn io(failure: std::io::Error) -> Fault {
    Fault::Os(failure)
}

/// Every entry under `root` with its lstat metadata, by relative POSIX path, walking without following
/// links (os.walk with followlinks=False).
pub fn tree(
    root: &Path,
    check: &mut dyn FnMut() -> Result<(), Failure>,
) -> Result<BTreeMap<String, Metadata>, Fault> {
    let mut result = BTreeMap::new();
    let mut pending = vec![root.to_path_buf()];
    while let Some(directory) = pending.pop() {
        let mut names: Vec<PathBuf> = fs::read_dir(&directory)
            .map_err(io)?
            .map(|entry| entry.map(|entry| entry.path()))
            .collect::<Result<_, _>>()
            .map_err(io)?;
        names.sort();
        for path in names {
            check()?;
            let metadata = Metadata::of(&fs::symlink_metadata(&path).map_err(io)?);
            if metadata.is_dir() {
                pending.push(path.clone());
            }
            let relative = path
                .strip_prefix(root)
                .unwrap_or(&path)
                .to_string_lossy()
                .to_string();
            result.insert(relative, metadata);
        }
    }
    Ok(result)
}

/// Hash one regular file opened without following links, its metadata unchanged before, during and after;
/// returns `{"size", "sha256", "mode"}`.
pub fn stable_file(
    path: &Path,
    check: &mut dyn FnMut() -> Result<(), Failure>,
) -> Result<Object, Fault> {
    let before = Metadata::of(&fs::symlink_metadata(path).map_err(io)?);
    let (mut file, _) = fang_hash::open_regular(path).map_err(io)?;
    let opened = Metadata::of(&file.metadata().map_err(io)?);
    if !opened.is_file() || before != opened {
        return Err(error(
            "Toolchain dependency replaced before hashing",
            "adapter",
        ));
    }
    let mut hasher = fang_hash::Hasher::new();
    let mut block = vec![0u8; 1 << 20];
    loop {
        let read = file.read(&mut block).map_err(io)?;
        if read == 0 {
            break;
        }
        check()?;
        hasher.update(&block[..read]);
    }
    if opened != Metadata::of(&file.metadata().map_err(io)?) {
        return Err(error(
            "Toolchain dependency changed during hashing",
            "adapter",
        ));
    }
    if opened != Metadata::of(&fs::symlink_metadata(path).map_err(io)?) {
        return Err(error(
            "Toolchain dependency replaced during hashing",
            "adapter",
        ));
    }
    let mut record = Object::new();
    record.set("size", Value::from(opened.size as i64));
    record.set("sha256", fang_hash::hex(&hasher.finish()));
    record.set("mode", Value::from(i64::from(opened.mode & 0o7777)));
    Ok(record)
}

/// The inventory record of every non-directory member of `root`, as toolchain.py's `verify` builds it.
pub fn inventory(
    root: &Path,
    check: &mut dyn FnMut() -> Result<(), Failure>,
) -> Result<(BTreeMap<String, Metadata>, Object), Fault> {
    let before = tree(root, check)?;
    let mut actual = Object::new();
    for (relative, identity) in &before {
        check()?;
        let path = root.join(relative);
        if identity.is_dir() {
            continue;
        }
        let mut record = Object::new();
        if identity.is_link() {
            let resolved = fs::canonicalize(&path).map_err(io)?;
            if !resolved.starts_with(root) || !resolved.is_file() {
                return Err(error(
                    "Toolchain symlink escapes the recorded tree",
                    "adapter",
                ));
            }
            let target = fs::read_link(&path).map_err(io)?;
            record.set("kind", "symlink");
            record.set("target", target.to_string_lossy().to_string());
            record.set(
                "resolved",
                resolved
                    .strip_prefix(root)
                    .unwrap_or(&resolved)
                    .to_string_lossy()
                    .to_string(),
            );
            for (key, value) in stable_file(&resolved, check)?.iter() {
                record.set(key, value.clone());
            }
            if fs::canonicalize(&path).map_err(io)? != resolved {
                return Err(error("Toolchain symlink changed during hashing", "adapter"));
            }
        } else if identity.is_file() {
            record.set("kind", "file");
            for (key, value) in stable_file(&path, check)?.iter() {
                record.set(key, value.clone());
            }
        } else {
            return Err(error("Nonregular toolchain member", "adapter"));
        }
        if *identity != Metadata::of(&fs::symlink_metadata(&path).map_err(io)?) {
            return Err(error("Toolchain changed during inventory", "adapter"));
        }
        actual.set(relative.as_str(), Value::Object(record));
    }
    Ok((before, actual))
}

/// Require the installed toolchain at the absolute real directory `root` to equal its reviewed inventory.
pub fn verify(
    root: &Path,
    expected: &Value,
    check: &mut dyn FnMut() -> Result<(), Failure>,
) -> Result<(), Fault> {
    let real = fs::symlink_metadata(root)
        .map(|metadata| metadata.is_dir())
        .unwrap_or(false);
    if !root.is_absolute() || !real {
        return Err(error(
            "Toolchain root must be an absolute real directory",
            "adapter",
        ));
    }
    let root = fs::canonicalize(root).map_err(io)?;
    let (before, actual) = inventory(&root, check)?;
    if tree(&root, check)? != before || !crate::older::json_equal(&Value::Object(actual), expected)
    {
        return Err(error(
            "Installed Lean toolchain differs from its reviewed inventory",
            "adapter",
        ));
    }
    Ok(())
}
