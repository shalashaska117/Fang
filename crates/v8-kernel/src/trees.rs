// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! entry/trees.py: hash the installation's Lean trees and compare them with the installation
//! record.
//!
//! A tree is a directory the compiler or the dynamic loader reads: the toolchain, the helper
//! objects and every entry of the recorded LEAN_PATH and LD_LIBRARY_PATH, where an entry inside
//! another recorded directory is covered by it. An entry missing at install is recorded as
//! absent and must stay absent. Every regular file below a tree is hashed; symbolic links are
//! recorded by target and never followed. Any added, removed or changed entry, or a change of
//! existence, makes the status `changed`. A directory that cannot be read is skipped, as
//! `os.walk` skips it; a name that is not UTF-8 is an error, where Python would have kept it
//! with surrogate escapes.

use std::collections::BTreeMap;
use std::fs::{self, File};
use std::io::Read;
use std::os::unix::fs::FileTypeExt;
use std::path::Path;

use fang_json::{DumpOptions, Object, Value};

/// The record of one tree: relative path to a file hash, `link:TARGET` or `special`.
pub type Files = BTreeMap<String, String>;

fn digest_file(path: &Path) -> std::io::Result<String> {
    let mut hasher = fang_hash::Hasher::new();
    let mut file = File::open(path)?;
    let mut buffer = vec![0u8; 1 << 20];
    loop {
        let count = file.read(&mut buffer)?;
        if count == 0 {
            break;
        }
        hasher.update(&buffer[..count]);
    }
    Ok(fang_hash::hex(&hasher.finish()))
}

fn walk(base: &Path, directory: &Path, files: &mut Files) -> Result<(), String> {
    let Ok(entries) = fs::read_dir(directory) else {
        return Ok(());
    };
    let mut names = Vec::new();
    for entry in entries.flatten() {
        names.push(entry.file_name());
    }
    names.sort();
    for name in names {
        let path = directory.join(&name);
        let Ok(relative) = path.strip_prefix(base) else {
            continue;
        };
        let Some(relative) = relative.to_str() else {
            return Err(format!("Tree entry name is not UTF-8: {}", path.display()));
        };
        let Ok(info) = fs::symlink_metadata(&path) else {
            continue;
        };
        let kind = info.file_type();
        if kind.is_symlink() {
            let target =
                fs::read_link(&path).map_err(|error| format!("{}: {error}", path.display()))?;
            let Some(target) = target.to_str() else {
                return Err(format!("Link target is not UTF-8: {}", path.display()));
            };
            files.insert(relative.to_owned(), format!("link:{target}"));
        } else if kind.is_dir() {
            walk(base, &path, files)?;
        } else if kind.is_file() {
            let hash =
                digest_file(&path).map_err(|error| format!("{}: {error}", path.display()))?;
            files.insert(relative.to_owned(), hash);
        } else if kind.is_fifo()
            || kind.is_socket()
            || kind.is_block_device()
            || kind.is_char_device()
        {
            files.insert(relative.to_owned(), "special".to_owned());
        }
    }
    Ok(())
}

/// `tree(directory)`.
pub fn tree(directory: &Path) -> Result<Files, String> {
    let mut files = Files::new();
    // os.walk does not list a symbolic link given as the top directory unless it names a directory.
    if fs::metadata(directory).is_ok_and(|info| info.is_dir()) {
        walk(directory, directory, &mut files)?;
    }
    Ok(files)
}

fn files_value(files: &Files) -> Value {
    Value::Object(
        files
            .iter()
            .map(|(key, value)| (key.clone(), Value::from(value.as_str())))
            .collect::<Object>(),
    )
}

/// `summary(files)`: SHA-256 of `json.dumps(files, sort_keys=True)`.
pub fn summary(files: &Files) -> Result<String, String> {
    let text = fang_json::dumps(
        &files_value(files),
        &DumpOptions {
            indent: None,
            sort_keys: true,
        },
    )
    .map_err(|error| error.0)?;
    Ok(fang_hash::sha256_hex(text.as_bytes()))
}

/// One recorded tree, as `record` writes it into trees.json.
pub fn record(directory: &str) -> Result<Value, String> {
    let files = tree(Path::new(directory))?;
    let mut item = Object::new();
    item.set("directory", directory);
    item.set("exists", Path::new(directory).is_dir());
    item.set("files", files.len() as u64);
    item.set("sha256", summary(&files)?);
    item.set("files_sha256", files_value(&files));
    Ok(Value::Object(item))
}

/// `verify`: recompute every recorded tree and report the differences, at most 50 of each kind.
pub fn verify(recorded: &Object) -> Result<(bool, Value, Value), String> {
    let mut differences = Object::new();
    let mut totals = Object::new();
    let mut unchanged = true;
    let mut names: Vec<&str> = recorded.keys().collect();
    names.sort_unstable();
    for name in names {
        let item = recorded
            .get(name)
            .and_then(Value::as_object)
            .ok_or("Tree record entry is not an object")?;
        let directory = item
            .get("directory")
            .and_then(Value::as_str)
            .ok_or("Tree record without a directory")?;
        let exists = item
            .get("exists")
            .and_then(Value::as_bool)
            .ok_or("Tree record without existence")?;
        let old = item
            .get("files_sha256")
            .and_then(Value::as_object)
            .ok_or("Tree record without files")?;
        let files = tree(Path::new(directory))?;
        let mut added: Vec<&String> = files.keys().filter(|key| !old.contains_key(key)).collect();
        let mut removed: Vec<&str> = old.keys().filter(|key| !files.contains_key(*key)).collect();
        let mut changed: Vec<&String> = files
            .iter()
            .filter(|(key, value)| {
                old.get(key)
                    .and_then(Value::as_str)
                    .is_some_and(|recorded| recorded != value.as_str())
            })
            .map(|(key, _)| key)
            .collect();
        added.truncate(50);
        removed.sort_unstable();
        removed.truncate(50);
        changed.truncate(50);
        let existence: Vec<Value> = if Path::new(directory).is_dir() == exists {
            Vec::new()
        } else {
            vec![Value::from(directory)]
        };
        unchanged &=
            added.is_empty() && removed.is_empty() && changed.is_empty() && existence.is_empty();
        let mut entry = Object::new();
        entry.set(
            "added",
            Value::Array(
                added
                    .into_iter()
                    .map(|key| Value::from(key.as_str()))
                    .collect(),
            ),
        );
        entry.set(
            "removed",
            Value::Array(removed.into_iter().map(Value::from).collect()),
        );
        entry.set(
            "changed",
            Value::Array(
                changed
                    .into_iter()
                    .map(|key| Value::from(key.as_str()))
                    .collect(),
            ),
        );
        entry.set("existence", Value::Array(existence));
        differences.set(name, Value::Object(entry));
        let mut total = Object::new();
        total.set("files", files.len() as u64);
        total.set("sha256", summary(&files)?);
        totals.set(name, Value::Object(total));
    }
    Ok((unchanged, Value::Object(totals), Value::Object(differences)))
}
