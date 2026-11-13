// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! tools/fang_szs/v8_backend.py: compact content pins for the Aeneas backend packages.

use std::collections::{BTreeMap, BTreeSet};
use std::io::Read;
use std::path::{Path, PathBuf};

use fang_json::{Object, Value};

use crate::error::Error;
use crate::util::{self, Check, display, get, integer, lstat, object, optional, read_json, text};

pub const PINS: &str = "tools/v8_szs/backend-pins.json";
pub const AENEAS_EXCLUDED: [&str; 1] = [".lake/lean-build-aeneas-x86_64-unknown-linux-gnu.tar.gz"];
pub const AENEAS_SUBDIR: &str = "backends/lean";
pub const BUILD_RECORDS: [&str; 4] = [".hash", ".trace", ".setup.json", ".rsp"];

fn fail<T>(message: impl Into<String>) -> Result<T, Error> {
    Err(Error::value(message))
}

/// One inventory row: kind ("file" or "symlink"), SHA-256, size and, for a symlink, its text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Row {
    pub kind: String,
    pub sha256: String,
    pub size: u64,
    pub target: Option<String>,
}

impl Row {
    pub fn to_json(&self) -> Value {
        let mut object = Object::new();
        object.set("kind", self.kind.as_str());
        if let Some(target) = &self.target {
            object.set("target", target.as_str());
        }
        object.set("sha256", self.sha256.as_str());
        object.set("size", self.size);
        Value::Object(object)
    }
}

/// The rows of one package directory, by relative path.
pub type PackageRows = BTreeMap<String, Row>;

/// The rows of every package, by package name, as check_packages returns them.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Rows(pub BTreeMap<String, PackageRows>);

pub struct CheckOptions<'a> {
    pub allow_additions: bool,
    pub before: Option<&'a Rows>,
    pub content: bool,
    pub fetch: bool,
}

pub fn excluded(relative: &str) -> bool {
    AENEAS_EXCLUDED.contains(&relative) || relative.starts_with(".lake/config/")
}

pub fn lake_hash_file(relative: &str) -> bool {
    relative.ends_with(".hash")
}

pub fn build_record(relative: &str) -> bool {
    BUILD_RECORDS
        .iter()
        .any(|suffix| relative.ends_with(suffix))
}

pub fn file_kind(relative: &str) -> String {
    let name = relative.rsplit('/').next().unwrap_or(relative);
    match name.split_once('.') {
        Some((_, kind)) => kind.to_owned(),
        None => "(none)".to_owned(),
    }
}

fn kept(relative: &str, content: bool, fetch: bool) -> bool {
    !(excluded(relative)
        || (content && lake_hash_file(relative))
        || (fetch && build_record(relative)))
}

/// `package_digest(rows, content=..., fetch=...)`.
pub fn package_digest(rows: &PackageRows, content: bool, fetch: bool) -> String {
    let mut hasher = fang_hash::Hasher::new();
    for (relative, row) in rows {
        if !kept(relative, content, fetch) {
            continue;
        }
        let size = row.size.to_string();
        let line = [
            relative.as_str(),
            row.kind.as_str(),
            size.as_str(),
            row.sha256.as_str(),
            row.target.as_deref().unwrap_or(""),
        ]
        .join("\0");
        hasher.update(line.as_bytes());
        hasher.update(b"\n");
    }
    fang_hash::hex(&hasher.finish())
}

/// `kind_digests(rows)`: exact digest and file count per file kind.
pub fn kind_digests(rows: &PackageRows) -> Value {
    let mut groups: BTreeMap<String, PackageRows> = BTreeMap::new();
    for (relative, row) in rows {
        if !excluded(relative) {
            groups
                .entry(file_kind(relative))
                .or_default()
                .insert(relative.clone(), row.clone());
        }
    }
    let mut result = Object::new();
    for (kind, group) in groups {
        let mut entry = Object::new();
        entry.set("files", group.len());
        entry.set("digest", package_digest(&group, false, false));
        result.set(kind, entry);
    }
    Value::Object(result)
}

fn file_hash(path: &Path, check: Check<'_>) -> Result<(String, u64), Error> {
    let mut file = std::fs::File::open(path).map_err(util::os_error(path))?;
    let mut hasher = fang_hash::Hasher::new();
    let mut size = 0u64;
    let mut block = vec![0u8; 1 << 20];
    loop {
        let read = file.read(&mut block).map_err(util::os_error(path))?;
        if read == 0 {
            break;
        }
        check()?;
        hasher.update(&block[..read]);
        size += read as u64;
    }
    Ok((fang_hash::hex(&hasher.finish()), size))
}

/// `scan(directory, check)`: one package directory with the pinned inventory's row fields.
pub fn scan(directory: &Path, check: Check<'_>) -> Result<PackageRows, Error> {
    let directory = util::resolve_strict(directory)?;
    let mut rows = PackageRows::new();
    // os.walk(directory, followlinks=False), top down: a directory that cannot be listed (or
    // fails part way) is skipped; files are taken in listing order, then the subdirectories,
    // sorted and without .git, are checked and walked depth first in that order.
    let mut pending = vec![directory.clone()];
    while let Some(current) = pending.pop() {
        let Ok(entries) =
            std::fs::read_dir(&current).and_then(|entries| entries.collect::<Result<Vec<_>, _>>())
        else {
            continue;
        };
        check()?;
        let mut directories: Vec<(String, PathBuf)> = Vec::new();
        let mut files: Vec<PathBuf> = Vec::new();
        for entry in entries {
            let path = entry.path();
            // os.walk sorts with entry.is_dir(), which follows symbolic links.
            if std::fs::metadata(&path).is_ok_and(|metadata| metadata.is_dir()) {
                let name = entry.file_name().to_string_lossy().into_owned();
                if name != ".git" {
                    directories.push((name, path));
                }
            } else {
                files.push(path);
            }
        }
        directories.sort();
        for path in files {
            let relative = util::relative_posix(&path, &directory);
            if excluded(&relative) {
                continue;
            }
            let kind = lstat(&path)?.file_type();
            if kind.is_symlink() {
                let resolved = util::resolve_strict(&path)?;
                if !resolved.starts_with(&directory) || !resolved.is_file() {
                    return fail(format!(
                        "Backend symlink leaves its package: {}",
                        display(&path)
                    ));
                }
                let (digest, size) = file_hash(&resolved, check)?;
                let target = std::fs::read_link(&path).map_err(util::os_error(&path))?;
                rows.insert(
                    relative,
                    Row {
                        kind: "symlink".into(),
                        sha256: digest,
                        size,
                        target: Some(display(&target)),
                    },
                );
            } else if kind.is_file() {
                let (digest, size) = file_hash(&path, check)?;
                rows.insert(
                    relative,
                    Row {
                        kind: "file".into(),
                        sha256: digest,
                        size,
                        target: None,
                    },
                );
            } else {
                return fail(format!("Unsupported backend entry: {}", display(&path)));
            }
        }
        for (_, path) in &directories {
            // Path.is_symlink() is False when lstat fails.
            if std::fs::symlink_metadata(path)
                .is_ok_and(|metadata| metadata.file_type().is_symlink())
            {
                return fail(format!("Backend directory symlink: {}", display(path)));
            }
        }
        pending.extend(directories.into_iter().rev().map(|(_, path)| path));
    }
    Ok(rows)
}

/// `load_pins(root)`.
pub fn load_pins(root: &Path) -> Result<Value, Error> {
    let value = read_json(&root.join(PINS))?;
    if optional(&value, "schema").and_then(Value::as_str) != Some("fang-v8-backend-pins-v1") {
        return fail("Unexpected backend pin schema");
    }
    Ok(value)
}

/// `package_directory(packages, name)`.
pub fn package_directory(packages: &Path, name: &str) -> PathBuf {
    if name == "aeneas" {
        packages.join(name).join(AENEAS_SUBDIR)
    } else {
        packages.join(name)
    }
}

/// `differing_kinds(rows, pin)`: the kinds that differ, split into other kinds and build records.
pub fn differing_kinds(
    rows: &PackageRows,
    pin: &Value,
) -> Result<(Vec<String>, Vec<String>), Error> {
    let actual = kind_digests(rows);
    let pinned = get(pin, "kinds")?;
    let actual_object = object(&actual)?;
    let pinned_object = object(pinned)?;
    let names: BTreeSet<&str> = actual_object.keys().chain(pinned_object.keys()).collect();
    let kinds: Vec<String> = names
        .into_iter()
        .filter(|kind| actual_object.get(kind) != pinned_object.get(kind))
        .map(str::to_owned)
        .collect();
    let records: Vec<String> = kinds
        .iter()
        .filter(|kind| build_record(&format!(".{kind}")))
        .cloned()
        .collect();
    let other: Vec<String> = kinds
        .into_iter()
        .filter(|kind| !records.contains(kind))
        .collect();
    Ok((other, records))
}

fn strings(items: &[String]) -> Value {
    Value::Array(
        items
            .iter()
            .map(|item| Value::from(item.as_str()))
            .collect(),
    )
}

/// `check_packages(packages, pins, check, ...)`: (result, rows by package, problems).
pub fn check_packages(
    packages: &Path,
    pins: &Value,
    check: Check<'_>,
    options: &CheckOptions<'_>,
) -> Result<(Value, Rows, Vec<String>), Error> {
    let mut result = Object::new();
    let mut rows_by_package = Rows::default();
    let mut problems = Vec::new();
    let mut pinned: Vec<(&str, &Value)> = object(get(pins, "packages")?)?.iter().collect();
    pinned.sort_by(|left, right| left.0.cmp(right.0));
    for (name, pin) in pinned {
        let rows = scan(&package_directory(packages, name), check)?;
        rows_by_package.0.insert(name.to_owned(), rows.clone());
        let mut entry = Object::new();
        let exact = || -> Result<bool, Error> {
            Ok(rows.len() as i64 == integer(get(pin, "files")?)?
                && package_digest(&rows, false, false) == text(get(pin, "digest")?)?)
        };
        match options.before {
            None => {
                let matches;
                if options.fetch {
                    let fetch_files = rows
                        .keys()
                        .filter(|relative| kept(relative, false, true))
                        .count();
                    let (other, records) = differing_kinds(&rows, pin)?;
                    let digest = package_digest(&rows, false, true);
                    matches = fetch_files as i64 == integer(get(pin, "fetch_files")?)?
                        && digest == text(get(pin, "fetch_digest")?)?
                        && other.is_empty();
                    entry.set("fetch_files", fetch_files);
                    entry.set("fetch_digest", digest);
                    entry.set("matches_fetch_pin", matches);
                    entry.set("differing_kinds", strings(&other));
                    entry.set("differing_build_record_kinds", strings(&records));
                    entry.set("matches_exact_pin", exact()?);
                } else if options.content {
                    let content_files = rows
                        .keys()
                        .filter(|relative| !lake_hash_file(relative))
                        .count();
                    let digest = package_digest(&rows, true, false);
                    matches = content_files as i64 == integer(get(pin, "content_files")?)?
                        && digest == text(get(pin, "content_digest")?)?;
                    entry.set("content_files", content_files);
                    entry.set("content_digest", digest);
                    entry.set("matches_content_pin", matches);
                    entry.set("exact_digest", package_digest(&rows, false, false));
                    entry.set("matches_exact_pin", exact()?);
                } else {
                    matches = exact()?;
                    entry.set("files", rows.len());
                    entry.set("digest", package_digest(&rows, false, false));
                    entry.set("matches_pin", matches);
                }
                if !matches {
                    problems.push(name.to_owned());
                }
            }
            Some(before) => {
                let earlier = before
                    .0
                    .get(name)
                    .ok_or_else(|| Error::Key(name.to_owned()))?;
                let changed_all: Vec<String> = earlier
                    .iter()
                    .filter(|(key, row)| rows.get(*key) != Some(row))
                    .map(|(key, _)| key.clone())
                    .collect();
                let rehashed: Vec<String> = changed_all
                    .iter()
                    .filter(|key| key.ends_with(".hash") && rows.contains_key(*key))
                    .cloned()
                    .collect();
                let changed: Vec<String> = changed_all
                    .into_iter()
                    .filter(|key| !rehashed.contains(key))
                    .collect();
                let added: Vec<String> = rows
                    .keys()
                    .filter(|key| !earlier.contains_key(*key))
                    .cloned()
                    .collect();
                entry.set("files", rows.len());
                entry.set("changed_or_removed", changed.len());
                entry.set("rehashed", rehashed.len());
                entry.set("added", added.len());
                let examples: Vec<String> = changed
                    .iter()
                    .chain(rehashed.iter())
                    .chain(added.iter())
                    .take(5)
                    .cloned()
                    .collect();
                entry.set("examples", strings(&examples));
                if !changed.is_empty() || (!added.is_empty() && !options.allow_additions) {
                    problems.push(name.to_owned());
                }
            }
        }
        result.set(name, entry);
    }
    Ok((Value::Object(result), rows_by_package, problems))
}
