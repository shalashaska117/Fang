// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! tools/fang_szs/dependencies.py: the declared local Rust dependency, inventoried before it is
//! snapshotted or checked.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use fang_json::{Object, Value};

use crate::error::Error;
use crate::util::{self, Check, display, lstat, optional, read_toml};

pub const CORE: &str = "crates/fang-predicate-index";
pub const CORE_FILES: [&str; 6] = [
    "Cargo.toml",
    "Cargo.lock",
    "rust-toolchain.toml",
    "LICENSE",
    "src/lib.rs",
    "tests/index.rs",
];
pub const LOCAL_NOTES: [&str; 3] = ["README.md", "CONTRACT.md", "PROMOTION.md"];

fn fail<T>(message: impl Into<String>) -> Result<T, Error> {
    Err(Error::value(message))
}

fn package(name: &str, version: &str, dependencies: Option<&[&str]>) -> Value {
    let mut object = Object::new();
    object.set("name", name);
    object.set("version", version);
    if let Some(dependencies) = dependencies {
        object.set(
            "dependencies",
            Value::Array(dependencies.iter().map(|name| Value::from(*name)).collect()),
        );
    }
    Value::Object(object)
}

fn core_package() -> Value {
    package("fang-predicate-index-core", "0.0.0", None)
}

/// `regular(path, check)` of dependencies.py, with its own message.
fn regular(path: &Path, check: Check<'_>) -> Result<(), Error> {
    check()?;
    if !lstat(path)?.file_type().is_file() {
        return fail(format!(
            "Dependency input must be a regular file: {}",
            display(path)
        ));
    }
    Ok(())
}

/// `read_toml(path, check)`: regular, then parsed.
pub(crate) fn read_checked_toml(path: &Path, check: Check<'_>) -> Result<Value, Error> {
    regular(path, check)?;
    read_toml(path)
}

/// `reject_other_dependencies(manifest)`.
pub fn reject_other_dependencies(manifest: &Value) -> Result<(), Error> {
    for key in [
        "dev-dependencies",
        "build-dependencies",
        "target",
        "workspace",
        "patch",
        "replace",
    ] {
        if optional(manifest, key).is_some() {
            return fail(format!("Unreviewed Cargo dependency section: {key}"));
        }
    }
    let package = optional(manifest, "package");
    if package
        .and_then(|package| optional(package, "build"))
        .is_some()
    {
        return fail("Explicit build scripts require review");
    }
    if package
        .and_then(|package| optional(package, "workspace"))
        .is_some()
    {
        return fail("External package workspaces require review");
    }
    for key in ["lib", "bin", "example", "test", "bench"] {
        if optional(manifest, key).is_some() {
            return fail(format!(
                "Explicit Cargo source targets require review: {key}"
            ));
        }
    }
    Ok(())
}

fn real_directory(path: &Path, check: Check<'_>) -> Result<(), Error> {
    check()?;
    if !lstat(path)?.file_type().is_dir() {
        return fail(format!(
            "Dependency parent must be a real directory: {}",
            display(path)
        ));
    }
    Ok(())
}

fn check_lock(path: &Path, packages: Vec<Value>, check: Check<'_>) -> Result<(), Error> {
    let mut expected = Object::new();
    expected.set("version", 4u8);
    expected.set("package", Value::Array(packages));
    if read_checked_toml(path, check)? != Value::Object(expected) {
        return fail(format!(
            "Unreviewed Cargo lockfile graph: {}",
            display(path)
        ));
    }
    Ok(())
}

fn lexists(path: &Path) -> bool {
    std::fs::symlink_metadata(path).is_ok()
}

fn empty_object(value: Option<&Value>) -> bool {
    match value {
        None => true,
        Some(Value::Object(object)) => object.is_empty(),
        Some(_) => false,
    }
}

/// `_root_dependency_files(root, check, allowed_crates)`.
pub fn root_dependency_files(
    root: &Path,
    check: Check<'_>,
    allowed_crates: &BTreeSet<String>,
) -> Result<Vec<PathBuf>, Error> {
    let mut manifest = read_checked_toml(&root.join("Cargo.toml"), check)?;
    let workspace = optional(&manifest, "workspace").is_some();
    if workspace {
        let map = crate::v8::load_map(root, crate::v8::RUST_MAP, crate::v8::RUST_SCHEMA, check)?;
        crate::v8::check_workspace(root, &manifest, &map, check)?;
        if let Some(object) = manifest.as_object_mut() {
            object.remove("workspace");
        }
    }
    reject_other_dependencies(&manifest)?;
    if lexists(&root.join("build.rs")) {
        return fail("Implicit root build scripts require review");
    }
    let package_value = optional(&manifest, "package");
    let identity = (
        package_value
            .and_then(|package| optional(package, "name"))
            .and_then(Value::as_str),
        package_value
            .and_then(|package| optional(package, "version"))
            .and_then(Value::as_str),
    );
    if identity != (Some("fang"), Some("0.1.0")) {
        return fail("Unreviewed root package identity");
    }
    let dependencies = optional(&manifest, "dependencies");
    if empty_object(dependencies) {
        check_lock(
            &root.join("Cargo.lock"),
            vec![package("fang", "0.1.0", None)],
            check,
        )?;
        if lexists(&root.join("crates")) {
            return fail("Local crates exist without a declared dependency");
        }
        return Ok(Vec::new());
    }
    let mut expected = Object::new();
    let mut path = Object::new();
    path.set("path", CORE);
    expected.set("fang-predicate-index-core", path);
    if dependencies != Some(&Value::Object(expected)) {
        return fail("Unreviewed local Rust dependency graph");
    }
    if !workspace {
        check_lock(
            &root.join("Cargo.lock"),
            vec![
                package("fang", "0.1.0", Some(&["fang-predicate-index-core"])),
                core_package(),
            ],
            check,
        )?;
    }
    real_directory(&root.join("crates"), check)?;
    let crate_directory = root.join(CORE);
    real_directory(&crate_directory, check)?;
    for entry in
        std::fs::read_dir(root.join("crates")).map_err(util::os_error(&root.join("crates")))?
    {
        check()?;
        let entry = entry.map_err(util::os_error(&root.join("crates")))?;
        if !allowed_crates.contains(&entry.file_name().to_string_lossy().into_owned()) {
            return fail("Unexpected local crate");
        }
    }
    let mut found = BTreeSet::new();
    let mut pending = vec![crate_directory.clone()];
    while let Some(directory) = pending.pop() {
        real_directory(&directory, check)?;
        for entry in std::fs::read_dir(&directory).map_err(util::os_error(&directory))? {
            check()?;
            let entry = entry.map_err(util::os_error(&directory))?;
            let path = entry.path();
            let relative = util::relative_posix(&path, &crate_directory);
            let kind = lstat(&path)?.file_type();
            if kind.is_dir() {
                if relative == "target" {
                    continue;
                }
                if relative != "src" && relative != "tests" {
                    return fail(format!("Unexpected dependency directory: {relative}"));
                }
                pending.push(path);
            } else if kind.is_file() && CORE_FILES.contains(&relative.as_str()) {
                found.insert(relative);
            } else if kind.is_file() && LOCAL_NOTES.contains(&relative.as_str()) {
                continue;
            } else {
                return fail(format!("Unexpected dependency member: {relative}"));
            }
        }
    }
    let all: BTreeSet<String> = CORE_FILES.iter().map(|name| (*name).to_owned()).collect();
    if found != all {
        let missing: Vec<&str> = all.difference(&found).map(String::as_str).collect();
        return fail(format!(
            "Incomplete dependency inventory: {}",
            fang_json::python_repr_list(missing)
        ));
    }
    let core_manifest = read_checked_toml(&crate_directory.join("Cargo.toml"), check)?;
    reject_other_dependencies(&core_manifest)?;
    if !empty_object(optional(&core_manifest, "dependencies")) {
        return fail("Transitive core dependencies require review");
    }
    let core_identity = optional(&core_manifest, "package");
    for (key, value) in [("name", "fang-predicate-index-core"), ("version", "0.0.0")] {
        if core_identity
            .and_then(|package| optional(package, key))
            .and_then(Value::as_str)
            != Some(value)
        {
            return fail("Unexpected core package identity");
        }
    }
    check_lock(
        &crate_directory.join("Cargo.lock"),
        vec![core_package()],
        check,
    )?;
    let mut files: Vec<&str> = CORE_FILES.to_vec();
    files.sort();
    Ok(files
        .into_iter()
        .map(|relative| crate_directory.join(relative))
        .collect())
}

/// `dependency_files(root, check)`.
pub fn dependency_files(root: &Path, check: Check<'_>) -> Result<Vec<PathBuf>, Error> {
    let manifest = read_checked_toml(&root.join("Cargo.toml"), check)?;
    let old: BTreeSet<String> = ["fang-predicate-index".to_owned()].into_iter().collect();
    if empty_object(optional(&manifest, "dependencies")) {
        return root_dependency_files(root, check, &old);
    }
    let (extra, allowed) = crate::fof::leaf_files(root, check)?;
    let mut files = root_dependency_files(root, check, &allowed)?;
    files.extend(extra);
    if optional(
        &read_checked_toml(&root.join("Cargo.toml"), check)?,
        "workspace",
    )
    .is_some()
    {
        files.extend(crate::v8::rust_files(root, check)?);
    }
    Ok(files)
}
