// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! tools/fang_szs/fof_dependencies.py: the explicitly declared FOF installed-tool graph.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use fang_json::{Object, Value};

use crate::error::Error;
use crate::util::{self, Check, array, get, lstat, object, optional, read_json, read_toml, text};

pub const OLD: [&str; 1] = ["fang-predicate-index"];
pub const ORDER: [&str; 4] = [
    "ground-fof-core",
    "ground-fof-frontend",
    "ground-fof-search",
    "ground-fof-versioned",
];

fn fail<T>(message: impl Into<String>) -> Result<T, Error> {
    Err(Error::value(message))
}

fn set(names: &[&str]) -> BTreeSet<String> {
    names.iter().map(|name| (*name).to_owned()).collect()
}

fn path_dependency(path: &str) -> Value {
    let mut object = Object::new();
    object.set("path", path);
    Value::Object(object)
}

/// `graph(name, manifest, lock)`.
pub fn graph(name: &str, manifest: &Value, lock: &Value) -> Result<(), Error> {
    let index = ORDER
        .iter()
        .position(|other| *other == name)
        .ok_or_else(|| Error::value(format!("{name:?} is not in tuple")))?;
    let mut dependencies = Object::new();
    dependencies.set("fang", path_dependency("../.."));
    for earlier in &ORDER[..index] {
        dependencies.set(
            format!("fang-{earlier}"),
            path_dependency(&format!("../{earlier}")),
        );
    }
    let mut package = Object::new();
    package.set("name", format!("fang-{name}"));
    package.set("version", "0.0.0");
    package.set("edition", "2024");
    package.set("publish", false);
    package.set("license", "BSD-3-Clause");
    if index < 2 {
        package.set("rust-version", "1.90");
    }
    let mut lints_rust = Object::new();
    lints_rust.set("unsafe_code", "forbid");
    let mut lints = Object::new();
    lints.set("rust", lints_rust);
    let mut release = Object::new();
    release.set("overflow-checks", true);
    let mut profile = Object::new();
    profile.set("release", release);
    let mut expected = Object::new();
    if name == "ground-fof-versioned" {
        package.set("autobins", false);
        let mut binary = Object::new();
        binary.set("name", "fang-ground-fof-driver");
        binary.set("path", "src/bin/driver.rs");
        expected.set("bin", Value::Array(vec![Value::Object(binary)]));
    }
    expected.set("package", package);
    expected.set("dependencies", dependencies);
    expected.set("lints", lints);
    expected.set("profile", profile);
    if *manifest != Value::Object(expected) {
        return fail("Unreviewed FOF package or path graph");
    }
    let mut packages: Vec<Value> = Vec::new();
    let entry = |name: &str, version: &str, dependencies: Option<Vec<String>>| {
        let mut object = Object::new();
        object.set("name", name);
        object.set("version", version);
        if let Some(dependencies) = dependencies {
            object.set(
                "dependencies",
                Value::Array(dependencies.into_iter().map(Value::from).collect()),
            );
        }
        Value::Object(object)
    };
    packages.push(entry(
        "fang",
        "0.1.0",
        Some(vec!["fang-predicate-index-core".to_owned()]),
    ));
    packages.push(entry("fang-predicate-index-core", "0.0.0", None));
    for (position, leaf) in ORDER[..=index].iter().enumerate() {
        let mut depends = vec!["fang".to_owned()];
        depends.extend(
            ORDER[..position]
                .iter()
                .map(|earlier| format!("fang-{earlier}")),
        );
        packages.push(entry(&format!("fang-{leaf}"), "0.0.0", Some(depends)));
    }
    packages.sort_by(|left, right| {
        left.get("name")
            .and_then(Value::as_str)
            .unwrap_or("")
            .cmp(right.get("name").and_then(Value::as_str).unwrap_or(""))
    });
    let mut expected_lock = Object::new();
    expected_lock.set("version", 4u8);
    expected_lock.set("package", Value::Array(packages));
    if *lock != Value::Object(expected_lock) {
        return fail("Unreviewed FOF transitive lock graph");
    }
    Ok(())
}

/// `leaf_files(root, check)`: the FOF leaf crates' files and the allowed crate names.
pub fn leaf_files(
    root: &Path,
    check: Check<'_>,
) -> Result<(Vec<PathBuf>, BTreeSet<String>), Error> {
    let crate_root = root.join("crates");
    let old = set(&OLD);
    if !crate_root.exists() {
        return Ok((Vec::new(), old));
    }
    if !lstat(&crate_root)?.file_type().is_dir() {
        return fail("Crate root must be a real directory");
    }
    let mut actual = BTreeSet::new();
    for child in std::fs::read_dir(&crate_root).map_err(util::os_error(&crate_root))? {
        check()?;
        let child = child.map_err(util::os_error(&crate_root))?;
        if !lstat(&child.path())?.file_type().is_dir() {
            return fail("Crate entry must be a real directory");
        }
        actual.insert(child.file_name().to_string_lossy().into_owned());
    }
    if actual == old {
        return Ok((Vec::new(), old));
    }
    let leaves = set(&ORDER);
    let mut version8 = BTreeSet::new();
    if optional(&read_toml(&root.join("Cargo.toml"))?, "workspace").is_some() {
        version8 = crate::v8::crate_names(root, check)?;
    }
    let allowed: BTreeSet<String> = old
        .iter()
        .chain(leaves.iter())
        .chain(version8.iter())
        .cloned()
        .collect();
    if actual != allowed {
        return fail("Incomplete or unknown FOF leaf graph");
    }
    let policy_path = root.join("tools/fof_szs/sources.json");
    if !lstat(&policy_path)?.file_type().is_file() {
        return fail("FOF source policy must be regular");
    }
    let policy = read_json(&policy_path)?;
    let policy_keys: BTreeSet<String> = object(&policy)?.keys().map(str::to_owned).collect();
    if policy_keys != set(&["schema", "crates"])
        || optional(&policy, "schema").and_then(Value::as_str) != Some("fang-fof-source-graph-v1")
        || object(get(&policy, "crates")?)?
            .keys()
            .map(str::to_owned)
            .collect::<BTreeSet<_>>()
            != leaves
    {
        return fail("FOF source policy differs");
    }
    let mut result = vec![policy_path];
    for name in &leaves {
        let crate_directory = crate_root.join(name);
        let declared = get(get(&policy, "crates")?, name)?;
        if object(declared)?
            .keys()
            .map(str::to_owned)
            .collect::<BTreeSet<_>>()
            != set(&["files", "manifest", "lock"])
        {
            return fail("Malformed FOF crate policy");
        }
        let listed: Vec<String> = array(get(declared, "files")?)?
            .iter()
            .map(|item| text(item).map(str::to_owned))
            .collect::<Result<_, _>>()?;
        let expected: BTreeSet<String> = listed.iter().cloned().collect();
        let mut reviewed = set(&["Cargo.toml", "Cargo.lock", "src/lib.rs"]);
        if name == "ground-fof-versioned" {
            reviewed.extend(set(&["src/bin/driver.rs", "tests/driver_cli.rs"]));
        }
        if expected.len() != listed.len() || expected != reviewed {
            return fail("FOF crate file policy differs from the reviewed inventory");
        }
        for relative in &expected {
            let parts: Vec<&str> = relative
                .split('/')
                .filter(|part| !part.is_empty() && *part != ".")
                .collect();
            if relative.starts_with('/') || parts.contains(&"..") || parts.is_empty() {
                return fail("Unsafe FOF source policy path");
            }
        }
        // os.walk(crate, followlinks=False), top down: in each directory the subdirectories are
        // checked first, then the files, and the walk descends depth first in listing order. A
        // directory that cannot be listed is skipped, as os.walk does without onerror.
        let mut found = BTreeSet::new();
        let mut pending = vec![crate_directory.clone()];
        while let Some(directory) = pending.pop() {
            // A listing error part way skips the whole directory, as in os.walk.
            let Ok(entries) = std::fs::read_dir(&directory)
                .and_then(|entries| entries.collect::<Result<Vec<_>, _>>())
            else {
                continue;
            };
            let mut directories: Vec<PathBuf> = Vec::new();
            let mut files: Vec<PathBuf> = Vec::new();
            for entry in entries {
                let path = entry.path();
                // os.walk sorts with entry.is_dir(), which follows symbolic links.
                if std::fs::metadata(&path).is_ok_and(|metadata| metadata.is_dir()) {
                    directories.push(path);
                } else {
                    files.push(path);
                }
            }
            check()?;
            let mut descend = Vec::new();
            for path in directories {
                let relative = util::relative_posix(&path, &crate_directory);
                if !lstat(&path)?.file_type().is_dir() {
                    return fail("FOF directory is a symlink or non-directory");
                }
                if relative == "target" {
                    continue;
                }
                if !expected
                    .iter()
                    .any(|value| value.starts_with(&format!("{relative}/")))
                {
                    return fail("Unlisted FOF source directory");
                }
                descend.push(path);
            }
            for path in files {
                check()?;
                let relative = util::relative_posix(&path, &crate_directory);
                if !expected.contains(&relative) || !lstat(&path)?.file_type().is_file() {
                    return fail("Unlisted or nonregular FOF source");
                }
                found.insert(relative);
            }
            pending.extend(descend.into_iter().rev());
        }
        if found != expected {
            return fail("Missing FOF source");
        }
        for (filename, key) in [("Cargo.toml", "manifest"), ("Cargo.lock", "lock")] {
            if read_toml(&crate_directory.join(filename))? != *get(declared, key)? {
                return fail(format!("FOF Cargo graph differs: {name}/{filename}"));
            }
        }
        graph(name, get(declared, "manifest")?, get(declared, "lock")?)?;
        result.extend(found.iter().map(|relative| crate_directory.join(relative)));
    }
    Ok((result, allowed))
}
