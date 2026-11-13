// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Install the version-8 kernel entry, revision 8, into a fresh installation root.
//!
//! The port of install-kernel.py. Inputs: the repository snapshot, a lean-v8 project built by
//! the lean-v8 build, the helper build written by `fang-v8-kernel-helpers` against that
//! project, and the pinned toolchain. Every repository file the entry policy pins must match
//! its pin: they are the sources the entry binary was built from. The entry binary beside this
//! installer is copied to `ROOT/bin/fang-v8-kernel`; the helper binary beside it must be the one
//! that wrote the helper build. The helper build must have been made with these helper and
//! closure pins, and the project's source of every module in the kernel's lean-v8 import
//! closure must still match pins/lean-v8-closure.json; the install stops otherwise, and also
//! when the toolchain's lean and lake binaries or the tree summary of its lib/ directory differ
//! from the policy's pins. The installer then records the tree manifests (the toolchain, the
//! helper objects and every entry of the recorded LEAN_PATH and LD_LIBRARY_PATH, an entry inside
//! another recorded directory being covered by it and a missing one recorded as absent) and
//! writes `ROOT/installation.json`: the root, the output root, HOME, the entry binary, the
//! toolchain, the project, the helper objects and closure pins, the recorded Lean environment
//! and the tree record. No receipt is read.

use std::ffi::OsString;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};

use fang_json::{Object, ParseLimits, Value};

use crate::trees;
use crate::util::{file_sha256, inside, manifest_bytes, resolve, utc_now};

pub const POLICY: &str = "tools/v8_kernel/policy.json";
pub const POLICY_SCHEMA: &str = "fang-v8-equality-kernel-entry-policy-v5";
pub const HELPER_PINS: &str = "tools/v8_kernel/pins/helper-sources.json";
pub const CLOSURE: &str = "tools/v8_kernel/pins/lean-v8-closure.json";
pub const ENTRY_BINARY: &str = "fang-v8-kernel";
pub const HELPER_BINARY: &str = "fang-v8-kernel-helpers";
pub const HELPER_SCHEMA: &str = "fang-v8-kernel-helpers-build-v3";
pub const INSTALLATION_SCHEMA: &str = "fang-v8-kernel-installation-v3";

type Fallible<T> = Result<T, String>;

fn json(path: &Path) -> Fallible<(Vec<u8>, Value)> {
    let data = fs::read(path).map_err(|error| format!("{}: {error}", path.display()))?;
    let value = fang_json::parse(
        &data,
        &ParseLimits {
            max_bytes: 64 << 20,
            max_depth: 64,
        },
    )
    .map_err(|error| format!("{}: {}", path.display(), error.python_message(&data)))?;
    Ok((data, value))
}

fn object<'a>(value: &'a Value, key: &str) -> Fallible<&'a Object> {
    value
        .get(key)
        .and_then(Value::as_object)
        .ok_or_else(|| format!("Missing object field {key}"))
}

/// The source path of a module name: `A.B` is `A/B.lean`.
pub fn module_source(project: &Path, name: &str) -> PathBuf {
    project.join(format!("{}.lean", name.replace('.', "/")))
}

/// The closure modules whose project source is missing or differs from its pin, at most ten.
pub fn closure_differences(project: &Path, closure: &Value) -> Fallible<Vec<String>> {
    let pins = object(closure, "sources_sha256")?;
    let mut names: Vec<&str> = pins.keys().collect();
    names.sort_unstable();
    let mut differing = Vec::new();
    for name in names {
        let path = module_source(project, name);
        let expected = pins.get(name).and_then(Value::as_str).unwrap_or_default();
        let same = path.is_file() && file_sha256(&path).is_ok_and(|actual| actual == expected);
        if !same {
            differing.push(name.to_owned());
        }
    }
    Ok(differing)
}

struct Arguments {
    repository: PathBuf,
    root: PathBuf,
    project: PathBuf,
    lean_build: PathBuf,
    helpers: PathBuf,
    toolchain: PathBuf,
    output_root: Option<PathBuf>,
}

fn arguments(raw: &[OsString]) -> Fallible<Arguments> {
    let mut values: Vec<(String, PathBuf)> = Vec::new();
    let mut index = 1;
    while index < raw.len() {
        let flag = raw[index].to_string_lossy().into_owned();
        let Some(value) = raw.get(index + 1) else {
            return Err(format!("{flag} needs a value"));
        };
        if !flag.starts_with("--") || values.iter().any(|(existing, _)| *existing == flag) {
            return Err(format!("unexpected argument {flag}"));
        }
        values.push((flag, PathBuf::from(value)));
        index += 2;
    }
    let mut take = |name: &str| {
        values
            .iter()
            .position(|(flag, _)| flag == name)
            .map(|position| values.remove(position).1)
    };
    let required = [
        "--repository",
        "--root",
        "--project",
        "--lean-build",
        "--helpers",
        "--lean-toolchain",
    ];
    let mut found = Vec::new();
    for name in required {
        found.push(
            take(name).ok_or_else(|| format!("the following arguments are required: {name}"))?,
        );
    }
    let output_root = take("--output-root");
    if let Some((flag, _)) = values.first() {
        return Err(format!("unrecognized arguments: {flag}"));
    }
    let mut found = found.into_iter();
    let mut next = || found.next().unwrap_or_default();
    Ok(Arguments {
        repository: next(),
        root: next(),
        project: next(),
        lean_build: next(),
        helpers: next(),
        toolchain: next(),
        output_root,
    })
}

/// The trees to record: the toolchain, the helper objects and every recorded search entry,
/// named, and without an entry that lies inside another.
pub fn tree_candidates(
    toolchain: &str,
    helpers: &str,
    environment: &Object,
) -> Fallible<Vec<(String, String)>> {
    let mut candidates = vec![
        ("toolchain".to_owned(), toolchain.to_owned()),
        ("helpers".to_owned(), helpers.to_owned()),
    ];
    for key in ["LEAN_PATH", "LD_LIBRARY_PATH"] {
        let value = environment
            .get(key)
            .and_then(Value::as_str)
            .ok_or_else(|| format!("Missing {key}"))?;
        for (index, item) in value.split(':').filter(|part| !part.is_empty()).enumerate() {
            candidates.push((
                format!("{}_{index:02}", key.to_lowercase()),
                item.to_owned(),
            ));
        }
    }
    // `str(Path(item))` keys, the first name kept.
    let mut unique: Vec<(String, String)> = Vec::new();
    for (name, item) in candidates {
        let normal = PathBuf::from(&item)
            .components()
            .collect::<PathBuf>()
            .to_string_lossy()
            .into_owned();
        if !unique.iter().any(|(path, _)| *path == normal) {
            unique.push((normal, name));
        }
    }
    let mut trees: Vec<(String, String)> = Vec::new();
    for (path, name) in &unique {
        let covered = unique
            .iter()
            .any(|(other, _)| other != path && inside(Path::new(path), Path::new(other)));
        if !covered {
            trees.push((name.clone(), path.clone()));
        }
    }
    trees.sort();
    Ok(trees)
}

fn sibling(name: &str) -> Fallible<PathBuf> {
    let executable = std::env::current_exe()
        .map_err(|error| format!("cannot locate this installer: {error}"))?;
    let directory = executable
        .parent()
        .ok_or("the installer has no directory")?;
    Ok(directory.join(name))
}

/// `fang-v8-kernel-install`.
pub fn main(raw: &[OsString]) -> Fallible<Value> {
    let arguments = arguments(raw)?;
    if !cfg!(target_os = "linux") {
        return Err("Use Linux/WSL".to_owned());
    }
    let repository = resolve(&arguments.repository);
    let root = resolve(&arguments.root);
    if let Some(parent) = root.parent() {
        fs::create_dir_all(parent).map_err(|error| format!("{}: {error}", parent.display()))?;
    }
    fs::create_dir(&root).map_err(|error| format!("{}: {error}", root.display()))?;
    let project = resolve(&arguments.project);
    let toolchain = resolve(&arguments.toolchain);
    let (policy_data, policy) = json(&repository.join(POLICY))?;
    if policy.get("schema").and_then(Value::as_str) != Some(POLICY_SCHEMA) {
        return Err("Unknown entry policy".to_owned());
    }
    let files = object(&policy, "files")?;
    let mut relatives: Vec<&str> = files.keys().collect();
    relatives.sort_unstable();
    for relative in relatives {
        let pin = files
            .get(relative)
            .and_then(Value::as_str)
            .unwrap_or_default();
        let path = Path::new(relative);
        if path.is_absolute() || path.components().any(|part| part.as_os_str() == "..") {
            return Err(format!("Policy path escapes the repository: {relative}"));
        }
        if file_sha256(&repository.join(relative)).ok().as_deref() != Some(pin) {
            return Err(format!(
                "Repository file differs from the entry policy: {relative}"
            ));
        }
    }
    let entry_source = sibling(ENTRY_BINARY)?;
    let entry_data =
        fs::read(&entry_source).map_err(|error| format!("{}: {error}", entry_source.display()))?;
    let bin = root.join("bin");
    fs::create_dir(&bin).map_err(|error| format!("{}: {error}", bin.display()))?;
    let entry = bin.join(ENTRY_BINARY);
    fs::write(&entry, &entry_data).map_err(|error| format!("{}: {error}", entry.display()))?;
    fs::set_permissions(&entry, fs::Permissions::from_mode(0o555))
        .map_err(|error| error.to_string())?;
    let entry_sha256 = fang_hash::sha256_hex(&entry_data);
    if file_sha256(&entry)? != entry_sha256 {
        return Err("The installed entry differs from its source".to_owned());
    }
    fs::write(root.join("policy.json"), &policy_data).map_err(|error| error.to_string())?;
    let (lean_build_data, lean_build) = json(&arguments.lean_build.join("manifest.json"))?;
    let lean_toolchain = lean_build
        .get("toolchain")
        .and_then(|value| value.get("path"))
        .and_then(Value::as_str);
    if lean_build.get("status").and_then(Value::as_str) != Some("built-and-audited")
        || lean_toolchain.map(|path| resolve(Path::new(path))) != Some(toolchain.clone())
    {
        return Err("The lean-v8 build did not pass with this toolchain".to_owned());
    }
    let pinned = policy
        .get("toolchain")
        .ok_or("Policy without a toolchain")?;
    let mut binaries = Object::new();
    for binary in ["lean", "lake"] {
        let digest = file_sha256(&toolchain.join("bin").join(binary))?;
        if pinned
            .get(&format!("{binary}_sha256"))
            .and_then(Value::as_str)
            != Some(digest.as_str())
        {
            return Err(format!(
                "The toolchain is not the pinned Lean release: {binary}"
            ));
        }
        binaries.set(binary, digest);
    }
    let (helpers_data, helpers) = json(&arguments.helpers.join("manifest.json"))?;
    let helpers_ok = helpers.get("status").and_then(Value::as_str) == Some("built-and-audited")
        && helpers
            .get("project")
            .and_then(Value::as_str)
            .map(PathBuf::from)
            == Some(project.clone())
        && helpers
            .get("toolchain")
            .and_then(Value::as_str)
            .map(PathBuf::from)
            == Some(toolchain.clone());
    if !helpers_ok {
        return Err("The helper build did not pass against this project and toolchain".to_owned());
    }
    if helpers.get("schema").and_then(Value::as_str) != Some(HELPER_SCHEMA) {
        return Err("Unknown helper build record".to_owned());
    }
    let helper_binary = sibling(HELPER_BINARY)?;
    for (key, path, label) in [
        (
            "runner_sha256",
            helper_binary.clone(),
            HELPER_BINARY.to_owned(),
        ),
        (
            "pins_sha256",
            repository.join(HELPER_PINS),
            HELPER_PINS.to_owned(),
        ),
        (
            "closure_sha256",
            repository.join(CLOSURE),
            CLOSURE.to_owned(),
        ),
    ] {
        if helpers.get(key).and_then(Value::as_str) != Some(file_sha256(&path)?.as_str()) {
            return Err(format!("The helper build used another {label}"));
        }
    }
    let (closure_data, closure) = json(&repository.join(CLOSURE))?;
    let differing = closure_differences(&project, &closure)?;
    if !differing.is_empty() {
        let shown: Vec<&str> = differing.iter().take(10).map(String::as_str).collect();
        return Err(format!(
            "lean-v8 differs from the kernel import closure: {}",
            shown.join(", ")
        ));
    }
    let helper_directory = resolve(&arguments.helpers.join("source"));
    let objects = object(&helpers, "objects_sha256")?;
    for (relative, pin) in objects.iter() {
        if file_sha256(&helper_directory.join(relative))
            .ok()
            .as_deref()
            != pin.as_str()
        {
            return Err(format!(
                "Helper object differs from its build record: {relative}"
            ));
        }
    }
    let environment = object(&helpers, "lean_environment")?;
    let toolchain_text = toolchain.to_string_lossy().into_owned();
    let helper_text = helper_directory.to_string_lossy().into_owned();
    let mut recorded = Object::new();
    for (name, directory) in tree_candidates(&toolchain_text, &helper_text, environment)? {
        recorded.set(name.as_str(), trees::record(&directory)?);
    }
    // The toolchain's lib/ directory as the tree collector records it on its own.
    let toolchain_files = recorded
        .get("toolchain")
        .and_then(|item| item.get("files_sha256"))
        .and_then(Value::as_object)
        .ok_or("No toolchain tree")?;
    let mut lib_files = trees::Files::new();
    for (key, value) in toolchain_files.iter() {
        if let Some(rest) = key.strip_prefix("lib/") {
            lib_files.insert(
                rest.to_owned(),
                value.as_str().unwrap_or_default().to_owned(),
            );
        }
    }
    let lib_tree_sha256 = trees::summary(&lib_files)?;
    if pinned.get("lib_tree_sha256").and_then(Value::as_str) != Some(lib_tree_sha256.as_str()) {
        return Err("The toolchain is not the pinned Lean release: lib".to_owned());
    }
    let trees_value = Value::Object(recorded.clone());
    let trees_data = manifest_bytes(&trees_value)?;
    fs::write(root.join("trees.json"), &trees_data).map_err(|error| error.to_string())?;
    let output_root = resolve(
        &arguments
            .output_root
            .clone()
            .unwrap_or_else(|| root.join("run")),
    );
    if let Some(parent) = output_root.parent() {
        fs::create_dir_all(parent).map_err(|error| format!("{}: {error}", parent.display()))?;
    }
    fs::create_dir(&output_root).map_err(|error| format!("{}: {error}", output_root.display()))?;
    fs::create_dir(root.join("home")).map_err(|error| error.to_string())?;
    let mut summary = Object::new();
    for (name, item) in recorded.iter() {
        summary.set(
            name,
            Value::Array(vec![
                item.get("files").cloned().unwrap_or(Value::Null),
                item.get("sha256").cloned().unwrap_or(Value::Null),
            ]),
        );
    }
    let mut record = Object::new();
    record.set("schema", INSTALLATION_SCHEMA);
    record.set("installed_utc", utc_now());
    record.set("root", root.to_string_lossy().as_ref());
    record.set("output_root", output_root.to_string_lossy().as_ref());
    record.set("home", root.join("home").to_string_lossy().as_ref());
    let mut entry_record = Object::new();
    entry_record.set("path", entry.to_string_lossy().as_ref());
    entry_record.set("sha256", entry_sha256.as_str());
    record.set("entry", Value::Object(entry_record));
    let mut toolchain_record = Object::new();
    toolchain_record.set("directory", toolchain_text.as_str());
    toolchain_record.set(
        "lean_sha256",
        binaries.get("lean").cloned().unwrap_or(Value::Null),
    );
    toolchain_record.set(
        "lake_sha256",
        binaries.get("lake").cloned().unwrap_or(Value::Null),
    );
    toolchain_record.set("lib_tree_sha256", lib_tree_sha256.as_str());
    record.set("toolchain", Value::Object(toolchain_record));
    let mut project_record = Object::new();
    project_record.set("directory", project.to_string_lossy().as_ref());
    project_record.set(
        "build_manifest_sha256",
        fang_hash::sha256_hex(&lean_build_data),
    );
    project_record.set(
        "source_map_sha256",
        lean_build
            .get("source_map_sha256")
            .cloned()
            .unwrap_or(Value::Null),
    );
    record.set("project", Value::Object(project_record));
    let mut helper_record = Object::new();
    helper_record.set("directory", helper_text.as_str());
    helper_record.set("objects_sha256", Value::Object(objects.clone()));
    helper_record.set(
        "build_manifest_sha256",
        fang_hash::sha256_hex(&helpers_data),
    );
    helper_record.set(
        "audits",
        helpers.get("audits").cloned().unwrap_or(Value::Null),
    );
    helper_record.set(
        "runner_sha256",
        helpers.get("runner_sha256").cloned().unwrap_or(Value::Null),
    );
    helper_record.set(
        "pins_sha256",
        helpers.get("pins_sha256").cloned().unwrap_or(Value::Null),
    );
    record.set("helpers", Value::Object(helper_record));
    let mut closure_record = Object::new();
    closure_record.set("sha256", fang_hash::sha256_hex(&closure_data));
    closure_record.set(
        "sources_checked",
        object(&closure, "sources_sha256")?.len() as u64,
    );
    record.set("closure", Value::Object(closure_record));
    record.set("lean_environment", Value::Object(environment.clone()));
    let mut tree_record = Object::new();
    tree_record.set("path", root.join("trees.json").to_string_lossy().as_ref());
    tree_record.set("sha256", fang_hash::sha256_hex(&trees_data));
    tree_record.set("summary", Value::Object(summary.clone()));
    record.set("trees", Value::Object(tree_record));
    record.set("policy_sha256", fang_hash::sha256_hex(&policy_data));
    record.set(
        "installer_sha256",
        file_sha256(&std::env::current_exe().map_err(|error| error.to_string())?)?,
    );
    let data = manifest_bytes(&Value::Object(record))?;
    fs::write(root.join("installation.json"), &data).map_err(|error| error.to_string())?;
    let mut printed = Object::new();
    printed.set("root", root.to_string_lossy().as_ref());
    printed.set("installation_sha256", fang_hash::sha256_hex(&data));
    printed.set("policy_sha256", fang_hash::sha256_hex(&policy_data));
    printed.set("trees", Value::Object(summary));
    Ok(Value::Object(printed))
}

#[cfg(test)]
mod tests {
    use super::tree_candidates;
    use fang_json::Object;

    #[test]
    fn covered_entries_are_left_out() {
        let mut environment = Object::new();
        environment.set(
            "LEAN_PATH",
            "/p/.lake/build/lib/lean:/t/lib/lean:/p/.lake/packages/x/.lake/build/lib/lean:",
        );
        environment.set("LD_LIBRARY_PATH", "/t/lib:/missing");
        let trees = tree_candidates("/t", "/h", &environment).unwrap_or_default();
        let names: Vec<&str> = trees.iter().map(|(name, _)| name.as_str()).collect();
        assert_eq!(
            names,
            [
                "helpers",
                "ld_library_path_01",
                "lean_path_00",
                "lean_path_02",
                "toolchain"
            ]
        );
        assert!(
            trees
                .iter()
                .all(|(_, path)| path != "/t/lib/lean" && path != "/t/lib")
        );
    }
}
