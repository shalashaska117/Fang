// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The source inventory and snapshot of the local builds (build-local.py `source_files` and `snapshot`), the
//! lookup of a command on PATH (`shutil.which`), and Python's path order.

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Component, Path, PathBuf};

use fang_json::{Object, Value};
use fang_supervisor::Supervisor;

use crate::adapt;
use crate::common::{At, Error, Result, copyfile, mkdir, sha256_file, text_of};

/// Python's ordering of paths: by components, not by the joined text.
pub fn path_key(path: &Path) -> Vec<String> {
    path.components()
        .filter_map(|component| match component {
            Component::Normal(name) => Some(name.to_string_lossy().into_owned()),
            Component::RootDir => Some(String::new()),
            _ => None,
        })
        .collect()
}

/// The path relative to `root` in POSIX form.
pub fn relative(path: &Path, root: &Path) -> String {
    path.strip_prefix(root)
        .map(|inner| {
            inner
                .components()
                .map(|component| component.as_os_str().to_string_lossy().into_owned())
                .collect::<Vec<_>>()
                .join("/")
        })
        .unwrap_or_else(|_| text_of(path))
}

/// `directory.rglob("*")`: every entry below it, without following directory links.
pub fn rglob(directory: &Path) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let mut pending = vec![directory.to_path_buf()];
    while let Some(current) = pending.pop() {
        let Ok(entries) = fs::read_dir(&current) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if entry.file_type().is_ok_and(|kind| kind.is_dir()) {
                pending.push(path.clone());
            }
            found.push(path);
        }
    }
    found
}

/// build-local.py `source_files(root, check)`. lean/check-local.sh is listed while the tree has it.
pub fn source_files(root: &Path, supervisor: &Supervisor, stage: &str) -> Result<Vec<PathBuf>> {
    let mut files: Vec<PathBuf> = [
        "Cargo.toml",
        "Cargo.lock",
        "rust-toolchain.toml",
        "LICENSE",
        "CONTRIBUTORS.md",
    ]
    .iter()
    .map(|name| root.join(name))
    .collect();
    for folder in ["src", "tests", "examples", "LICENSES", "tools", "proofs"] {
        for path in rglob(&root.join(folder)) {
            let inner = relative(&path, root);
            let parts: Vec<&str> = inner.split('/').collect();
            let excluded = parts.iter().any(|part| {
                matches!(
                    *part,
                    "__pycache__" | ".local" | "evidence" | "runs" | "logs"
                )
            });
            if path.is_file()
                && !excluded
                && path.extension().is_none_or(|extension| extension != "pyc")
                && inner != "tools/tests/native_integration.py"
            {
                files.push(path);
            }
        }
    }
    for path in rglob(&root.join("lean")) {
        let inner = relative(&path, root);
        if path
            .extension()
            .is_some_and(|extension| extension == "lean")
            && !inner
                .split('/')
                .any(|part| matches!(part, ".lake" | "Generated"))
        {
            files.push(path);
        }
    }
    for name in [
        "lean-toolchain",
        "lakefile.toml",
        "check-local.sh",
        "tstp-sources.json",
    ] {
        let path = root.join("lean").join(name);
        if name != "check-local.sh" || path.exists() {
            files.push(path);
        }
    }
    files.push(root.join("LICENSES/Vampire.ORIGIN"));
    files.extend(adapt::dependency_files(root, supervisor, stage)?);
    files.sort_by_key(|path| path_key(path));
    files.dedup();
    Ok(files)
}

/// build-local.py `snapshot(root, target, supervisor)`: copy each source, check it did not change while it
/// was copied, and return relative path -> SHA-256.
pub fn snapshot(root: &Path, target: &Path, supervisor: &Supervisor) -> Result<Object> {
    let mut hashes = Object::new();
    for source in source_files(root, supervisor, "source-inventory")? {
        adapt::check_stage(supervisor, "snapshot")?;
        let regular =
            fs::symlink_metadata(&source).is_ok_and(|metadata| metadata.file_type().is_file());
        if !regular {
            return Err(Error::Value(format!(
                "Source must be a regular file: {}",
                text_of(&source)
            )));
        }
        let inner = relative(&source, root);
        let before = sha256_file(&source)?;
        let destination = target.join(&inner);
        if let Some(parent) = destination.parent() {
            mkdir(parent, 0o777, true, true)?;
        }
        copyfile(&source, &destination)?;
        if sha256_file(&source)? != before || sha256_file(&destination)? != before {
            return Err(Error::Value(format!(
                "Source changed during capture: {inner}"
            )));
        }
        hashes.set(inner, before);
    }
    Ok(hashes)
}

/// The names of the inventory, for the final comparison with the snapshot.
pub fn inventory_names(root: &Path, supervisor: &Supervisor, stage: &str) -> Result<Vec<String>> {
    let mut names: Vec<String> = source_files(root, supervisor, stage)?
        .iter()
        .map(|path| relative(path, root))
        .collect();
    names.sort();
    Ok(names)
}

/// `shutil.which(command)` against this process's PATH.
pub fn which(command: &str) -> Option<String> {
    let executable = |path: &Path| {
        fs::metadata(path)
            .is_ok_and(|metadata| metadata.is_file() && metadata.permissions().mode() & 0o111 != 0)
    };
    if command.contains('/') {
        return executable(Path::new(command)).then(|| command.to_string());
    }
    let path = std::env::var("PATH").unwrap_or_default();
    path.split(':')
        .filter(|directory| !directory.is_empty())
        .map(|directory| Path::new(directory).join(command))
        .find(|candidate| executable(candidate))
        .map(|candidate| text_of(&candidate))
}

/// The running binary's path and SHA-256: the `installer` record that replaces the `python` record.
pub fn installer_record() -> Result<Value> {
    let path = fs::canonicalize("/proc/self/exe").at(Path::new("/proc/self/exe"))?;
    Ok(crate::common::object(vec![
        ("path", text_of(&path).into()),
        ("sha256", sha256_file(&path)?.into()),
    ]))
}

/// A sibling binary of the running one, from the same build.
pub fn sibling(name: &str) -> Result<PathBuf> {
    let path = fs::canonicalize("/proc/self/exe").at(Path::new("/proc/self/exe"))?;
    Ok(path.with_file_name(name))
}

#[cfg(test)]
mod tests {
    use super::*;
    use fang_source_checks::deps::{CORE, CORE_FILES};
    use std::collections::BTreeSet;

    fn write(root: &Path, name: &str, text: &str) {
        let path = root.join(name);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, text).unwrap();
    }

    fn fixture(root: &Path) {
        write(
            root,
            "Cargo.toml",
            "[package]\nname = \"fang\"\nversion = \"0.1.0\"\n",
        );
        write(
            root,
            "Cargo.lock",
            "version = 4\n[[package]]\nname = \"fang\"\nversion = \"0.1.0\"\n",
        );
        write(root, "src/lib.rs", "// fixture\n");
    }

    fn names(root: &Path) -> Result<BTreeSet<String>> {
        let supervisor = adapt::supervisor(60.0, 2048, 1 << 20, 1 << 20).unwrap();
        Ok(source_files(root, &supervisor, "inventory-test")?
            .iter()
            .map(|p| relative(p, root))
            .collect())
    }

    #[test]
    fn bootstrap_inventory_includes_notices_and_rejects_build_scripts() {
        let root = adapt::make_temp_dir(&std::env::temp_dir(), "fang-inventory-deps-").unwrap();
        fixture(&root);
        write(
            &root,
            "Cargo.toml",
            "[package]\nname = \"fang\"\nversion = \"0.1.0\"\n[dependencies]\nfang-predicate-index-core = { path = \"crates/fang-predicate-index\" }\n",
        );
        write(
            &root,
            "Cargo.lock",
            "version = 4\n[[package]]\nname = \"fang\"\nversion = \"0.1.0\"\ndependencies = [\"fang-predicate-index-core\"]\n[[package]]\nname = \"fang-predicate-index-core\"\nversion = \"0.0.0\"\n",
        );
        for name in CORE_FILES {
            write(&root, &format!("{CORE}/{name}"), "fixture\n");
        }
        write(
            &root,
            &format!("{CORE}/Cargo.toml"),
            "[package]\nname = \"fang-predicate-index-core\"\nversion = \"0.0.0\"\n",
        );
        write(
            &root,
            &format!("{CORE}/Cargo.lock"),
            "version = 4\n[[package]]\nname = \"fang-predicate-index-core\"\nversion = \"0.0.0\"\n",
        );
        let actual: BTreeSet<_> = names(&root)
            .unwrap()
            .into_iter()
            .filter(|p| p.starts_with("crates/"))
            .collect();
        let expected: BTreeSet<_> = CORE_FILES
            .iter()
            .map(|name| format!("{CORE}/{name}"))
            .collect();
        assert_eq!(actual, expected);
        write(&root, &format!("{CORE}/build.rs"), "fn main() {}\n");
        assert!(
            names(&root)
                .unwrap_err()
                .typed()
                .contains("Unexpected dependency member: build.rs")
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn cache_ancestors_do_not_hide_project_sources() {
        let scratch = adapt::make_temp_dir(&std::env::temp_dir(), "fang-inventory-cache-").unwrap();
        for ancestor in [".local", "evidence", ".lake", "Generated"] {
            let root = scratch.join(ancestor).join("source");
            fixture(&root);
            let visible = [
                "src/lib.rs",
                "lean/Visible.lean",
                "tests/visible.rs",
                "examples/problems/visible.p",
                "LICENSES/Vampire.ORIGIN",
            ];
            let hidden = [
                "src/.local/stale.rs",
                "tests/evidence/stale.rs",
                "tools/runs/stale.py",
                "tools/logs/stale.py",
                "tools/__pycache__/stale.py",
                "lean/.lake/Hidden.lean",
                "lean/Generated/Hidden.lean",
            ];
            for name in visible.into_iter().chain(hidden) {
                write(&root, name, "fixture\n");
            }
            let found = names(&root).unwrap();
            for name in visible {
                assert!(found.contains(name), "missing {ancestor}/{name}");
            }
            for name in hidden {
                assert!(!found.contains(name), "included {ancestor}/{name}");
            }
        }
        fs::remove_dir_all(scratch).unwrap();
    }
}
