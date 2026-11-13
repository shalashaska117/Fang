// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Snapshot and check the std-only Lean checker and frontend proof sources. The specification is
//! tools/replay/check-suite.py.
//!
//! The runner copies every project Lean source into a fresh run directory, rejects proof holes, explicit
//! custom axioms and native decision shortcuts, compiles the import graph in dependency order in a new native
//! directory under /var/tmp, samples each compile's process-tree RSS every 50 ms, checks GNU time's maximum
//! RSS, and requires every printed axiom report to use only propext, Classical.choice and Quot.sound. The
//! manifest is written as the script wrote it: `json.dumps(manifest, indent=2)` in insertion order.
//!
//! Differences: the run directory holds a copy of this binary where the script copied itself; lean/check-local.sh
//! is copied only while the tree still has it; each compile runs in its own process group rather than its own
//! session; directory permission bits of the native copy are not copied.

use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use fang_json::{DumpOptions, Object, Value};

use crate::adapt;
use crate::common::{
    At, Error, Result, copy2, copyfile, mkdir, mkdir_plain, object, resolve, sha256_file, strings,
    text_of, utc_stamp, write_bytes,
};
use crate::scan::{audit_count, forbidden, imports, path_key, py_space};

/// `path.read_text()`: UTF-8 with universal newlines.
fn read_text(path: &Path) -> Result<String> {
    Ok(crate::scan::universal_newlines(
        &fs::read_to_string(path).at(path)?,
    ))
}

/// `lean_code(text)`, with its refusal as the script's RuntimeError.
pub fn lean_code(text: &str) -> Result<String> {
    crate::scan::lean_code(text).map_err(Error::Runtime)
}

pub struct Options {
    pub root: PathBuf,
    pub lean: PathBuf,
    pub out: Option<PathBuf>,
    pub with_tstp: bool,
    pub timeout_seconds: i64,
    pub memory_mib: i64,
}

const RSS_MONITOR: &str = "Sample summed process-tree RSS every 50 ms; kill the process group above the limit. GNU time \
independently records maximum RSS. Brief peaks between samples can escape the sampler.";
const LIMITS: &str = "Kernel checks cover stated Lean theorems. Compiling IO entrypoints does not run their native IO \
regressions; compiled #eval checks are not kernel instance proofs.";

/// `sorted(directory.rglob("*"))` restricted by `keep`, in Python's order.
fn walk(directory: &Path, keep: &dyn Fn(&Path) -> bool) -> Result<Vec<PathBuf>> {
    let mut found = Vec::new();
    let mut pending = vec![directory.to_path_buf()];
    while let Some(current) = pending.pop() {
        for entry in fs::read_dir(&current).at(&current)? {
            let path = entry.at(&current)?.path();
            if path.is_dir() && !path.is_symlink() {
                pending.push(path.clone());
            }
            if keep(&path) {
                found.push(path);
            }
        }
    }
    found.sort_by_key(|path| path_key(path));
    Ok(found)
}

fn lean_suffix(path: &Path) -> bool {
    path.extension()
        .is_some_and(|extension| extension == "lean")
}

fn posix(path: &Path) -> String {
    path_key(path).join("/")
}

/// `process_tree_rss(pid)`: VmRSS of a process and its current descendants, in KiB.
pub fn process_tree_rss(pid: u32) -> u64 {
    let status = match fs::read_to_string(format!("/proc/{pid}/status")) {
        Ok(text) => text,
        Err(_) => return 0,
    };
    let own = status
        .lines()
        .find_map(|line| {
            let rest = line.strip_prefix("VmRSS:")?;
            let number = rest.trim_start().strip_suffix("kB")?.trim_end();
            number.parse::<u64>().ok()
        })
        .unwrap_or(0);
    let children = match fs::read_to_string(format!("/proc/{pid}/task/{pid}/children")) {
        Ok(text) => text,
        Err(_) => return 0,
    };
    own + children
        .split_whitespace()
        .filter_map(|child| child.parse::<u32>().ok())
        .map(process_tree_rss)
        .sum::<u64>()
}

fn record(path: &Path, manifest: &Object) -> Result<()> {
    let text = fang_json::dumps(
        &Value::Object(manifest.clone()),
        &DumpOptions {
            indent: Some(2),
            sort_keys: false,
        },
    )
    .map_err(|error| Error::Value(error.0))?;
    write_bytes(path, format!("{text}\n").as_bytes())
}

fn output_of(command: &[&str]) -> Result<String> {
    let done = Command::new(command[0])
        .args(&command[1..])
        .stderr(Stdio::inherit())
        .output()
        .at(Path::new(command[0]))?;
    if !done.status.success() {
        return Err(Error::Runtime(format!(
            "Command '{}' returned non-zero exit status {}.",
            crate::common::py_repr_list(
                &command
                    .iter()
                    .map(|item| item.to_string())
                    .collect::<Vec<_>>()
            ),
            done.status.code().unwrap_or(-1)
        )));
    }
    Ok(String::from_utf8_lossy(&done.stdout).into_owned())
}

fn strip(text: &str) -> &str {
    text.trim_matches(py_space)
}

/// Run the suite. Returns the exit status.
pub fn main(options: &Options) -> Result<i32> {
    let root = resolve(&options.root)?;
    let lean = resolve(&options.lean)?;
    let stamp = utc_stamp();
    let run = match &options.out {
        Some(out) => resolve(out)?,
        None => root
            .join(".local")
            .join("checks")
            .join(format!("proof-suite-{stamp}")),
    };
    mkdir(&run, 0o777, true, false)?;
    let source = run.join("project");
    mkdir(&source, 0o777, true, false)?;
    mkdir_plain(&run.join("logs"))?;
    let native = adapt::make_temp_dir(Path::new("/var/tmp"), &format!("fang-checker-{stamp}-"))?;
    let mut manifest: Object = [
        ("status", Value::from("running")),
        ("suite", "std-only-checker-frontend".into()),
        ("source_root", text_of(&root.join("lean")).into()),
        ("native_project", text_of(&native).into()),
        ("timeout_seconds_per_module", options.timeout_seconds.into()),
        ("lean_heap_limit_mib", options.memory_mib.into()),
        ("rss_limit_mib", options.memory_mib.into()),
        ("rss_monitor", RSS_MONITOR.into()),
        ("lean_threads", 1u64.into()),
        ("completed_modules", Value::Array(Vec::new())),
        ("axiom_audits", Value::Array(Vec::new())),
        ("module_resources", Value::Object(Object::new())),
        ("limits", LIMITS.into()),
    ]
    .into_iter()
    .collect();
    let manifest_path = run.join("manifest.json");
    println!("{}", text_of(&run));
    manifest.set(
        "inherited_descriptors",
        crate::adapt::inherited_descriptors(),
    );
    record(&manifest_path, &manifest)?;
    match suite(
        options,
        &root,
        &lean,
        &run,
        &source,
        &native,
        &mut manifest,
        &manifest_path,
    ) {
        Ok((modules, audits)) => {
            let printed = object(vec![
                ("status", "passed".into()),
                ("modules", (modules as u64).into()),
                ("audits", (audits as u64).into()),
                ("run", text_of(&run).into()),
            ]);
            println!("{}", crate::common::compact(&printed));
            Ok(0)
        }
        Err(error) => {
            manifest.set("status", "failed");
            manifest.set("error", error.message());
            record(&manifest_path, &manifest)?;
            println!("{}", error.message());
            Ok(1)
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn suite(
    options: &Options,
    root: &Path,
    lean: &Path,
    run: &Path,
    source: &Path,
    native: &Path,
    manifest: &mut Object,
    manifest_path: &Path,
) -> Result<(usize, usize)> {
    let lean_root = root.join("lean");
    let mut paths = walk(&lean_root.join("Fang"), &|path| {
        path.is_file() && lean_suffix(path)
    })?;
    let mut top: Vec<PathBuf> = fs::read_dir(&lean_root)
        .at(&lean_root)?
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| lean_suffix(path) && path.is_file())
        .collect();
    top.sort_by_key(|path| path_key(path));
    paths.extend(top);
    for path in &paths {
        let destination = source.join(path.strip_prefix(&lean_root).expect("under lean/"));
        if let Some(parent) = destination.parent() {
            mkdir(parent, 0o777, true, true)?;
        }
        copyfile(path, &destination)?;
    }
    if options.with_tstp {
        for (folder, prefix) in [("tstp", ""), ("fof-tstp", "Fang/FOF/TSTP")] {
            let directory = root.join("proofs").join(folder);
            let mut members: Vec<PathBuf> = fs::read_dir(&directory)
                .map(|entries| {
                    entries
                        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
                        .filter(|path| lean_suffix(path))
                        .collect()
                })
                .unwrap_or_default();
            members.sort_by_key(|path| path_key(path));
            if members.is_empty() {
                return Err(Error::Runtime(format!(
                    "Missing text proof source directory: {folder}"
                )));
            }
            for path in members {
                let destination = source
                    .join(prefix)
                    .join(path.file_name().expect("file name"));
                if destination.exists() {
                    return Err(Error::Runtime(format!(
                        "Duplicate proof module: {}",
                        text_of(&destination)
                    )));
                }
                if let Some(parent) = destination.parent() {
                    mkdir(parent, 0o777, true, true)?;
                }
                copyfile(&path, &destination)?;
            }
        }
    }
    for name in ["lean-toolchain", "lakefile.toml", "check-local.sh"] {
        if name != "check-local.sh" || lean_root.join(name).exists() {
            copyfile(&lean_root.join(name), &source.join(name))?;
        }
    }
    let runner = std::env::current_exe().at(Path::new("/proc/self/exe"))?;
    copyfile(&runner, &run.join("fang-check-suite"))?;
    let toolchain = strip(&read_text(&source.join("lean-toolchain"))?).to_string();
    manifest.set("toolchain", toolchain.as_str());
    let lean_text = text_of(lean);
    let version = strip(&output_of(&[&lean_text, "--version"])?).to_string();
    manifest.set("lean_version", version.as_str());
    manifest.set("lean_executable_sha256", sha256_file(lean)?);
    let expected = toolchain
        .rsplit_once(":v")
        .map_or(toolchain.as_str(), |(_, version)| version);
    if !version.contains(&format!("version {expected},")) {
        return Err(Error::Runtime(format!(
            "Expected Lean {expected}, observed {version}"
        )));
    }
    write_bytes(
        &run.join("lean-version.txt"),
        format!("{version}\n").as_bytes(),
    )?;
    let mut modules: BTreeMap<String, PathBuf> = BTreeMap::new();
    let mut module_paths: Vec<(String, PathBuf)> = Vec::new();
    for path in walk(source, &|path| lean_suffix(path))? {
        let relative = path
            .strip_prefix(source)
            .expect("under the project")
            .with_extension("");
        let name = posix(&relative).replace('/', ".");
        module_paths.push((name.clone(), path.clone()));
        modules.insert(name, path);
    }
    let mut dependencies: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut declared = 0;
    for (module, path) in &module_paths {
        let code = lean_code(&read_text(path)?)?;
        if let Some(found) = forbidden(&code) {
            return Err(Error::Runtime(format!(
                "Forbidden proof construct in {module}: {found}"
            )));
        }
        dependencies.insert(module.clone(), imports(&code));
        declared += audit_count(&code);
    }
    manifest.set("declared_axiom_audits", declared as u64);
    let mut hashes = Object::new();
    for path in walk(source, &|path| path.is_file())? {
        hashes.set(
            posix(path.strip_prefix(source).expect("under the project")),
            sha256_file(&path)?,
        );
    }
    manifest.set("source_sha256", Value::Object(hashes.clone()));
    let mut order: Vec<String> = Vec::new();
    let mut visiting = BTreeSet::new();
    let mut visited = BTreeSet::new();
    let mut external = BTreeSet::new();
    fn visit(
        module: &str,
        dependencies: &BTreeMap<String, Vec<String>>,
        order: &mut Vec<String>,
        visiting: &mut BTreeSet<String>,
        visited: &mut BTreeSet<String>,
        external: &mut BTreeSet<String>,
    ) -> Result<()> {
        if visited.contains(module) {
            return Ok(());
        }
        let Some(imported) = dependencies.get(module) else {
            if !matches!(module.split('.').next(), Some("Init" | "Std" | "Lean")) {
                return Err(Error::Runtime(format!(
                    "Non-standard or missing dependency: {module}"
                )));
            }
            external.insert(module.to_string());
            return Ok(());
        };
        if visiting.contains(module) {
            return Err(Error::Runtime(format!(
                "Cyclic module dependency: {module}"
            )));
        }
        visiting.insert(module.to_string());
        for dependency in imported {
            visit(dependency, dependencies, order, visiting, visited, external)?;
        }
        visiting.remove(module);
        visited.insert(module.to_string());
        order.push(module.to_string());
        Ok(())
    }
    for module in modules.keys() {
        visit(
            module,
            &dependencies,
            &mut order,
            &mut visiting,
            &mut visited,
            &mut external,
        )?;
    }
    let prefix = PathBuf::from(strip(&output_of(&[&lean_text, "--print-prefix"])?));
    let mut standard = Object::new();
    for module in &external {
        let path = prefix
            .join("lib")
            .join("lean")
            .join(format!("{}.olean", module.replace('.', "/")));
        standard.set(
            module.as_str(),
            object(vec![
                ("path", text_of(&path).into()),
                ("sha256", sha256_file(&path)?.into()),
            ]),
        );
    }
    manifest.set("standard_library_imports", Value::Object(standard));
    manifest.set("module_order", strings(&order));
    record(manifest_path, manifest)?;
    copy_tree(source, native)?;
    let started = Instant::now();
    let limit_kib = options.memory_mib.max(0) as u64 * 1024;
    for module in &order {
        compile(options, module, lean, run, native, limit_kib, manifest)?;
        record(manifest_path, manifest)?;
    }
    let printed = manifest
        .get("axiom_audits")
        .and_then(Value::as_array)
        .map_or(0, Vec::len);
    if printed != declared {
        return Err(Error::Runtime(
            "Printed axiom-audit count differs from source commands".to_string(),
        ));
    }
    for (relative, expected) in hashes.iter() {
        let expected = expected.as_str();
        if Some(sha256_file(&source.join(relative))?.as_str()) != expected
            || Some(sha256_file(&native.join(relative))?.as_str()) != expected
        {
            return Err(Error::Runtime(format!(
                "Snapshot source changed: {relative}"
            )));
        }
    }
    let mut outputs = Object::new();
    for path in walk(native, &|path| {
        path.is_file()
            && path
                .extension()
                .is_some_and(|extension| extension == "olean")
    })? {
        outputs.set(
            posix(path.strip_prefix(native).expect("under the native project")),
            sha256_file(&path)?,
        );
    }
    manifest.set("build_output_sha256", Value::Object(outputs));
    manifest.set("status", "passed");
    let elapsed: f64 = format!("{:.3}", started.elapsed().as_secs_f64())
        .parse()
        .unwrap_or(0.0);
    manifest.set("elapsed_seconds", elapsed);
    record(manifest_path, manifest)?;
    Ok((order.len(), declared))
}

/// `shutil.copytree(source, native, dirs_exist_ok=True)`: files through copy2.
fn copy_tree(source: &Path, target: &Path) -> Result<()> {
    mkdir(target, 0o777, true, true)?;
    for entry in fs::read_dir(source).at(source)? {
        let path = entry.at(source)?.path();
        let destination = target.join(path.file_name().expect("entry name"));
        if path.is_dir() {
            copy_tree(&path, &destination)?;
        } else {
            copy2(&path, &destination)?;
        }
    }
    Ok(())
}

fn compile(
    options: &Options,
    module: &str,
    lean: &Path,
    run: &Path,
    native: &Path,
    limit_kib: u64,
    manifest: &mut Object,
) -> Result<()> {
    use std::os::unix::process::CommandExt;
    let relative = module.replace('.', "/");
    let log = run.join("logs").join(format!("{module}.log"));
    let command: Vec<String> = vec![
        "/usr/bin/time".into(),
        "-v".into(),
        "timeout".into(),
        options.timeout_seconds.to_string(),
        text_of(lean),
        "-j1".into(),
        format!("-M{}", options.memory_mib),
        "--root".into(),
        text_of(native),
        "-o".into(),
        text_of(&native.join(format!("{relative}.olean"))),
        text_of(&native.join(format!("{relative}.lean"))),
    ];
    let stream = File::create(&log).at(&log)?;
    let errors = stream.try_clone().at(&log)?;
    let mut child = Command::new(&command[0])
        .args(&command[1..])
        .current_dir(native)
        .env("LEAN_PATH", native)
        .stdin(Stdio::inherit())
        .stdout(stream)
        .stderr(errors)
        .process_group(0)
        .spawn()
        .at(Path::new(&command[0]))?;
    let (mut peak, mut exceeded) = (0u64, false);
    while child.try_wait().at(&log)?.is_none() {
        peak = peak.max(process_tree_rss(child.id()));
        if peak > limit_kib {
            exceeded = true;
            let _ = Command::new("/bin/kill")
                .args(["-s", "KILL", "--", &format!("-{}", child.id())])
                .status();
            break;
        }
        std::thread::sleep(Duration::from_millis(50));
    }
    let status = child.wait().at(&log)?;
    let returncode = status.code().unwrap_or_else(|| {
        use std::os::unix::process::ExitStatusExt;
        -status.signal().unwrap_or(0)
    });
    let mut resources = object(vec![
        ("sampled_process_tree_peak_rss_kib", peak.into()),
        ("memory_limit_exceeded", exceeded.into()),
        ("command", strings(&command)),
    ]);
    let set_resources = |manifest: &mut Object, resources: &Value| {
        if let Some(Value::Object(table)) = manifest.get_mut("module_resources") {
            table.set(module, resources.clone());
        }
    };
    set_resources(manifest, &resources);
    if returncode != 0 || exceeded {
        manifest.set("failed_module", module);
        manifest.set("exit_code", i64::from(returncode));
        return Err(Error::Runtime(format!(
            "Compilation failed: {module}; see {}",
            text_of(&log)
        )));
    }
    let output = read_text(&log)?;
    let measured = output
        .find("Maximum resident set size (kbytes):")
        .and_then(|at| {
            let rest = &output[at + "Maximum resident set size (kbytes):".len()..];
            let digits: String = rest
                .trim_start_matches(py_space)
                .chars()
                .take_while(char::is_ascii_digit)
                .collect();
            digits.parse::<u64>().ok()
        })
        .ok_or_else(|| {
            Error::Runtime(format!("Missing GNU time memory measurement for {module}"))
        })?;
    if let Value::Object(table) = &mut resources {
        table.set("gnu_time_maximum_rss_kib", measured);
    }
    set_resources(manifest, &resources);
    if measured > limit_kib {
        return Err(Error::Runtime(format!(
            "Measured RSS exceeds the limit for {module}: {measured} KiB"
        )));
    }
    if output.contains("sorryAx") {
        return Err(Error::Runtime(format!("Unexpected sorryAx in {module}")));
    }
    let audits = adapt::check_suite_audit(&output, module)?;
    if let Some(Value::Array(rows)) = manifest.get_mut("axiom_audits") {
        for (name, axioms) in audits {
            rows.push(object(vec![
                ("declaration", name.into()),
                ("axioms", strings(&axioms)),
                ("module", module.into()),
            ]));
        }
    }
    if let Some(Value::Array(done)) = manifest.get_mut("completed_modules") {
        done.push(module.into());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn comments_strings_and_literals_are_blanked() {
        let code = lean_code("def a := \"x\\\"y\" -- sorry\n/- axiom /- nested -/ -/ b '\\'' 'c' «x\ny» Foo.axiom | axiom").unwrap();
        let expected = format!(
            "def a :={}\n{}b{}\n Foo.{}|{}",
            " ".repeat(6),
            " ".repeat(17),
            " ".repeat(6),
            " ".repeat(6),
            " ".repeat(6)
        );
        assert_eq!(code, expected);
        assert!(lean_code("«open").is_err());
    }

    #[test]
    fn forbidden_constructs_follow_the_regex() {
        assert_eq!(
            forbidden("theorem t : True := by sorry"),
            Some("sorry".to_string())
        );
        assert_eq!(
            forbidden("by decide  +\nnative"),
            Some("decide  +\nnative".to_string())
        );
        assert_eq!(
            forbidden("set_option debug.skipKernelTC true"),
            Some("debug.skipKernelTC".to_string())
        );
        assert_eq!(
            forbidden("sorryish native_decided x.sorry"),
            Some("sorry".to_string())
        );
        assert_eq!(forbidden("sorryish native_decided"), None);
    }

    #[test]
    fn imports_follow_findall_in_multiline_mode() {
        assert_eq!(
            imports("import A.B\npublic import C\n  import D -- x\nx import E\n\n\nimport\n  F"),
            vec!["A.B", "C", "D", "F"]
        );
        assert_eq!(imports("public  import G\npublicimport H"), vec!["G"]);
    }

    #[test]
    fn audit_commands_are_counted_without_overlap() {
        assert_eq!(
            audit_count("#print axioms a\n#print  axioms\nb\n#printaxioms c\n#print axiomsd"),
            2
        );
    }

    #[test]
    fn paths_sort_by_components() {
        let mut paths = vec![PathBuf::from("Fang/A.lean"), PathBuf::from("Fang/A/B.lean")];
        paths.sort_by_key(|path| path_key(path));
        assert_eq!(
            paths,
            vec![PathBuf::from("Fang/A/B.lean"), PathBuf::from("Fang/A.lean")]
        );
    }
}
