// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Provide the kernel helper modules on a built lean-v8 project: compile those it lacks and
//! rerun their audits. The port of build-helpers.py.
//!
//! Inputs: the repository snapshot, a lean-v8 Lake project built by the lean-v8 build, and the
//! pinned Lean toolchain. The helper sources come from tools/v8_kernel/lean/ (or --sources);
//! every one must match its pin in pins/helper-sources.json. The project's source of every
//! module in the kernel's lean-v8 import closure must match pins/lean-v8-closure.json, or the
//! build stops. The Lean environment is taken once from `lake env` in the project, as a
//! supervised stage; every search path must lie inside the project or the toolchain. Of the
//! helper modules, only those pinned as provided by lean-v8 may already be on that search path:
//! they are not compiled again, their lean-v8 sources must be byte-identical to the pinned helper
//! sources, and the lean-v8 objects are used. Every other module is compiled with the direct
//! compiler launch under a 60-second/4-GiB guard, in the pinned order, and its axiom report must
//! equal its pin. The output directory receives the sources, the objects, the logs and a
//! manifest with every object hash. On SIGTERM the command exits with status 143 and the
//! manifest records the build as failed with the reason Forced.

use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use fang_json::{Number, Object, ParseLimits, Value};
use fang_supervisor::guard::Worker;
use fang_supervisor::{Environment, Limits, Stage, Supervisor};

use crate::install::{CLOSURE, HELPER_PINS, HELPER_SCHEMA, closure_differences, module_source};
use crate::launch;
use crate::util::{file_sha256, manifest_bytes, resolve, sorted_line, utc_now};

const SEARCH: [&str; 4] = [
    "LEAN_PATH",
    "LEAN_SRC_PATH",
    "LEAN_SYSROOT",
    "LD_LIBRARY_PATH",
];
const ADDED: [&str; 3] = ["LEAN_SRC_PATH", "LEAN_SYSROOT", "LD_LIBRARY_PATH"];

type Fallible<T> = Result<T, String>;

struct Arguments {
    repository: PathBuf,
    project: PathBuf,
    toolchain: PathBuf,
    out: PathBuf,
    sources: Option<PathBuf>,
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
    let repository = take("--repository");
    let project = take("--project");
    let toolchain = take("--lean-toolchain");
    let out = take("--out");
    let sources = take("--sources");
    if let Some((flag, _)) = values.first() {
        return Err(format!("unrecognized arguments: {flag}"));
    }
    match (repository, project, toolchain, out) {
        (Some(repository), Some(project), Some(toolchain), Some(out)) => {
            Ok(Arguments { repository, project, toolchain, out, sources })
        }
        _ => Err("the following arguments are required: --repository, --project, --lean-toolchain, --out".to_owned()),
    }
}

fn json(path: &Path) -> Fallible<Value> {
    let data = fs::read(path).map_err(|error| format!("{}: {error}", path.display()))?;
    fang_json::parse(
        &data,
        &ParseLimits {
            max_bytes: 64 << 20,
            max_depth: 64,
        },
    )
    .map_err(|error| format!("{}: {}", path.display(), error.python_message(&data)))
}

fn strings(value: Option<&Value>) -> Vec<String> {
    value
        .and_then(Value::as_array)
        .map(|items| {
            items
                .iter()
                .filter_map(Value::as_str)
                .map(str::to_owned)
                .collect()
        })
        .unwrap_or_default()
}

fn float(value: f64) -> Value {
    Value::Number(Number::Float(value))
}

/// The `.olean` module names below one search directory, without following directory links.
fn olean_modules(base: &Path, directory: &Path, found: &mut Vec<String>) {
    let Ok(entries) = fs::read_dir(directory) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let Ok(kind) = entry.file_type() else {
            continue;
        };
        if kind.is_dir() {
            olean_modules(base, &path, found);
        }
        let name = entry.file_name();
        let Some(name) = name.to_str() else { continue };
        if let Some(stem) = name.strip_suffix(".olean")
            && let Ok(relative) = path.strip_prefix(base)
        {
            let parent = relative
                .parent()
                .map(|parent| parent.to_string_lossy().replace('/', "."))
                .unwrap_or_default();
            found.push(if parent.is_empty() {
                stem.to_owned()
            } else {
                format!("{parent}.{stem}")
            });
        }
    }
}

/// Every regular file below `directory`, sorted, as relative paths.
fn files_below(base: &Path, directory: &Path, found: &mut Vec<(String, PathBuf)>) -> Fallible<()> {
    let entries =
        fs::read_dir(directory).map_err(|error| format!("{}: {error}", directory.display()))?;
    for entry in entries.flatten() {
        let path = entry.path();
        let kind = entry.file_type().map_err(|error| error.to_string())?;
        if kind.is_dir() {
            files_below(base, &path, found)?;
        } else if kind.is_file() {
            let relative = path.strip_prefix(base).map_err(|error| error.to_string())?;
            found.push((relative.to_string_lossy().into_owned(), path.clone()));
        }
    }
    Ok(())
}

/// The search variables `lake env` sets in the built project, from a supervised stage; nothing
/// is built.
fn lake_environment(
    executable: &Path,
    toolchain: &Path,
    project: &Path,
    out: &Path,
    report: &Arc<Mutex<Object>>,
    worker: &Worker,
) -> Fallible<Object> {
    let mut supervisor = Supervisor::new(
        Limits {
            wall_seconds: 300.0,
            memory_mib: 4096,
            log_bytes: 8 << 20,
            artifact_bytes: 1 << 30,
            ..Limits::default()
        },
        None,
    )
    .map_err(|failure| failure.reason)?;
    supervisor.set_cancel_token(worker.cancel_token());
    let mut environment = Environment::new();
    environment.set("HOME", out.join("home").to_string_lossy().as_ref());
    environment.set(
        "PATH",
        format!("{}:/usr/bin:/bin", toolchain.join("bin").display()),
    );
    environment.set("LANG", "C.UTF-8");
    environment.set("LC_ALL", "C.UTF-8");
    let mut command = launch::command(
        executable,
        project,
        "{\"GIT_ALLOW_PROTOCOL\": \"file\"}",
        &toolchain.join("bin/lake"),
    );
    command.extend([
        "-d".into(),
        project.as_os_str().to_owned(),
        "env".into(),
        "/usr/bin/env".into(),
    ]);
    let directory = out.join("stages/lake-env");
    let stage = Stage {
        name: "lake-env",
        command: &command,
        directory: &directory,
        run_root: out,
        environment: Some(&environment),
        stdin: None,
        stdout_limit: None,
        cwd: None,
    };
    let result = supervisor.run(&stage);
    if let Some(record) = supervisor.records.last()
        && let Ok(mut report) = report.lock()
    {
        report.set("lake_env_stage", record.to_json());
    }
    let output = result.map_err(|fault| format!("lake env failed: {}", fault.reason()))?;
    if output.record.exit_code != Some(0) {
        let text = String::from_utf8_lossy(&output.stderr).into_owned();
        let tail: String = text
            .chars()
            .rev()
            .take(800)
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect();
        return Err(format!("lake env failed: {tail}"));
    }
    let text = String::from_utf8(output.stdout)
        .map_err(|_| "lake env printed text that is not UTF-8".to_owned())?;
    let mut values: Vec<(String, String)> = Vec::new();
    for line in text.lines() {
        if let Some((key, value)) = line.split_once('=') {
            match values.iter_mut().find(|(existing, _)| existing == key) {
                Some(entry) => entry.1 = value.to_owned(),
                None => values.push((key.to_owned(), value.to_owned())),
            }
        }
    }
    let mut result = Object::new();
    for key in SEARCH {
        let value = values
            .iter()
            .find(|(existing, _)| existing == key)
            .map(|(_, value)| value.as_str())
            .unwrap_or("");
        result.set(key, value);
    }
    Ok(result)
}

fn save(out: &Path, report: &Arc<Mutex<Object>>) {
    if let Ok(report) = report.lock()
        && let Ok(data) = manifest_bytes(&Value::Object(report.clone()))
    {
        let _ = fs::write(out.join("manifest.json"), data);
    }
}

fn set(report: &Arc<Mutex<Object>>, key: &str, value: impl Into<Value>) {
    if let Ok(mut report) = report.lock() {
        report.set(key, value);
    }
}

#[allow(clippy::too_many_lines)]
fn build(
    arguments: &Arguments,
    out: &Path,
    report: &Arc<Mutex<Object>>,
    worker: &Worker,
) -> Fallible<()> {
    let repository = resolve(&arguments.repository);
    let project = resolve(&arguments.project);
    let toolchain = resolve(&arguments.toolchain);
    let sources = arguments
        .sources
        .clone()
        .unwrap_or_else(|| repository.join("tools/v8_kernel/lean"));
    let source = out.join("source");
    let pins = json(&repository.join(HELPER_PINS))?;
    let closure = json(&repository.join(CLOSURE))?;
    let differing = closure_differences(&project, &closure)?;
    if !differing.is_empty() {
        let shown: Vec<&str> = differing.iter().take(10).map(String::as_str).collect();
        return Err(format!(
            "lean-v8 differs from the kernel import closure: {}",
            shown.join(", ")
        ));
    }
    let checked = closure
        .get("sources_sha256")
        .and_then(Value::as_object)
        .map_or(0, Object::len);
    set(report, "closure_modules_checked", checked as u64);
    let order = strings(pins.get("module_order"));
    let mut provided_pins = strings(pins.get("provided_by_lean_v8"));
    let source_pins = pins
        .get("sources_sha256")
        .and_then(Value::as_object)
        .ok_or("Pins without sources")?;
    let audit_pins = pins
        .get("axiom_audits")
        .and_then(Value::as_object)
        .ok_or("Pins without audits")?;
    for name in &order {
        if provided_pins.contains(name) {
            continue;
        }
        let relative = format!("{}.lean", name.replace('.', "/"));
        let path = sources.join(&relative);
        let data = fs::read(&path).map_err(|error| format!("{}: {error}", path.display()))?;
        if source_pins.get(name).and_then(Value::as_str)
            != Some(fang_hash::sha256_hex(&data).as_str())
        {
            return Err(format!("Helper source differs from its pin: {name}"));
        }
        let target = source.join(&relative);
        if let Some(parent) = target.parent() {
            fs::create_dir_all(parent).map_err(|error| error.to_string())?;
        }
        fs::write(&target, &data).map_err(|error| error.to_string())?;
    }
    let executable = std::env::current_exe().map_err(|error| error.to_string())?;
    let environment = lake_environment(&executable, &toolchain, &project, out, report, worker)?;
    set(
        report,
        "lean_environment",
        Value::Object(environment.clone()),
    );
    let value = |key: &str| {
        environment
            .get(key)
            .and_then(Value::as_str)
            .unwrap_or("")
            .to_owned()
    };
    for key in SEARCH {
        for item in value(key).split(':').filter(|item| !item.is_empty()) {
            let resolved = resolve(Path::new(item));
            if !(resolved.starts_with(&project) || resolved.starts_with(&toolchain)) {
                return Err(format!(
                    "Search path outside the project and toolchain: {item}"
                ));
            }
        }
    }
    if resolve(Path::new(&value("LEAN_SYSROOT"))) != toolchain {
        return Err("Lean sysroot differs from the toolchain".to_owned());
    }
    let mut existing: Vec<String> = Vec::new();
    for item in value("LEAN_PATH")
        .split(':')
        .filter(|item| !item.is_empty())
    {
        let directory = Path::new(item);
        if directory.is_dir() {
            olean_modules(directory, directory, &mut existing);
        }
    }
    let mut provided: Vec<String> = order
        .iter()
        .filter(|name| existing.contains(name))
        .cloned()
        .collect();
    provided.sort();
    provided.dedup();
    provided_pins.sort();
    if provided != provided_pins {
        return Err(format!(
            "lean-v8 provides other helper modules than pinned: {}",
            provided.join(", ")
        ));
    }
    for name in &provided {
        let shipped = module_source(&project, name);
        let same = shipped.is_file()
            && file_sha256(&shipped).ok().as_deref()
                == source_pins.get(name).and_then(Value::as_str);
        if !same {
            return Err(format!(
                "Helper name on the search path with a different source: {name}"
            ));
        }
        if audit_pins
            .get(name)
            .and_then(Value::as_object)
            .is_some_and(|audits| !audits.is_empty())
        {
            return Err(format!(
                "A provided helper has recorded audits; compile it here instead: {name}"
            ));
        }
    }
    set(
        report,
        "provided_by_project",
        Value::Array(
            provided
                .iter()
                .map(|name| Value::from(name.as_str()))
                .collect(),
        ),
    );
    let mut added = Object::new();
    for key in ADDED {
        added.set(key, value(key));
    }
    let added_text = sorted_line(&Value::Object(added.clone()))?;
    let mut compile = Environment::new();
    compile.set("HOME", out.join("home").to_string_lossy().as_ref());
    compile.set(
        "PATH",
        format!("{}:/usr/bin:/bin", toolchain.join("bin").display()),
    );
    compile.set(
        "LEAN_PATH",
        format!(
            "{}:{}",
            value("LEAN_PATH").trim_end_matches(':'),
            source.display()
        ),
    );
    compile.set("LEAN_NUM_THREADS", "1");
    compile.set("LANG", "C.UTF-8");
    compile.set("LC_ALL", "C.UTF-8");
    let mut compile_record = Object::new();
    compile_record.set(
        "supervised",
        Value::Object(
            compile
                .iter()
                .map(|(key, value)| (key.to_owned(), Value::from(value)))
                .collect(),
        ),
    );
    compile_record.set("added_at_exec", Value::Object(added));
    compile_record.set("working_directory", project.to_string_lossy().as_ref());
    compile_record.set("launch", "this executable with --launch: enter the project, add the recorded variables, exec the compiler");
    set(report, "compile_environment", Value::Object(compile_record));
    let mut total = 0u64;
    let lean = toolchain.join("bin/lean");
    for name in order.iter().filter(|name| !provided.contains(name)) {
        let relative = name.replace('.', "/");
        let mut supervisor = Supervisor::new(
            Limits {
                wall_seconds: 60.0,
                memory_mib: 4096,
                log_bytes: 8 << 20,
                artifact_bytes: 1 << 30,
                ..Limits::default()
            },
            None,
        )
        .map_err(|failure| failure.reason)?;
        supervisor.set_cancel_token(worker.cancel_token());
        let mut command = launch::command(&executable, &project, &added_text, &lean);
        let object = source.join(format!("{relative}.olean"));
        let input = source.join(format!("{relative}.lean"));
        for part in [
            OsString::from("-j1"),
            "-M4096".into(),
            "--root".into(),
            source.clone().into(),
            "-o".into(),
            object.into(),
            input.into(),
        ] {
            command.push(part);
        }
        let directory = out.join("stages").join(name);
        let stage = Stage {
            name,
            command: &command,
            directory: &directory,
            run_root: out,
            environment: Some(&compile),
            stdin: None,
            stdout_limit: None,
            cwd: None,
        };
        let result = supervisor.run(&stage);
        let stage_record = supervisor.records.last().cloned().unwrap_or_default();
        let mut record = Object::new();
        record.set("exit_code", stage_record.exit_code);
        record.set("classification", stage_record.classification.as_str());
        record.set(
            "seconds",
            float((stage_record.elapsed_seconds * 100.0).round() / 100.0),
        );
        record.set("peak_kib", stage_record.peak_adapter_tree_rss_kib);
        let failed = |record: &mut Object, output: String| {
            record.set("output", output);
            if let Ok(mut report) = report.lock()
                && let Some(Value::Object(modules)) = report.get_mut("modules")
            {
                modules.set(name.as_str(), Value::Object(record.clone()));
            }
            format!("Helper compile failed or printed diagnostics: {name}")
        };
        let output = match result {
            Ok(output) => output,
            Err(fault) => return Err(failed(&mut record, fault.reason())),
        };
        let text = String::from_utf8_lossy(&output.stdout).into_owned();
        let leftover = fang_axiom_audit::strip_reports(&text);
        if stage_record.classification != "completed"
            || stage_record.exit_code != Some(0)
            || !output.stderr.is_empty()
            || !fang_axiom_audit::python_strip(&leftover).is_empty()
        {
            let combined = format!("{text}{}", String::from_utf8_lossy(&output.stderr));
            let tail: String = combined
                .chars()
                .rev()
                .take(2000)
                .collect::<Vec<_>>()
                .into_iter()
                .rev()
                .collect();
            return Err(failed(&mut record, tail));
        }
        let mut audits = Object::new();
        for item in fang_axiom_audit::reports(&text) {
            let mut used: Vec<String> = match &item.axioms {
                None => Vec::new(),
                Some(axioms) => axioms
                    .split(',')
                    .map(fang_axiom_audit::python_strip)
                    .filter(|axiom| !axiom.is_empty())
                    .map(str::to_owned)
                    .collect(),
            };
            used.sort();
            if !used
                .iter()
                .all(|axiom| fang_axiom_audit::ALLOWED_AXIOMS.contains(&axiom.as_str()))
            {
                return Err(format!("Unapproved axiom in {}", item.name));
            }
            audits.set(
                item.name.as_str(),
                Value::Array(used.into_iter().map(Value::from).collect()),
            );
        }
        let pinned = audit_pins
            .get(name)
            .and_then(Value::as_object)
            .cloned()
            .unwrap_or_default();
        if audits != pinned {
            return Err(format!("Axiom report differs from its pin: {name}"));
        }
        record.set("audits", audits.len() as u64);
        total += audits.len() as u64;
        if let Ok(mut report) = report.lock()
            && let Some(Value::Object(modules)) = report.get_mut("modules")
        {
            modules.set(name.as_str(), Value::Object(record));
        }
        save(out, report);
    }
    let mut files = Vec::new();
    files_below(&source, &source, &mut files)?;
    files.sort();
    let mut objects = Object::new();
    for (relative, path) in files {
        objects.set(relative.as_str(), file_sha256(&path)?);
    }
    let built = report
        .lock()
        .map(|report| {
            report
                .get("modules")
                .and_then(Value::as_object)
                .map_or(0, Object::len)
        })
        .unwrap_or(0);
    if let Ok(mut report) = report.lock() {
        report.set("objects_sha256", Value::Object(objects));
        report.set("status", "built-and-audited");
        report.set("audits", total);
        report.set("modules_built", built as u64);
        report.set("finished_utc", utc_now());
    }
    Ok(())
}

/// `fang-v8-kernel-helpers` in the guarded worker; the exit status.
pub fn main(raw: &[OsString], worker: &Worker) -> i32 {
    let arguments = match arguments(raw) {
        Ok(arguments) => arguments,
        Err(message) => {
            eprintln!("{message}");
            return 2;
        }
    };
    let out = resolve(&arguments.out);
    if let Some(parent) = out.parent() {
        let _ = fs::create_dir_all(parent);
    }
    if let Err(error) = fs::create_dir(&out) {
        eprintln!("{}: {error}", out.display());
        return 2;
    }
    for directory in ["source", "stages", "home"] {
        if let Err(error) = fs::create_dir(out.join(directory)) {
            eprintln!("{error}");
            return 2;
        }
    }
    let repository = resolve(&arguments.repository);
    let digest = |path: &Path| file_sha256(path).unwrap_or_default();
    let toolchain = resolve(&arguments.toolchain);
    let executable = std::env::current_exe()
        .map(|path| digest(&path))
        .unwrap_or_default();
    let mut report = Object::new();
    report.set("schema", HELPER_SCHEMA);
    // Descriptors above 2 without close-on-exec reach every child; the run record lists them.
    report.set(
        "inherited_descriptors",
        Value::Array(
            fang_supervisor::inherited_descriptors()
                .iter()
                .map(|item| item.to_json())
                .collect(),
        ),
    );
    report.set("status", "running");
    report.set("started_utc", utc_now());
    report.set("runner_sha256", executable);
    report.set("pins_sha256", digest(&repository.join(HELPER_PINS)));
    report.set("closure_sha256", digest(&repository.join(CLOSURE)));
    report.set(
        "project",
        resolve(&arguments.project).to_string_lossy().as_ref(),
    );
    report.set("toolchain", toolchain.to_string_lossy().as_ref());
    let mut binaries = Object::new();
    for binary in ["lean", "lake"] {
        binaries.set(binary, digest(&toolchain.join("bin").join(binary)));
    }
    report.set("toolchain_sha256", Value::Object(binaries));
    report.set("scope", "The kernel helper modules compiled against a built lean-v8 project; audits rerun and compared.");
    report.set("modules", Value::Object(Object::new()));
    let report = Arc::new(Mutex::new(report));
    let hook_report = Arc::clone(&report);
    let hook_out = out.clone();
    worker.on_parent_death(move || {
        if let Ok(mut report) = hook_report.lock() {
            report.set("status", "failed");
            report.set("error", "External cancellation");
            report.set("failure_type", "Forced");
            report.set("finished_utc", utc_now());
        }
        save(&hook_out, &hook_report);
    });
    let result = build(&arguments, &out, &report, worker);
    let finished = worker.finalize(|| {
        if let Err(message) = &result
            && let Ok(mut report) = report.lock()
        {
            report.set("status", "failed");
            report.set("error", message.as_str());
            report.set("failure_type", "ValueError");
            report.set("finished_utc", utc_now());
        }
        save(&out, &report);
    });
    if finished.is_none() {
        return 9;
    }
    let report = report
        .lock()
        .map(|report| report.clone())
        .unwrap_or_default();
    let mut printed = Object::new();
    for key in ["status", "modules_built", "audits", "error"] {
        printed.set(key, report.get(key).cloned().unwrap_or(Value::Null));
    }
    println!(
        "{}",
        fang_json::dumps(&Value::Object(printed), &fang_json::DumpOptions::default())
            .unwrap_or_default()
    );
    i32::from(report.get("status").and_then(Value::as_str) != Some("built-and-audited"))
}
