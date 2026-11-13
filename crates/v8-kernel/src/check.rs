// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The exact-instance proof bundle for one sealed pair: the port of entry/check.py, run in the
//! entry's guarded worker, with generation and compilation in supervised children.
//!
//! Every machine-specific value comes from the installation record the entry pinned: HOME, the
//! toolchain, the Lean search environment that `lake env` gave in the built lean-v8 project, the
//! helper objects and the output root. The compiler reads the installed lean-v8 objects and the
//! helper objects through the recorded search path; the entry checks those trees before and
//! after. The generated modules go to a fresh native workspace under /var/tmp, are compiled
//! phase by phase under a 60-second/4-GiB guard per phase within a 600-second whole check, and
//! are archived with the sealed inputs into the run directory, after which the native workspace
//! is removed.

use std::collections::BTreeMap;
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;

use fang_json::{Number, Object, Value};
use fang_kernel_workspace::KernelWorkspace;
use fang_supervisor::{Environment, Failure, Fault, Limits, Stage, Status, Supervisor};

use crate::util::{resolve, sorted_line, utc_now};
use crate::{internal, launch};

const PHASE_SECONDS: f64 = 60.0;
const CHECKING_SECONDS: f64 = 600.0;
const SEARCH: [&str; 3] = ["LEAN_SRC_PATH", "LEAN_SYSROOT", "LD_LIBRARY_PATH"];

/// Why the proof step stopped, with the class revision 7 recorded as `failure_class`.
pub struct Stopped {
    pub class: &'static str,
    pub error: String,
}

impl Stopped {
    fn error(message: impl Into<String>) -> Stopped {
        Stopped {
            class: "Error",
            error: message.into(),
        }
    }
}

impl From<Fault> for Stopped {
    fn from(fault: Fault) -> Stopped {
        let class = match fault.status() {
            Status::Timeout => "Timeout",
            Status::MemoryOut => "MemoryOut",
            Status::ResourceOut => "ResourceOut",
            Status::Forced => "Forced",
            _ => "Error",
        };
        Stopped {
            class,
            error: fault.python_str(),
        }
    }
}

impl From<Failure> for Stopped {
    fn from(failure: Failure) -> Stopped {
        Stopped::from(Fault::Failure(failure))
    }
}

/// The inputs of one proof step.
pub struct Inputs<'a> {
    pub out: &'a Path,
    pub installation: &'a Value,
    pub installation_path: &'a Path,
    pub installation_sha256: &'a str,
    pub sealed: &'a [(&'static str, PathBuf, String)],
    /// The pinned copy of this executable, which runs the compiler launch.
    pub launcher: &'a Path,
    pub started: Instant,
}

fn float(value: f64) -> Value {
    Value::Number(Number::Float(value))
}

fn field<'a>(value: &'a Value, path: &[&str]) -> Result<&'a Value, Stopped> {
    let mut current = value;
    for key in path {
        current = current.get(key).ok_or_else(|| {
            Stopped::error(format!("Installation record without {}", path.join(".")))
        })?;
    }
    Ok(current)
}

fn text<'a>(value: &'a Value, path: &[&str]) -> Result<&'a str, Stopped> {
    field(value, path)?.as_str().ok_or_else(|| {
        Stopped::error(format!(
            "Installation record field {} is not text",
            path.join(".")
        ))
    })
}

/// Read a file through the supervisor's checks, at most `cap` bytes.
fn read(supervisor: &Supervisor, path: &Path, cap: u64) -> Result<Vec<u8>, Stopped> {
    Ok(fang_supervisor::read_regular(path, cap, &mut || {
        supervisor.check("adapter", 0.15)
    })?)
}

fn phase_supervisor(
    parent: &Supervisor,
    remaining: f64,
    native: &Path,
) -> Result<Supervisor, Failure> {
    let mut phase = Supervisor::new(
        Limits {
            wall_seconds: PHASE_SECONDS.min(remaining),
            memory_mib: 4096,
            log_bytes: 8 << 20,
            artifact_bytes: 1 << 30,
            ..Limits::default()
        },
        None,
    )?;
    phase.set_deadline(phase.deadline().min(parent.deadline()));
    phase.set_cancel_token(parent.cancel_token());
    phase.additional_artifact_roots.push(native.to_path_buf());
    Ok(phase)
}

/// `^#print axioms ([A-Za-z0-9_.]+)\r?$` over the module text: the theorems it audits.
pub fn required_audits(text: &str) -> Vec<String> {
    let mut names = Vec::new();
    for line in text.split('\n') {
        let line = line.strip_suffix('\r').unwrap_or(line);
        if let Some(name) = line.strip_prefix("#print axioms ")
            && !name.is_empty()
            && name
                .bytes()
                .all(|byte| byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'.')
        {
            names.push(name.to_owned());
        }
    }
    names
}

/// The proof record and why it stopped, if it did. The record is the proof manifest.
pub struct Proof {
    pub record: Object,
    pub stopped: Option<Stopped>,
}

struct State {
    report: Object,
    pins: BTreeMap<String, String>,
    captured: BTreeMap<String, String>,
}

/// Only module names, digests and a complete schedule cross the generator boundary.
struct Prepared {
    recipe: String,
    modules: Vec<(String, String)>,
    phases: Vec<Vec<String>>,
}

impl Prepared {
    fn parse(value: &Value) -> Result<Self, Stopped> {
        let invalid = || Stopped::error("Invalid generated module schedule");
        if value.get("status").and_then(Value::as_str) != Some("generated") {
            return Err(invalid());
        }
        let recipe = value
            .get("recipe")
            .and_then(Value::as_str)
            .ok_or_else(invalid)?
            .to_owned();
        let mut modules = Vec::new();
        let mut names = std::collections::BTreeSet::new();
        for item in value
            .get("modules")
            .and_then(Value::as_array)
            .ok_or_else(invalid)?
        {
            let name = item
                .get("name")
                .and_then(Value::as_str)
                .ok_or_else(invalid)?;
            let digest = item
                .get("sha256")
                .and_then(Value::as_str)
                .ok_or_else(invalid)?;
            if !internal::module_name(name)
                || !names.insert(name.to_owned())
                || digest.len() != 64
                || !digest.bytes().all(|c| c.is_ascii_hexdigit())
            {
                return Err(invalid());
            }
            modules.push((name.to_owned(), digest.to_owned()));
        }
        let mut scheduled = std::collections::BTreeSet::new();
        let mut phases = Vec::new();
        for phase in value
            .get("phases")
            .and_then(Value::as_array)
            .ok_or_else(invalid)?
        {
            let mut phase_names = Vec::new();
            for item in phase.as_array().ok_or_else(invalid)? {
                let name = item.as_str().ok_or_else(invalid)?;
                if !names.contains(name) || !scheduled.insert(name.to_owned()) {
                    return Err(invalid());
                }
                phase_names.push(name.to_owned());
            }
            if phase_names.is_empty() {
                return Err(invalid());
            }
            phases.push(phase_names);
        }
        if names.is_empty() || scheduled != names {
            return Err(invalid());
        }
        Ok(Self {
            recipe,
            modules,
            phases,
        })
    }
}

/// Run the proof step into `inputs.out` with the entry's supervisor; write its manifest.
pub fn run(supervisor: &mut Supervisor, inputs: &Inputs<'_>) -> Proof {
    let mut state = State {
        report: Object::new(),
        pins: BTreeMap::new(),
        captured: BTreeMap::new(),
    };
    state.report.set("status", "starting");
    state.report.set("started_utc", utc_now());
    let mut limits = Object::new();
    limits.set("phase_seconds", 60u64);
    limits.set("sampled_tree_rss_mib", 4096u64);
    limits.set("checking_seconds", 600u64);
    state.report.set("limits", Value::Object(limits));
    state.report.set("stages", Value::Array(Vec::new()));
    state
        .report
        .set("axiom_audits", Value::Object(Object::new()));
    state
        .report
        .set("installation_sha256", inputs.installation_sha256);
    state.report.set(
        "scope",
        "Exact sealed version-8 instance: actual decoding, transport, preprocessing, conversion and v8 acceptance.",
    );
    let mut storage = Object::new();
    let public = inputs.out.join("run");
    let outcome = fs::create_dir(inputs.out)
        .map_err(|error| Stopped::error(format!("{}: {error}", inputs.out.display())))
        .and_then(|()| crate::entry::case_sensitive(inputs.out, false).map_err(Stopped::error))
        .and_then(|()| {
            fs::create_dir(&public)
                .map_err(|error| Stopped::error(format!("{}: {error}", public.display())))
        })
        .and_then(|()| {
            KernelWorkspace::create(supervisor, &public, &mut storage).map_err(Stopped::from)
        });
    let stopped = match outcome {
        Err(stopped) => Some(stopped),
        Ok(workspace) => {
            state.report.set(
                "native_workspace",
                workspace.native().to_string_lossy().as_ref(),
            );
            // Recorded now, so that a run ended by SIGTERM still names its native workspace.
            let mut early = state.report.clone();
            early.set("kernel_storage", Value::Object(storage.clone()));
            if let Ok(data) = crate::util::manifest_bytes(&Value::Object(early)) {
                let _ = fs::write(inputs.out.join("manifest.json"), data);
            }
            let result = check(supervisor, inputs, &workspace, &mut state);
            let mut expected: BTreeMap<String, String> = BTreeMap::new();
            if let Some(Value::Object(sources)) = state.report.get("source_sha256") {
                for (name, digest) in sources.iter() {
                    expected.insert(
                        format!("source/{name}.lean"),
                        digest.as_str().unwrap_or_default().to_owned(),
                    );
                }
            }
            for (relative, digest) in &state.captured {
                expected.insert(relative.clone(), digest.clone());
            }
            let archived = workspace
                .archive(supervisor, &expected, &mut storage)
                .and_then(|()| workspace.cleanup(supervisor, &mut storage));
            match (result, archived) {
                (Ok(()), Ok(())) => None,
                (Err(stopped), Ok(())) => {
                    workspace.retain_failure(&Fault::Value(stopped.error.clone()), &mut storage);
                    Some(stopped)
                }
                (Ok(()), Err(fault)) => {
                    workspace.retain_failure(&fault, &mut storage);
                    Some(Stopped::from(fault))
                }
                (Err(stopped), Err(fault)) => {
                    workspace.retain_failure(&fault, &mut storage);
                    Some(stopped)
                }
            }
        }
    };
    let mut report = state.report;
    let archived = matches!(storage.get("archive_completed"), Some(Value::Bool(true)));
    report.set("archive_hashes_verified", archived);
    report.set("kernel_storage", Value::Object(storage));
    report.set(
        "captured_inputs_sha256",
        Value::Object(
            state
                .captured
                .iter()
                .map(|(key, value)| (key.clone(), Value::from(value.as_str())))
                .collect(),
        ),
    );
    report.set("finished_utc", utc_now());
    if let Some(stopped) = &stopped {
        report.set("status", "failed");
        report.set("error", stopped.error.as_str());
        report.set("failure_class", stopped.class);
    }
    if let Ok(data) = crate::util::manifest_bytes(&Value::Object(report.clone())) {
        let _ = fs::write(inputs.out.join("manifest.json"), data);
    }
    Proof {
        record: report,
        stopped,
    }
}

#[allow(clippy::too_many_lines)]
fn check(
    supervisor: &mut Supervisor,
    inputs: &Inputs<'_>,
    workspace: &KernelWorkspace,
    state: &mut State,
) -> Result<(), Stopped> {
    let native = workspace.native().to_path_buf();
    let source = native.join("source");
    let stages = native.join("stages");
    for directory in [&source, &stages, &native.join("sealed")] {
        fs::create_dir(directory)
            .map_err(|error| Stopped::error(format!("{}: {error}", directory.display())))?;
    }
    let within = |supervisor: &Supervisor| -> Result<(), Stopped> {
        supervisor.check("check", 0.15)?;
        if inputs.started.elapsed().as_secs_f64() >= CHECKING_SECONDS {
            return Err(Stopped {
                class: "Timeout",
                error: "Whole checking deadline exceeded".to_owned(),
            });
        }
        Ok(())
    };
    let installation = inputs.installation;
    let toolchain = PathBuf::from(text(installation, &["toolchain", "directory"])?);
    let tools = toolchain.join("bin");
    let project = PathBuf::from(text(installation, &["project", "directory"])?);
    let helpers = PathBuf::from(text(installation, &["helpers", "directory"])?);
    // The installation record, copied into the workspace and pinned.
    let record = read(supervisor, inputs.installation_path, 4 << 20)?;
    if fang_hash::sha256_hex(&record) != inputs.installation_sha256 {
        return Err(Stopped::error("Installation record differs from its pin"));
    }
    fs::write(native.join("installation.json"), &record)
        .map_err(|error| Stopped::error(error.to_string()))?;
    state.captured.insert(
        "installation.json".to_owned(),
        inputs.installation_sha256.to_owned(),
    );
    state.pins.insert(
        inputs.installation_path.to_string_lossy().into_owned(),
        inputs.installation_sha256.to_owned(),
    );
    // The helper objects are read in place through the search path; each is pinned and checked again at the end.
    let objects = field(installation, &["helpers", "objects_sha256"])?
        .as_object()
        .ok_or_else(|| Stopped::error("Helper objects are not recorded"))?;
    let mut owners = Object::new();
    for (relative, pin) in objects.iter() {
        let path = helpers.join(relative);
        let data = read(supervisor, &path, 256 << 20)?;
        if Some(fang_hash::sha256_hex(&data).as_str()) != pin.as_str() {
            return Err(Stopped::error(format!(
                "Installed helper object differs: {relative}"
            )));
        }
        state.pins.insert(
            path.to_string_lossy().into_owned(),
            pin.as_str().unwrap_or_default().to_owned(),
        );
        owners.set(relative, "helpers");
        within(supervisor)?;
    }
    // The sealed triple, captured into the workspace and compared with the outer pins.
    let mut sealed = Object::new();
    for (name, path, digest) in inputs.sealed {
        let (file, cap) = match *name {
            "input" => ("input.p", 4096),
            "certificate" => ("proof.fang", 65536),
            _ => ("witness.json", 16 << 20),
        };
        let data = read(supervisor, path, cap)?;
        if fang_hash::sha256_hex(&data) != *digest {
            return Err(Stopped::error(
                "Input capture differs from outer sealed bytes",
            ));
        }
        fs::write(native.join("sealed").join(file), &data)
            .map_err(|error| Stopped::error(error.to_string()))?;
        state
            .captured
            .insert(format!("sealed/{file}"), digest.clone());
        state
            .pins
            .insert(path.to_string_lossy().into_owned(), digest.clone());
        sealed.set(*name, digest.as_str());
        within(supervisor)?;
    }
    let command = [
        inputs.launcher.as_os_str().to_owned(),
        OsString::from(internal::GENERATE),
        native.join("sealed/input.p").into_os_string(),
        native.join("sealed/proof.fang").into_os_string(),
        native.join("sealed/witness.json").into_os_string(),
        source.as_os_str().to_owned(),
    ];
    let generated = internal::supervised(
        supervisor,
        &command,
        "generate",
        &stages.join("generate"),
        &native,
    );
    if let Some(record) = supervisor.records.last() {
        state.report.set("generation_stage", record.to_json());
    }
    let generated = generated?;
    if let Some(recipe) = generated.get("selected_generator").and_then(Value::as_str) {
        state.report.set("selected_generator", recipe);
    }
    if generated.get("status").and_then(Value::as_str) == Some("refused") {
        let class = match generated.get("class").and_then(Value::as_str) {
            Some("Rejected") => "Rejected",
            Some("Error") => "Error",
            _ => return Err(Stopped::error("Invalid generator refusal class")),
        };
        let error = generated
            .get("message")
            .and_then(Value::as_str)
            .ok_or_else(|| Stopped::error("Missing generator refusal message"))?
            .to_owned();
        return Err(Stopped { class, error });
    }
    let prepared = Prepared::parse(&generated)?;
    state
        .report
        .set("selected_generator", prepared.recipe.as_str());
    // The library is read through the recorded search path, ahead of the run's source directory,
    // so a generated name must not exist there or among the helpers either.
    let lean_path = text(installation, &["lean_environment", "LEAN_PATH"])?.to_owned();
    let mut search: Vec<PathBuf> = lean_path
        .split(':')
        .filter(|part| !part.is_empty())
        .map(PathBuf::from)
        .collect();
    search.push(helpers.clone());
    for (name, digest) in &prepared.modules {
        let relative = name.replace('.', "/");
        let taken = search.iter().any(|directory| {
            [".olean", ".lean"]
                .iter()
                .any(|suffix| directory.join(format!("{relative}{suffix}")).exists())
        });
        if taken {
            return Err(Stopped::error(format!(
                "Generated module collision: {name}"
            )));
        }
        let data = read(supervisor, &source.join(format!("{name}.lean")), 1 << 30)?;
        if fang_hash::sha256_hex(&data) != *digest {
            return Err(Stopped::error(format!("Generated source differs: {name}")));
        }
    }
    state.report.set("sealed_sha256", Value::Object(sealed));
    for path in [
        tools.join("lean"),
        tools.join("lake"),
        inputs.launcher.to_path_buf(),
    ] {
        let data = read(supervisor, &path, 1 << 30)?;
        state.pins.insert(
            path.to_string_lossy().into_owned(),
            fang_hash::sha256_hex(&data),
        );
    }
    let module_order: Vec<String> = prepared
        .modules
        .iter()
        .map(|(name, _)| name.clone())
        .collect();
    let mut source_sha256 = Object::new();
    for (name, digest) in &prepared.modules {
        source_sha256.set(name.as_str(), digest.as_str());
    }
    state.report.set("status", "running");
    state.report.set(
        "module_order",
        Value::Array(
            module_order
                .iter()
                .map(|name| Value::from(name.as_str()))
                .collect(),
        ),
    );
    state.report.set(
        "phases",
        Value::Array(
            prepared
                .phases
                .iter()
                .map(|phase| {
                    Value::Array(
                        phase
                            .iter()
                            .map(|name| Value::from(name.as_str()))
                            .collect(),
                    )
                })
                .collect(),
        ),
    );
    state
        .report
        .set("source_sha256", Value::Object(source_sha256));
    state
        .report
        .set("imported_dependency_owners", Value::Object(owners));
    state.report.set(
        "input_helper_tool_sha256",
        Value::Object(
            state
                .pins
                .iter()
                .map(|(key, value)| (key.clone(), Value::from(value.as_str())))
                .collect(),
        ),
    );
    // The compiler environment is the `lake env` environment recorded at install in the built
    // lean-v8 project, plus the helper objects and this run's source root. Every search path stays
    // inside the installed project or toolchain tree; the compiler is the installed toolchain binary.
    let effective = field(installation, &["lean_environment"])?
        .as_object()
        .ok_or_else(|| Stopped::error("No recorded environment"))?;
    let value = |key: &str| {
        effective
            .get(key)
            .and_then(Value::as_str)
            .unwrap_or("")
            .to_owned()
    };
    if !value("LD_PRELOAD").is_empty() || !value("LD_AUDIT").is_empty() {
        return Err(Stopped::error("Unexpected recorded compiler environment"));
    }
    let project_root = resolve(&project);
    let toolchain_root = resolve(&toolchain);
    for key in [
        "LEAN_PATH",
        "LEAN_SRC_PATH",
        "LEAN_SYSROOT",
        "LD_LIBRARY_PATH",
    ] {
        for item in value(key).split(':').filter(|item| !item.is_empty()) {
            let resolved = resolve(Path::new(item));
            if !(resolved.starts_with(&project_root) || resolved.starts_with(&toolchain_root)) {
                return Err(Stopped::error(format!(
                    "Compiler search path outside the installed trees: {item}"
                )));
            }
        }
    }
    if resolve(Path::new(&value("LEAN_SYSROOT"))) != toolchain_root {
        return Err(Stopped::error(
            "Compiler sysroot differs from the installed toolchain",
        ));
    }
    let mut added = Object::new();
    for key in SEARCH {
        added.set(key, value(key));
    }
    let added_text = sorted_line(&Value::Object(added.clone())).map_err(Stopped::error)?;
    let mut environment = Environment::new();
    environment.set("HOME", text(installation, &["home"])?);
    environment.set("PATH", format!("{}:/usr/bin:/bin", tools.display()));
    environment.set(
        "LEAN_PATH",
        format!(
            "{}:{}:{}",
            value("LEAN_PATH").trim_end_matches(':'),
            helpers.display(),
            source.display()
        ),
    );
    environment.set("LEAN_NUM_THREADS", "1");
    environment.set("LANG", "C.UTF-8");
    environment.set("LC_ALL", "C.UTF-8");
    let mut compiler = Object::new();
    compiler.set("compiler", tools.join("lean").to_string_lossy().as_ref());
    compiler.set("working_directory", project.to_string_lossy().as_ref());
    compiler.set(
        "supervised",
        Value::Object(
            environment
                .iter()
                .map(|(key, value)| (key.to_owned(), Value::from(value)))
                .collect(),
        ),
    );
    compiler.set("added_at_exec", Value::Object(added));
    compiler.set("installation_sha256", inputs.installation_sha256);
    let mut run_specific = Object::new();
    run_specific.set(
        "LEAN_PATH_suffix",
        format!("{}:{}", helpers.display(), source.display()),
    );
    compiler.set("run_specific", Value::Object(run_specific));
    compiler.set("launcher", inputs.launcher.to_string_lossy().as_ref());
    compiler.set(
        "scope",
        "Replaces the resident `lake env` wrapper; recorded search values are copied unchanged.",
    );
    state
        .report
        .set("compiler_environment", Value::Object(compiler));
    let digests: BTreeMap<_, _> = prepared.modules.iter().cloned().collect();
    let mut audits = 0usize;
    let mut stage_records: Vec<Value> = Vec::new();
    for phase in &prepared.phases {
        within(supervisor)?;
        let remaining = CHECKING_SECONDS - inputs.started.elapsed().as_secs_f64();
        let mut phase_supervisor = phase_supervisor(supervisor, remaining, &native)?;
        for name in phase {
            let mut command: Vec<OsString> =
                launch::command(inputs.launcher, &project, &added_text, &tools.join("lean"));
            let object = source.join(format!("{name}.olean"));
            let input_path = source.join(format!("{name}.lean"));
            let data = read(supervisor, &input_path, 1 << 30)?;
            if digests.get(name) != Some(&fang_hash::sha256_hex(&data)) {
                return Err(Stopped::error(format!("Generated source differs: {name}")));
            }
            let module_text = std::str::from_utf8(&data)
                .map_err(|_| Stopped::error("Generated source is not UTF-8"))?;
            let required = required_audits(module_text);
            audits += required.len();
            drop(data);
            for part in [
                OsString::from("-j1"),
                "-M4096".into(),
                "--root".into(),
                source.clone().into(),
                "-o".into(),
                object.into(),
                input_path.into(),
            ] {
                command.push(part);
            }
            let directory = stages.join(name);
            let stage = Stage {
                name,
                command: &command,
                directory: &directory,
                run_root: &native,
                environment: Some(&environment),
                stdin: None,
                stdout_limit: None,
                cwd: None,
            };
            let result = phase_supervisor.run(&stage);
            if let Some(record) = phase_supervisor.records.last() {
                stage_records.push(record.to_json());
                state
                    .report
                    .set("stages", Value::Array(stage_records.clone()));
            }
            let output = result?;
            if output.record.classification != "completed"
                || output.record.exit_code != Some(0)
                || !output.stderr.is_empty()
            {
                return Err(Stopped::error(format!("Lean stage failed: {name}")));
            }
            let mut unique: Vec<&str> = required.iter().map(String::as_str).collect();
            unique.sort_unstable();
            unique.dedup();
            let printed = String::from_utf8_lossy(&output.stdout).into_owned();
            let reports = fang_axiom_audit::reports(&printed);
            let leftover = fang_axiom_audit::strip_reports(&printed);
            if reports.len() != unique.len()
                || !fang_axiom_audit::python_strip(&leftover).is_empty()
            {
                return Err(Stopped::error(format!(
                    "Unexpected diagnostics/audits: {name}"
                )));
            }
            let audits = if unique.is_empty() {
                Object::new()
            } else {
                let found = fang_axiom_audit::audit_axioms(&printed, &unique)
                    .map_err(|error| Stopped::error(error.0))?;
                found
                    .into_iter()
                    .map(|(theorem, axioms)| {
                        (
                            theorem,
                            Value::Array(axioms.into_iter().map(Value::from).collect()),
                        )
                    })
                    .collect()
            };
            if let Some(Value::Object(all)) = state.report.get_mut("axiom_audits") {
                all.set(name.as_str(), Value::Object(audits));
            }
        }
    }
    for (path, pin) in &state.pins {
        let data = read(supervisor, Path::new(path), 1 << 30)?;
        if fang_hash::sha256_hex(&data) != *pin {
            return Err(Stopped::error("Input/helper/tool changed"));
        }
    }
    for (relative, pin) in &state.captured {
        let data = read(supervisor, &native.join(relative), 1 << 30)?;
        if fang_hash::sha256_hex(&data) != *pin {
            return Err(Stopped::error("Captured input changed"));
        }
    }
    within(supervisor)?;
    state.report.set("status", "kernel-bundle-passed");
    state.report.set("modules", prepared.modules.len() as u64);
    state.report.set("audits", audits as u64);
    state.report.set(
        "checking_seconds",
        float(inputs.started.elapsed().as_secs_f64()),
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{Prepared, phase_supervisor};
    use fang_json::{Object, Value};

    #[test]
    fn phase_cannot_outlive_the_outer_entry_deadline() {
        use fang_supervisor::{Limits, Status, Supervisor};
        use std::time::{Duration, Instant};
        let root =
            fang_supervisor::make_temp_dir(&std::env::temp_dir(), "fang-phase-deadline-").unwrap();
        let parent = Supervisor::new(
            Limits {
                wall_seconds: 0.5,
                ..Limits::default()
            },
            None,
        )
        .unwrap();
        let mut phase = phase_supervisor(&parent, 600.0, &root).unwrap();
        assert_eq!(phase.deadline(), parent.deadline());
        let started = Instant::now();
        let argv = vec!["/bin/sleep".into(), "30".into()];
        let error =
            crate::internal::supervised(&mut phase, &argv, "phase", &root.join("phase"), &root)
                .unwrap_err();
        assert_eq!(error.status(), Status::Timeout);
        assert!(started.elapsed() < Duration::from_secs(5));
        assert!(
            phase
                .records
                .last()
                .unwrap()
                .terminated_owned_pids
                .as_ref()
                .is_some_and(|pids| !pids.is_empty())
        );
        std::fs::remove_dir_all(root).unwrap();
    }

    fn metadata(names: &[&str], phases: &[&[&str]]) -> Value {
        let mut value = Object::new();
        value.set("status", "generated");
        value.set("recipe", "generate-cnf.py");
        value.set(
            "modules",
            Value::Array(
                names
                    .iter()
                    .map(|name| {
                        let mut item = Object::new();
                        item.set("name", *name);
                        item.set("sha256", "0".repeat(64));
                        Value::Object(item)
                    })
                    .collect(),
            ),
        );
        value.set(
            "phases",
            Value::Array(
                phases
                    .iter()
                    .map(|phase| {
                        Value::Array(phase.iter().map(|name| Value::from(*name)).collect())
                    })
                    .collect(),
            ),
        );
        Value::Object(value)
    }

    #[test]
    fn generator_schedule_requires_each_named_module_exactly_once() {
        assert!(Prepared::parse(&metadata(&["A", "B"], &[&["A"], &["B"]])).is_ok());
        for (names, phases) in [
            (vec!["A", "A"], vec![vec!["A"]]),
            (vec!["A", "B"], vec![vec!["A"]]),
            (vec!["A"], vec![vec!["A", "A"]]),
            (vec!["A"], vec![vec!["B"]]),
            (vec!["../A"], vec![vec!["../A"]]),
            (vec!["A"], vec![vec![], vec!["A"]]),
            (vec![], vec![]),
        ] {
            let phases: Vec<_> = phases.iter().map(Vec::as_slice).collect();
            assert!(Prepared::parse(&metadata(&names, &phases)).is_err());
        }
    }
}
