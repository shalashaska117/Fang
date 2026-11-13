// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The older ground-FOF profile (`--profile ground-fof`): a port of tools/fof_szs/main.py. Bounded ground-FOF
//! search, the pinned original-byte checker, an optional fresh kernel replay and an optional compiled TSTP
//! export, with the run record of schema "fang-ground-fof-run-v1".
//!
//! The run's statuses, reasons, stages, output text and record fields are main.py's. The differences are the
//! ones the launcher makes everywhere: the capability is schema v3 and pins the launcher in place of Python
//! and its sources, the captured input is a 0400 copy instead of a sealed memfd, and a signal to the command
//! is seen through the guard's worker, which writes the Forced record. The binaries a run executes are verified
//! by their chunked SHA-256 before their first execution and by identity after the run, as on the version-8
//! path, and the record lists them (`verified_before_run`) with the inherited descriptors
//! (`inherited_descriptors`); main.py rehashed every pin before and after.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::{Duration, Instant};

use fang_json::{Object, Value};
use fang_supervisor::guard::Worker;
use fang_supervisor::{Fault, Limits, Snapshot, Status, Supervisor};

use crate::capability::Record;
use crate::older::binaries::Binaries;
use crate::older::cli::{self, Arguments, Parse};
use crate::older::forced::{Published, Shared, processes};
use crate::older::tstp::{self, Profile};
use crate::older::{error, exit_code, failure, run_stage, value};
use crate::output::{Delivery, Stream};

pub mod capability;
pub mod kernel;
mod protocol;
pub mod replay;
pub mod toolchain;

const SCHEMA: &str = "fang-ground-fof-run-v1";
/// The record's `kernel_gate`; main.py said "an explicit v2 capability".
pub const KERNEL_GATE: &str = "Default kernel requires an explicit kernel capability; no fallback";
const SCOPE: &str = "Ground-FOF original-byte UNSAT with optional compiled TSTP output; no SAT or search-completeness claim";

fn text<'a>(manifest: &'a Object, key: &str) -> &'a str {
    match manifest.get(key) {
        Some(Value::String(text)) => text,
        _ => "",
    }
}

/// `output_bytes` of main.py.
fn output_bytes(manifest: &Object, status: &str, solution: &[u8]) -> Vec<u8> {
    let profile = text(manifest, "profile");
    let boundary = if profile == "kernel" {
        "fresh exact-byte kernel replay required"
    } else {
        "compilation/runtime trusted"
    };
    let problem = text(manifest, "problem_id");
    let mut data =
        format!("% Fang experimental ground-FOF profile: {profile}; {boundary}\n% SZS status {status} for {problem}\n").into_bytes();
    if status == "Unsatisfiable" && text(manifest, "output") == "tstp" {
        data.extend_from_slice(&tstp::solution_output(solution, problem));
    }
    data
}

fn finish(manifest: &mut Object, status: &str, reason: &str, stage: &str) {
    manifest.set("state", "finished");
    crate::manifest::update(manifest, status, exit_code(status), reason, stage);
}

fn pending_delivery() -> Value {
    let mut delivery = Object::new();
    delivery.set("state", "pending");
    delivery.set("closing_marker_delivered", false);
    Value::Object(delivery)
}

fn set_delivery_state(manifest: &mut Object, state: &str) {
    if let Some(Value::Object(delivery)) = manifest.get_mut("output_delivery") {
        delivery.set("state", state);
    }
}

fn written_delivery(output: &[u8], closing: bool) -> Value {
    let mut delivery = Object::new();
    delivery.set("state", "written");
    delivery.set("bytes", Value::from(output.len() as i64));
    delivery.set("sha256", fang_hash::sha256_hex(output));
    delivery.set("closing_marker_delivered", closing);
    delivery.set(
        "scope",
        "Written to caller descriptor; downstream consumption is not acknowledged",
    );
    Value::Object(delivery)
}

/// The Forced record main.py would write on cancellation, from the latest published state, and its status
/// output. Runs on the guard's watcher thread after the caller's process is gone.
fn forced(state: &Shared, started: Instant) -> (Object, Vec<u8>) {
    let mut manifest = state.manifest.clone();
    finish(&mut manifest, "Forced", "External cancellation", "adapter");
    manifest.set(
        "elapsed_before_status_seconds",
        started.elapsed().as_secs_f64(),
    );
    manifest.set("processes", state.processes.clone());
    manifest.set(
        "peak_adapter_tree_rss_kib",
        state.peak_kib.map_or(Value::Null, Value::from),
    );
    manifest.set("output_delivery", pending_delivery());
    let output = output_bytes(&manifest, "Forced", &[]);
    (manifest, output)
}

fn forced_delivery(manifest: &mut Object, output: &[u8], written: bool) {
    if written {
        manifest.set("output_delivery", written_delivery(output, false));
    } else {
        set_delivery_state(manifest, "incomplete");
    }
}

/// Run the ground-FOF profile on `arguments` (the command line without `--profile`). `capability` is the
/// pinned configuration file from the version-8 capability, or `None` when the command line names one with
/// `--capability`. With a pin, the command line is the public one main.py was given, `--capability PATH`
/// first, and the file must still hash to its pin.
pub fn run(worker: Worker, arguments: Vec<String>, capability: Option<&Record>) -> ExitCode {
    let started = Instant::now();
    let arguments = match capability {
        Some(record) => {
            let mut public = vec![
                "--capability".to_string(),
                record.path.display().to_string(),
            ];
            public.extend(arguments);
            public
        }
        None => arguments,
    };
    let mut manifest = Object::new();
    manifest.set("schema", SCHEMA);
    manifest.set("state", "starting");
    manifest.set("profile", "kernel");
    manifest.set("output", "status");
    manifest.set("problem_id", "fang_unavailable");
    manifest.set("language", capability::LANGUAGE);
    manifest.set("scope", SCOPE);
    let shared = Published::new(&manifest);
    shared.on_parent_death(
        &worker,
        move |state| forced(state, started),
        forced_delivery,
    );
    let mut state = State {
        supervisor: None,
        root: None,
        solution: Vec::new(),
    };
    let outcome = attempt(
        &mut state,
        &worker,
        &arguments,
        capability,
        &mut manifest,
        &shared,
        started,
    );
    let (mut status, reason, stage) = match outcome {
        Ok(Attempt::Help(text)) => {
            let printed = worker.finalize(|| {
                use std::io::Write;
                let mut stdout = std::io::stdout().lock();
                stdout
                    .write_all(text.as_bytes())
                    .and_then(|()| stdout.flush())
            });
            return match printed {
                Some(Ok(())) => ExitCode::SUCCESS,
                Some(Err(_)) => ExitCode::from(6),
                None => ExitCode::from(9),
            };
        }
        Ok(Attempt::Finished(status, reason)) => (status, reason, "complete".to_string()),
        Err(Fault::Failure(failure)) => (
            failure.status.name().to_string(),
            failure.reason,
            failure.stage,
        ),
        Err(other) => (
            "Error".to_string(),
            other.python_str(),
            "adapter".to_string(),
        ),
    };
    shared.publish(&manifest, state.supervisor.as_ref());
    let ended = worker.finalize(|| {
        conclude(
            &mut state,
            &mut manifest,
            &mut status,
            &reason,
            &stage,
            started,
        )
    });
    match ended {
        Some(code) => ExitCode::from(code),
        None => ExitCode::from(9),
    }
}

struct State {
    supervisor: Option<Supervisor>,
    root: Option<PathBuf>,
    solution: Vec<u8>,
}

enum Attempt {
    Help(String),
    Finished(String, String),
}

/// The `try` body of main.py's `main`.
fn attempt(
    state: &mut State,
    worker: &Worker,
    arguments: &[String],
    pin: Option<&Record>,
    manifest: &mut Object,
    shared: &Published,
    started: Instant,
) -> Result<Attempt, Fault> {
    let args = match cli::arguments(arguments, Some(capability::MAX_BYTES))? {
        Parse::Run(args) => args,
        Parse::Help(text) => return Ok(Attempt::Help(text)),
        Parse::Error(reason) => return Err(error(reason, "adapter")),
    };
    manifest.set("profile", args.check.clone());
    manifest.set("output", args.output.clone());
    let limits = Limits {
        wall_seconds: args.wall(),
        memory_mib: args.memory_mib as u64,
        input_bytes: args.max_input_bytes as u64,
        certificate_bytes: args.max_certificate_bytes as u64,
        log_bytes: args.max_log_bytes as u64,
        artifact_bytes: args.max_artifact_bytes as u64,
        ..Limits::default()
    };
    let mut supervisor = Supervisor::new(limits, Some(started))?;
    supervisor.set_cancel_token(worker.cancel_token());
    let supervisor = state.supervisor.insert(supervisor);
    let root: PathBuf = std::path::absolute(&args.artifacts)
        .map_err(Fault::at(&args.artifacts))?
        .components()
        .collect();
    crate::manifest::create_run_root(&root).map_err(Fault::at(&root))?;
    state.root = Some(root.clone());
    shared.own(&root);
    manifest.set("state", "running");
    manifest.set(
        "limits",
        crate::older::limits_json(&limits, &args.wall_seconds),
    );
    // Descriptors this process inherited without close-on-exec, which every child inherits too (a stated
    // difference from Python's close_fds, INTEGRATION.md).
    manifest.set(
        "inherited_descriptors",
        supervisor.inherited_descriptors_json(),
    );
    let mut engine_limits = Object::new();
    engine_limits.set("max_steps", Value::from(args.max_steps));
    engine_limits.set("max_clauses", Value::from(args.max_clauses));
    engine_limits.set("max_operations", Value::from(args.max_operations));
    manifest.set("engine_limits", Value::Object(engine_limits));
    manifest.set("resource_method", "One total monotonic deadline; 20ms sampled adapter/owned-descendant RSS, not address-space enforcement");
    manifest.set("kernel_gate", KERNEL_GATE);
    fang_supervisor::write_json(
        &root.join("manifest.json"),
        &Value::Object(manifest.clone()),
    )?;
    shared.publish(manifest, Some(supervisor));
    announce_artifacts(&args, &root, supervisor)?;
    let (status, reason) = pipeline(&args, supervisor, manifest, &root, pin, shared)?;
    if status == "Unsatisfiable" && args.output == "tstp" {
        let Some(Value::Object(record)) = manifest.get("solution") else {
            return Err(error("Captured solution changed before output", "exporter"));
        };
        let supervisor: &Supervisor = supervisor;
        state.solution =
            tstp::read_solution(&root, record, &mut || crate::older::check(supervisor))?;
    }
    supervisor.check_default()?;
    Ok(Attempt::Finished(status, reason))
}

/// `cli.announce_artifacts`: name an automatically created run directory on standard error.
fn announce_artifacts(args: &Arguments, root: &Path, supervisor: &Supervisor) -> Result<(), Fault> {
    if !args.auto_artifacts {
        return Ok(());
    }
    let mut message = b"Fang artifacts: ".to_vec();
    message.extend_from_slice(&crate::older::python_path_bytes(root));
    message.push(b'\n');
    let cancelled = || supervisor.cancelled();
    match crate::output::emit(
        Stream::Stderr,
        message,
        supervisor.deadline(),
        Some(&cancelled),
    )? {
        Delivery::Written => Ok(()),
        Delivery::DeadlinePassed => Err(failure(
            Status::Timeout,
            "Caller did not accept artifact location before the deadline",
            "artifact-output",
        )),
        Delivery::Failed(failure) => Err(Fault::Os(failure)),
    }
}

fn pin_path(config: &Object, name: &str) -> Result<PathBuf, Fault> {
    match config.get(name) {
        Some(Value::Object(pin)) => match pin.get("path") {
            Some(Value::String(path)) => Ok(PathBuf::from(path)),
            _ => Err(value("Unsupported FOF capability schema")),
        },
        _ => Err(value("Unsupported FOF capability schema")),
    }
}

/// Wait for the named binaries' hashes before their first execution and list what was verified in the record.
fn verified(
    binaries: &mut Binaries,
    names: &[&str],
    manifest: &mut Object,
    supervisor: &Supervisor,
) -> Result<(), Fault> {
    binaries.verify_checked(names, &mut || {
        crate::older::check(supervisor).map_err(Fault::from)
    })?;
    let listed = binaries.listed().into_iter().map(Value::from).collect();
    manifest.set("verified_before_run", Value::Array(listed));
    Ok(())
}

fn listed(config: &Object, key: &str, wanted: &str) -> bool {
    matches!(config.get(key), Some(Value::Array(items)) if items.iter().any(|item| matches!(item, Value::String(text) if text == wanted)))
}

/// `pipeline` of main.py.
fn pipeline(
    args: &Arguments,
    supervisor: &mut Supervisor,
    manifest: &mut Object,
    root: &Path,
    pin: Option<&Record>,
    shared: &Published,
) -> Result<(String, String), Fault> {
    let raw = {
        let supervisor: &Supervisor = supervisor;
        fang_supervisor::read_regular(&args.configuration, 32 << 20, &mut || {
            crate::older::check(supervisor)
        })?
    };
    let sha256 = fang_hash::sha256_hex(&raw);
    if pin.is_some_and(|pin| pin.sha256 != sha256) {
        return Err(value(format!(
            "Pinned configuration file changed: {}",
            args.configuration.display()
        )));
    }
    let config = capability::strict_json(crate::older::python_utf8(&raw)?.as_bytes())?;
    {
        let supervisor: &Supervisor = supervisor;
        capability::verify(&config, &mut || crate::older::check(supervisor))?;
    }
    let Value::Object(config) = config else {
        return Err(value("Unsupported FOF capability schema"));
    };
    if !listed(&config, "profiles", &args.check) {
        return Err(failure(
            Status::Inappropriate,
            "Requested checking profile is not installed; no fallback was performed",
            "capability",
        ));
    }
    if !listed(&config, "outputs", &args.output) {
        return Err(failure(
            Status::Inappropriate,
            "Requested output capability is not installed",
            "capability",
        ));
    }
    // The binaries this run may execute are hashed from now on, each verified before its first execution.
    let mut binaries = capability::binaries_of(&Value::Object(config.clone()))?;
    let mut route = vec!["launcher", "engine", "checker"];
    if args.check == "kernel" {
        route.push("lean");
    }
    if args.output == "tstp" {
        route.push("exporter");
    }
    binaries.start(&route);
    verified(&mut binaries, &["launcher"], manifest, supervisor)?;
    let copy = root.join("capability.json");
    std::fs::write(&copy, &raw).map_err(Fault::at(&copy))?;
    manifest.set("capability_sha256", sha256);
    manifest.set("capability", Value::Object(config.clone()));
    let data = {
        let supervisor: &Supervisor = supervisor;
        fang_supervisor::read_regular(&args.input, args.max_input_bytes as u64, &mut || {
            crate::older::check(supervisor)
        })?
    };
    let source = Snapshot::create(&root.join("input.p"), &data)?;
    let mut input = Object::new();
    input.set("bytes", Value::from(source.data.len() as i64));
    input.set("sha256", source.sha256.clone());
    input.set("identity", crate::older::SNAPSHOT_IDENTITY);
    manifest.set("input", Value::Object(input));
    manifest.set("problem_id", format!("fang_{}", &source.sha256[..24]));
    shared.publish(manifest, Some(supervisor));
    supervisor.memory()?;
    verified(&mut binaries, &["engine"], manifest, supervisor)?;
    let candidate = root.join("search/candidate.fang");
    let command: Vec<OsString> = vec![
        pin_path(&config, "engine")?.into(),
        source.argument().into(),
        "--proof".into(),
        candidate.clone().into(),
        "--max-steps".into(),
        args.max_steps.to_string().into(),
        "--max-clauses".into(),
        args.max_clauses.to_string().into(),
        "--max-operations".into(),
        args.max_operations.to_string().into(),
    ];
    let output = run_stage(
        supervisor,
        "search",
        &command,
        &root.join("search"),
        root,
        None,
        None,
        None,
    )?;
    shared.publish(manifest, Some(supervisor));
    {
        let supervisor: &Supervisor = supervisor;
        source.verify(&mut || crate::older::check(supervisor))?;
    }
    let (status, reason) = protocol::engine_outcome(&output, &source.data)?;
    if status != "candidate" {
        if std::fs::symlink_metadata(&candidate).is_ok() {
            return Err(error("Noncandidate driver left a certificate", "search"));
        }
        return Ok((status, reason));
    }
    let data = {
        let supervisor: &Supervisor = supervisor;
        fang_supervisor::read_regular(&candidate, args.max_certificate_bytes as u64, &mut || {
            crate::older::check(supervisor)
        })?
    };
    let certificate = Snapshot::create(&root.join("proof.fang"), &data)?;
    let mut record = Object::new();
    record.set("bytes", Value::from(certificate.data.len() as i64));
    record.set("sha256", certificate.sha256.clone());
    record.set("version", Value::from(2i64));
    record.set("preprocessing", "ground-fof-distributive-v1");
    manifest.set("certificate", Value::Object(record));
    verified(&mut binaries, &["checker"], manifest, supervisor)?;
    let command: Vec<OsString> = vec![
        pin_path(&config, "checker")?.into(),
        source.argument().into(),
        certificate.argument().into(),
    ];
    let output = run_stage(
        supervisor,
        "checker",
        &command,
        &root.join("checker"),
        root,
        None,
        None,
        None,
    )?;
    shared.publish(manifest, Some(supervisor));
    protocol::checker_acceptance(&output)?;
    let mut compiled = Object::new();
    compiled.set("accepted", true);
    compiled.set("kernel_instance", false);
    compiled.set(
        "scope",
        "Pinned original-byte v2 checker execution; compilation/runtime trusted",
    );
    manifest.set("compiled_check", Value::Object(compiled));
    if args.check == "kernel" {
        verified(&mut binaries, &["lean"], manifest, supervisor)?;
        let mut storage = Object::new();
        let result = kernel::verify(
            supervisor,
            &config,
            root,
            &source,
            &certificate,
            &mut storage,
        );
        manifest.set("kernel_storage", Value::Object(storage));
        let checked = result?;
        manifest.set("kernel_check", checked);
        shared.publish(manifest, Some(supervisor));
    }
    if args.output == "tstp" {
        verified(&mut binaries, &["exporter"], manifest, supervisor)?;
        let exporter = pin_path(&config, "exporter")?;
        let solution = tstp::export_solution(
            supervisor,
            &exporter,
            root,
            &source,
            &certificate,
            args.max_solution_bytes as u64,
            Profile::GroundFof,
        )?;
        manifest.set("solution", solution);
        shared.publish(manifest, Some(supervisor));
    }
    {
        let supervisor: &Supervisor = supervisor;
        let mut check = || crate::older::check(supervisor);
        source.verify(&mut check)?;
        certificate.verify(&mut check)?;
        if fang_supervisor::read_regular(&candidate, args.max_certificate_bytes as u64, &mut check)?
            != certificate.data
        {
            return Err(error(
                "Candidate certificate changed after capture",
                "checker",
            ));
        }
        capability::verify(&Value::Object(config), &mut check)?;
    }
    binaries.check_identities()?;
    supervisor.tree_bytes(root)?;
    supervisor.check("checked", 0.15)?;
    let reason = if args.check == "kernel" {
        "Fresh exact-byte Lean kernel replay accepted the captured version-2 pair"
    } else {
        "Compiled original-byte version-2 checker accepted the captured pair"
    };
    Ok(("Unsatisfiable".to_string(), reason.to_string()))
}

/// The rest of main.py's `main`, after its `try`: the terminal record, the status output and the final
/// record. Returns the exit code.
fn conclude(
    state: &mut State,
    manifest: &mut Object,
    status: &mut String,
    reason: &str,
    stage: &str,
    started: Instant,
) -> u8 {
    finish(manifest, status, reason, stage);
    manifest.set(
        "elapsed_before_status_seconds",
        started.elapsed().as_secs_f64(),
    );
    manifest.set(
        "processes",
        state
            .supervisor
            .as_ref()
            .map_or(Value::Array(Vec::new()), processes),
    );
    manifest.set(
        "peak_adapter_tree_rss_kib",
        state
            .supervisor
            .as_ref()
            .map_or(Value::Null, |supervisor| Value::from(supervisor.peak_kib)),
    );
    manifest.set("output_delivery", pending_delivery());
    if let Some(supervisor) = state.supervisor.as_mut()
        && status == "Unsatisfiable"
    {
        let checked = supervisor
            .memory()
            .map(|_| ())
            .and_then(|()| supervisor.check("output-preparation", 0.15));
        if let Err(failure) = checked {
            *status = failure.status.name().to_string();
            crate::manifest::update(
                manifest,
                status,
                exit_code(status),
                &failure.reason,
                &failure.stage,
            );
        }
    }
    let positive = |status: &str| status == "Unsatisfiable";
    if let Some(root) = &state.root {
        *status = crate::manifest::terminal_checkpoint(
            &root.join("manifest.json"),
            manifest,
            state.supervisor.as_ref(),
            &positive,
            &exit_code,
        );
    }
    let output = output_bytes(manifest, status, &state.solution);
    let positive_run = state
        .supervisor
        .as_ref()
        .filter(|_| status == "Unsatisfiable");
    let deadline = positive_run.map_or_else(
        || Instant::now() + Duration::from_millis(150),
        Supervisor::deadline,
    );
    let cancelled = positive_run.map(|supervisor| move || supervisor.cancelled());
    let delivered = crate::output::emit_status(
        output.clone(),
        deadline,
        cancelled.as_ref().map(|check| check as &dyn Fn() -> bool),
    );
    let refused = match delivered {
        Ok(Delivery::Written) => {
            let closing = status == "Unsatisfiable" && text(manifest, "output") == "tstp";
            manifest.set("output_delivery", written_delivery(&output, closing));
            None
        }
        Ok(Delivery::Failed(failure)) => Some((
            "Error".to_string(),
            Fault::Os(failure).python_str(),
            "status-output".to_string(),
        )),
        Ok(Delivery::DeadlinePassed) => Some((
            "Timeout".to_string(),
            "Caller did not accept status before deadline".to_string(),
            "status-output".to_string(),
        )),
        Err(failure) => Some((
            failure.status.name().to_string(),
            failure.reason,
            failure.stage,
        )),
    };
    if let Some((refused, reason, stage)) = refused {
        *status = refused;
        crate::manifest::update(manifest, status, exit_code(status), &reason, &stage);
        set_delivery_state(manifest, "incomplete");
    }
    if let Some(root) = &state.root {
        let supervisor = state
            .supervisor
            .as_ref()
            .filter(|_| status == "Unsatisfiable");
        *status = crate::manifest::terminal_checkpoint(
            &root.join("manifest.json"),
            manifest,
            supervisor,
            &positive,
            &exit_code,
        );
    }
    exit_code(status) as u8
}
