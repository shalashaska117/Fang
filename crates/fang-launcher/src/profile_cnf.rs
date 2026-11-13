// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The older CNF profile (`--profile cnf`): a port of tools/fang_szs/app.py. Bounded CNF search, the pinned
//! compiled checker, an optional fresh kernel replay and an optional compiled TSTP export, with the run record
//! of schema "fang-local-run-v2".
//!
//! The run's statuses, reasons, stages, output text and record fields are app.py's. The differences are the
//! ones the launcher makes everywhere: the installation is schema v3 and pins the launcher in place of Python
//! and its sources (so the record has no `adapter_source_sha256`), the captured input and certificate are 0400
//! copies instead of sealed memfds, the adapter's CPU times come from /proc/self/stat, and a signal to the
//! command is seen through the guard's worker, which writes the Forced record. The binaries a run executes are
//! verified by their chunked SHA-256 before their first execution and by identity after the run, as on the
//! version-8 path, and the record lists them (`verified_before_run`) with the inherited descriptors
//! (`inherited_descriptors`); app.py rehashed every pin before and after.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::{Duration, Instant};

use fang_json::{Object, Value};
use fang_supervisor::guard::Worker;
use fang_supervisor::{Fault, Limits, Snapshot, Status, Supervisor, Times};

use crate::capability::Record;
use crate::older::binaries::Binaries;
use crate::older::cli::{self, Arguments, Parse};
use crate::older::forced::{Published, Shared, processes};
use crate::older::tstp::{self, Profile};
use crate::older::{error, exit_code, run_stage};
use crate::output::{Delivery, Stream};

pub mod decompose;
pub mod installation;
pub mod kernel;
pub mod protocol;

const SCHEMA: &str = "fang-local-run-v2";
const SCOPE: &str =
    "Strict equality-free CNF; no SAT, calculus-completeness or whole-Rust proof claim";
const RESOURCE_METHOD: &str = "20ms sampled RSS sums adapter and owned descendants; may miss brief peaks. This is not an address-space cap. Whole monotonic deadline includes capture and selected checking. Cleanup/finalization costs are retained.";
/// The record's description of the captured certificate; app.py described a sealed memfd.
pub const CERTIFICATE_IDENTITY: &str =
    "0400 disk copy of the exact engine bytes, checked by identity and SHA-256 after each child";

fn text<'a>(manifest: &'a Object, key: &str) -> &'a str {
    match manifest.get(key) {
        Some(Value::String(text)) => text,
        _ => "",
    }
}

/// `output_bytes` of app.py.
fn output_bytes(manifest: &Object, status: &str, solution: &[u8]) -> Vec<u8> {
    let problem = text(manifest, "problem_id");
    let mut data = format!(
        "% Fang checking profile: {}\n% SZS status {status} for {problem}\n",
        text(manifest, "profile")
    )
    .into_bytes();
    if status == "Unsatisfiable" && text(manifest, "output") == "tstp" {
        data.extend_from_slice(&tstp::solution_output(solution, problem));
    }
    data
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

fn written_delivery(output: &[u8], closing: bool, started: Instant) -> Value {
    let mut delivery = Object::new();
    delivery.set("state", "written");
    delivery.set("bytes", Value::from(output.len() as i64));
    delivery.set("sha256", fang_hash::sha256_hex(output));
    delivery.set("closing_marker_delivered", closing);
    delivery.set("elapsed_seconds", started.elapsed().as_secs_f64());
    delivery.set(
        "scope",
        "Written to the caller descriptor; downstream storage/consumption is not acknowledged",
    );
    Value::Object(delivery)
}

/// `sum(record.get(key, 0) for record in records)`: the integer 0 when no record has the key, as in Python.
fn children_seconds(processes: &Value, key: &str) -> Value {
    let values: Vec<f64> = match processes {
        Value::Array(records) => records
            .iter()
            .filter_map(|record| record.get(key).and_then(Value::as_f64))
            .collect(),
        _ => Vec::new(),
    };
    if values.is_empty() {
        Value::from(0i64)
    } else {
        Value::from(values.iter().sum::<f64>())
    }
}

/// The terminal fields app.py sets after its `try`.
#[allow(
    clippy::too_many_arguments,
    reason = "one parameter per field app.py sets in the same update"
)]
fn finish(
    manifest: &mut Object,
    status: &str,
    reason: &str,
    stage: &str,
    started: Instant,
    cpu: Option<Times>,
    processes: Value,
    peak_kib: Option<u64>,
) {
    manifest.set("state", "finished");
    crate::manifest::update(manifest, status, exit_code(status), reason, stage);
    manifest.set(
        "elapsed_before_status_seconds",
        started.elapsed().as_secs_f64(),
    );
    let now = fang_supervisor::process_times().ok();
    let (user, system) = match (cpu, now) {
        (Some(before), Some(after)) => (after.user - before.user, after.system - before.system),
        _ => (0.0, 0.0),
    };
    manifest.set("adapter_user_seconds", user);
    manifest.set("adapter_system_seconds", system);
    manifest.set(
        "children_user_seconds",
        children_seconds(&processes, "children_user_seconds"),
    );
    manifest.set(
        "children_system_seconds",
        children_seconds(&processes, "children_system_seconds"),
    );
    manifest.set("processes", processes);
    manifest.set(
        "peak_adapter_tree_rss_kib",
        peak_kib.map_or(Value::Null, Value::from),
    );
}

/// The Forced record app.py would write on cancellation, from the latest published state, and its output.
fn forced(state: &Shared, started: Instant, cpu: Option<Times>) -> (Object, Vec<u8>) {
    let mut manifest = state.manifest.clone();
    finish(
        &mut manifest,
        "Forced",
        "External cancellation",
        "adapter",
        started,
        cpu,
        state.processes.clone(),
        state.peak_kib,
    );
    manifest.set("output_delivery", pending_delivery());
    let output = output_bytes(&manifest, "Forced", &[]);
    (manifest, output)
}

/// Run the CNF profile on `arguments` (the command line without `--profile`). `installation` is the pinned
/// configuration file from the capability, or `None` when the command line names one with `--installation`.
/// With a pin, the command line is the public one app.py was given, `--installation PATH` first, and the file
/// must still hash to its pin.
pub fn run(worker: Worker, arguments: Vec<String>, installation: Option<&Record>) -> ExitCode {
    let started = Instant::now();
    let cpu = fang_supervisor::process_times().ok();
    let arguments = match installation {
        Some(record) => {
            let mut public = vec![
                "--installation".to_string(),
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
    manifest.set("problem_id", "fang_unavailable");
    manifest.set("profile", "kernel");
    manifest.set("output", "status");
    manifest.set("scope", SCOPE);
    let shared = Published::new(&manifest);
    shared.on_parent_death(
        &worker,
        move |state| forced(state, started, cpu),
        move |manifest, output, written| {
            if written {
                manifest.set("output_delivery", written_delivery(output, false, started));
            } else {
                set_delivery_state(manifest, "incomplete");
            }
        },
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
        installation,
        &mut manifest,
        &shared,
        started,
    );
    let (status, reason, stage) = match outcome {
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
        Err(other) => ("Error".to_string(), other.reason(), "adapter".to_string()),
    };
    shared.publish(&manifest, state.supervisor.as_ref());
    let ended = worker.finalize(|| {
        conclude(
            &mut state,
            &mut manifest,
            status,
            &reason,
            &stage,
            started,
            cpu,
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

/// The `try` body of app.py's `main`.
fn attempt(
    state: &mut State,
    worker: &Worker,
    arguments: &[String],
    pin: Option<&Record>,
    manifest: &mut Object,
    shared: &Published,
    started: Instant,
) -> Result<Attempt, Fault> {
    let args = match cli::arguments(arguments, None)? {
        Parse::Run(args) => args,
        Parse::Help(text) => return Ok(Attempt::Help(text)),
        Parse::Error(reason) => return Err(error(reason, "adapter")),
    };
    manifest.set("profile", args.check.clone());
    manifest.set("output", args.output.clone());
    manifest.set("max_solution_bytes", Value::from(args.max_solution_bytes));
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
    // A stale run is never overwritten, even when its manifest says failed.
    crate::manifest::create_run_root(&root).map_err(Fault::at(&root))?;
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
    manifest.set("resource_method", RESOURCE_METHOD);
    manifest.set("state", "running");
    state.root = Some(root.clone());
    shared.own(&root);
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
        Delivery::DeadlinePassed => Err(crate::older::failure(
            Status::Timeout,
            "Caller did not accept artifact location before the deadline",
            "artifact-output",
        )),
        Delivery::Failed(failure) => Err(Fault::Os(failure)),
    }
}

fn verify(config: &Value, supervisor: &Supervisor) -> Result<(), Fault> {
    let mut check = || crate::older::check(supervisor);
    installation::verify_installation(config, &mut check)
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

/// `run_pipeline` of app.py.
fn pipeline(
    args: &Arguments,
    supervisor: &mut Supervisor,
    manifest: &mut Object,
    run_root: &Path,
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
        return Err(Fault::Value(format!(
            "Pinned configuration file changed: {}",
            args.configuration.display()
        )));
    }
    let config = fang_supervisor::strict_json(crate::older::python_utf8(&raw)?.as_bytes())?;
    verify(&config, supervisor)?;
    if args.output == "tstp" && !installation::exporting(&config) {
        return Err(error(
            "This installation has no pinned TSTP exporter",
            "adapter",
        ));
    }
    // The binaries this run may execute are hashed from now on, each verified before its first execution.
    let mut binaries = installation::binaries_of(&config)?;
    let mut route = vec!["launcher", "engine", "checker"];
    if args.check == "kernel" {
        route.push("lean");
    }
    if args.output == "tstp" {
        route.push("exporter");
    }
    binaries.start(&route);
    verified(&mut binaries, &["launcher"], manifest, supervisor)?;
    manifest.set("installation", config.clone());
    manifest.set("installation_sha256", sha256);
    let copy = run_root.join("installation.json");
    std::fs::write(&copy, &raw).map_err(Fault::at(&copy))?;
    let data = {
        let supervisor: &Supervisor = supervisor;
        let limit = supervisor.limits.input_bytes;
        fang_supervisor::read_regular(&args.input, limit, &mut || crate::older::check(supervisor))?
    };
    let source = Snapshot::create(&run_root.join("input.p"), &data)?;
    let caller: PathBuf = std::path::absolute(&args.input)
        .map_err(Fault::at(&args.input))?
        .components()
        .collect();
    let mut input = Object::new();
    input.set("caller_path", caller.display().to_string());
    input.set("bytes", Value::from(source.data.len() as i64));
    input.set("sha256", source.sha256.clone());
    input.set("child_identity", crate::older::SNAPSHOT_IDENTITY);
    manifest.set("input", Value::Object(input));
    manifest.set("problem_id", format!("fang_{}", &source.sha256[..24]));
    shared.publish(manifest, Some(supervisor));
    supervisor.memory()?;
    verified(&mut binaries, &["engine"], manifest, supervisor)?;
    let candidate = run_root.join("search/candidate.fang");
    let command: Vec<OsString> = vec![
        installation::binary(&config, "engine").into(),
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
        &run_root.join("search"),
        run_root,
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
            return Err(error(
                "Engine left a certificate for a noncandidate outcome",
                "search",
            ));
        }
        return Ok((status, reason));
    }
    let data = {
        let supervisor: &Supervisor = supervisor;
        let limit = supervisor.limits.certificate_bytes;
        fang_supervisor::read_regular(&candidate, limit, &mut || crate::older::check(supervisor))?
    };
    let certificate = Snapshot::create(&run_root.join("proof.fang"), &data)?;
    let mut record = Object::new();
    record.set("bytes", Value::from(certificate.data.len() as i64));
    record.set("sha256", certificate.sha256.clone());
    record.set("child_identity", CERTIFICATE_IDENTITY);
    manifest.set("certificate", Value::Object(record));
    verified(&mut binaries, &["checker"], manifest, supervisor)?;
    let command: Vec<OsString> = vec![
        installation::binary(&config, "checker").into(),
        source.argument().into(),
        certificate.argument().into(),
    ];
    let output = run_stage(
        supervisor,
        "checker",
        &command,
        &run_root.join("checker"),
        run_root,
        None,
        None,
        None,
    )?;
    shared.publish(manifest, Some(supervisor));
    protocol::checker_acceptance(&output)?;
    {
        let supervisor: &Supervisor = supervisor;
        let mut check = || crate::older::check(supervisor);
        source.verify(&mut check)?;
        certificate.verify(&mut check)?;
        if fang_supervisor::read_regular(
            &candidate,
            supervisor.limits.certificate_bytes,
            &mut check,
        )? != certificate.data
        {
            return Err(error("Engine certificate changed after capture", "checker"));
        }
    }
    let mut compiled = Object::new();
    compiled.set("accepted", true);
    compiled.set("kernel_instance", false);
    manifest.set("compiled_check", Value::Object(compiled));
    if args.check == "kernel" {
        verified(&mut binaries, &["lean"], manifest, supervisor)?;
        let mut storage = Object::new();
        let result = kernel::verify(
            supervisor,
            &config,
            run_root,
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
        let exporter = installation::binary(&config, "exporter");
        let solution = tstp::export_solution(
            supervisor,
            &exporter,
            run_root,
            &source,
            &certificate,
            args.max_solution_bytes as u64,
            Profile::Cnf,
        )?;
        manifest.set("solution", solution);
        shared.publish(manifest, Some(supervisor));
    }
    verify(&config, supervisor)?;
    binaries.check_identities()?;
    {
        let supervisor: &Supervisor = supervisor;
        let mut check = || crate::older::check(supervisor);
        source.verify(&mut check)?;
        certificate.verify(&mut check)?;
    }
    supervisor.tree_bytes(run_root)?;
    supervisor.check_default()?;
    Ok((
        "Unsatisfiable".to_string(),
        "Selected checking profile accepted the exact captured problem".to_string(),
    ))
}

/// The rest of app.py's `main`, after its `try`. Returns the exit code.
fn conclude(
    state: &mut State,
    manifest: &mut Object,
    mut status: String,
    reason: &str,
    stage: &str,
    started: Instant,
    cpu: Option<Times>,
) -> u8 {
    let processes = state
        .supervisor
        .as_ref()
        .map_or(Value::Array(Vec::new()), processes);
    let peak = state
        .supervisor
        .as_ref()
        .map(|supervisor| supervisor.peak_kib);
    finish(
        manifest, &status, reason, stage, started, cpu, processes, peak,
    );
    manifest.set("output_delivery", pending_delivery());
    let mut output = output_bytes(manifest, &status, &state.solution);
    if let Some(supervisor) = state.supervisor.as_mut()
        && status == "Unsatisfiable"
    {
        let checked = supervisor
            .memory()
            .map(|_| ())
            .and_then(|()| supervisor.check("output-preparation", 0.15));
        if let Err(failure) = checked {
            status = failure.status.name().to_string();
            crate::manifest::update(
                manifest,
                &status,
                exit_code(&status),
                &failure.reason,
                "output-preparation",
            );
            output = output_bytes(manifest, &status, b"");
        }
        manifest.set(
            "peak_adapter_tree_rss_kib",
            Value::from(supervisor.peak_kib),
        );
    }
    let positive = |status: &str| status == "Unsatisfiable";
    let checkpoint = |manifest: &mut Object, supervisor: Option<&Supervisor>| {
        state.root.as_ref().map(|root| {
            crate::manifest::terminal_checkpoint(
                &root.join("manifest.json"),
                manifest,
                supervisor,
                &positive,
                &exit_code,
            )
        })
    };
    if let Some(saved) = checkpoint(manifest, state.supervisor.as_ref())
        && saved != status
    {
        status = saved;
        output = output_bytes(manifest, &status, b"");
    }
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
        Ok(Delivery::Written) => None,
        Ok(Delivery::DeadlinePassed) => Some((
            "Timeout".to_string(),
            "Caller did not accept final output before the deadline".to_string(),
            "status-output".to_string(),
        )),
        Err(failure) => Some((
            failure.status.name().to_string(),
            failure.reason,
            failure.stage,
        )),
        Ok(Delivery::Failed(failure)) => Some((
            "Error".to_string(),
            format!("Caller output failed: {}", Fault::Os(failure).python_str()),
            "status-output".to_string(),
        )),
    };
    if let Some((refused, reason, stage)) = refused {
        crate::manifest::update(manifest, &refused, exit_code(&refused), &reason, &stage);
        set_delivery_state(manifest, "incomplete");
        checkpoint(manifest, None);
        return exit_code(&refused) as u8;
    }
    let closing = status == "Unsatisfiable" && text(manifest, "output") == "tstp";
    manifest.set(
        "output_delivery",
        written_delivery(&output, closing, started),
    );
    if let Some(saved) = checkpoint(manifest, state.supervisor.as_ref()) {
        status = saved;
    }
    exit_code(&status) as u8
}
