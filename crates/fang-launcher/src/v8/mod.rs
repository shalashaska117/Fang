// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The version-8 profile: expanded TPTP input, the producers, the compiled Lean checkers, the model steps and
//! the exporters, with SZS output and a run record of schema "fang-v8-run-v1".

pub mod bundle;
pub mod cli;
pub mod kernel;
pub mod models;
pub mod protocol;
pub mod run;
pub mod signed;
pub mod stages;
pub mod verify;

use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::{Duration, Instant};

use fang_json::{Object, Value};
use fang_supervisor::guard::Worker;
use fang_supervisor::{Fault, Status, Supervisor};

use crate::capability::{self, Capability, DEFAULT_CHECK, LANGUAGE};
use crate::manifest;
use crate::older::forced::{Published, Shared, processes};
use crate::output::{Delivery, Stream, emit};
use run::{Args, POSITIVE, Run, exit_code, output_bytes};

/// The saturation search of the third version: the producers take its options before their own arguments. The
/// schedule is the portfolio of the search gate kept for this install round.
pub const SEARCH_SCHEDULE: &str = concat!(
    "4/step5,index:on,prune_passive:on,der:on,simplify_new:on,selection:lookahead,age_weight:1:1;",
    "4/step5,index:on,prune_passive:on;4/step5,index:on,prune_passive:on,selection:none;",
    "4/step5,index:on,prune_passive:on,sine:2.0;",
    "44/step5,index:on,prune_passive:on,der:on,simplify_new:on,selection:lookahead,age_weight:1:1;",
    "41/step5,index:on,prune_passive:on;41/step5,index:on,prune_passive:on,selection:none;",
    "41/step5,index:on,prune_passive:on,sine:2.0;",
    "17/step5,index:on,prune_passive:on,der:on,simplify_new:on,selection:lookahead,age_weight:1:1,",
    "horn_layer:on"
);
const SCHEMA: &str = "fang-v8-run-v1";
const SCOPE: &str =
    "Expanded TPTP CNF/FOF axioms with equality; no SAT, conjecture or search-completeness claim";
const ERROR_EXIT: u8 = 6;
const FORCED_EXIT: u8 = 9;

/// `fang --self-check`: the capability's fields, the running launcher and every pinned file, hashed against
/// the installation.
fn self_check(capability_path: &Path) -> ExitCode {
    let result = Capability::load(capability_path).and_then(|capability| {
        capability::check_launcher(&capability).map_err(Fault::Value)?;
        let pins = capability.pins();
        for pin in &pins {
            let changed = || {
                Fault::Value(format!(
                    "Pinned version-8 dependency changed: {}",
                    pin.path.display()
                ))
            };
            let mut check = || Ok::<(), ()>(());
            let limit = fang_hash::DEFAULT_FILE_LIMIT;
            let plain =
                fang_hash::hash_file(&pin.path, limit, &mut check).map_err(|_| changed())?;
            if plain.0 != pin.sha256 {
                return Err(changed());
            }
            if let Some(chunked) = &pin.chunked_sha256 {
                let (digest, _) = fang_hash::hash_file_chunked(&pin.path, limit, 0, &mut check)
                    .map_err(|_| changed())?;
                if format!("{}{digest}", capability::CHUNKED_TAG) != *chunked {
                    return Err(changed());
                }
            }
        }
        Ok(pins.len())
    });
    match result {
        Ok(count) => {
            println!(
                "% Fang self-check: {count} pinned files, the running launcher among them, match the installation"
            );
            ExitCode::SUCCESS
        }
        Err(fault) => {
            println!("% Fang self-check failed: {}", fault.python_str());
            ExitCode::from(ERROR_EXIT)
        }
    }
}

/// The record fields every finished run sets, on the main path or the Forced path.
fn finish(record: &mut Object, status: &str, reason: &str, stage: &str, started: Instant) {
    record.set("state", "finished");
    manifest::update(record, status, exit_code(status), reason, stage);
    record.set(
        "elapsed_before_status_seconds",
        Value::from(started.elapsed().as_secs_f64()),
    );
}

fn pending() -> Value {
    let mut delivery = Object::new();
    delivery.set("state", "pending");
    Value::Object(delivery)
}

fn written(output: &[u8], document: bool) -> Value {
    let mut delivery = Object::new();
    delivery.set("state", "written");
    delivery.set("bytes", Value::from(output.len() as u64));
    delivery.set("sha256", fang_hash::sha256_hex(output));
    delivery.set("document", document);
    Value::Object(delivery)
}

fn incomplete(record: &mut Object) {
    if let Some(Value::Object(delivery)) = record.get_mut("output_delivery") {
        delivery.set("state", "incomplete");
    }
}

/// The Forced record and status block, from what the main path last published.
fn forced(state: &Shared, started: Instant) -> (Object, Vec<u8>) {
    let mut record = state.manifest.clone();
    finish(
        &mut record,
        "Forced",
        "External cancellation",
        "adapter",
        started,
    );
    record.set("processes", state.processes.clone());
    record.set(
        "peak_adapter_tree_rss_kib",
        state.peak_kib.map_or(Value::Null, Value::from),
    );
    record.set("output_delivery", pending());
    let output = output_bytes(&record, "Forced", &[]);
    (record, output)
}

fn forced_delivery(record: &mut Object, output: &[u8], delivered: bool) {
    if delivered {
        record.set("output_delivery", written(output, false));
    } else {
        incomplete(record);
    }
}

enum Attempt {
    Help(String),
    Finished(String, String),
}

/// Run the version-8 profile on `arguments` (the command line without `--profile`) with the capability at
/// `capability`, and return its exit code.
pub fn run(worker: Worker, arguments: Vec<String>, capability: &Path) -> ExitCode {
    if arguments.iter().any(|argument| argument == "--self-check") {
        return self_check(capability);
    }
    let started = Instant::now();
    let mut record = Object::new();
    record.set("schema", SCHEMA);
    record.set("state", "starting");
    record.set("check", DEFAULT_CHECK);
    record.set("check_source", "default");
    record.set("output", "status");
    record.set("problem_id", "fang_unavailable");
    record.set("language", LANGUAGE);
    record.set("scope", SCOPE);
    let published = Published::new(&record);
    published.on_parent_death(
        &worker,
        move |state| forced(state, started),
        forced_delivery,
    );
    let mut held: Option<Run> = None;
    let mut root: Option<PathBuf> = None;
    let outcome = attempt(
        &worker,
        &arguments,
        capability,
        &mut record,
        &published,
        &mut held,
        &mut root,
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
                Some(Err(_)) => ExitCode::from(ERROR_EXIT),
                None => ExitCode::from(FORCED_EXIT),
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
    if let Some(run) = held.as_mut() {
        record = std::mem::take(&mut run.manifest);
    }
    finish(&mut record, &status, &reason, &stage, started);
    let supervisor = held.as_ref().map(|run| &run.supervisor);
    record.set(
        "processes",
        supervisor.map_or(Value::Array(Vec::new()), processes),
    );
    record.set(
        "peak_adapter_tree_rss_kib",
        supervisor.map_or(Value::Null, |supervisor| Value::from(supervisor.peak_kib)),
    );
    record.set("output_delivery", pending());
    published.publish(&record, supervisor);
    let ended = worker.finalize(|| conclude(&mut held, &mut record, status, root.as_deref()));
    ExitCode::from(ended.unwrap_or(FORCED_EXIT))
}

/// The `try` body of the Python adapter's `main`: arguments, limits, the run directory, the first record, the
/// artifact notice and the pipeline.
#[allow(clippy::too_many_arguments)]
fn attempt(
    worker: &Worker,
    arguments: &[String],
    capability_path: &Path,
    record: &mut Object,
    published: &Published,
    held: &mut Option<Run>,
    owned: &mut Option<PathBuf>,
    started: Instant,
) -> Result<Attempt, Fault> {
    let values = match cli::arguments(arguments, true) {
        cli::Parsed::Help(text) => return Ok(Attempt::Help(text)),
        cli::Parsed::Refused(message) => {
            return Err(run::failure(
                Status::Error,
                format!("Invalid command arguments: {message}"),
                "adapter",
            ));
        }
        cli::Parsed::Values(values) => values,
    };
    let args = Args::from_values(&values)?;
    record.set("check", args.check.as_str());
    record.set("check_source", args.check_source.as_str());
    record.set("output", args.output.as_str());
    record.set("problem_id", run::problem_name(&args.input));
    published.publish(record, None);
    run::requested_features(&args, capability_path)?;
    let mut supervisor = Supervisor::new(run::limits(&args), Some(started))?;
    supervisor.set_cancel_token(worker.cancel_token());
    let root: PathBuf = std::path::absolute(&args.artifacts)
        .map_err(Fault::at(&args.artifacts))?
        .components()
        .collect();
    manifest::create_run_root(&root).map_err(Fault::at(&root))?;
    *owned = Some(root.clone());
    published.own(&root);
    record.set("state", "running");
    record.set("limits", supervisor.limits.to_json());
    // Descriptors this process inherited without close-on-exec, which every child inherits too (a stated
    // difference from Python's close_fds).
    record.set(
        "inherited_descriptors",
        supervisor.inherited_descriptors_json(),
    );
    record.set(
        "resource_method",
        "One monotonic deadline; sampled adapter and owned-descendant RSS, not an address-space cap",
    );
    record.set(
        "engine_limits",
        "Producer defaults of the accepted v8 producer; no search-limit flag",
    );
    fang_supervisor::write_json(&root.join("manifest.json"), &Value::Object(record.clone()))?;
    published.publish(record, Some(&supervisor));
    if args.auto_artifacts {
        let mut message = b"Fang artifacts: ".to_vec();
        message.extend_from_slice(&crate::older::python_path_bytes(&root));
        message.push(b'\n');
        let cancelled = || supervisor.cancelled();
        match emit(
            Stream::Stderr,
            message,
            supervisor.deadline(),
            Some(&cancelled),
        )? {
            Delivery::Written => {}
            Delivery::DeadlinePassed => {
                return Err(run::failure(
                    Status::Timeout,
                    "Caller did not accept artifact location before the deadline",
                    "artifact-output",
                ));
            }
            Delivery::Failed(error) => return Err(Fault::Os(error)),
        }
    }
    let capability = Capability::load(capability_path)?;
    let run = held.insert(Run::new(
        args,
        supervisor,
        std::mem::take(record),
        root,
        capability,
    ));
    run.published = Some(published.clone());
    let result = run::pipeline(run);
    published.publish(&run.manifest, Some(&run.supervisor));
    let (status, reason) = result?;
    run.supervisor.check_default()?;
    Ok(Attempt::Finished(status, reason))
}

/// The end of a run: documents, output preparation, the terminal checkpoint, the status delivery and the
/// final checkpoint. Returns the exit code.
fn conclude(
    held: &mut Option<Run>,
    record: &mut Object,
    mut status: String,
    root: Option<&Path>,
) -> u8 {
    let positive = |status: &str| POSITIVE.contains(&status);
    let documents = match held.as_mut() {
        Some(run) if positive(&status) => {
            run.manifest = std::mem::take(record);
            let documents = run::read_documents(run);
            *record = std::mem::take(&mut run.manifest);
            documents
        }
        _ => Vec::new(),
    };
    let mut output = output_bytes(record, &status, &documents);
    if positive(&status)
        && let Some(run) = held.as_mut()
    {
        let checked = match run.supervisor.memory() {
            Ok(_) => run.supervisor.check("output-preparation", 0.15),
            Err(failure) => Err(failure),
        };
        if let Err(failure) = checked {
            status = failure.status.name().to_string();
            manifest::update(
                record,
                &status,
                exit_code(&status),
                &failure.reason,
                &failure.stage,
            );
            output = output_bytes(record, &status, &[]);
        }
    }
    let path = root.map(|root| root.join("manifest.json"));
    let supervisor = held.as_ref().map(|run| &run.supervisor);
    if let Some(path) = &path {
        let saved = manifest::terminal_checkpoint(path, record, supervisor, &positive, &exit_code);
        if saved != status {
            status = saved;
            output = output_bytes(record, &status, &[]);
        }
    }
    let live = supervisor.filter(|_| positive(&status));
    let deadline = live.map_or_else(
        || Instant::now() + Duration::from_millis(150),
        Supervisor::deadline,
    );
    let cancelled = || live.is_some_and(Supervisor::cancelled);
    let watched: Option<&dyn Fn() -> bool> = if live.is_some() {
        Some(&cancelled)
    } else {
        None
    };
    match emit(Stream::Stdout, output.clone(), deadline, watched) {
        Ok(Delivery::Written) => {
            record.set("output_delivery", written(&output, !documents.is_empty()));
            let note = record
                .get("export_note")
                .and_then(Value::as_str)
                .map(str::to_string);
            if positive(&status)
                && let Some(note) = note
            {
                let notice = format!("fang: {note}\n").into_bytes();
                let _ = emit(
                    Stream::Stderr,
                    notice,
                    Instant::now() + Duration::from_millis(150),
                    None,
                );
            }
        }
        Ok(Delivery::DeadlinePassed) => {
            status = "Timeout".to_string();
            let reason = "Caller did not accept status before the deadline";
            manifest::update(record, &status, exit_code(&status), reason, "status-output");
            incomplete(record);
        }
        Ok(Delivery::Failed(error)) => {
            status = "Error".to_string();
            let reason = Fault::Os(error).python_str();
            manifest::update(
                record,
                &status,
                exit_code(&status),
                &reason,
                "status-output",
            );
            incomplete(record);
        }
        Err(failure) => {
            status = failure.status.name().to_string();
            manifest::update(
                record,
                &status,
                exit_code(&status),
                &failure.reason,
                &failure.stage,
            );
            incomplete(record);
        }
    }
    if let Some(path) = &path {
        let supervisor = supervisor.filter(|_| positive(&status));
        status = manifest::terminal_checkpoint(path, record, supervisor, &positive, &exit_code);
    }
    u8::try_from(exit_code(&status)).unwrap_or(ERROR_EXIT)
}
