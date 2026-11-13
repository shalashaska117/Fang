// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The version-8 command: expanded TPTP input, the producers, the compiled Lean checkers, SZS status.
//!
//! Axiom-only single files go to the version-8 checker. Axiom-only inputs with include directives, distinct
//! objects or annotations go to the bundle producer and checker, and with --output tstp to the bundle exporter
//! after the checker accepted. Inputs with any role other than axiom, conjectures included, go to the signed
//! producer and checker, and with --output tstp the proved conjectures of a single file get one document each.
//! The run record and the first output line record which path ran; the second line names the checking mode.

use std::ffi::OsString;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use fang_json::{Object, Value};
use fang_supervisor::{
    Environment, Failure, Fault, Limits, Snapshot, Stage, StageOutput, Status, Supervisor,
};

use super::bundle;
use super::protocol::{self, ContractError};
use super::signed::{self, BundleFile, Checked, Item, Listing};
use super::stages::STAGE_ORDER;
use super::verify::{V8_MESSAGES, Verifier};
use crate::capability::{
    self, Capability, DEFAULT_CHECK, KERNEL_MINIMUMS, LANGUAGE, MAX_MODEL_BYTES, Pin,
};
use crate::older::forced::Published;

pub const PATHS: [(&str, &str); 3] = [
    ("single", "single file"),
    (
        "bundle",
        "bundle (include directives, distinct objects or annotations)",
    ),
    (
        "signed",
        "signed bundle (conjectures or other non-axiom roles)",
    ),
];
pub const POSITIVE: [&str; 4] = [
    "Unsatisfiable",
    "Theorem",
    "Satisfiable",
    "CounterSatisfiable",
];
pub const NONE_REASON: &str =
    "No checker ran on this result (--check none); the producer's candidate is reported as found";
pub const NONE_TSTP: &str = "TSTP output prints a checked refutation and is not available with --check none; rerun \
                             without --check for the compiled checker. No fallback was performed.";
pub const TSTP_UNAVAILABLE: &str = "TSTP output is not installed for version-8 input; rerun with --output status. No fallback was performed.";
pub const KERNEL_UNAVAILABLE: &str = "Kernel replay is not installed in this package; rerun without --check for the \
                                      compiled checker (the default; trusts the Lean compiler and runtime). No \
                                      fallback was performed.";
pub const KERNEL_SINGLE_ONLY: &str = "Kernel replay covers single-file axiom input; rerun without --check for the \
                                      compiled checker (the default). No fallback was performed.";
pub const KERNEL_TSTP: &str = "TSTP output is not available with --check kernel; rerun with --output status, or \
                               without --check. No fallback was performed.";
/// A signed input whose documents no installed exporter covers: include directives, or the inputs task when
/// the conjecture exporter has no inputs mode.
pub const SIGNED_TSTP_SCOPE: &str = "TSTP output for this input is not available yet (include directives, or no conjecture to prove); no document \
     printed";
/// A signed single file with a distinct object: the conjecture exporter's decoder does not read objects.
pub const OBJECT_TSTP_SCOPE: &str = "TSTP output for a single file with conjectures and distinct objects is not available yet; no document printed";
/// The single-file exporter reads at most 1,000 statements.
pub const STATEMENT_LIMIT: usize = 1000;
pub const STATEMENT_LIMIT_NOTE: &str = "TSTP export stopped at the single-file exporter's limit of 1,000 statements; no document printed";

pub fn kernel_below() -> String {
    format!(
        "--check kernel needs at least {}; rerun with those flags, or without --check for the compiled checker (the \
         default). No fallback was performed.",
        super::cli::kernel_flags()
    )
}

fn mode_text(check: &str) -> &'static str {
    match check {
        "kernel" => "kernel replay requested",
        "none" => "not checked, the producer's result as found",
        _ => "checked by the compiled Lean checker",
    }
}

fn trust_text(check: &str) -> &'static str {
    match check {
        "kernel" => "Lean kernel trusted",
        "none" => "producer trusted, no checker ran",
        _ => "compiler and runtime trusted",
    }
}

/// Exit codes by status; the positive statuses exit 0.
pub fn exit_code(status: &str) -> i64 {
    if POSITIVE.contains(&status) {
        return 0;
    }
    Status::from_name(status)
        .map(|status| i64::from(status.exit_code()))
        .unwrap_or(6)
}

pub fn failure(status: Status, reason: impl Into<String>, stage: &str) -> Fault {
    Fault::Failure(Failure::new(status, reason, stage))
}

fn contract(error: ContractError, stage: &str) -> Fault {
    failure(Status::Error, error.0, stage)
}

/// Python's `bytes.decode("ascii", "replace")`: every byte above 127 becomes U+FFFD.
pub fn ascii_text(bytes: &[u8]) -> String {
    bytes
        .iter()
        .map(|&byte| {
            if byte.is_ascii() {
                char::from(byte)
            } else {
                '\u{fffd}'
            }
        })
        .collect()
}

/// Python's `str.strip()` on text decoded from ASCII.
pub fn python_strip(text: &str) -> &str {
    text.trim_matches(|character| {
        matches!(
            character,
            '\t' | '\n' | '\x0b' | '\x0c' | '\r' | '\x1c'..='\x1f' | ' '
        )
    })
}

/// The first line of a diagnostic, at most 200 characters: Python's
/// `(text.strip().splitlines() or ["no diagnostic"])[0][:200]` on the ASCII decoding.
pub fn first_line(bytes: &[u8]) -> String {
    let text = ascii_text(bytes);
    let stripped = python_strip(&text);
    if stripped.is_empty() {
        return "no diagnostic".to_string();
    }
    let end = stripped
        .find(['\n', '\r', '\x0b', '\x0c', '\x1c', '\x1d', '\x1e'])
        .unwrap_or(stripped.len());
    stripped[..end].chars().take(200).collect()
}

/// An exit code as Python formats it: the number, or None for a child stopped by a signal.
pub fn python_code(code: Option<i32>) -> String {
    code.map_or_else(|| "None".to_string(), |code| code.to_string())
}

/// An exit code as the run record holds it: the number, or null.
pub fn code_value(code: Option<i32>) -> Value {
    code.map_or(Value::Null, |code| Value::from(i64::from(code)))
}

/// Write `data` to a new file at `path`; an existing file is an error, as Python's `open("xb")`.
pub fn write_new(path: &Path, data: &[u8]) -> Result<(), Fault> {
    std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .and_then(|mut file| std::io::Write::write_all(&mut file, data))
        .map_err(Fault::at(path))
}

/// The command's arguments after parsing and range checks.
#[derive(Clone, Debug)]
pub struct Args {
    pub input: PathBuf,
    pub artifacts: PathBuf,
    pub auto_artifacts: bool,
    pub tptp_root: Option<PathBuf>,
    pub check: String,
    pub check_source: String,
    pub output: String,
    pub max_solution_bytes: u64,
    pub wall_seconds: f64,
    pub memory_mib: u64,
    pub max_input_bytes: u64,
    pub max_certificate_bytes: u64,
    pub max_log_bytes: u64,
    pub max_artifact_bytes: u64,
}

impl Args {
    pub fn from_values(values: &crate::cli::Values) -> Result<Args, Fault> {
        let text = |name: &str| values.text(name).map(str::to_string);
        let number = |name: &str| values.int(name).unwrap_or(0).max(0) as u64;
        let input = PathBuf::from(text("input").unwrap_or_default());
        let (artifacts, auto_artifacts) = match text("artifacts") {
            Some(path) => (PathBuf::from(path), false),
            None => {
                let token = fang_supervisor::fresh_token()?.replace('-', "");
                let current = std::env::current_dir().map_err(Fault::Os)?;
                (current.join(".local").join("runs").join(token), true)
            }
        };
        let tptp_root = text("tptp_root")
            .or_else(|| std::env::var("TPTP").ok().filter(|value| !value.is_empty()))
            .map(PathBuf::from);
        let (check, check_source) = match text("check") {
            Some(check) => (check, "explicit".to_string()),
            None => (DEFAULT_CHECK.to_string(), "default".to_string()),
        };
        Ok(Args {
            input,
            artifacts,
            auto_artifacts,
            tptp_root,
            check,
            check_source,
            output: text("output").unwrap_or_else(|| "status".to_string()),
            max_solution_bytes: number("max_solution_bytes"),
            wall_seconds: values.float("wall_seconds").unwrap_or(60.0),
            memory_mib: number("memory_mib"),
            max_input_bytes: number("max_input_bytes"),
            max_certificate_bytes: number("max_certificate_bytes"),
            max_log_bytes: number("max_log_bytes"),
            max_artifact_bytes: number("max_artifact_bytes"),
        })
    }

    fn minimum(&self, option: &str) -> f64 {
        match option {
            "--wall-seconds" => self.wall_seconds,
            "--memory-mib" => self.memory_mib as f64,
            _ => self.max_artifact_bytes as f64,
        }
    }
}

/// The SZS problem name: the input's base name without a trailing ".p".
pub fn problem_name(path: &Path) -> String {
    let absolute = std::path::absolute(path).unwrap_or_else(|_| path.to_path_buf());
    let name = absolute
        .file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_default();
    match name.strip_suffix(".p") {
        Some(stem) if !stem.is_empty() => stem.to_string(),
        _ => name,
    }
}

/// Refuse kernel checking before any input is read: below its minimum limits, or when this installation has no
/// kernel mode, or with TSTP output. Other TSTP refusals come after routing, before search.
pub fn requested_features(args: &Args, capability_path: &Path) -> Result<(), Fault> {
    if args.check == "kernel" {
        if KERNEL_MINIMUMS
            .iter()
            .any(|(option, minimum)| args.minimum(option) < *minimum as f64)
        {
            return Err(failure(Status::Inappropriate, kernel_below(), "capability"));
        }
        let installed = Capability::load(capability_path)
            .ok()
            .and_then(|capability| capability.section("kernel").cloned());
        if installed.is_none() {
            return Err(failure(
                Status::Inappropriate,
                KERNEL_UNAVAILABLE,
                "capability",
            ));
        }
        if args.output == "tstp" {
            return Err(failure(Status::Inappropriate, KERNEL_TSTP, "capability"));
        }
    }
    if args.check == "none" && args.output == "tstp" {
        return Err(failure(Status::Inappropriate, NONE_TSTP, "capability"));
    }
    Ok(())
}

/// One run of the command: its arguments, supervisor, record and pinned files.
pub struct Run {
    pub args: Args,
    pub supervisor: Supervisor,
    pub manifest: Object,
    pub root: PathBuf,
    pub capability: Capability,
    pub verifier: Verifier,
    pub environment: Environment,
    /// Where the record and the stage records are published for the Forced path, before and after each stage.
    pub published: Option<Published>,
}

impl Run {
    pub fn new(
        args: Args,
        supervisor: Supervisor,
        manifest: Object,
        root: PathBuf,
        capability: Capability,
    ) -> Run {
        let mut pins = capability.pins();
        // The running launcher is checked against the launcher's pin under the path it runs from.
        if let (Ok(running), Some(launcher)) = (
            std::env::current_exe(),
            pins.iter()
                .find(|pin| pin.path == capability.launcher().path)
                .cloned(),
        ) {
            pins.push(Pin {
                path: running,
                ..launcher
            });
        }
        let mut environment = fang_supervisor::child_environment();
        environment.set("LEAN_NUM_THREADS", "1");
        Run {
            args,
            supervisor,
            manifest,
            root,
            capability,
            verifier: Verifier::new(pins, V8_MESSAGES),
            environment,
            published: None,
        }
    }

    fn publish(&self) {
        if let Some(published) = &self.published {
            published.publish(&self.manifest, Some(&self.supervisor));
        }
    }

    /// The path of a pinned binary of a section, for example ("bundle", "producer").
    pub fn binary(&self, section: &str, name: &str) -> PathBuf {
        if section.is_empty() {
            return self.capability.record(name).path;
        }
        self.capability
            .section_record(section, name)
            .map(|record| record.path)
            .unwrap_or_default()
    }

    /// Hash the pinned files not hashed yet in this run, in parallel, and list them in the record.
    pub fn verify(&mut self, paths: &[&Path]) -> Result<(), Fault> {
        self.verifier.verify_checked(paths, &mut || {
            self.supervisor.check("adapter", 0.15).map_err(Fault::from)
        })?;
        self.manifest.set(
            "verified_before_run",
            Value::Array(
                self.verifier
                    .listed()
                    .into_iter()
                    .map(Value::from)
                    .collect(),
            ),
        );
        Ok(())
    }

    /// Run one stage: its executable is verified at first use, then the supervisor runs it.
    pub fn stage(
        &mut self,
        name: &str,
        command: &[OsString],
        directory: &Path,
        stdin: Option<&Path>,
        stdout_limit: Option<u64>,
    ) -> Result<StageOutput, Fault> {
        let executable = PathBuf::from(&command[0]);
        self.verify(&[&executable])?;
        self.publish();
        let environment = self.environment.clone();
        let root = self.root.clone();
        let output = self.supervisor.run(&Stage {
            name,
            command,
            directory,
            run_root: &root,
            environment: Some(&environment),
            stdin,
            stdout_limit,
            cwd: None,
        });
        self.publish();
        output
    }

    /// The search options of one producer run: its time limit is what is left of the current deadline less the
    /// checker reserve, its memory the command's limit less the margin the model steps also keep.
    pub fn search_options(&self) -> Vec<OsString> {
        let left = self
            .supervisor
            .deadline()
            .saturating_duration_since(Instant::now())
            .as_secs_f64();
        let seconds = ((left - STAGE_ORDER.search_check_reserve_seconds).floor() as i64).max(1);
        let memory = self
            .args
            .memory_mib
            .saturating_sub(STAGE_ORDER.memory_margin_mib)
            .max(16);
        [
            "--search".to_string(),
            "v3".to_string(),
            "--time-limit".to_string(),
            seconds.to_string(),
            "--memory-mib".to_string(),
            memory.to_string(),
            "--set".to_string(),
            format!("portfolio={}", super::SEARCH_SCHEDULE),
        ]
        .into_iter()
        .map(OsString::from)
        .collect()
    }

    /// After execution and before a positive status: the sealed files, the executed binaries' identities, the
    /// memory sample, the run tree's size and the deadline.
    pub fn confirm(&mut self, snapshots: &[&Snapshot], stage: &str) -> Result<(), Fault> {
        let mut check = || self.supervisor.check_default();
        for snapshot in snapshots {
            snapshot.verify(&mut check)?;
        }
        self.verifier.check_identities()?;
        self.supervisor.memory().map_err(Fault::Failure)?;
        self.supervisor.tree_bytes(&self.root)?;
        self.supervisor.check(stage, 0.15).map_err(Fault::Failure)?;
        Ok(())
    }

    fn read_regular(&self, path: &Path, limit: u64) -> Result<Vec<u8>, Fault> {
        let mut check = || self.supervisor.check_default();
        fang_supervisor::read_regular(path, limit, &mut check)
    }

    /// --check none: the producer's candidate stands as the result, with no checker run on it. The sealed files
    /// and certificates must still be the ones the producer read and wrote, and the executed binaries the ones
    /// hashed before they ran; only the checking step is left out.
    fn unchecked(&mut self, snapshots: &[&Snapshot]) -> Result<(), Fault> {
        self.confirm(snapshots, "unchecked")?;
        let mut record = Object::new();
        record.set("reason", NONE_REASON);
        record.set("trust", "the producer");
        self.manifest.set("unchecked", Value::Object(record));
        Ok(())
    }

    /// Print the TSTP document of what the checker has accepted, or record why there is none. An export error,
    /// an invalid document, a resource stop or a time-out only removes the document; the status stays what the
    /// checker decided. Any other supervisor failure during the export is raised again.
    pub fn export_document(
        &mut self,
        command: &[OsString],
        label: &str,
        solution: &str,
    ) -> Result<(), Fault> {
        let name = self.input_name();
        let saved = self.supervisor.deadline();
        let reserve = Duration::from_secs_f64(STAGE_ORDER.export_reserve_seconds);
        self.supervisor
            .set_deadline(saved.checked_sub(reserve).unwrap_or(saved));
        let mut record = Object::new();
        record.set("file_name", name.as_str());
        self.manifest.set("export", Value::Object(record.clone()));
        let directory = self.root.join(label);
        let limit = Some(self.args.max_solution_bytes);
        let outcome = self.stage(label, command, &directory, None, limit);
        self.supervisor.set_deadline(saved);
        let output = match outcome {
            Ok(output) => output,
            Err(Fault::Failure(error))
                if matches!(
                    error.status,
                    Status::Timeout | Status::MemoryOut | Status::ResourceOut
                ) =>
            {
                record.set("state", "resource");
                record.set("detail", error.status.name());
                self.manifest.set("export", Value::Object(record));
                self.manifest.set(
                    "export_note",
                    format!(
                        "TSTP export stopped at a resource limit ({}); no document printed",
                        error.status.name()
                    ),
                );
                return Ok(());
            }
            Err(other) => return Err(other),
        };
        let code = output.record.exit_code;
        record.set("exit_code", code_value(code));
        if code == Some(0) && output.stderr.is_empty() && is_document(&output.stdout) {
            let path = self.root.join(solution);
            write_new(&path, &output.stdout)?;
            record.set("state", "document");
            record.set("bytes", Value::from(output.stdout.len() as u64));
            record.set("sha256", fang_hash::sha256_hex(&output.stdout));
            record.set("path", path.display().to_string());
            self.manifest.set("export", Value::Object(record));
            return Ok(());
        }
        let first = first_line(&output.stderr);
        record.set("state", "failed");
        record.set("diagnostic", first.as_str());
        self.manifest.set("export", Value::Object(record));
        self.manifest.set(
            "export_note",
            format!(
                "TSTP export failed (exit {}: {first}); no document printed",
                python_code(code)
            ),
        );
        Ok(())
    }

    pub fn input_name(&self) -> String {
        std::path::absolute(&self.args.input)
            .ok()
            .and_then(|path| {
                path.file_name()
                    .map(|name| name.to_string_lossy().into_owned())
            })
            .unwrap_or_default()
    }
}

/// A document: one or more lines of printable ASCII.
fn is_document(bytes: &[u8]) -> bool {
    !bytes.is_empty()
        && bytes.ends_with(b"\n")
        && bytes
            .split(|&byte| byte == b'\n')
            .all(|line| line.iter().all(|&byte| (b' '..=b'~').contains(&byte)))
}

fn os(items: impl IntoIterator<Item = impl Into<OsString>>) -> Vec<OsString> {
    items.into_iter().map(Into::into).collect()
}

/// The pipeline of one run after the record and run directory exist: routing, then the path's stages.
pub fn pipeline(run: &mut Run) -> Result<(String, String), Fault> {
    run.manifest
        .set("capability", Value::Object(run.capability.value().clone()));
    run.manifest
        .set("capability_sha256", run.capability.sha256.as_str());
    let launcher = std::env::current_exe()
        .map_err(|_| Fault::Value("Cannot locate the running launcher".to_string()))?;
    run.verify(&[&launcher])?;
    let data = run.read_regular(&run.args.input.clone(), run.args.max_input_bytes)?;
    let source = Snapshot::create(&run.root.join("input.p"), &data)?;
    let mut input = Object::new();
    input.set(
        "caller_path",
        std::path::absolute(&run.args.input)
            .unwrap_or_default()
            .display()
            .to_string(),
    );
    input.set("bytes", Value::from(data.len() as u64));
    input.set("sha256", source.sha256.as_str());
    input.set(
        "child_identity",
        "0400 file in the run directory; identity and hash checked after every child",
    );
    run.manifest.set("input", Value::Object(input));
    let name = run.input_name();
    let plain_bundle = bundle::needs_bundle(&data);
    let mut files = vec![BundleFile {
        root: "base".to_string(),
        path: name.clone(),
        location: None,
        data: data.clone(),
    }];
    if plain_bundle {
        let base = std::path::absolute(&run.args.input)
            .ok()
            .and_then(|path| path.parent().map(Path::to_path_buf))
            .unwrap_or_default();
        let tptp = run
            .args
            .tptp_root
            .as_ref()
            .map(|root| std::path::absolute(root).unwrap_or_else(|_| root.clone()));
        let mut total = data.len() as u64;
        let supervisor = &run.supervisor;
        let mut read = |location: &Path| -> Result<Vec<u8>, Fault> {
            let mut check = || supervisor.check_default();
            let bytes = fang_supervisor::read_regular(location, signed::FILE_BYTES, &mut check)?;
            total += bytes.len() as u64;
            if total > signed::TOTAL_BYTES {
                return Err(failure(
                    Status::ResourceOut,
                    "Bundle total byte limit exceeded",
                    "bundle-discovery",
                ));
            }
            Ok(bytes)
        };
        files = signed::discover(&name, data.clone(), &base, tptp.as_deref(), &mut read)?;
    }
    let route = signed::route(&files, plain_bundle);
    run.manifest.set("path", route);
    let tstp = run.capability.section("tstp").cloned();
    let has = |name: &str| {
        tstp.as_ref()
            .is_some_and(|section| section.contains_key(name))
    };
    if run.args.output == "tstp"
        && (tstp.is_none()
            || (route == "signed" && !has("goal_exporter"))
            || (route == "bundle" && !has("bundle_exporter")))
    {
        let message = match route {
            "single" => TSTP_UNAVAILABLE,
            "bundle" => bundle::TSTP_UNAVAILABLE,
            _ => signed::TSTP_UNAVAILABLE,
        };
        return Err(failure(Status::Inappropriate, message, "capability"));
    }
    let kernel_installed = run.capability.section("kernel").is_some();
    if run.args.check == "kernel" && (route != "single" || !kernel_installed) {
        let message = if kernel_installed {
            KERNEL_SINGLE_ONLY
        } else {
            KERNEL_UNAVAILABLE
        };
        return Err(failure(Status::Inappropriate, message, "capability"));
    }
    if route != "single" && run.capability.section(route).is_none() {
        let message = if route == "signed" {
            signed::NOT_INSTALLED
        } else {
            bundle::NOT_INSTALLED
        };
        return Err(failure(Status::Inappropriate, message, "capability"));
    }
    if run.args.check == "kernel"
        && run
            .capability
            .value()
            .get("engine_preparation")
            .and_then(Value::as_str)
            == Some("named")
        && run
            .capability
            .section_record("kernel", "producer")
            .is_none()
    {
        return Err(failure(
            Status::Inappropriate,
            "Kernel replay needs its pinned unnamed producer; the installed main engine uses naming",
            "capability",
        ));
    }
    let binaries = route_binaries(run, route, &files);
    let paths: Vec<&Path> = binaries.iter().map(PathBuf::as_path).collect();
    run.verifier.start(&paths);
    let mut stages = super::models::ModelStages::new(run, &files)?;
    match route {
        "signed" => signed_pipeline(run, &source, &files, stages.as_mut()),
        "bundle" => {
            super::models::around(run, stages.as_mut(), "bundle", None, &mut |run, attempt| {
                bundle_pipeline(run, &source, attempt)
            })
        }
        _ => super::models::around(run, stages.as_mut(), "single", None, &mut |run, attempt| {
            single_pipeline(run, &source, attempt)
        }),
    }
}

/// The pinned files a run on `route` may execute, which it starts hashing once the input is routed (see
/// `PER_RUN`, before_execution).
fn route_binaries(run: &Run, route: &str, files: &[BundleFile]) -> Vec<PathBuf> {
    let check = run.args.check.as_str();
    let tstp = run.args.output == "tstp";
    let named = |section: &str, names: &[&str]| -> Vec<PathBuf> {
        names
            .iter()
            .filter_map(|name| run.capability.section_record(section, name))
            .map(|record| record.path)
            .collect()
    };
    let mut paths = match (route, check) {
        ("single", "kernel") => {
            let mut paths = vec![single_producer(run)];
            paths.extend(named("kernel", &["witness", "entry", "installation"]));
            paths
        }
        ("single", "none") => vec![run.binary("", "engine")],
        ("single", _) => vec![run.binary("", "engine"), run.binary("", "checker")],
        ("bundle", "none") => named("bundle", &["producer"]),
        ("signed", _) => vec![
            signed_producer(run, files).1,
            run.binary("signed", "checker"),
        ],
        (section, _) => named(section, &["producer", "checker"]),
    };
    if tstp && check == "compiled" {
        paths.extend(match route {
            "single" => named("tstp", &["exporter"]),
            "bundle" => named("tstp", &["bundle_exporter"]),
            _ => named("tstp", &["goal_exporter", "inputs_exporter"]),
        });
    }
    if check == "compiled" {
        paths.extend(named("model", &["producer", "checker"]));
        if tstp {
            paths.extend(named("model", &["exporter"]));
        }
    }
    paths
}

fn signed_producer(run: &Run, files: &[BundleFile]) -> (signed::Producer, PathBuf) {
    let Some(single) = run.capability.section_record("signed", "single_producer") else {
        return (
            signed::Producer::LegacyBundle,
            run.binary("signed", "producer"),
        );
    };
    if files.len() == 1 && !bundle::needs_bundle(&files[0].data) {
        (signed::Producer::NamedSingle, single.path)
    } else {
        (
            signed::Producer::CitedBundle,
            run.binary("signed", "producer"),
        )
    }
}

fn single_producer(run: &Run) -> PathBuf {
    if run.args.check == "kernel"
        && let Some(producer) = run.capability.section_record("kernel", "producer")
    {
        return producer.path;
    }
    run.binary("", "engine")
}

/// The suffix of a refutation pass's artifact names: none for pass 1, so a second pass never reuses a name.
pub fn pass_tag(attempt: u32) -> String {
    if attempt == 1 {
        String::new()
    } else {
        format!("-pass{attempt}")
    }
}

/// Single-file refutation: the engine's candidate, then the compiled checker or kernel replay.
fn single_pipeline(
    run: &mut Run,
    source: &Snapshot,
    attempt: u32,
) -> Result<(String, String), Fault> {
    let tag = pass_tag(attempt);
    let search_name = format!("search{tag}");
    let mut command = os([single_producer(run)]);
    command.extend(run.search_options());
    let output = run.stage(
        &search_name,
        &command,
        &run.root.join(&search_name),
        Some(source.argument()),
        Some(run.args.max_certificate_bytes),
    )?;
    let mut check = || run.supervisor.check_default();
    source.verify(&mut check)?;
    let record = record_object(&output);
    let (status, reason) =
        protocol::engine_outcome(&record, &output.stdout, &output.stderr, &read_back(source))
            .map_err(|error| contract(error, "search"))?;
    run.manifest.set("producer_outcome", status.as_str());
    if status != "candidate" {
        return Ok((status, reason));
    }
    let proof_name = format!("proof{tag}.fang");
    let certificate = Snapshot::create(&run.root.join(&proof_name), &output.stdout)?;
    let mut details = Object::new();
    details.set("bytes", Value::from(output.stdout.len() as u64));
    details.set("sha256", certificate.sha256.as_str());
    details.set("version", Value::from(8i64));
    details.set("preprocessing", LANGUAGE);
    details.set("accepted", false);
    details.set("file", proof_name.as_str());
    run.manifest.set("certificate", Value::Object(details));
    if run.args.check == "kernel" {
        let result = super::kernel::kernel_check(run, source, &certificate)?;
        run.confirm(&[source, &certificate], "checked")?;
        set_accepted(run);
        return Ok(result);
    }
    if run.args.check == "none" {
        run.unchecked(&[source, &certificate])?;
        return Ok(("Unsatisfiable".to_string(), NONE_REASON.to_string()));
    }
    let checker_name = format!("checker{tag}");
    let command = os([
        run.binary("", "checker").into_os_string(),
        source.argument().as_os_str().to_os_string(),
        certificate.argument().as_os_str().to_os_string(),
    ]);
    let output = run.stage(
        &checker_name,
        &command,
        &run.root.join(&checker_name),
        None,
        None,
    )?;
    let outcome =
        protocol::checker_outcome(&record_object(&output), &output.stdout, &output.stderr)
            .map_err(|error| contract(error, "checker"))?;
    let mut compiled = Object::new();
    compiled.set("outcome", outcome);
    compiled.set("accepted", outcome == "accepted");
    compiled.set("kernel_instance", false);
    compiled.set("trust", "Lean compiler, runtime and operating system");
    run.manifest.set("compiled_check", Value::Object(compiled));
    let (status, reason) = protocol::checked_status(outcome);
    if status != "Unsatisfiable" {
        return Err(failure(
            Status::from_name(status).unwrap_or(Status::Error),
            reason,
            "checker",
        ));
    }
    let mut check = || run.supervisor.check_default();
    source.verify(&mut check)?;
    certificate.verify(&mut check)?;
    let captured = run.read_regular(
        &run.root.join(&search_name).join("stdout"),
        run.args.max_certificate_bytes,
    )?;
    if captured != output_bytes_of(&certificate) {
        return Err(failure(
            Status::Error,
            "Captured producer certificate changed",
            "checker",
        ));
    }
    if run.args.output == "tstp" {
        let command = os([
            run.binary("tstp", "exporter").into_os_string(),
            source.argument().as_os_str().to_os_string(),
            certificate.argument().as_os_str().to_os_string(),
            run.input_name().into(),
        ]);
        run.export_document(
            &command,
            &format!("export{tag}"),
            &format!("solution{tag}.p"),
        )?;
        // The single-file exporter reads at most 1,000 statements; name that limit when it is the cause.
        let failed = run
            .manifest
            .get("export")
            .and_then(|record| record.get("state"))
            .and_then(Value::as_str)
            == Some("failed");
        if failed && signed::statements(&read_back(source)).len() > STATEMENT_LIMIT {
            run.manifest.set("export_note", STATEMENT_LIMIT_NOTE);
        }
    }
    run.confirm(&[source, &certificate], "checked")?;
    set_accepted(run);
    Ok((protocol::task_status(0, 1).to_string(), reason))
}

fn set_accepted(run: &mut Run) {
    if let Some(Value::Object(details)) = run.manifest.get_mut("certificate") {
        details.set("accepted", true);
    }
}

/// The bytes a snapshot holds, read back from its file.
fn read_back(snapshot: &Snapshot) -> Vec<u8> {
    std::fs::read(snapshot.argument()).unwrap_or_default()
}

fn output_bytes_of(snapshot: &Snapshot) -> Vec<u8> {
    read_back(snapshot)
}

pub fn record_object(output: &StageOutput) -> Object {
    output
        .record
        .to_json()
        .as_object()
        .cloned()
        .unwrap_or_default()
}

/// Producer reads the bundle; every listed file is then read once, sealed, hashed and passed to the checker.
fn bundle_pipeline(
    run: &mut Run,
    source: &Snapshot,
    attempt: u32,
) -> Result<(String, String), Fault> {
    let tag = pass_tag(attempt);
    let tptp_root = run
        .args
        .tptp_root
        .as_ref()
        .map(|root| std::path::absolute(root).unwrap_or_else(|_| root.clone()));
    run.manifest.set(
        "tptp_root",
        tptp_root
            .as_ref()
            .map(|root| Value::from(root.display().to_string()))
            .unwrap_or(Value::Null),
    );
    let search_name = format!("search{tag}");
    let mut command = os([run.binary("bundle", "producer")]);
    command.extend(run.search_options());
    command.push(
        std::path::absolute(&run.args.input)
            .unwrap_or_default()
            .into_os_string(),
    );
    if let Some(root) = &tptp_root {
        command.push("--tptp-root".into());
        command.push(root.clone().into_os_string());
    }
    let output = run.stage(
        &search_name,
        &command,
        &run.root.join(&search_name),
        None,
        Some(run.args.max_certificate_bytes),
    )?;
    let mut check = || run.supervisor.check_default();
    source.verify(&mut check)?;
    let outcome = bundle::producer_outcome(&record_object(&output), &output.stdout, &output.stderr)
        .map_err(|error| contract(error, "search"))?;
    let info = match outcome {
        bundle::Outcome::Status(status, reason) => {
            run.manifest.set("producer_outcome", status.as_str());
            return Ok((status, reason));
        }
        bundle::Outcome::Candidate(info) => info,
    };
    run.manifest.set("producer_outcome", "candidate");
    let places = bundle::locate(&info, &run.args.input, tptp_root.as_deref())
        .map_err(|error| contract(error, "search"))?;
    let source_data = read_back(source);
    let mut sealed: Vec<(String, String, PathBuf, Snapshot)> = Vec::new();
    let mut total = 0u64;
    let mut kept_source = None;
    for (index, (root_name, path, location)) in places.iter().enumerate() {
        let data = if index == 0 {
            source_data.clone()
        } else {
            run.read_regular(location, bundle::FILE_BYTES)?
        };
        total += data.len() as u64;
        if data.len() as u64 > bundle::FILE_BYTES || total > bundle::TOTAL_BYTES {
            return Err(failure(
                Status::ResourceOut,
                "Bundle file or total byte limit exceeded",
                "bundle-capture",
            ));
        }
        if index == 0 {
            kept_source = Some(data);
            continue;
        }
        let snapshot = Snapshot::create(&run.root.join(format!("bundle{tag}-{index}.p")), &data)?;
        sealed.push((root_name.clone(), path.clone(), location.clone(), snapshot));
    }
    let source_data = kept_source.unwrap_or_default();
    let mut triples: Vec<(&str, &str, &[u8])> = vec![(
        places[0].0.as_str(),
        places[0].1.as_str(),
        source_data.as_slice(),
    )];
    let sealed_data: Vec<Vec<u8>> = sealed
        .iter()
        .map(|(_, _, _, snapshot)| read_back(snapshot))
        .collect();
    for ((root_name, path, _, _), data) in sealed.iter().zip(&sealed_data) {
        triples.push((root_name, path, data));
    }
    let captured = bundle::digest(&triples);
    let mut files_record = Vec::new();
    let all: Vec<(&str, &str, &Path, &Snapshot)> = std::iter::once((
        places[0].0.as_str(),
        places[0].1.as_str(),
        places[0].2.as_path(),
        source,
    ))
    .chain(sealed.iter().map(|(root, path, location, snapshot)| {
        (root.as_str(), path.as_str(), location.as_path(), snapshot)
    }))
    .collect();
    for (index, (root_name, path, location, snapshot)) in all.iter().enumerate() {
        let mut row = Object::new();
        row.set("index", Value::from(index as u64));
        row.set("root", *root_name);
        row.set("path", *path);
        row.set("read_from", location.display().to_string());
        row.set("bytes", Value::from(read_back(snapshot).len() as u64));
        row.set("sha256", snapshot.sha256.as_str());
        files_record.push(Value::Object(row));
    }
    let mut details = Object::new();
    details.set("files", Value::Array(files_record));
    details.set("producer_digest", info.bundle_sha256.as_str());
    details.set("captured_digest", captured.as_str());
    details.set("digests_equal", captured == info.bundle_sha256);
    details.set("declarations", info.declarations.clone());
    details.set("objects", info.objects.clone());
    run.manifest.set("bundle", Value::Object(details));
    let proof_name = format!("proof{tag}.fang");
    let certificate = Snapshot::create(&run.root.join(&proof_name), &output.stdout)?;
    let mut cert = Object::new();
    cert.set("bytes", Value::from(output.stdout.len() as u64));
    cert.set("sha256", certificate.sha256.as_str());
    cert.set("version", Value::from(8i64));
    cert.set("preprocessing", LANGUAGE);
    cert.set("accepted", false);
    cert.set("file", proof_name.as_str());
    run.manifest.set("certificate", Value::Object(cert));
    let mut arguments: Vec<OsString> = Vec::new();
    for (root_name, path, _, snapshot) in &all {
        arguments.push((*root_name).into());
        arguments.push((*path).into());
        arguments.push(snapshot.argument().as_os_str().to_os_string());
    }
    let snapshots: Vec<&Snapshot> = all
        .iter()
        .map(|(_, _, _, snapshot)| *snapshot)
        .chain(std::iter::once(&certificate))
        .collect();
    if run.args.check == "none" {
        run.unchecked(&snapshots)?;
        return Ok(("Unsatisfiable".to_string(), NONE_REASON.to_string()));
    }
    let checker_name = format!("checker{tag}");
    let mut command = os([
        run.binary("bundle", "checker").into_os_string(),
        certificate.argument().as_os_str().to_os_string(),
    ]);
    command.extend(arguments.iter().cloned());
    let output = run.stage(
        &checker_name,
        &command,
        &run.root.join(&checker_name),
        None,
        None,
    )?;
    let outcome = bundle::checker_outcome(&record_object(&output), &output.stdout, &output.stderr)
        .map_err(|error| contract(error, "checker"))?;
    let mut compiled = Object::new();
    compiled.set("outcome", outcome);
    compiled.set("accepted", outcome == "accepted");
    compiled.set("kernel_instance", false);
    compiled.set("checker", "bundle");
    compiled.set("trust", "Lean compiler, runtime and operating system");
    run.manifest.set("compiled_check", Value::Object(compiled));
    let (status, reason) = protocol::checked_status(outcome);
    if status != "Unsatisfiable" {
        return Err(failure(
            Status::from_name(status).unwrap_or(Status::Error),
            reason.replace("version-8", "bundle"),
            "checker",
        ));
    }
    let mut check = || run.supervisor.check_default();
    for snapshot in &snapshots {
        snapshot.verify(&mut check)?;
    }
    let captured = run.read_regular(
        &run.root.join(&search_name).join("stdout"),
        run.args.max_certificate_bytes,
    )?;
    if captured != read_back(&certificate) {
        return Err(failure(
            Status::Error,
            "Captured producer certificate changed",
            "checker",
        ));
    }
    if run.args.output == "tstp" {
        let mut command = os([
            run.binary("tstp", "bundle_exporter").into_os_string(),
            certificate.argument().as_os_str().to_os_string(),
        ]);
        command.extend(arguments.iter().cloned());
        run.export_document(
            &command,
            &format!("export{tag}"),
            &format!("solution{tag}.p"),
        )?;
    }
    run.confirm(&snapshots, "checked")?;
    set_accepted(run);
    Ok((
        protocol::task_status(0, 1).to_string(),
        "The native bundle checker accepted the exact captured files and certificate".to_string(),
    ))
}

/// Signed tasks over the sealed bundle; statuses follow docs/DESIGN.md, "Status rules for conjectures". Every
/// file is sealed and hashed once and passed as ROOT PATH FILE triples to every producer and checker run. The
/// checker's own --goals listing decides the tasks; the whole command's limits cover all of them.
fn signed_pipeline(
    run: &mut Run,
    source: &Snapshot,
    files: &[BundleFile],
    stages: Option<&mut super::models::ModelStages>,
) -> Result<(String, String), Fault> {
    let result = signed_tasks(run, source, files, stages);
    match result {
        Err(Fault::Failure(error))
            if matches!(error.status, Status::Timeout | Status::MemoryOut) =>
        {
            Err(failure(
                Status::ResourceOut,
                format!(
                    "The command limits ran out before every signed task was accepted ({})",
                    error.status.name()
                ),
                &error.stage,
            ))
        }
        other => other,
    }
}

fn signed_tasks(
    run: &mut Run,
    source: &Snapshot,
    files: &[BundleFile],
    stages: Option<&mut super::models::ModelStages>,
) -> Result<(String, String), Fault> {
    let mut sealed: Vec<(String, String, Option<PathBuf>, Option<Snapshot>)> = Vec::new();
    for (index, file) in files.iter().enumerate() {
        let snapshot = if index == 0 {
            None
        } else {
            Some(Snapshot::create(
                &run.root.join(format!("signed-{index}.p")),
                &file.data,
            )?)
        };
        sealed.push((
            file.root.clone(),
            file.path.clone(),
            file.location.clone(),
            snapshot,
        ));
    }
    let snapshot_of = |entry: &(String, String, Option<PathBuf>, Option<Snapshot>)| -> PathBuf {
        entry.3.as_ref().map_or_else(
            || source.argument().to_path_buf(),
            |snapshot| snapshot.argument().to_path_buf(),
        )
    };
    let mut triples: Vec<OsString> = Vec::new();
    for entry in &sealed {
        triples.push(entry.0.clone().into());
        triples.push(entry.1.clone().into());
        triples.push(snapshot_of(entry).into_os_string());
    }
    let caller = std::path::absolute(&run.args.input).unwrap_or_default();
    let mut rows = Vec::new();
    for (index, entry) in sealed.iter().enumerate() {
        let data = &files[index].data;
        let mut row = Object::new();
        row.set("index", Value::from(index as u64));
        row.set("root", entry.0.as_str());
        row.set("path", entry.1.as_str());
        row.set(
            "read_from",
            entry
                .2
                .clone()
                .unwrap_or_else(|| caller.clone())
                .display()
                .to_string(),
        );
        row.set("bytes", Value::from(data.len() as u64));
        row.set("sha256", fang_hash::sha256_hex(data));
        rows.push(Value::Object(row));
    }
    let mut record = Object::new();
    record.set("files", Value::Array(rows));
    record.set("tasks", Value::Array(Vec::new()));
    run.manifest.set("signed", Value::Object(record));
    let checker = run.binary("signed", "checker");
    let (producer_kind, producer) = signed_producer(run, files);
    let mut command = os([checker.clone().into_os_string(), "--goals".into()]);
    command.extend(triples.iter().cloned());
    let output = run.stage("goals", &command, &run.root.join("goals"), None, None)?;
    let listed = match signed::listing(&record_object(&output), &output.stdout, &output.stderr)
        .map_err(|error| contract(error, "goals"))?
    {
        Listing::Rejected(status) => {
            let diagnostic = ascii_text(&output.stderr);
            let diagnostic = python_strip(&diagnostic);
            return Ok((
                status,
                format!("The signed checker rejected the bundle while listing goals: {diagnostic}"),
            ));
        }
        Listing::Listed(items) => items,
    };
    if let Some(Value::Object(signed)) = run.manifest.get_mut("signed") {
        signed.set(
            "listing",
            Value::Array(
                listed
                    .iter()
                    .map(|(file, statement)| {
                        Value::Array(vec![Value::from(*file), Value::from(*statement)])
                    })
                    .collect(),
            ),
        );
    }
    let single_file = sealed.len() == 1;
    let has_objects = files.first().is_some_and(|file| file.data.contains(&b'"'));
    let mut refute = |run: &mut Run, attempt: u32| -> Result<(String, String), Fault> {
        signed_attempt(
            run,
            source,
            &sealed,
            &triples,
            &listed,
            &producer,
            producer_kind,
            &checker,
            attempt,
            single_file,
            has_objects,
        )
    };
    super::models::around(run, stages, "signed", Some(&listed), &mut refute)
}

#[allow(clippy::too_many_arguments)]
fn signed_attempt(
    run: &mut Run,
    source: &Snapshot,
    sealed: &[(String, String, Option<PathBuf>, Option<Snapshot>)],
    triples: &[OsString],
    listed: &[Item],
    producer: &Path,
    producer_kind: signed::Producer,
    checker: &Path,
    attempt: u32,
    single_file: bool,
    has_objects: bool,
) -> Result<(String, String), Fault> {
    let tag = pass_tag(attempt);
    let tasks: Vec<Option<u64>> = if listed.is_empty() {
        vec![None]
    } else {
        (0..listed.len() as u64).map(Some).collect()
    };
    let mut outcomes: Vec<Checked> = Vec::new();
    let mut produced: Vec<Snapshot> = Vec::new();
    for task in tasks {
        let label = format!(
            "{}{tag}",
            task.map_or_else(|| "inputs".to_string(), |index| format!("goal-{index}"))
        );
        let selection: Vec<OsString> = match task {
            None => os(["--inputs"]),
            Some(index) => os(["--goal".to_string(), index.to_string()]),
        };
        let mut command = os([producer.as_os_str().to_os_string()]);
        command.extend(run.search_options());
        command.extend(selection.iter().cloned());
        let stdin = if producer_kind == signed::Producer::NamedSingle {
            Some(source.argument())
        } else {
            command.extend(triples.iter().cloned());
            None
        };
        let produce = format!("produce-{label}");
        let output = run.stage(
            &produce,
            &command,
            &run.root.join(&produce),
            stdin,
            Some(run.args.max_certificate_bytes),
        )?;
        let outcome = signed::producer_outcome_for(
            &record_object(&output),
            &output.stdout,
            &output.stderr,
            producer_kind,
        )
        .map_err(|error| contract(error, &produce))?;
        let mut entry = Object::new();
        entry.set("task", label.as_str());
        entry.set("producer", outcome);
        if outcome != "candidate" {
            push_task(run, entry);
            outcomes.push(Checked::Rejected(outcome.to_string()));
            break;
        }
        let certificate = Snapshot::create(
            &run.root.join(format!("proof-{label}.fang")),
            &output.stdout,
        )?;
        entry.set("certificate_sha256", certificate.sha256.as_str());
        if run.args.check == "none" {
            // The checker listed the goals; no checker runs on the candidate.
            entry.set("checker", "not run (--check none)");
            push_task(run, entry);
            outcomes.push(match task {
                None => Checked::Inputs,
                Some(index) => Checked::Goal(listed[index as usize]),
            });
            produced.push(certificate);
            continue;
        }
        let check_name = format!("check-{label}");
        let mut command = os([checker.as_os_str().to_os_string()]);
        command.extend(selection.iter().cloned());
        command.push(certificate.argument().as_os_str().to_os_string());
        command.extend(triples.iter().cloned());
        let output = run.stage(
            &check_name,
            &command,
            &run.root.join(&check_name),
            None,
            None,
        )?;
        let record = record_object(&output);
        let result = match signed::accepted(&record, &output.stdout, &output.stderr, task)
            .map_err(|error| contract(error, &check_name))?
        {
            Some(checked) => checked,
            None => {
                let code =
                    protocol::normal(&record).map_err(|error| contract(error, &check_name))?;
                Checked::Rejected(
                    signed::rejection(code, &output.stdout, &output.stderr, false)
                        .map_err(|error| contract(error, &check_name))?,
                )
            }
        };
        entry.set(
            "checker",
            match &result {
                Checked::Goal((file, statement)) => {
                    Value::Array(vec![Value::from(*file), Value::from(*statement)])
                }
                Checked::Inputs => Value::from(true),
                Checked::Rejected(status) => Value::from(status.as_str()),
            },
        );
        push_task(run, entry);
        let rejected = matches!(result, Checked::Rejected(_));
        outcomes.push(result);
        produced.push(certificate);
        if rejected {
            break;
        }
    }
    let status = signed::final_status(listed, &outcomes);
    if let Some(Value::Object(signed)) = run.manifest.get_mut("signed") {
        signed.set(
            "status_rule",
            "docs/DESIGN.md, Status rules for conjectures",
        );
    }
    let mut all: Vec<&Snapshot> = vec![source];
    all.extend(sealed.iter().filter_map(|entry| entry.3.as_ref()));
    all.extend(produced.iter());
    if (status == "Theorem" || status == "Unsatisfiable") && run.args.check == "none" {
        run.unchecked(&all)?;
        return Ok((status, NONE_REASON.to_string()));
    }
    if status == "Theorem" || status == "Unsatisfiable" {
        let mut check = || run.supervisor.check_default();
        for snapshot in &all {
            snapshot.verify(&mut check)?;
        }
        if run.args.output == "tstp" {
            signed_documents(
                run,
                source,
                &produced,
                listed,
                &status,
                single_file,
                has_objects,
                &tag,
            )?;
        }
        run.confirm(&all, "checked")?;
        let reason = if status == "Theorem" {
            "The signed checker accepted a certificate for every listed conjecture"
        } else {
            "No conjecture is selected and the signed checker accepted the inputs certificate"
        };
        return Ok((status, reason.to_string()));
    }
    let listed_outcomes: Vec<String> = outcomes
        .iter()
        .map(|outcome| match outcome {
            Checked::Goal((file, statement)) => format!("({file}, {statement})"),
            Checked::Inputs => "True".to_string(),
            Checked::Rejected(status) => status.clone(),
        })
        .collect();
    Ok((
        status,
        format!(
            "Not every signed task was accepted: {}",
            listed_outcomes.join(", ")
        ),
    ))
}

fn push_task(run: &mut Run, entry: Object) {
    if let Some(Value::Object(signed)) = run.manifest.get_mut("signed")
        && let Some(Value::Array(tasks)) = signed.get_mut("tasks")
    {
        tasks.push(Value::Object(entry));
    }
}

/// The documents of a signed result, when an installed exporter covers it: one per proved conjecture of a
/// single file without distinct objects, or the inputs task of such a file when the conjecture exporter has an
/// inputs mode. Anything else keeps the status and gets one note.
#[allow(clippy::too_many_arguments)]
fn signed_documents(
    run: &mut Run,
    source: &Snapshot,
    produced: &[Snapshot],
    listed: &[Item],
    status: &str,
    single_file: bool,
    has_objects: bool,
    tag: &str,
) -> Result<(), Fault> {
    let name = run.input_name();
    let not_covered = |run: &mut Run, note: &str| {
        let mut record = Object::new();
        record.set("file_name", name.as_str());
        record.set("state", "not-covered");
        run.manifest.set("export", Value::Object(record));
        run.manifest.set("export_note", note);
    };
    if !single_file {
        not_covered(run, SIGNED_TSTP_SCOPE);
        return Ok(());
    }
    if has_objects {
        not_covered(run, OBJECT_TSTP_SCOPE);
        return Ok(());
    }
    if status == "Theorem" && produced.len() == listed.len() {
        let exporter = run.binary("tstp", "goal_exporter");
        let mut records = Vec::new();
        for (index, certificate) in produced.iter().enumerate() {
            let command = os([
                exporter.clone().into_os_string(),
                source.argument().as_os_str().to_os_string(),
                certificate.argument().as_os_str().to_os_string(),
                index.to_string().into(),
                name.clone().into(),
            ]);
            run.export_document(
                &command,
                &format!("export-goal-{index}{tag}"),
                &format!("solution-goal-{index}{tag}.p"),
            )?;
            let mut row = run
                .manifest
                .get("export")
                .and_then(Value::as_object)
                .cloned()
                .unwrap_or_default();
            row.set("goal", Value::from(index as u64));
            let state = row.get("state").and_then(Value::as_str).map(str::to_string);
            records.push(Value::Object(row));
            if state.as_deref() != Some("document") {
                let mut record = Object::new();
                record.set("file_name", name.as_str());
                record.set("state", state.map(Value::from).unwrap_or(Value::Null));
                record.set("goals", Value::Array(records));
                run.manifest.set("export", Value::Object(record));
                return Ok(());
            }
        }
        let mut record = Object::new();
        record.set("file_name", name.as_str());
        record.set("state", "documents");
        record.set("documents", Value::Array(records));
        run.manifest.set("export", Value::Object(record));
        return Ok(());
    }
    if status == "Unsatisfiable"
        && produced.len() == 1
        && let Some(exporter) = run.capability.section_record("tstp", "inputs_exporter")
    {
        let command = os([
            exporter.path.into_os_string(),
            "--inputs".into(),
            source.argument().as_os_str().to_os_string(),
            produced[0].argument().as_os_str().to_os_string(),
            name.clone().into(),
        ]);
        return run.export_document(
            &command,
            &format!("export-inputs{tag}"),
            &format!("solution-inputs{tag}.p"),
        );
    }
    not_covered(run, SIGNED_TSTP_SCOPE);
    Ok(())
}

/// The status block: the profile line, the mode line, an optional capability note, the status line and the
/// documents of a positive result.
pub fn output_bytes(manifest: &Object, status: &str, documents: &[Vec<u8>]) -> Vec<u8> {
    let path_key = manifest.get("path").and_then(Value::as_str).unwrap_or("");
    let path = PATHS
        .iter()
        .find(|(key, _)| *key == path_key)
        .map(|(_, text)| *text)
        .unwrap_or("not chosen");
    let check = manifest
        .get("check")
        .and_then(Value::as_str)
        .unwrap_or(DEFAULT_CHECK);
    let chosen = if manifest.get("check_source").and_then(Value::as_str) == Some("default") {
        "default mode".to_string()
    } else {
        format!("--check {check}")
    };
    let model = manifest
        .get("model_check")
        .and_then(|record| record.get("accepted"))
        .and_then(Value::as_bool)
        .unwrap_or(false);
    let mode = if model {
        super::models::MODE
    } else {
        mode_text(check)
    };
    let problem = manifest
        .get("problem_id")
        .and_then(Value::as_str)
        .unwrap_or("fang_unavailable");
    let mut lines = vec![
        format!("% Fang profile: v8, {path}"),
        format!("% fang: {mode} ({chosen}; {})", trust_text(check)),
    ];
    if manifest.get("stage").and_then(Value::as_str) == Some("capability") {
        lines.push(format!(
            "% Fang: {}",
            manifest
                .get("reason")
                .and_then(Value::as_str)
                .unwrap_or_default()
        ));
    }
    lines.push(format!("% SZS status {status} for {problem}"));
    let mut output = ascii(&(lines.join("\n") + "\n"));
    if POSITIVE.contains(&status) && !documents.is_empty() {
        let kind = if model {
            "FiniteModel"
        } else {
            "CNFRefutation"
        };
        for text in documents {
            output.extend(ascii(&format!("% SZS output start {kind} for {problem}\n")));
            output.extend_from_slice(text);
            output.extend(ascii(&format!("% SZS output end {kind} for {problem}\n")));
        }
    }
    output
}

/// Python's encode("ascii", errors="replace").
fn ascii(text: &str) -> Vec<u8> {
    text.chars()
        .map(|character| {
            if character.is_ascii() {
                character as u8
            } else {
                b'?'
            }
        })
        .collect()
}

/// The exported document bytes, checked against the run record, or none with a note.
pub fn read_documents(run: &mut Run) -> Vec<Vec<u8>> {
    let record = run
        .manifest
        .get("export")
        .and_then(Value::as_object)
        .cloned()
        .unwrap_or_default();
    let state = record.get("state").and_then(Value::as_str).unwrap_or("");
    if state != "document" && state != "documents" {
        return Vec::new();
    }
    let rows: Vec<Object> = if state == "documents" {
        record
            .get("documents")
            .and_then(Value::as_array)
            .map(|rows| {
                rows.iter()
                    .filter_map(|row| row.as_object().cloned())
                    .collect()
            })
            .unwrap_or_default()
    } else {
        vec![record.clone()]
    };
    let mut texts = Vec::new();
    for row in &rows {
        let path = row.get("path").and_then(Value::as_str).unwrap_or_default();
        let expected = row
            .get("sha256")
            .and_then(Value::as_str)
            .unwrap_or_default();
        match run.read_regular(Path::new(path), run.args.max_solution_bytes) {
            Ok(text) if fang_hash::sha256_hex(&text) == expected => texts.push(text),
            _ => {
                if let Some(Value::Object(export)) = run.manifest.get_mut("export") {
                    export.set("state", "unreadable");
                }
                run.manifest.set(
                    "export_note",
                    "TSTP document could not be read back; no document printed",
                );
                return Vec::new();
            }
        }
    }
    texts
}

/// The identity of a file for the record, as an integer list.
pub fn identity_value(path: &Path) -> Value {
    match std::fs::symlink_metadata(path) {
        Ok(metadata) => Value::Array(vec![
            Value::from(metadata.dev()),
            Value::from(metadata.ino()),
            Value::from(metadata.size()),
        ]),
        Err(_) => Value::Null,
    }
}

/// The checking mode's model-step memory bound.
pub fn model_limit(run: &Run) -> u64 {
    run.args.max_certificate_bytes.min(MAX_MODEL_BYTES)
}

/// The limits of a run, from its arguments.
pub fn limits(args: &Args) -> Limits {
    Limits {
        wall_seconds: args.wall_seconds,
        memory_mib: args.memory_mib,
        input_bytes: args.max_input_bytes,
        certificate_bytes: args.max_certificate_bytes,
        log_bytes: args.max_log_bytes,
        artifact_bytes: args.max_artifact_bytes,
        ..Limits::default()
    }
}

/// Whether the installed capability names this path for `section`.`name`.
pub fn installed(capability: &Capability, section: &str, name: &str) -> bool {
    capability::Capability::section_record(capability, section, name).is_some()
}
