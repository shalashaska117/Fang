// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Bounded local version-8 kernel entry for expanded CNF/FOF input, revision 8: the port of
//! entry/main.py, with check.py and the tree inventory run in the same guarded worker.
//!
//! Revision 8 is installed, not run from a development tree: installation.json in the directory
//! above this executable is written by the installer and names the installation root, the
//! output root, HOME, this executable and its SHA-256, the toolchain, the built lean-v8 project,
//! the helper objects, the recorded Lean environment and the tree manifests. The policy beside it
//! pins the sources the executable was built from and carries the reviews as pin data: no
//! receipt is read at run time. The policy also pins the Lean release (its lean and lake
//! binaries and the summary of its lib/ directory), and the entry refuses an installation that
//! records others, or an executable whose bytes differ from the installation record. No stage
//! starts before a refusal, ReviewPending included. For an output directory under /mnt/c,
//! `case_sensitive` runs wslpath and fsutil.exe once, unsupervised, before the review checks.
//! The entry accepts its own review only if the review's pin data names this policy as it was
//! before the review slot was filled.
//!
//! The command runs as two processes (fang-supervisor's guard). On SIGTERM the outer process
//! exits with status 143 and the worker writes the manifest with status Forced before it ends.

use std::ffi::OsString;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use fang_json::{Number, Object, ParseLimits, Value};
use fang_supervisor::guard::Worker;
use fang_supervisor::{Fault, Limits, Snapshot, Supervisor};

use crate::check;
use crate::install::{ENTRY_BINARY, INSTALLATION_SCHEMA, POLICY_SCHEMA};
use crate::internal;
use crate::util::{manifest_bytes, resolve, utc_now};

pub const SCHEMA: &str = "fang-v8-equality-kernel-entry-v3";
const CAPS: [(&str, u64, &str); 3] = [
    ("input", 4096, "input.p"),
    ("certificate", 65536, "proof.fang"),
    ("witness", 16 << 20, "witness.json"),
];
const EXPECTED_AUDITS: [&str; 2] = [
    "EqInstance.actual_sealed_acceptance",
    "EqInstance.actual_original_bytes_unsat",
];

/// The entry statuses and their exit codes; SIGTERM ends the outer process with 143.
pub fn exit_code(status: &str) -> i32 {
    match status {
        "KernelChecked" => 0,
        "Rejected" => 3,
        "ReviewPending" => 4,
        "ResourceOut" => 5,
        "Timeout" => 7,
        "MemoryOut" => 8,
        "Forced" => 9,
        _ => 6,
    }
}

/// A refusal of the run, with the entry status it gives.
struct Stop {
    status: &'static str,
    error: String,
    kind: &'static str,
}

impl Stop {
    fn error(message: impl Into<String>) -> Stop {
        Stop {
            status: "Error",
            error: message.into(),
            kind: "ValueError",
        }
    }

    fn review(message: impl Into<String>) -> Stop {
        Stop {
            status: "ReviewPending",
            error: message.into(),
            kind: "Failure",
        }
    }
}

impl From<Fault> for Stop {
    fn from(fault: Fault) -> Stop {
        let stopped = check::Stopped::from(fault);
        Stop {
            status: stopped.class,
            error: stopped.error,
            kind: "Failure",
        }
    }
}

impl From<fang_supervisor::Failure> for Stop {
    fn from(failure: fang_supervisor::Failure) -> Stop {
        Stop::from(Fault::Failure(failure))
    }
}

fn require(condition: bool, message: &str) -> Result<(), Stop> {
    if condition {
        Ok(())
    } else {
        Err(Stop::error(message))
    }
}

/// Bootstrap read: a regular file, no symbolic link, at most `cap` bytes.
fn bootstrap_read(path: &Path, cap: u64) -> Result<Vec<u8>, String> {
    fang_supervisor::read_regular(path, cap, &mut || Ok(()))
        .map_err(|fault| format!("{}: {}", path.display(), fault.python_str()))
}

fn parse(data: &[u8]) -> Result<Value, String> {
    fang_json::parse(
        data,
        &ParseLimits {
            max_bytes: 64 << 20,
            max_depth: 64,
        },
    )
    .map_err(|error| error.python_message(data))
}

/// The version-8 library has case-only module pairs: make a new /mnt/c output case-sensitive
/// (when `windows` is set) and prove that the directory keeps such pairs apart.
pub fn case_sensitive(directory: &Path, windows: bool) -> Result<(), String> {
    if windows && directory.starts_with("/mnt/c/") {
        let output = Command::new("/usr/bin/wslpath")
            .arg("-w")
            .arg(directory)
            .stdin(Stdio::null())
            .output()
            .map_err(|error| format!("wslpath: {error}"))?;
        if !output.status.success() {
            return Err("wslpath failed".to_owned());
        }
        let windows_path = String::from_utf8_lossy(&output.stdout).trim().to_owned();
        let mut child = Command::new("/mnt/c/Windows/System32/fsutil.exe")
            .args(["file", "setCaseSensitiveInfo", &windows_path, "enable"])
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .map_err(|error| format!("fsutil.exe: {error}"))?;
        let deadline = Instant::now() + Duration::from_secs(60);
        loop {
            if child
                .try_wait()
                .map_err(|error| error.to_string())?
                .is_some()
            {
                break;
            }
            if Instant::now() >= deadline {
                let _ = child.kill();
                let _ = child.wait();
                return Err("fsutil.exe did not finish within 60 seconds".to_owned());
            }
            std::thread::sleep(Duration::from_millis(20));
        }
    }
    let (lower, upper) = (directory.join("case-probe"), directory.join("CASE-PROBE"));
    fs::write(&lower, b"lower").map_err(|error| error.to_string())?;
    fs::write(&upper, b"upper").map_err(|error| error.to_string())?;
    let distinct = fs::read(&lower).ok().as_deref() == Some(b"lower".as_slice())
        && fs::read(&upper).ok().as_deref() == Some(b"upper".as_slice());
    let _ = fs::remove_file(&lower);
    if upper.exists() {
        let _ = fs::remove_file(&upper);
    }
    if distinct {
        Ok(())
    } else {
        Err("Output directory is not case-sensitive".to_owned())
    }
}

struct Arguments {
    input: PathBuf,
    certificate: PathBuf,
    witness: PathBuf,
    out: PathBuf,
}

fn arguments(raw: &[OsString]) -> Result<Arguments, String> {
    let mut values: Vec<(String, PathBuf)> = Vec::new();
    let mut index = 1;
    while index < raw.len() {
        let flag = raw[index].to_string_lossy().into_owned();
        let Some(value) = raw.get(index + 1) else {
            return Err(format!("argument {flag}: expected one argument"));
        };
        if !["--input", "--certificate", "--witness", "--out"].contains(&flag.as_str())
            || values.iter().any(|(existing, _)| *existing == flag)
        {
            return Err(format!("unrecognized arguments: {flag}"));
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
    match (
        take("--input"),
        take("--certificate"),
        take("--witness"),
        take("--out"),
    ) {
        (Some(input), Some(certificate), Some(witness), Some(out)) => Ok(Arguments {
            input,
            certificate,
            witness,
            out,
        }),
        _ => Err(
            "the following arguments are required: --input, --certificate, --witness, --out"
                .to_owned(),
        ),
    }
}

/// `check_child`: the proof record must be a complete pass over exactly the sealed bytes.
fn check_proof(record: &Object, sealed: &Object) -> Result<(), Stop> {
    let get = |key: &str| record.get(key);
    require(
        get("status").and_then(Value::as_str) == Some("kernel-bundle-passed"),
        "Kernel stage did not pass",
    )?;
    require(
        matches!(get("archive_hashes_verified"), Some(Value::Bool(true))),
        "Kernel archive differs",
    )?;
    require(
        get("sealed_sha256") == Some(&Value::Object(sealed.clone())),
        "Kernel receipt detached from sealed bytes",
    )?;
    let audits = get("axiom_audits")
        .and_then(Value::as_object)
        .ok_or_else(|| Stop::error("Missing exact endpoint audit"))?;
    let endpoint: Vec<&str> = audits
        .get("EqInstanceFixedAudit")
        .and_then(Value::as_object)
        .map(|item| item.keys().collect())
        .unwrap_or_default();
    let mut endpoint_sorted = endpoint.clone();
    endpoint_sorted.sort_unstable();
    let mut expected = EXPECTED_AUDITS.to_vec();
    expected.sort_unstable();
    require(endpoint_sorted == expected, "Missing exact endpoint audit")?;
    let modules = get("modules").and_then(Value::as_u64).unwrap_or(0);
    let audit_count = get("audits").and_then(Value::as_u64).unwrap_or(0);
    require(modules > 0 && audit_count >= 2, "Empty proof result")?;
    let phases: Vec<String> = get("phases")
        .and_then(Value::as_array)
        .map(|phases| {
            phases
                .iter()
                .flat_map(|phase| phase.as_array().cloned().unwrap_or_default())
                .filter_map(|name| name.as_str().map(str::to_owned))
                .collect()
        })
        .unwrap_or_default();
    let mut unique = phases.clone();
    unique.sort();
    unique.dedup();
    require(
        !phases.is_empty() && unique.len() == phases.len(),
        "Invalid phase schedule",
    )?;
    require(modules == phases.len() as u64, "Module count differs")?;
    let total: usize = audits
        .values()
        .map(|item| item.as_object().map_or(0, Object::len))
        .sum();
    require(audit_count == total as u64, "Audit count differs")?;
    let order: Vec<String> = get("module_order")
        .and_then(Value::as_array)
        .map(|items| {
            items
                .iter()
                .filter_map(Value::as_str)
                .map(str::to_owned)
                .collect()
        })
        .unwrap_or_default();
    require(phases == order, "Detached module schedule")?;
    let stages: Vec<&Value> = get("stages")
        .and_then(Value::as_array)
        .map(|items| items.iter().collect())
        .unwrap_or_default();
    let stage_names: Vec<String> = stages
        .iter()
        .filter_map(|stage| stage.get("stage").and_then(Value::as_str))
        .map(str::to_owned)
        .collect();
    require(stage_names == phases, "Incomplete proof stages")?;
    require(
        phases.last().map(String::as_str) == Some("EqInstanceFixedAudit"),
        "Final endpoint is not last",
    )?;
    let successful = stages.iter().all(|stage| {
        stage.get("classification").and_then(Value::as_str) == Some("completed")
            && stage.get("exit_code").and_then(Value::as_i64) == Some(0)
    });
    require(successful, "Unsuccessful proof stage")?;
    let mut limits = Object::new();
    limits.set("phase_seconds", 60u64);
    limits.set("sampled_tree_rss_mib", 4096u64);
    limits.set("checking_seconds", 600u64);
    require(
        get("limits") == Some(&Value::Object(limits)),
        "Proof guards differ",
    )
}

/// The tree inventory: recompute the recorded trees and write `directory/manifest.json`.
fn inventory(
    supervisor: &mut Supervisor,
    installation: &Value,
    installation_data: &[u8],
    directory: &Path,
    launcher: &Path,
) -> Result<bool, Stop> {
    supervisor.check("inventory", 0.15)?;
    fs::create_dir(directory)
        .map_err(|error| Stop::error(format!("{}: {error}", directory.display())))?;
    let started = utc_now();
    let path = installation
        .get("trees")
        .and_then(|item| item.get("path"))
        .and_then(Value::as_str)
        .ok_or_else(|| Stop::error("No tree record"))?;
    let data = fang_supervisor::read_regular(Path::new(path), 256 << 20, &mut || {
        supervisor.check("inventory", 0.15)
    })?;
    let pinned = installation
        .get("trees")
        .and_then(|item| item.get("sha256"))
        .and_then(Value::as_str)
        .ok_or_else(|| Stop::error("No tree record digest"))?;
    let capture = Snapshot::create(&directory.join("trees.json"), &data)?;
    drop(data);
    let launcher_pin = installation
        .get("entry")
        .and_then(|entry| entry.get("sha256"))
        .and_then(Value::as_str)
        .ok_or_else(|| Stop::error("No entry digest"))?;
    let check_launcher = |supervisor: &Supervisor| -> Result<(), Stop> {
        require(
            fang_hash::sha256_hex(&fang_supervisor::read_regular(
                launcher,
                1 << 30,
                &mut || supervisor.check("inventory", 0.15),
            )?) == launcher_pin,
            "Inventory executable differs from its installation record",
        )
    };
    check_launcher(supervisor)?;
    let command = [
        launcher.as_os_str().to_owned(),
        OsString::from(internal::INVENTORY),
        capture.path.as_os_str().to_owned(),
        OsString::from(pinned),
    ];
    let scanned = internal::supervised(
        supervisor,
        &command,
        "inventory",
        &directory.join("scan"),
        directory,
    )?;
    check_launcher(supervisor)?;
    capture.verify(&mut || supervisor.check("inventory", 0.15))?;
    let unchanged = scanned
        .get("unchanged")
        .and_then(Value::as_bool)
        .ok_or_else(|| Stop::error("Invalid inventory result"))?;
    let totals = scanned
        .get("totals")
        .cloned()
        .ok_or_else(|| Stop::error("Missing inventory totals"))?;
    let differences = scanned
        .get("differences")
        .cloned()
        .ok_or_else(|| Stop::error("Missing inventory differences"))?;
    supervisor.check("inventory", 0.15)?;
    let mut report = Object::new();
    report.set("schema", "fang-v8-kernel-trees-v2");
    report.set("status", if unchanged { "unchanged" } else { "changed" });
    report.set("started_utc", started);
    report.set("finished_utc", utc_now());
    report.set(
        "installation_sha256",
        fang_hash::sha256_hex(installation_data),
    );
    report.set("trees", totals);
    report.set("differences", differences);
    if let Some(stage) = supervisor.records.last() {
        report.set("stage", stage.to_json());
    }
    let bytes = manifest_bytes(&Value::Object(report)).map_err(Stop::error)?;
    fs::write(directory.join("manifest.json"), bytes)
        .map_err(|error| Stop::error(error.to_string()))?;
    Ok(unchanged)
}

/// The tree inventory for tools outside the entry, such as the gate: recompute the recorded
/// trees and write `directory/manifest.json`; whether every tree is unchanged.
pub fn trees_unchanged(
    installation: &Value,
    installation_data: &[u8],
    directory: &Path,
) -> Result<bool, String> {
    let mut supervisor = Supervisor::new(
        Limits {
            wall_seconds: 600.0,
            memory_mib: 4096,
            log_bytes: 8 << 20,
            artifact_bytes: 1 << 30,
            ..Limits::default()
        },
        None,
    )
    .map_err(|failure| failure.reason)?;
    let launcher = installation
        .get("entry")
        .and_then(|entry| entry.get("path"))
        .and_then(Value::as_str)
        .ok_or("No entry path")?;
    inventory(
        &mut supervisor,
        installation,
        installation_data,
        directory,
        Path::new(launcher),
    )
    .map_err(|stop| stop.error)
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

fn float(value: f64) -> Value {
    Value::Number(Number::Float(value))
}

struct Run {
    out: PathBuf,
    root: PathBuf,
    installation: Value,
    installation_data: Vec<u8>,
    started: Instant,
}

#[allow(clippy::too_many_lines)]
fn run(
    arguments: &Arguments,
    context: &Run,
    report: &Arc<Mutex<Object>>,
    worker: &Worker,
    snapshots: &mut Vec<Snapshot>,
) -> Result<(), Stop> {
    let out = &context.out;
    let capture = out.join("capture");
    let installation = &context.installation;
    let policy_data =
        bootstrap_read(&context.root.join("policy.json"), 2 << 20).map_err(Stop::error)?;
    let policy = parse(&policy_data).map_err(Stop::error)?;
    require(
        policy.get("schema").and_then(Value::as_str) == Some(POLICY_SCHEMA),
        "Unknown policy",
    )?;
    require(
        installation.get("schema").and_then(Value::as_str) == Some(INSTALLATION_SCHEMA),
        "Unknown installation record",
    )?;
    require(
        installation.get("policy_sha256").and_then(Value::as_str)
            == Some(fang_hash::sha256_hex(&policy_data).as_str()),
        "Policy differs from the installation record",
    )?;
    fs::write(capture.join("policy.json"), &policy_data)
        .map_err(|error| Stop::error(error.to_string()))?;
    fs::write(
        capture.join("installation.json"),
        &context.installation_data,
    )
    .map_err(|error| Stop::error(error.to_string()))?;
    let mut supervisor = Supervisor::new(
        Limits {
            wall_seconds: 600.0,
            memory_mib: 4096,
            log_bytes: 8 << 20,
            artifact_bytes: 1 << 30,
            ..Limits::default()
        },
        Some(context.started),
    )?;
    supervisor.set_cancel_token(worker.cancel_token());
    let result = supervised(
        arguments,
        context,
        report,
        snapshots,
        &mut supervisor,
        &policy_data,
        &policy,
    );
    set(report, "peak_kib", supervisor.peak_kib);
    result
}

#[allow(clippy::too_many_lines, clippy::too_many_arguments)]
fn supervised(
    arguments: &Arguments,
    context: &Run,
    report: &Arc<Mutex<Object>>,
    snapshots: &mut Vec<Snapshot>,
    supervisor: &mut Supervisor,
    policy_data: &[u8],
    policy: &Value,
) -> Result<(), Stop> {
    let out = &context.out;
    let capture = out.join("capture");
    let installation = &context.installation;
    let read = |supervisor: &Supervisor, path: &Path, cap: u64| -> Result<Vec<u8>, Stop> {
        Ok(fang_supervisor::read_regular(path, cap, &mut || {
            supervisor.check("adapter", 0.15)
        })?)
    };
    // This executable: the installed copy the record names, with the recorded bytes; a pinned copy
    // in the capture runs the compiler launches.
    let executable = std::env::current_exe().map_err(|error| Stop::error(error.to_string()))?;
    let recorded_entry = installation
        .get("entry")
        .and_then(|item| item.get("path"))
        .and_then(Value::as_str)
        .unwrap_or_default();
    let recorded_sha = installation
        .get("entry")
        .and_then(|item| item.get("sha256"))
        .and_then(Value::as_str)
        .unwrap_or_default()
        .to_owned();
    require(
        executable == Path::new(recorded_entry)
            && executable == context.root.join("bin").join(ENTRY_BINARY),
        "Entry executable is not the installed copy",
    )?;
    let binary = read(supervisor, &executable, 1 << 30)?;
    require(
        fang_hash::sha256_hex(&binary) == recorded_sha,
        "Entry executable differs from its installation record",
    )?;
    let launcher = capture.join("bin").join(ENTRY_BINARY);
    fs::create_dir_all(capture.join("bin")).map_err(|error| Stop::error(error.to_string()))?;
    fs::write(&launcher, &binary).map_err(|error| Stop::error(error.to_string()))?;
    fs::set_permissions(&launcher, fs::Permissions::from_mode(0o500))
        .map_err(|error| Stop::error(error.to_string()))?;
    drop(binary);
    let mut pins = Object::new();
    pins.set(executable.to_string_lossy().as_ref(), recorded_sha.as_str());
    pins.set(
        context.root.join("policy.json").to_string_lossy().as_ref(),
        fang_hash::sha256_hex(policy_data),
    );
    // The sealed triple: read once under the caps, then snapshots that the proof step reads.
    let paths = [&arguments.input, &arguments.certificate, &arguments.witness];
    let mut sealed = Object::new();
    for ((name, cap, file), path) in CAPS.iter().zip(paths) {
        let data = read(supervisor, path, *cap)?;
        let snapshot = Snapshot::create(&capture.join(file), &data)?;
        sealed.set(*name, snapshot.sha256.as_str());
        snapshots.push(snapshot);
    }
    set(report, "sealed_sha256", Value::Object(sealed.clone()));
    set(report, "source_helper_sha256", Value::Object(pins.clone()));
    set(report, "policy_sha256", fang_hash::sha256_hex(policy_data));
    // The reviews are pin data in the policy; no receipt is read at run time.
    let review = policy
        .get("independent_review")
        .cloned()
        .unwrap_or(Value::Null);
    if review == Value::Null {
        return Err(Stop::review(
            "Version-8 endpoint independent review is not provisioned",
        ));
    }
    let link = review
        .get("bindings")
        .and_then(|item| item.get("pins.link_v2"));
    require(
        link.is_some() && link == policy.get("batch_sha256"),
        "Endpoint review does not bind the policy link",
    )?;
    // This entry's own review gates every proof step; until it exists the entry stops here.
    let entry_review = policy.get("entry_review").cloned().unwrap_or(Value::Null);
    if entry_review == Value::Null {
        return Err(Stop::review(
            "Version-8 entry independent review is not provisioned",
        ));
    }
    // The review must name this policy as it was before the review slot was filled.
    let mut unprovisioned = policy.as_object().cloned().unwrap_or_default();
    unprovisioned.set("entry_review", Value::Null);
    let own_policy =
        fang_hash::sha256_hex(&manifest_bytes(&Value::Object(unprovisioned)).map_err(Stop::error)?);
    let mut own = Object::new();
    own.set("policy.json", own_policy);
    require(
        entry_review.get("status").and_then(Value::as_str) == Some("passed")
            && entry_review.get("entry_sources_sha256") == Some(&Value::Object(own)),
        "Version-8 entry review does not name this entry and its policy",
    )?;
    set(
        report,
        "entry_review_sha256",
        entry_review.get("sha256").cloned().unwrap_or(Value::Null),
    );
    set(
        report,
        "independent_review_sha256",
        review.get("sha256").cloned().unwrap_or(Value::Null),
    );
    let pinned = policy.get("toolchain").cloned().unwrap_or(Value::Null);
    let recorded = installation
        .get("toolchain")
        .cloned()
        .unwrap_or(Value::Null);
    let same = ["lean_sha256", "lake_sha256", "lib_tree_sha256"]
        .iter()
        .all(|key| recorded.get(key).is_some() && recorded.get(key) == pinned.get(key));
    require(same, "Lean toolchain differs from the policy")?;
    // The inventory before, the proof, the inventory after.
    let step = Instant::now();
    let before = inventory(
        supervisor,
        installation,
        &context.installation_data,
        &out.join("before"),
        &launcher,
    )?;
    let mut steps = vec![step_record("inventory-before", step)];
    set(report, "steps", Value::Array(steps.clone()));
    save(out, report);
    require(before, "Installed Lean trees changed")?;
    let step = Instant::now();
    let sealed_inputs: Vec<(&'static str, PathBuf, String)> = CAPS
        .iter()
        .zip(snapshots.iter())
        .map(|((name, _, _), snapshot)| (*name, snapshot.path.clone(), snapshot.sha256.clone()))
        .collect();
    let installation_path = capture.join("installation.json");
    let installation_sha256 = fang_hash::sha256_hex(&context.installation_data);
    let proof = check::run(
        supervisor,
        &check::Inputs {
            out: &out.join("proof"),
            installation,
            installation_path: &installation_path,
            installation_sha256: &installation_sha256,
            sealed: &sealed_inputs,
            launcher: &launcher,
            started: Instant::now(),
        },
    );
    steps.push(step_record("check", step));
    set(report, "steps", Value::Array(steps.clone()));
    save(out, report);
    if let Some(stopped) = proof.stopped {
        return Err(Stop {
            status: stopped.class,
            error: format!("Proof step failed: {}", stopped.error),
            kind: "Failure",
        });
    }
    check_proof(&proof.record, &sealed)?;
    let step = Instant::now();
    let after = inventory(
        supervisor,
        installation,
        &context.installation_data,
        &out.join("after"),
        &launcher,
    )?;
    steps.push(step_record("inventory-after", step));
    set(report, "steps", Value::Array(steps));
    require(after, "Installed Lean trees changed")?;
    for snapshot in snapshots.iter() {
        snapshot.verify(&mut || supervisor.check("verify", 0.15))?;
    }
    for (path, pin) in pins.iter() {
        let data = read(supervisor, Path::new(path), 1 << 30)?;
        require(
            Some(fang_hash::sha256_hex(&data).as_str()) == pin.as_str(),
            "Source/tool identity changed",
        )?;
    }
    require(
        read(supervisor, &capture.join("policy.json"), 2 << 20)?.as_slice() == policy_data,
        "Captured policy changed",
    )?;
    let installation_now = read(supervisor, &capture.join("installation.json"), 4 << 20)?;
    let installed_now = read(supervisor, &context.root.join("installation.json"), 4 << 20)?;
    require(
        installation_now == context.installation_data && installed_now == context.installation_data,
        "Installation record changed",
    )?;
    let launcher_now = read(supervisor, &launcher, 1 << 30)?;
    require(
        fang_hash::sha256_hex(&launcher_now) == recorded_sha,
        "Captured entry changed",
    )?;
    let mut artifacts = Object::new();
    let mut files = Vec::new();
    collect_files(out, out, &mut files).map_err(Stop::error)?;
    files.sort();
    for (relative, path) in files {
        supervisor.check("archive", 0.15)?;
        if relative == "manifest.json" {
            continue;
        }
        let data = read(supervisor, &path, 256 << 20)?;
        artifacts.set(relative.as_str(), fang_hash::sha256_hex(&data));
    }
    supervisor.tree_bytes(out)?;
    supervisor.memory()?;
    supervisor.check("final", 0.15)?;
    let proof_manifest = read(supervisor, &out.join("proof/manifest.json"), 256 << 20)?;
    let before_manifest = read(supervisor, &out.join("before/manifest.json"), 256 << 20)?;
    let after_manifest = read(supervisor, &out.join("after/manifest.json"), 256 << 20)?;
    if let Ok(mut report) = report.lock() {
        report.set("status", "KernelChecked");
        report.set(
            "modules",
            proof.record.get("modules").cloned().unwrap_or(Value::Null),
        );
        report.set(
            "audits",
            proof.record.get("audits").cloned().unwrap_or(Value::Null),
        );
        report.set("artifacts_sha256", Value::Object(artifacts));
        report.set(
            "proof_manifest_sha256",
            fang_hash::sha256_hex(&proof_manifest),
        );
        report.set("before_sha256", fang_hash::sha256_hex(&before_manifest));
        report.set("after_sha256", fang_hash::sha256_hex(&after_manifest));
    }
    supervisor.check("positive-result", 0.15)?;
    Ok(())
}

fn step_record(name: &str, started: Instant) -> Value {
    let mut record = Object::new();
    record.set("step", name);
    record.set("seconds", float(started.elapsed().as_secs_f64()));
    Value::Object(record)
}

/// Every regular file below `directory`; a symbolic link or a special file is an error.
fn collect_files(
    base: &Path,
    directory: &Path,
    found: &mut Vec<(String, PathBuf)>,
) -> Result<(), String> {
    for entry in fs::read_dir(directory).map_err(|error| error.to_string())? {
        let entry = entry.map_err(|error| error.to_string())?;
        let path = entry.path();
        let kind = entry.file_type().map_err(|error| error.to_string())?;
        if kind.is_symlink() {
            return Err("Symlink in the run directory".to_owned());
        }
        if kind.is_dir() {
            collect_files(base, &path, found)?;
        } else if kind.is_file() {
            let relative = path.strip_prefix(base).map_err(|error| error.to_string())?;
            found.push((relative.to_string_lossy().into_owned(), path.clone()));
        }
    }
    Ok(())
}

/// The entry in the guarded worker; the exit status.
pub fn main(raw: &[OsString], worker: &Worker) -> i32 {
    let arguments = match arguments(raw) {
        Ok(arguments) => arguments,
        Err(message) => {
            eprintln!("error: {message}");
            return 2;
        }
    };
    if !cfg!(target_os = "linux") {
        eprintln!("error: Use Linux/WSL");
        return 2;
    }
    let executable = match std::env::current_exe() {
        Ok(path) => path,
        Err(error) => {
            eprintln!("error: {error}");
            return 2;
        }
    };
    let Some(root) = executable
        .parent()
        .and_then(Path::parent)
        .map(Path::to_path_buf)
    else {
        eprintln!("error: the entry is not installed");
        return 2;
    };
    let installation_data = match bootstrap_read(&root.join("installation.json"), 4 << 20) {
        Ok(data) => data,
        Err(message) => {
            eprintln!("error: {message}");
            return 2;
        }
    };
    let installation = match parse(&installation_data) {
        Ok(value) => value,
        Err(message) => {
            eprintln!("error: installation record: {message}");
            return 2;
        }
    };
    let output_root = installation
        .get("output_root")
        .and_then(Value::as_str)
        .map(PathBuf::from);
    let out = resolve(&arguments.out);
    if !output_root.is_some_and(|root| out.starts_with(&root) && out != root) {
        eprintln!("error: Use a fresh directory under the installation output root");
        return 2;
    }
    let started = Instant::now();
    if let Err(error) =
        fs::create_dir_all(out.parent().unwrap_or(&out)).and_then(|()| fs::create_dir(&out))
    {
        eprintln!("error: {}: {error}", out.display());
        return 2;
    }
    let report = Arc::new(Mutex::new(Object::new()));
    if let Ok(mut record) = report.lock() {
        record.set("schema", SCHEMA);
        // Descriptors above 2 without close-on-exec reach every child; the run record lists them.
        record.set(
            "inherited_descriptors",
            Value::Array(
                fang_supervisor::inherited_descriptors()
                    .iter()
                    .map(|item| item.to_json())
                    .collect(),
            ),
        );
        record.set("status", "Error");
        record.set(
            "installation_sha256",
            fang_hash::sha256_hex(&installation_data),
        );
        record.set("started_utc", utc_now());
        let mut limits = Object::new();
        limits.set("wall_seconds", 600u64);
        limits.set("sampled_tree_rss_mib", 4096u64);
        limits.set("artifact_bytes", 1u64 << 30);
        let mut caps = Object::new();
        for (name, cap, _) in CAPS {
            caps.set(name, cap);
        }
        limits.set("input_bytes", Value::Object(caps));
        record.set("limits", Value::Object(limits));
        record.set(
            "scope",
            "One exact source/certificate pair of the bounded version-8 expanded grammar. Witnesses suggest values; Lean checks actual calls. No installed profile or full TPTP claim.",
        );
        record.set(
            "trust",
            "This local entry, its build from the policy-pinned sources, policy provisioning, Lean/backend, OS and filesystem are trusted. Inventories detect retained changes, not change-and-restore attacks.",
        );
    }
    let hook_report = Arc::clone(&report);
    let hook_out = out.clone();
    worker.on_parent_death(move || {
        if let Ok(mut record) = hook_report.lock() {
            record.set("status", "Forced");
            record.set("error", "External cancellation");
            record.set("failure_type", "Failure");
            record.set("finished_utc", utc_now());
            record.set("wall_seconds", float(started.elapsed().as_secs_f64()));
        }
        save(&hook_out, &hook_report);
    });
    let context = Run {
        out: out.clone(),
        root,
        installation,
        installation_data,
        started,
    };
    let mut snapshots = Vec::new();
    // Unsupervised and before the review checks; see the module documentation.
    let prepared = case_sensitive(&out, true)
        .and_then(|()| fs::create_dir(out.join("capture")).map_err(|error| error.to_string()))
        .map_err(Stop::error);
    let result = prepared.and_then(|()| run(&arguments, &context, &report, worker, &mut snapshots));
    let finished = worker.finalize(|| {
        if let Ok(mut record) = report.lock() {
            if let Err(stop) = &result {
                record.set("status", stop.status);
                record.set("error", stop.error.as_str());
                record.set("failure_type", stop.kind);
            }
            record.set("finished_utc", utc_now());
            record.set("wall_seconds", float(started.elapsed().as_secs_f64()));
        }
        save(&out, &report);
    });
    if finished.is_none() {
        return exit_code("Forced");
    }
    let record = report
        .lock()
        .map(|record| record.clone())
        .unwrap_or_default();
    let status = record
        .get("status")
        .and_then(Value::as_str)
        .unwrap_or("Error")
        .to_owned();
    let mut printed = Object::new();
    printed.set("status", status.as_str());
    printed.set("error", record.get("error").cloned().unwrap_or(Value::Null));
    printed.set(
        "manifest",
        out.join("manifest.json").to_string_lossy().as_ref(),
    );
    println!(
        "{}",
        fang_json::dumps(&Value::Object(printed), &fang_json::DumpOptions::default())
            .unwrap_or_default()
    );
    exit_code(&status)
}
