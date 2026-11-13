// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The Supervisor of supervisor.py: deadline, cancellation, sampled tree RSS, artifact bytes,
//! and one bounded child per stage with its record.

use std::ffi::OsString;
use std::fs::{File, OpenOptions};
use std::io::Read;
use std::os::unix::fs::{DirBuilderExt, MetadataExt};
use std::os::unix::process::{CommandExt, ExitStatusExt};
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};

use fang_hash::{Hasher, hex, open_regular};
use fang_json::{Object, Value};

use crate::io::{Fault, Snapshot, read_regular};
use crate::limits::Limits;
use crate::procfs::{self, kill_verified, owned, owned_unreaped, process_table, process_times};
use crate::status::{Failure, Status};

/// The entries of one directory, as tree_bytes lists them.
pub(crate) type Listing = Box<dyn Iterator<Item = std::io::Result<PathBuf>>>;

/// The cancellation flag that `check` turns into Forced; the guard's watcher sets it.
#[derive(Clone, Debug, Default)]
pub struct CancelToken(Arc<AtomicBool>);

impl CancelToken {
    pub fn new() -> CancelToken {
        CancelToken::default()
    }

    pub fn cancel(&self) {
        self.0.store(true, Ordering::SeqCst);
    }

    pub fn is_cancelled(&self) -> bool {
        self.0.load(Ordering::SeqCst)
    }
}

/// supervisor.ENVIRONMENT_KEYS without PYTHONDONTWRITEBYTECODE, which no Rust child needs.
pub const ENVIRONMENT_KEYS: &[&str] = &[
    "PATH",
    "LANG",
    "LC_ALL",
    "LC_CTYPE",
    "HOME",
    "USER",
    "TMPDIR",
    "TMP",
    "TEMP",
    "XDG_CACHE_HOME",
    "RUSTUP_HOME",
    "CARGO_HOME",
    "RUSTUP_TOOLCHAIN",
    "CARGO_TARGET_DIR",
    "CARGO_NET_OFFLINE",
    "CARGO_BUILD_JOBS",
    "LEAN_PATH",
    "LEAN_NUM_THREADS",
];

/// A child environment: exactly these variables, nothing inherited.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Environment {
    entries: Vec<(String, String)>,
}

impl Environment {
    pub fn new() -> Environment {
        Environment::default()
    }

    /// Set a variable, keeping the position of an existing one, as a dict assignment does.
    pub fn set(&mut self, key: impl Into<String>, value: impl Into<String>) {
        let key = key.into();
        let value = value.into();
        match self.entries.iter_mut().find(|(name, _)| *name == key) {
            Some(entry) => entry.1 = value,
            None => self.entries.push((key, value)),
        }
    }

    pub fn get(&self, key: &str) -> Option<&str> {
        self.entries
            .iter()
            .find(|(name, _)| name == key)
            .map(|(_, value)| value.as_str())
    }

    pub fn iter(&self) -> impl Iterator<Item = (&str, &str)> {
        self.entries
            .iter()
            .map(|(name, value)| (name.as_str(), value.as_str()))
    }

    fn approved(&self) -> bool {
        self.entries
            .iter()
            .all(|(name, _)| ENVIRONMENT_KEYS.contains(&name.as_str()))
    }

    fn to_json(&self) -> Value {
        Value::Object(
            self.entries
                .iter()
                .map(|(name, value)| (name.clone(), Value::from(value.as_str())))
                .collect(),
        )
    }
}

/// supervisor.child_environment: a fixed PATH and locale.
pub fn child_environment() -> Environment {
    let mut environment = Environment::new();
    environment.set("PATH", "/usr/bin:/bin");
    environment.set("LANG", "C.UTF-8");
    environment.set("LC_ALL", "C.UTF-8");
    environment
}

/// One child: its command, stage directory (created, must not exist), run root, environment,
/// stdin file (default /dev/null), stdout byte limit (default Limits.log_bytes) and working
/// directory (default the stage directory).
#[derive(Clone, Copy, Debug)]
pub struct Stage<'a> {
    pub name: &'a str,
    pub command: &'a [OsString],
    pub directory: &'a Path,
    pub run_root: &'a Path,
    pub environment: Option<&'a Environment>,
    pub stdin: Option<&'a Path>,
    pub stdout_limit: Option<u64>,
    pub cwd: Option<&'a Path>,
}

/// The per-stage record of supervisor.run, with Python's field names.
#[derive(Clone, Debug, Default, PartialEq)]
pub struct StageRecord {
    pub stage: String,
    pub command: Vec<String>,
    pub started_seconds: f64,
    pub stdout: String,
    pub stderr: String,
    pub classification: String,
    pub exit_code: Option<i32>,
    pub stream_byte_limits: (u64, u64),
    pub environment: Option<Environment>,
    pub pid: Option<u32>,
    pub terminated_owned_pids: Option<Vec<i32>>,
    pub elapsed_seconds: f64,
    pub peak_adapter_tree_rss_kib: u64,
    pub children_user_seconds: f64,
    pub children_system_seconds: f64,
    pub stdout_bytes: Option<u64>,
    pub stdout_sha256: Option<String>,
    pub stdout_hash_status: Option<String>,
    pub stderr_bytes: Option<u64>,
    pub stderr_sha256: Option<String>,
    pub stderr_hash_status: Option<String>,
}

impl StageRecord {
    /// The record as Python writes it: seconds as floats, counts and codes as integers.
    pub fn to_json(&self) -> Value {
        let mut object = Object::new();
        object.set("stage", self.stage.as_str());
        object.set(
            "command",
            Value::Array(
                self.command
                    .iter()
                    .map(|part| Value::from(part.as_str()))
                    .collect(),
            ),
        );
        object.set("started_seconds", self.started_seconds);
        object.set("stdout", self.stdout.as_str());
        object.set("stderr", self.stderr.as_str());
        object.set("classification", self.classification.as_str());
        object.set("exit_code", self.exit_code);
        let mut limits = Object::new();
        limits.set("stdout", self.stream_byte_limits.0);
        limits.set("stderr", self.stream_byte_limits.1);
        object.set("stream_byte_limits", limits);
        if let Some(environment) = &self.environment {
            object.set("environment", environment.to_json());
        }
        if let Some(pid) = self.pid {
            object.set("pid", pid);
        }
        if let Some(pids) = &self.terminated_owned_pids {
            object.set(
                "terminated_owned_pids",
                Value::Array(pids.iter().map(|pid| Value::from(*pid)).collect()),
            );
        }
        object.set("elapsed_seconds", self.elapsed_seconds);
        object.set("peak_adapter_tree_rss_kib", self.peak_adapter_tree_rss_kib);
        object.set("children_user_seconds", self.children_user_seconds);
        object.set("children_system_seconds", self.children_system_seconds);
        for (name, bytes, sha256, status) in [
            (
                "stdout",
                self.stdout_bytes,
                &self.stdout_sha256,
                &self.stdout_hash_status,
            ),
            (
                "stderr",
                self.stderr_bytes,
                &self.stderr_sha256,
                &self.stderr_hash_status,
            ),
        ] {
            if let Some(bytes) = bytes {
                object.set(format!("{name}_bytes"), bytes);
            }
            if let Some(sha256) = sha256 {
                object.set(format!("{name}_sha256"), sha256.as_str());
            }
            if let Some(status) = status {
                object.set(format!("{name}_hash_status"), status.as_str());
            }
        }
        Value::Object(object)
    }

    fn set_hash(&mut self, stdout: bool, status: &str) {
        let slot = if stdout {
            &mut self.stdout_hash_status
        } else {
            &mut self.stderr_hash_status
        };
        *slot = Some(status.to_owned());
    }
}

pub struct StageOutput {
    pub record: StageRecord,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}

/// Proof that `Supervisor::confirm_clean` found no stray process and no changed snapshot.
/// It is consumed by `positive_status_line`, so every positive line needs a fresh check.
#[derive(Debug)]
pub struct Clean {
    _private: (),
}

/// The statuses that report a proof or a model.
const POSITIVE: &[&str] = &[
    "Unsatisfiable",
    "Theorem",
    "ContradictoryAxioms",
    "Satisfiable",
    "CounterSatisfiable",
];

/// "% SZS status STATUS for PROBLEM", only for a positive status and only after a clean check.
pub fn positive_status_line(clean: Clean, status: &str, problem: &str) -> Option<String> {
    let Clean { _private: () } = clean;
    POSITIVE
        .contains(&status)
        .then(|| format!("% SZS status {status} for {problem}"))
}

pub struct Supervisor {
    pub limits: Limits,
    pub started: Instant,
    deadline: Instant,
    cancel: CancelToken,
    pub records: Vec<StageRecord>,
    pub peak_kib: u64,
    pub additional_artifact_roots: Vec<PathBuf>,
    /// The descriptors every child inherits, taken when the supervisor starts (DESIGN.md,
    /// "Inherited descriptors"); a run record writes them with `inherited_descriptors_json`.
    pub inherited_descriptors: Vec<procfs::InheritedDescriptor>,
    pid: i32,
    /// Process groups whose members other than this process are owned.
    groups: Vec<i32>,
    /// This process leads its group (the guard's worker): children join the group.
    leader: bool,
}

fn seconds(value: f64) -> Duration {
    Duration::try_from_secs_f64(value.max(0.0)).unwrap_or(Duration::MAX)
}

impl Supervisor {
    pub fn new(limits: Limits, started: Option<Instant>) -> Result<Supervisor, Failure> {
        let started = started.unwrap_or_else(Instant::now);
        let pid = std::process::id() as i32;
        let entry = procfs::entry(pid)
            .ok_or_else(|| Failure::adapter(Status::Error, "This adapter requires Linux/WSL"))?;
        let leader = entry.group == pid;
        Ok(Supervisor {
            limits,
            started,
            deadline: started
                .checked_add(seconds(limits.wall_seconds))
                .or_else(|| started.checked_add(Duration::from_secs(1 << 31)))
                .unwrap_or(started),
            cancel: CancelToken::new(),
            records: Vec::new(),
            peak_kib: 0,
            additional_artifact_roots: Vec::new(),
            inherited_descriptors: procfs::inherited_descriptors(),
            pid,
            groups: if leader { vec![pid] } else { Vec::new() },
            leader,
        })
    }

    /// `[{"fd": N, "target": "..."}, ...]` for the run record.
    pub fn inherited_descriptors_json(&self) -> Value {
        Value::Array(
            self.inherited_descriptors
                .iter()
                .map(procfs::InheritedDescriptor::to_json)
                .collect(),
        )
    }

    pub fn deadline(&self) -> Instant {
        self.deadline
    }

    pub fn set_deadline(&mut self, deadline: Instant) {
        self.deadline = deadline;
    }

    pub fn cancel_token(&self) -> CancelToken {
        self.cancel.clone()
    }

    /// Share an existing token, such as the guard worker's.
    pub fn set_cancel_token(&mut self, token: CancelToken) {
        self.cancel = token;
    }

    pub fn cancelled(&self) -> bool {
        self.cancel.is_cancelled()
    }

    fn past(&self, reserve: f64) -> bool {
        Instant::now() + seconds(reserve) >= self.deadline
    }

    /// Forced when cancelled; Timeout once the deadline minus `reserve` seconds has passed.
    pub fn check(&self, stage: &str, reserve: f64) -> Result<(), Failure> {
        if self.cancelled() {
            return Err(Failure::new(Status::Forced, "External cancellation", stage));
        }
        if self.past(reserve) {
            return Err(Failure::new(
                Status::Timeout,
                "Whole-pipeline deadline reached",
                stage,
            ));
        }
        Ok(())
    }

    /// `check("adapter", 0.15)`, Python's defaults.
    pub fn check_default(&self) -> Result<(), Failure> {
        self.check("adapter", 0.15)
    }

    /// Sampled RSS of this process and its owned processes, in KiB; MemoryOut above the limit.
    pub fn memory(&mut self) -> Result<u64, Failure> {
        let table = process_table();
        let mut members = owned(&table, self.pid, &self.groups);
        members.insert(self.pid);
        let total: u64 = members
            .iter()
            .filter_map(|pid| table.get(pid))
            .map(|entry| entry.rss_kib)
            .sum();
        self.peak_kib = self.peak_kib.max(total);
        if total > self.limits.memory_mib * 1024 {
            return Err(Failure::adapter(
                Status::MemoryOut,
                "Sampled adapter-plus-descendant RSS limit reached",
            ));
        }
        Ok(total)
    }

    /// Bytes of the regular files under `directory` and the additional roots.
    pub fn tree_bytes(&self, directory: &Path) -> Result<u64, Fault> {
        self.tree_bytes_with(
            directory,
            &mut |path| {
                let entries = std::fs::read_dir(path)?;
                Ok(Box::new(
                    entries.map(|entry| entry.map(|entry| entry.path())),
                ))
            },
            &mut |path| std::fs::symlink_metadata(path),
        )
    }

    /// `tree_bytes` with the directory listing and the lstat given, so tests can make an entry
    /// vanish between the listing and its stat, as Python's mocks do.
    pub(crate) fn tree_bytes_with(
        &self,
        directory: &Path,
        list: &mut dyn FnMut(&Path) -> std::io::Result<Listing>,
        stat: &mut dyn FnMut(&Path) -> std::io::Result<std::fs::Metadata>,
    ) -> Result<u64, Fault> {
        let mut roots: Vec<PathBuf> = vec![directory.to_path_buf()];
        for root in &self.additional_artifact_roots {
            if !roots.contains(root) {
                roots.push(root.clone());
            }
        }
        let (mut total, mut count) = (0u64, 0u64);
        let mut pending = roots.clone();
        while let Some(current) = pending.pop() {
            self.check("artifact-scan", 0.15)?;
            let entries = match list(&current) {
                Ok(entries) => entries,
                Err(error)
                    if error.kind() == std::io::ErrorKind::NotFound
                        && !roots.contains(&current) =>
                {
                    continue;
                }
                Err(error) => return Err(error.into()),
            };
            for entry in entries {
                self.check("artifact-scan", 0.15)?;
                let entry = entry?;
                count += 1;
                if count > 100_000 {
                    return Err(Failure::adapter(
                        Status::ResourceOut,
                        "Run artifact entry limit reached",
                    )
                    .into());
                }
                let metadata = match stat(&entry) {
                    Ok(metadata) => metadata,
                    Err(error) if error.kind() == std::io::ErrorKind::NotFound => continue,
                    Err(error) => return Err(error.into()),
                };
                let kind = metadata.file_type();
                if kind.is_symlink() || !(kind.is_dir() || kind.is_file()) {
                    return Err(Failure::adapter(
                        Status::Error,
                        "Child created a nonregular artifact",
                    )
                    .into());
                }
                if kind.is_dir() {
                    pending.push(entry);
                } else {
                    total += metadata.size();
                }
                if total > self.limits.artifact_bytes {
                    return Err(Failure::adapter(
                        Status::ResourceOut,
                        "Aggregate run artifact byte limit reached",
                    )
                    .into());
                }
            }
        }
        Ok(total)
    }

    fn owned_now(&self) -> Vec<(i32, u64)> {
        self.owned_pids(false)
    }

    /// The owned processes with their start times; `unreaped` also lists zombies not yet reaped.
    fn owned_pids(&self, unreaped: bool) -> Vec<(i32, u64)> {
        let table = process_table();
        let view = if unreaped {
            owned_unreaped(&table, self.pid, &self.groups)
        } else {
            owned(&table, self.pid, &self.groups)
        };
        let mut pids: Vec<(i32, u64)> = view
            .into_iter()
            .map(|pid| (pid, table[&pid].start))
            .collect();
        pids.sort();
        pids
    }

    /// Kill every owned process (identity checked), reap the child, and wait up to 1 s for the rest.
    /// The PIDs returned are those owned at the start, zombies not yet reaped included, as Python
    /// recorded them; the wait is for the living ones only, since without a subreaper an orphaned
    /// zombie is reaped by init, not here.
    fn cleanup(&mut self, child: &mut Child) -> Result<Vec<i32>, Failure> {
        let first = self.owned_pids(true);
        kill_verified(&first);
        let _ = child.wait();
        let limit = Instant::now() + Duration::from_secs(1);
        loop {
            let remaining = self.owned_now();
            if remaining.is_empty() {
                return Ok(first.into_iter().map(|(pid, _)| pid).collect());
            }
            kill_verified(&remaining);
            if self.owned_now().is_empty() {
                return Ok(first.into_iter().map(|(pid, _)| pid).collect());
            }
            if Instant::now() >= limit {
                return Err(Failure::adapter(
                    Status::Error,
                    "Owned descendants did not terminate during cleanup",
                ));
            }
            std::thread::sleep(Duration::from_millis(5));
        }
    }

    /// No owned process alive, and every snapshot unchanged; required before any positive status.
    pub fn confirm_clean(&mut self, stage: &str, snapshots: &[&Snapshot]) -> Result<Clean, Fault> {
        if !self.owned_now().is_empty() {
            return Err(Failure::new(
                Status::Error,
                "An owned process is alive before a positive status",
                stage,
            )
            .into());
        }
        for snapshot in snapshots {
            snapshot.verify(&mut || self.check(stage, 0.15))?;
        }
        Ok(Clean { _private: () })
    }

    /// supervisor.run, step for step. The record is appended to `records` in every case after
    /// the stage directory exists.
    pub fn run(&mut self, stage: &Stage<'_>) -> Result<StageOutput, Fault> {
        self.check(stage.name, 0.15)?;
        let stdout_limit = stage.stdout_limit.unwrap_or(self.limits.log_bytes);
        std::fs::DirBuilder::new()
            .mode(0o700)
            .create(stage.directory)
            .map_err(Fault::at(stage.directory))?;
        let stdout_path = stage.directory.join("stdout");
        let stderr_path = stage.directory.join("stderr");
        let relative = |path: &Path| -> Result<String, Fault> {
            path.strip_prefix(stage.run_root)
                .map(|relative| relative.to_string_lossy().into_owned())
                .map_err(|_| {
                    Fault::Value(format!(
                        "{:?} is not in the subpath of {:?}",
                        path, stage.run_root
                    ))
                })
        };
        let started = Instant::now();
        let usage = process_times()?;
        let mut record = StageRecord {
            stage: stage.name.to_owned(),
            command: stage
                .command
                .iter()
                .map(|part| part.to_string_lossy().into_owned())
                .collect(),
            started_seconds: started.duration_since(self.started).as_secs_f64(),
            stdout: relative(&stdout_path)?,
            stderr: relative(&stderr_path)?,
            classification: "starting".to_owned(),
            stream_byte_limits: (stdout_limit, self.limits.log_bytes),
            ..StageRecord::default()
        };
        let mut child: Option<Child> = None;
        let mut identities: [Option<(u64, u64)>; 2] = [None, None];
        let mut peak = 0u64;
        let mut failure: Option<Fault> = None;
        let attempt = self.supervise(
            stage,
            &stdout_path,
            &stderr_path,
            stdout_limit,
            &mut record,
            &mut child,
            &mut identities,
            &mut peak,
        );
        match attempt {
            Ok(()) => {}
            Err(Fault::Failure(error)) => {
                record.classification = error.status.name().to_owned();
                failure = Some(error.into());
            }
            Err(fault) => {
                record.classification = "Error".to_owned();
                let reason = format!("Child launch or supervision failed: {}", fault.python_str());
                failure = Some(Failure::new(Status::Error, reason, stage.name).into());
            }
        }
        // Python's finally block.
        if let Some(process) = child.as_mut() {
            match self.cleanup(process) {
                Ok(pids) => record.terminated_owned_pids = Some(pids),
                Err(error) => {
                    record.classification = "Error".to_owned();
                    failure = Some(error.into());
                }
            }
            if let Ok(Some(status)) = process.try_wait() {
                record.exit_code = exit_code(status);
            }
        }
        if !self.leader
            && let Some(process) = &child
        {
            let group = process.id() as i32;
            self.groups.retain(|other| *other != group);
        }
        record.elapsed_seconds = started.elapsed().as_secs_f64();
        record.peak_adapter_tree_rss_kib = peak;
        let after = process_times()?;
        record.children_user_seconds = after.children_user - usage.children_user;
        record.children_system_seconds = after.children_system - usage.children_system;
        let limits = [stdout_limit, self.limits.log_bytes];
        for (index, path) in [&stdout_path, &stderr_path].into_iter().enumerate() {
            let stdout = index == 0;
            let metadata = match std::fs::symlink_metadata(path) {
                Ok(metadata) => metadata,
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                    record.set_hash(stdout, "missing");
                    if child.is_some() {
                        failure = Some(
                            Failure::new(
                                Status::Error,
                                "Child removed its log pathname",
                                stage.name,
                            )
                            .into(),
                        );
                        record.classification = "Error".to_owned();
                    }
                    continue;
                }
                Err(error) => return Err(self.finish(record, error.into())),
            };
            if !metadata.file_type().is_file()
                || Some((metadata.dev(), metadata.ino())) != identities[index]
            {
                record.set_hash(stdout, "nonregular-or-replaced-path");
                failure = Some(
                    Failure::new(Status::Error, "Child replaced its log pathname", stage.name)
                        .into(),
                );
                record.classification = "Error".to_owned();
                continue;
            }
            if stdout {
                record.stdout_bytes = Some(metadata.size());
            } else {
                record.stderr_bytes = Some(metadata.size());
            }
            if metadata.size() > limits[index] {
                record.set_hash(stdout, "skipped-over-log-limit");
                failure = Some(
                    Failure::new(
                        Status::ResourceOut,
                        "Child stdout/stderr byte limit reached",
                        stage.name,
                    )
                    .into(),
                );
                record.classification = "ResourceOut".to_owned();
            } else if self.cancelled() || self.past(0.15) {
                record.set_hash(stdout, "skipped-after-deadline-or-cancellation");
            } else {
                let (mut file, opened) = match open_regular(path) {
                    Ok(opened) => opened,
                    Err(error) => return Err(self.finish(record, error.into())),
                };
                if (opened.dev, opened.ino) != identities[index].expect("checked above") {
                    failure = Some(
                        Failure::new(
                            Status::Error,
                            "Log identity changed while opening",
                            stage.name,
                        )
                        .into(),
                    );
                    record.classification = "Error".to_owned();
                    record.set_hash(stdout, "changed-while-opening");
                    continue;
                }
                let mut hasher = Hasher::new();
                let mut remaining = limits[index] + 1;
                let mut block = vec![0u8; 65536];
                while remaining > 0 {
                    if self.cancelled() || self.past(0.15) {
                        record.set_hash(stdout, "incomplete-at-deadline-or-cancellation");
                        break;
                    }
                    let want = remaining.min(65536) as usize;
                    let read = match file.read(&mut block[..want]) {
                        Ok(read) => read,
                        Err(error) => return Err(self.finish(record, error.into())),
                    };
                    if read == 0 {
                        let digest = hex(&std::mem::take(&mut hasher).finish());
                        if stdout {
                            record.stdout_sha256 = Some(digest);
                        } else {
                            record.stderr_sha256 = Some(digest);
                        }
                        record.set_hash(stdout, "complete");
                        break;
                    }
                    hasher.update(&block[..read]);
                    remaining -= read as u64;
                }
                if remaining == 0 {
                    failure = Some(
                        Failure::new(Status::ResourceOut, "Log grew beyond its bound", stage.name)
                            .into(),
                    );
                    record.classification = "ResourceOut".to_owned();
                    record.set_hash(stdout, "grew-over-limit");
                }
            }
        }
        self.records.push(record.clone());
        if let Some(failure) = failure {
            return Err(failure);
        }
        self.check(stage.name, 0.15)?;
        let stdout = read_regular(&stdout_path, stdout_limit, &mut || {
            self.check("adapter", 0.15)
        })?;
        let stderr = read_regular(&stderr_path, self.limits.log_bytes, &mut || {
            self.check("adapter", 0.15)
        })?;
        Ok(StageOutput {
            record,
            stdout,
            stderr,
        })
    }

    /// An error that escapes Python's finally block: keep the record, then raise.
    fn finish(&mut self, record: StageRecord, fault: Fault) -> Fault {
        self.records.push(record);
        fault
    }

    /// The try block of supervisor.run: launch, then poll until the child exits.
    #[allow(clippy::too_many_arguments)]
    fn supervise(
        &mut self,
        stage: &Stage<'_>,
        stdout_path: &Path,
        stderr_path: &Path,
        stdout_limit: u64,
        record: &mut StageRecord,
        child: &mut Option<Child>,
        identities: &mut [Option<(u64, u64)>; 2],
        peak: &mut u64,
    ) -> Result<(), Fault> {
        let stdout = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(stdout_path)
            .map_err(Fault::at(stdout_path))?;
        let stderr = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(stderr_path)
            .map_err(Fault::at(stderr_path))?;
        for (index, stream) in [&stdout, &stderr].into_iter().enumerate() {
            let metadata = stream.metadata()?;
            identities[index] = Some((metadata.dev(), metadata.ino()));
        }
        let environment = stage.environment.cloned().unwrap_or_else(child_environment);
        if !environment.approved() {
            return Err(Failure::new(
                Status::Error,
                "Child environment contains unapproved variables",
                stage.name,
            )
            .into());
        }
        record.environment = Some(environment.clone());
        let stdin = match stage.stdin {
            None => Stdio::null(),
            Some(path) => Stdio::from(open_input(path)?),
        };
        let Some((program, arguments)) = stage.command.split_first() else {
            return Err(Fault::Value("empty command".to_owned()));
        };
        let mut command = Command::new(program);
        command
            .args(arguments)
            .current_dir(stage.cwd.unwrap_or(stage.directory))
            .env_clear()
            .envs(environment.iter())
            .stdin(stdin)
            .stdout(stdout)
            .stderr(stderr)
            .process_group(if self.leader { self.pid } else { 0 });
        let process = command.spawn().map_err(Fault::at(Path::new(program)))?;
        record.pid = Some(process.id());
        if !self.leader {
            self.groups.push(process.id() as i32);
        }
        *child = Some(process);
        let process = child.as_mut().expect("just set");
        loop {
            self.check(stage.name, 0.15)?;
            *peak = (*peak).max(self.memory()?);
            self.tree_bytes(stage.run_root)?;
            if std::fs::metadata(stdout_path)
                .map_err(Fault::at(stdout_path))?
                .size()
                > stdout_limit
                || std::fs::metadata(stderr_path)
                    .map_err(Fault::at(stderr_path))?
                    .size()
                    > self.limits.log_bytes
            {
                return Err(Failure::new(
                    Status::ResourceOut,
                    "Child stdout/stderr byte limit reached",
                    stage.name,
                )
                .into());
            }
            if let Some(status) = process.try_wait()? {
                record.exit_code = exit_code(status);
                break;
            }
            let left = self.deadline.saturating_duration_since(Instant::now());
            std::thread::sleep(
                seconds(self.limits.poll_seconds).min(left.max(Duration::from_millis(1))),
            );
        }
        let table = process_table();
        if !owned(&table, self.pid, &self.groups).is_empty() {
            return Err(Failure::new(
                Status::Error,
                "Child exited with live descendants",
                stage.name,
            )
            .into());
        }
        record.classification = match record.exit_code {
            Some(0) => "completed",
            Some(code) if code < 0 => "signal",
            _ => "nonzero-exit",
        }
        .to_owned();
        Ok(())
    }
}

/// Python's returncode: the exit code, or minus the signal number.
fn exit_code(status: std::process::ExitStatus) -> Option<i32> {
    status
        .code()
        .or_else(|| status.signal().map(|signal| -signal))
}

/// A stdin file: regular, opened without following a final symlink and without blocking.
fn open_input(path: &Path) -> Result<File, Fault> {
    match open_regular(path) {
        Ok((file, _)) => Ok(file),
        Err(error) if error.kind() == std::io::ErrorKind::InvalidInput => {
            Err(Failure::adapter(Status::Error, "A required artifact is not a regular file").into())
        }
        Err(error) => Err(error.into()),
    }
}

#[cfg(test)]
mod tests {
    //! ProtocolTests of tools/tests/test_fang_szs.py on the artifact scan, whose mocks make an
    //! entry vanish between its listing and its stat.
    use super::{Listing, Supervisor};
    use crate::{Fault, Limits};
    use std::io::{Error, ErrorKind};
    use std::path::{Path, PathBuf};

    fn listing(paths: Vec<&str>) -> std::io::Result<Listing> {
        let paths: Vec<std::io::Result<PathBuf>> = paths
            .into_iter()
            .map(|path| Ok(PathBuf::from(path)))
            .collect();
        Ok(Box::new(paths.into_iter()))
    }

    fn scan(
        list: &mut dyn FnMut(&Path) -> std::io::Result<Listing>,
        stat: &mut dyn FnMut(&Path) -> std::io::Result<std::fs::Metadata>,
    ) -> Result<u64, Fault> {
        let supervisor = Supervisor::new(Limits::default(), None).unwrap();
        supervisor.tree_bytes_with(Path::new("/owned-run"), list, stat)
    }

    fn kind(fault: Fault) -> ErrorKind {
        match fault {
            Fault::Os(error) | Fault::OsAt(error, _) => error.kind(),
            other => panic!("expected an OSError, got {other:?}"),
        }
    }

    #[test]
    fn artifact_scan_tolerates_disappearing_temporary_file() {
        let mut stats = 0;
        let found = scan(&mut |_| listing(vec!["/owned-run/temporary"]), &mut |_| {
            stats += 1;
            Err(Error::new(
                ErrorKind::NotFound,
                "temporary file was renamed",
            ))
        });
        assert_eq!((found.unwrap(), stats), (0, 1));
    }

    #[test]
    fn artifact_scan_tolerates_disappearing_queued_directory() {
        let directory = std::fs::symlink_metadata(std::env::temp_dir()).unwrap();
        let mut stats = 0;
        let found = scan(
            &mut |path| {
                if path == Path::new("/owned-run") {
                    listing(vec!["/owned-run/temporary"])
                } else {
                    Err(Error::new(
                        ErrorKind::NotFound,
                        "temporary directory removed",
                    ))
                }
            },
            &mut |_| {
                stats += 1;
                Ok(directory.clone())
            },
        );
        assert_eq!((found.unwrap(), stats), (0, 1));
    }

    #[test]
    fn artifact_scan_missing_root_is_still_an_error() {
        let fault = scan(
            &mut |_| Err(Error::new(ErrorKind::NotFound, "run root removed")),
            &mut |_| unreachable!("nothing to stat"),
        );
        assert_eq!(kind(fault.unwrap_err()), ErrorKind::NotFound);
    }

    #[test]
    fn artifact_scan_other_io_failures_remain_errors() {
        let fault = scan(&mut |_| listing(vec!["/owned-run/denied"]), &mut |_| {
            Err(Error::new(ErrorKind::PermissionDenied, "access denied"))
        });
        assert_eq!(kind(fault.unwrap_err()), ErrorKind::PermissionDenied);
    }
}
