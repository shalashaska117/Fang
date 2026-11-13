// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Cancellation without signal handlers.
//!
//! std cannot install a handler for SIGTERM, so the command runs as two processes. The outer
//! process starts the worker, the same executable with the same arguments, in a new process
//! group, and waits for it. A SIGTERM, SIGINT, SIGHUP or SIGKILL ends the outer process with
//! its default action (exit status 143 for SIGTERM). The worker watches its parent every
//! `WATCH_INTERVAL`; when the parent is gone it sets the cancel token, runs the Forced hook
//! once (unless the main path already finalized), and kills its whole process group, every
//! stage child included, through /bin/kill.
//!
//! ```ignore
//! fn main() {
//!     let worker = match fang_supervisor::guard::start() {
//!         Ok(fang_supervisor::guard::Role::Outer) => fang_supervisor::guard::run_outer(),
//!         Ok(fang_supervisor::guard::Role::Worker(worker)) => worker,
//!         Err(error) => { eprintln!("{error}"); std::process::exit(6) }
//!     };
//!     // supervisor.set_cancel_token(worker.cancel_token()); worker.on_parent_death(...); ...
//! }
//! ```

use std::os::unix::process::{CommandExt, ExitStatusExt};
use std::process::Command;
use std::sync::{Arc, Mutex, MutexGuard};
use std::time::Duration;

use crate::procfs;
use crate::run::CancelToken;
use crate::status::Status;

/// The environment variable that marks the worker; its value is the outer process's PID.
pub const MARKER: &str = "FANG_SUPERVISOR_GUARD";
/// How often the worker looks at its parent; Forced is written at most this late, plus the hook's time.
pub const WATCH_INTERVAL: Duration = Duration::from_millis(20);

pub enum Role {
    Outer,
    Worker(Worker),
}

/// Call first in `main`: `Outer` in the process the caller started, `Worker` in the guarded one.
pub fn start() -> std::io::Result<Role> {
    let Some(value) = std::env::var_os(MARKER) else {
        return Ok(Role::Outer);
    };
    let outer: u32 = value
        .to_str()
        .and_then(|text| text.parse().ok())
        .ok_or_else(|| {
            std::io::Error::new(std::io::ErrorKind::InvalidInput, "malformed guard marker")
        })?;
    let pid = std::process::id() as i32;
    match procfs::entry(pid) {
        Some(entry) if entry.group == pid => Ok(Role::Worker(Worker::new(outer, pid))),
        _ => Err(std::io::Error::other(
            "the guarded worker does not lead its own process group",
        )),
    }
}

/// Run the worker and exit with its status: its exit code, or 128 plus the signal that ended it.
pub fn run_outer() -> ! {
    let executable = match std::env::current_exe() {
        Ok(path) => path,
        Err(error) => {
            eprintln!("cannot locate the running executable: {error}");
            std::process::exit(Status::Error.exit_code());
        }
    };
    let status = Command::new(executable)
        .args(std::env::args_os().skip(1))
        .env(MARKER, std::process::id().to_string())
        .process_group(0)
        .status();
    match status {
        Ok(status) => std::process::exit(
            status
                .code()
                .unwrap_or_else(|| 128 + status.signal().unwrap_or(0)),
        ),
        Err(error) => {
            eprintln!("cannot start the guarded worker: {error}");
            std::process::exit(Status::Error.exit_code());
        }
    }
}

type Hook = Box<dyn FnOnce() + Send>;

struct State {
    finalized: bool,
    hook: Option<Hook>,
}

fn lock(state: &Mutex<State>) -> MutexGuard<'_, State> {
    state
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

pub struct Worker {
    outer: u32,
    token: CancelToken,
    state: Arc<Mutex<State>>,
    shares_stdout: bool,
}

impl Worker {
    fn new(outer: u32, pid: i32) -> Worker {
        let token = CancelToken::new();
        let state = Arc::new(Mutex::new(State {
            finalized: false,
            hook: None,
        }));
        let shares_stdout = match (
            std::fs::metadata("/proc/self/fd/1"),
            std::fs::metadata(format!("/proc/{outer}/fd/1")),
        ) {
            (Ok(own), Ok(caller)) => {
                use std::os::unix::fs::MetadataExt;
                (own.dev(), own.ino()) == (caller.dev(), caller.ino())
            }
            _ => false,
        };
        let watcher_token = token.clone();
        let watcher_state = Arc::clone(&state);
        std::thread::spawn(move || {
            loop {
                if std::os::unix::process::parent_id() != outer {
                    watcher_token.cancel();
                    {
                        let mut state = lock(&watcher_state);
                        if !state.finalized {
                            if let Some(hook) = state.hook.take() {
                                hook();
                            }
                            state.finalized = true;
                        }
                    }
                    procfs::kill_group(pid);
                    std::process::exit(Status::Forced.exit_code());
                }
                std::thread::sleep(WATCH_INTERVAL);
            }
        });
        Worker {
            outer,
            token,
            state,
            shares_stdout,
        }
    }

    /// The PID of the outer process.
    pub fn outer(&self) -> u32 {
        self.outer
    }

    /// The token the watcher sets; give it to the Supervisor with `set_cancel_token`.
    pub fn cancel_token(&self) -> CancelToken {
        self.token.clone()
    }

    /// The Forced path: runs on the watcher thread, at most once, and never after `finalize`.
    /// It must not call `finalize`. Capture shared state (an `Arc<Mutex<..>>` with the manifest)
    /// so it writes the same Forced record the main path would.
    pub fn on_parent_death(&self, hook: impl FnOnce() + Send + 'static) {
        lock(&self.state).hook = Some(Box::new(hook));
    }

    /// Run the main path's final step under the same once-guard; `None` if the Forced path ran.
    pub fn finalize<R>(&self, step: impl FnOnce() -> R) -> Option<R> {
        let mut state = lock(&self.state);
        if state.finalized {
            return None;
        }
        let result = step();
        state.finalized = true;
        Some(result)
    }

    /// Whether the worker's stdout is the caller's (the outer process's) stdout.
    pub fn shares_caller_stdout(&self) -> bool {
        self.shares_stdout
    }
}
