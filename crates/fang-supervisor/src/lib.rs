// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Bounded Linux children under one deadline, without a background service.
//!
//! The specification is tools/fang_szs/supervisor.py; every record field keeps its name and
//! meaning. Where std has no call for what Python did through the OS, this crate uses /proc,
//! /bin/kill and getconf, and the differences are listed in rust-tools/DESIGN.md:
//! - no child subreaper: owned processes are the process groups of the stages and the
//!   parent-PID tree, so a grandchild that leaves its group and is orphaned is not seen;
//! - no signal handlers: `guard` runs the work in a worker process that watches its parent;
//! - no sealed memfd: snapshots are 0400 files checked by identity and hash;
//! - children's CPU times come from /proc/self/stat at clock-tick resolution.
#![forbid(unsafe_code)]

pub mod guard;
mod io;
mod limits;
mod procfs;
mod run;
mod status;

pub use io::{Fault, Snapshot, fresh_token, make_temp_dir, read_regular, strict_json, write_json};
pub use limits::Limits;
pub use procfs::{InheritedDescriptor, Times, inherited_descriptors, process_times};
pub use run::{
    CancelToken, Clean, ENVIRONMENT_KEYS, Environment, Stage, StageOutput, StageRecord, Supervisor,
    child_environment, positive_status_line,
};
pub use status::{Failure, Status};
