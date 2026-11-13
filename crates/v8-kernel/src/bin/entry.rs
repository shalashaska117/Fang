// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! `fang-v8-kernel`: the version-8 kernel entry, revision 8, under the supervisor guard.

use std::ffi::OsString;
use std::process::ExitCode;

use fang_supervisor::guard::{self, Role};
use fang_v8_kernel::{entry, internal, launch};

fn main() -> ExitCode {
    let raw: Vec<OsString> = std::env::args_os().collect();
    if raw.get(1).is_some_and(|flag| internal::is_internal(flag)) {
        return internal::run(&raw);
    }
    if raw.get(1).is_some_and(|flag| flag == launch::FLAG) {
        return launch::run(&raw);
    }
    let worker = match guard::start() {
        Ok(Role::Outer) => guard::run_outer(),
        Ok(Role::Worker(worker)) => worker,
        Err(error) => {
            eprintln!("{error}");
            return ExitCode::from(6);
        }
    };
    ExitCode::from(u8::try_from(entry::main(&raw, &worker)).unwrap_or(6))
}
