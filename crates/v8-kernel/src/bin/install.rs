// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! `fang-v8-kernel-install`: install entry revision 8 into a fresh root, under the supervisor guard.

use std::ffi::OsString;
use std::process::ExitCode;

use fang_supervisor::guard::{self, Role};
use fang_v8_kernel::install;

fn main() -> ExitCode {
    let raw: Vec<OsString> = std::env::args_os().collect();
    match guard::start() {
        Ok(Role::Outer) => guard::run_outer(),
        Ok(Role::Worker(_)) => {}
        Err(error) => {
            eprintln!("{error}");
            return ExitCode::from(6);
        }
    }
    match install::main(&raw) {
        Ok(summary) => {
            let text =
                fang_json::dumps(&summary, &fang_json::DumpOptions::default()).unwrap_or_default();
            println!("{text}");
            ExitCode::SUCCESS
        }
        Err(message) => {
            eprintln!("{message}");
            ExitCode::from(1)
        }
    }
}
