// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Build and install steps of Fang, in Rust. Each module ports one Python script, which is its specification:
//! `lean_build` is tools/build-v8-lean.py, `fetch` tools/fetch-v8-backend.py, `check_suite`
//! tools/replay/check-suite.py, `local_build` tools/build-local.py and build-fof-local.py, and `v8_install`
//! tools/build-v8-local.py. The manifests keep the scripts' fields, stage names and commands;
//! experiments/product/install-chain/DESIGN.md lists the deliberate differences.
#![forbid(unsafe_code)]

pub mod adapt;
pub mod check_suite;
pub mod common;
pub mod fetch;
pub mod inventory;
pub mod lean_build;
pub mod local_build;
pub mod report;
pub mod scan;
pub mod v8_install;

/// Start under the supervisor's guard: the outer process waits for the worker and exits with its status.
pub fn guarded() -> fang_supervisor::guard::Worker {
    use fang_supervisor::guard::{self, Role};
    match guard::start() {
        Ok(Role::Outer) => guard::run_outer(),
        Ok(Role::Worker(worker)) => worker,
        Err(error) => {
            eprintln!("OSError: {error}");
            std::process::exit(1);
        }
    }
}

/// Exit with the step's status, or print the error as the last line of Python's traceback would and exit 1.
pub fn finish(result: common::Result<i32>) -> ! {
    match result {
        Ok(code) => std::process::exit(code),
        Err(error) => {
            eprintln!("{}", error.typed());
            std::process::exit(1);
        }
    }
}

/// Parse the command line with `parse`, or exit with argparse's status 2.
pub fn parsed<T>(
    program: &str,
    usage: &str,
    parse: impl FnOnce(&[String]) -> Result<T, String>,
) -> T {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    match parse(&arguments) {
        Ok(value) => value,
        Err(message) => std::process::exit(common::usage_error(program, usage, &message)),
    }
}

/// argparse's message for missing required options.
pub fn missing(parsed: &common::Arguments, names: &[&str]) -> Result<(), String> {
    let missing: Vec<String> = names
        .iter()
        .filter(|name| parsed.value(name).is_none())
        .map(|name| format!("--{name}"))
        .collect();
    if missing.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "the following arguments are required: {}",
            missing.join(", ")
        ))
    }
}
