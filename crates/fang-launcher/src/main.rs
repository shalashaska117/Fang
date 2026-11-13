// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Entry point of the installed `fang` command.
#![forbid(unsafe_code)]

use std::process::ExitCode;

use fang_supervisor::guard;

/// The marker of an internal stage: a profile runs this binary as a bounded child stage (for example the
/// ground-FOF kernel replay generator). It is matched only as the first argument, so `--profile` never reaches
/// it, and it reads no capability: the launcher pin already covers this binary.
const INTERNAL: &str = "--fang-internal";

fn main() -> ExitCode {
    let mut leading = std::env::args_os().skip(1);
    if leading.next().is_some_and(|first| first == INTERNAL) {
        // An internal stage runs inside the calling worker's process group, without a guard of its own, so
        // the caller's cleanup reaches it.
        let mut arguments = Vec::new();
        for argument in leading {
            match argument.into_string() {
                Ok(text) => arguments.push(text),
                Err(_) => {
                    eprintln!("fang: every argument must be valid UTF-8");
                    return ExitCode::from(64);
                }
            }
        }
        if arguments.is_empty() {
            eprintln!("fang: {INTERNAL} needs a stage name");
            return ExitCode::from(64);
        }
        let name = arguments.remove(0);
        return fang_launcher::older::internal(&name, arguments);
    }
    // The outer process only waits for the worker, so that a signal to the command still lets the worker
    // record Forced and stop every child.
    match guard::start() {
        Ok(guard::Role::Outer) => guard::run_outer(),
        Ok(guard::Role::Worker(worker)) => {
            let mut arguments = Vec::new();
            for argument in std::env::args_os().skip(1) {
                match argument.into_string() {
                    Ok(text) => arguments.push(text),
                    Err(_) => {
                        eprintln!("fang: every argument must be valid UTF-8");
                        return ExitCode::from(6);
                    }
                }
            }
            fang_launcher::dispatch::run(worker, arguments)
        }
        Err(error) => {
            eprintln!("fang: cannot start the command: {error}");
            ExitCode::from(6)
        }
    }
}
