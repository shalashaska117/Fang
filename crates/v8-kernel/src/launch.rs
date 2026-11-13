// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The direct compiler launch of revision 7 (its LAUNCH one-liner): change to the project
//! directory, add the recorded search variables to the supervised environment, and replace
//! this process with the program.
//!
//! The supervisor passes only approved variables to a child, and LEAN_SRC_PATH, LEAN_SYSROOT
//! and LD_LIBRARY_PATH are not among them. They are added here, at exec, and the stage record
//! names them under `added_at_exec`.

use std::ffi::OsString;
use std::os::unix::process::CommandExt;
use std::process::{Command, ExitCode};

use fang_json::{ParseLimits, Value};

/// The first argument that selects the launch.
pub const FLAG: &str = "--launch";

/// The launch command for `program arguments`: this executable with the flag in front.
pub fn command(
    executable: &std::path::Path,
    project: &std::path::Path,
    added: &str,
    program: &std::path::Path,
) -> Vec<OsString> {
    vec![
        executable.as_os_str().to_owned(),
        OsString::from(FLAG),
        project.as_os_str().to_owned(),
        OsString::from(added),
        program.as_os_str().to_owned(),
    ]
}

/// `[executable, FLAG, project, added JSON, program, arguments...]`; returns only on failure.
pub fn run(arguments: &[OsString]) -> ExitCode {
    let [_, _, project, added, program, rest @ ..] = arguments else {
        eprintln!("usage: {FLAG} PROJECT ADDED-JSON PROGRAM [ARGUMENTS...]");
        return ExitCode::from(2);
    };
    let Some(added) = added.to_str() else {
        eprintln!("The added environment is not UTF-8");
        return ExitCode::from(2);
    };
    let variables = match fang_json::parse(
        added.as_bytes(),
        &ParseLimits {
            max_bytes: 1 << 20,
            max_depth: 4,
        },
    ) {
        Ok(Value::Object(object)) => {
            let mut variables = Vec::new();
            for (key, value) in object.iter() {
                let Some(text) = value.as_str() else {
                    eprintln!("The added environment holds a value that is not a string");
                    return ExitCode::from(2);
                };
                variables.push((key.to_owned(), text.to_owned()));
            }
            variables
        }
        _ => {
            eprintln!("The added environment is not a JSON object");
            return ExitCode::from(2);
        }
    };
    if let Err(error) = std::env::set_current_dir(project) {
        eprintln!("cannot enter {}: {error}", project.to_string_lossy());
        return ExitCode::from(2);
    }
    let error = Command::new(program).args(rest).envs(variables).exec();
    eprintln!("cannot start {}: {error}", program.to_string_lossy());
    ExitCode::from(127)
}
