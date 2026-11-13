// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! `fang-v8-kernel-provision`: write the revision-8 entry policy, with the entry review once it exists.

use std::ffi::OsString;
use std::process::ExitCode;

use fang_v8_kernel::provision;

fn main() -> ExitCode {
    let raw: Vec<OsString> = std::env::args_os().collect();
    match provision::main(&raw) {
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
