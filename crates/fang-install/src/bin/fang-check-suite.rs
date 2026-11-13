// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Snapshot and check the std-only Lean checker and frontend proof sources; see `fang_install::check_suite`.
#![forbid(unsafe_code)]

use fang_install::check_suite::{self, Options};
use fang_install::common::Arguments;

const USAGE: &str = "[--out OUT] [--with-tstp] [--timeout-seconds TIMEOUT_SECONDS] [--memory-mib MEMORY_MIB] root lean";

fn options(arguments: &[String]) -> Result<Options, String> {
    let parsed = Arguments::parse(
        arguments,
        &["out", "timeout-seconds", "memory-mib"],
        &["with-tstp"],
    )?;
    let integer = |name: &str, default: i64| -> Result<i64, String> {
        parsed.value(name).map_or(Ok(default), |text| {
            text.parse()
                .map_err(|_| format!("argument --{name}: invalid int value: '{text}'"))
        })
    };
    match parsed.positional.len() {
        0 => return Err("the following arguments are required: root, lean".to_string()),
        1 => return Err("the following arguments are required: lean".to_string()),
        2 => {}
        _ => {
            return Err(format!(
                "unrecognized arguments: {}",
                parsed.positional[2..].join(" ")
            ));
        }
    }
    let options = Options {
        root: parsed.positional[0].clone().into(),
        lean: parsed.positional[1].clone().into(),
        out: parsed.path("out"),
        with_tstp: parsed.flag("with-tstp"),
        timeout_seconds: integer("timeout-seconds", 120)?,
        memory_mib: integer("memory-mib", 2048)?,
    };
    if options.timeout_seconds <= 0 || options.memory_mib <= 0 {
        return Err("resource limits must be positive".to_string());
    }
    Ok(options)
}

fn main() {
    let options = fang_install::parsed("fang-check-suite", USAGE, options);
    fang_install::finish(check_suite::main(&options))
}
