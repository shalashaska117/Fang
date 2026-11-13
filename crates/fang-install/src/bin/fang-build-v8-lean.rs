// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Build lean-v8 with Lake and rerun the fixed axiom audits; see `fang_install::lean_build`.
#![forbid(unsafe_code)]

use fang_install::common::Arguments;
use fang_install::lean_build::{self, Options};

const PROGRAM: &str = "fang-build-v8-lean";
const USAGE: &str = "--root ROOT --out OUT --lean-toolchain LEAN_TOOLCHAIN (--backend BACKEND | --packages PACKAGES) \
[--aeneas-checkout AENEAS_CHECKOUT] [--receipts] [--memory-mib MEMORY_MIB] [--wall-seconds WALL_SECONDS]";

fn integer(arguments: &Arguments, name: &str, default: u64) -> Result<u64, String> {
    match arguments.value(name) {
        None => Ok(default),
        Some(text) => text
            .parse()
            .map_err(|_| format!("argument --{name}: invalid int value: '{text}'")),
    }
}

fn options(arguments: &[String]) -> Result<Options, String> {
    let parsed = Arguments::parse(
        arguments,
        &[
            "root",
            "out",
            "lean-toolchain",
            "backend",
            "packages",
            "aeneas-checkout",
            "memory-mib",
            "wall-seconds",
        ],
        &["receipts"],
    )?;
    if let Some(extra) = parsed.positional.first() {
        return Err(format!("unrecognized arguments: {extra}"));
    }
    let missing: Vec<&str> = ["root", "out", "lean-toolchain"]
        .into_iter()
        .filter(|name| parsed.value(name).is_none())
        .collect();
    if !missing.is_empty() {
        return Err(format!(
            "the following arguments are required: {}",
            missing
                .iter()
                .map(|name| format!("--{name}"))
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    match (parsed.value("backend"), parsed.value("packages")) {
        (Some(_), Some(_)) => {
            return Err("argument --packages: not allowed with argument --backend".to_string());
        }
        (None, None) => {
            return Err("one of the arguments --backend --packages is required".to_string());
        }
        _ => {}
    }
    Ok(Options {
        root: parsed.path("root").expect("required"),
        out: parsed.path("out").expect("required"),
        lean_toolchain: parsed.path("lean-toolchain").expect("required"),
        backend: parsed.path("backend"),
        packages: parsed.path("packages"),
        aeneas_checkout: parsed.path("aeneas-checkout"),
        receipts: parsed.flag("receipts"),
        memory_mib: integer(&parsed, "memory-mib", 7168)?,
        wall_seconds: integer(&parsed, "wall-seconds", 5400)?,
    })
}

fn main() {
    let worker = fang_install::guarded();
    let options = fang_install::parsed(PROGRAM, USAGE, options);
    fang_install::finish(lean_build::main(&options, Some(&worker)))
}
