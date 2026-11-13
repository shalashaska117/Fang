// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Fetch the pinned Aeneas backend for a clean lean-v8 build; see `fang_install::fetch`.
#![forbid(unsafe_code)]

use fang_install::common::Arguments;
use fang_install::fetch::{self, Options};

const USAGE: &str = "[--root ROOT] --work WORK --lean-toolchain LEAN_TOOLCHAIN";

fn options(arguments: &[String]) -> Result<Options, String> {
    let parsed = Arguments::parse(arguments, &["root", "work", "lean-toolchain"], &[])?;
    if let Some(extra) = parsed.positional.first() {
        return Err(format!("unrecognized arguments: {extra}"));
    }
    fang_install::missing(&parsed, &["work", "lean-toolchain"])?;
    if !cfg!(target_os = "linux") {
        return Err("Run on Linux or WSL".to_string());
    }
    Ok(Options {
        root: parsed.path("root").unwrap_or_else(|| ".".into()),
        work: parsed.path("work").expect("required"),
        lean_toolchain: parsed.path("lean-toolchain").expect("required"),
    })
}

fn main() {
    let options = fang_install::parsed("fang-fetch-v8-backend", USAGE, options);
    fang_install::finish(fetch::main(&options))
}
