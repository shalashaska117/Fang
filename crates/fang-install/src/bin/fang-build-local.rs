// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Build the older CNF profile, and with --fof the bounded ground-FOF profile; see `fang_install::local_build`.
#![forbid(unsafe_code)]

use fang_install::common::Arguments;
use fang_install::local_build::{self, Options};

const USAGE: &str = "[--root ROOT] --out OUT --lean-tools LEAN_TOOLS [--cargo CARGO] [--fof]";

fn options(arguments: &[String]) -> Result<Options, String> {
    let parsed = Arguments::parse(arguments, &["root", "out", "lean-tools", "cargo"], &["fof"])?;
    if let Some(extra) = parsed.positional.first() {
        return Err(format!("unrecognized arguments: {extra}"));
    }
    fang_install::missing(&parsed, &["out", "lean-tools"])?;
    if !cfg!(target_os = "linux") {
        return Err("Local setup currently requires Linux or WSL".to_string());
    }
    Ok(Options {
        root: parsed.path("root").unwrap_or_else(|| ".".into()),
        out: parsed.path("out").expect("required"),
        lean_tools: parsed.path("lean-tools").expect("required"),
        cargo: parsed.value("cargo").unwrap_or("cargo").to_string(),
        fof: parsed.flag("fof"),
    })
}

fn main() {
    let worker = fang_install::guarded();
    let options = fang_install::parsed("fang-build-local", USAGE, options);
    fang_install::finish(local_build::main(&options, Some(&worker)))
}
