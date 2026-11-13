// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Install the version-8 fang command into a fresh directory; see `fang_install::v8_install`.
#![forbid(unsafe_code)]

use fang_install::common::Arguments;
use fang_install::v8_install::{self, Options};

const USAGE: &str = "[--root ROOT] --out OUT [--cargo CARGO] --lean-toolchain LEAN_TOOLCHAIN \
(--lean-build LEAN_BUILD | --backend BACKEND | --packages PACKAGES) [--aeneas-checkout AENEAS_CHECKOUT] [--lean-work LEAN_WORK] \
[--older OLDER]";

fn options(arguments: &[String]) -> Result<Options, String> {
    let parsed = Arguments::parse(
        arguments,
        &[
            "root",
            "out",
            "cargo",
            "lean-toolchain",
            "lean-build",
            "backend",
            "packages",
            "aeneas-checkout",
            "lean-work",
            "older",
        ],
        &[],
    )?;
    if let Some(extra) = parsed.positional.first() {
        return Err(format!("unrecognized arguments: {extra}"));
    }
    fang_install::missing(&parsed, &["out", "lean-toolchain"])?;
    let sources: Vec<&str> = ["lean-build", "backend", "packages"]
        .into_iter()
        .filter(|name| parsed.value(name).is_some())
        .collect();
    match sources.len() {
        0 => {
            return Err(
                "one of the arguments --lean-build --backend --packages is required".to_string(),
            );
        }
        1 => {}
        _ => {
            return Err(format!(
                "argument --{}: not allowed with argument --{}",
                sources[1], sources[0]
            ));
        }
    }
    Ok(Options {
        root: parsed.path("root").unwrap_or_else(|| ".".into()),
        out: parsed.path("out").expect("required"),
        cargo: parsed.value("cargo").unwrap_or("cargo").to_string(),
        lean_toolchain: parsed.path("lean-toolchain").expect("required"),
        lean_build: parsed.path("lean-build"),
        backend: parsed.path("backend"),
        packages: parsed.path("packages"),
        aeneas_checkout: parsed.path("aeneas-checkout"),
        lean_work: parsed.path("lean-work"),
        older: parsed.path("older"),
    })
}

fn main() {
    let worker = fang_install::guarded();
    let options = fang_install::parsed("fang-build-v8-local", USAGE, options);
    fang_install::finish(v8_install::main(&options, Some(&worker)))
}
