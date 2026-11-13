// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The command of tools/check-v8-sources.py: `[--root R] [--receipts] [--skip-lean]`, printing
//! the same one-line JSON and exiting 0 when the tree passes, 1 when it fails and 2 on a usage
//! error. Differences: Python's default root is the checkout holding the script, this binary's
//! is the current directory; argparse's abbreviated options (`--rec`) are not accepted.
#![forbid(unsafe_code)]

use std::path::{Component, Path, PathBuf};

use fang_json::{DumpOptions, dumps};

const USAGE: &str = "usage: fang-check-sources [-h] [--root ROOT] [--receipts] [--skip-lean]";

fn usage_error(message: &str) -> ! {
    eprintln!("{USAGE}");
    eprintln!("fang-check-sources: error: {message}");
    std::process::exit(2);
}

/// `Path.resolve()` (strict=False): symbolic links resolved through the longest existing
/// prefix, the rest appended with "." dropped and ".." taken lexically.
fn resolve(path: &Path) -> PathBuf {
    let absolute = std::path::absolute(path).unwrap_or_else(|_| path.to_path_buf());
    let components: Vec<Component<'_>> = absolute.components().collect();
    for split in (0..=components.len()).rev() {
        let prefix: PathBuf = components[..split].iter().collect();
        let Ok(mut resolved) = prefix.canonicalize() else {
            continue;
        };
        for component in &components[split..] {
            match component {
                Component::CurDir => {}
                Component::ParentDir => {
                    resolved.pop();
                }
                other => resolved.push(other.as_os_str()),
            }
        }
        return resolved;
    }
    absolute
}

fn main() {
    let mut root: Option<PathBuf> = None;
    let mut receipts = false;
    let mut skip_lean = false;
    let mut arguments = std::env::args_os().skip(1);
    while let Some(argument) = arguments.next() {
        match argument.to_str() {
            Some("-h" | "--help") => {
                println!("{USAGE}");
                println!();
                println!(
                    "Fail if any promoted version-8 Rust or Lean source differs from its source map or receipt."
                );
                return;
            }
            Some("--root") => match arguments.next() {
                Some(value) => root = Some(PathBuf::from(value)),
                None => usage_error("argument --root: expected one argument"),
            },
            Some("--receipts") => receipts = true,
            Some("--skip-lean") => skip_lean = true,
            Some(text) if text.starts_with("--root=") => {
                root = Some(PathBuf::from(&text["--root=".len()..]));
            }
            _ => usage_error(&format!(
                "unrecognized arguments: {}",
                argument.to_string_lossy()
            )),
        }
    }
    let root = resolve(&root.unwrap_or_else(|| PathBuf::from(".")));
    let report = fang_source_checks::check_tree(&root, receipts, skip_lean);
    println!(
        "{}",
        dumps(&report, &DumpOptions::default()).expect("finite values")
    );
    if report.get("status").and_then(fang_json::Value::as_str) != Some("passed") {
        std::process::exit(1);
    }
}
