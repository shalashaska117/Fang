// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The source-map and dependency checks of the Fang tools.
//!
//! - `v8`: tools/fang_szs/v8_dependencies.py (the Rust and Lean source maps, the code view,
//!   the receipt checks, the include rule);
//! - `deps`: tools/fang_szs/dependencies.py;
//! - `fof`: tools/fang_szs/fof_dependencies.py;
//! - `backend`: tools/fang_szs/v8_backend.py;
//! - `check_tree`: tools/check-v8-sources.py.
//!
//! Functions keep Python's names and contracts. A `check` callback runs where Python calls
//! check(), and its Failure passes through unchanged. Every other error carries the text of
//! the Python exception (`Error`'s Display is Python's `str(error)`).
#![forbid(unsafe_code)]

pub mod backend;
pub mod deps;
mod error;
pub mod fof;
mod util;
pub mod v8;

pub use error::Error;

use fang_json::{Object, Value};
use std::path::Path;

/// tools/check-v8-sources.py: the JSON it prints, passed or failed.
pub fn check_tree(root: &Path, receipts: bool, skip_lean: bool) -> Value {
    let run = || -> Result<Object, Error> {
        let mut no_check = || Ok(());
        let manifest = util::read_toml(&root.join("Cargo.toml"))?;
        let rust_map = v8::load_map(root, v8::RUST_MAP, v8::RUST_SCHEMA, &mut no_check)?;
        v8::check_workspace(root, &manifest, &rust_map, &mut no_check)?;
        let mut report = Object::new();
        report.set("status", "passed");
        report.set("rust_files", v8::rust_files(root, &mut no_check)?.len());
        if !skip_lean {
            report.set("lean_files", v8::lean_files(root, &mut no_check)?.len());
        }
        if receipts {
            report.set(
                "rust_receipt_entries",
                v8::check_rust_receipts(root, &mut no_check)?,
            );
            if !skip_lean {
                report.set(
                    "lean_receipt_entries",
                    v8::check_lean_receipts(root, &mut no_check)?,
                );
            }
        }
        Ok(report)
    };
    match run() {
        Ok(report) => Value::Object(report),
        Err(error) => {
            let mut report = Object::new();
            report.set("status", "failed");
            report.set("error", error.to_string());
            Value::Object(report)
        }
    }
}
