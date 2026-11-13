// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The command of tools/replay/axiom_audit.py: `--self-test`, or `LOG THEOREM...` printing the
//! reports as `json.dumps(..., indent=2)`. A refused audit prints "ValueError: <message>" on
//! stderr and exits 1, as the uncaught Python exception did.
#![forbid(unsafe_code)]

use fang_json::{DumpOptions, Object, Value, dumps};

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    if arguments.iter().any(|argument| argument == "--self-test") {
        match fang_axiom_audit::self_test() {
            Ok(result) => println!(
                "{}",
                dumps(&result, &DumpOptions::default()).expect("finite values")
            ),
            Err(error) => {
                eprintln!("AssertionError: {error}");
                std::process::exit(1);
            }
        }
        return;
    }
    let Some((log, theorems)) = arguments.split_first() else {
        eprintln!("usage: fang-axiom-audit [--self-test] [log] [theorems ...]");
        eprintln!("fang-axiom-audit: error: log and required theorem names are required");
        std::process::exit(2);
    };
    let bytes = match std::fs::read(log) {
        Ok(bytes) => bytes,
        Err(error) => {
            eprintln!("OSError: {error}");
            std::process::exit(1);
        }
    };
    let Ok(text) = String::from_utf8(bytes) else {
        eprintln!("UnicodeDecodeError: the log is not UTF-8");
        std::process::exit(1);
    };
    // Path.read_text() translates line endings.
    let text = text.replace("\r\n", "\n").replace('\r', "\n");
    let required: Vec<&str> = theorems.iter().map(String::as_str).collect();
    match fang_axiom_audit::audit_axioms(&text, &required) {
        Ok(reports) => {
            let object: Object = reports
                .into_iter()
                .map(|(name, axioms)| {
                    (
                        name,
                        Value::Array(axioms.into_iter().map(Value::from).collect()),
                    )
                })
                .collect();
            println!(
                "{}",
                dumps(
                    &Value::Object(object),
                    &DumpOptions {
                        indent: Some(2),
                        sort_keys: false
                    }
                )
                .expect("finite")
            );
        }
        Err(error) => {
            eprintln!("ValueError: {error}");
            std::process::exit(1);
        }
    }
}
