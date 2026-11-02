// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Diagnostic candidate transport. Exit 0 never means independently checked UNSAT.
#![forbid(unsafe_code)]

//! Usage: fang-bundle-candidate TOP [--tptp-root DIR] [--flat PATH]
//! Writes the candidate certificate to stdout. Stderr carries one JSON line
//! with the bundle digest and files, then the outcome line.

use fang_tptp_bundle_v8::{Error, produce_bundle};
use fang_tptp_coverage_candidate::Root;
use fang_tptp_expanded_v8::{Outcome, native_limits};
use std::io::Write;
use std::path::PathBuf;
use std::process::ExitCode;

fn json(text: &str) -> String {
    let mut output = String::from("\"");
    for character in text.chars() {
        match character {
            '"' => output.push_str("\\\""),
            '\\' => output.push_str("\\\\"),
            c if (c as u32) < 0x20 || (c as u32) > 0x7e => {
                output.push_str(&format!("\\u{:04x}", c as u32))
            }
            c => output.push(c),
        }
    }
    output.push('"');
    output
}

fn main() -> ExitCode {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let mut top = None;
    let mut tptp = None;
    let mut flat_path = None;
    let mut index = 0;
    while index < arguments.len() {
        match arguments[index].as_str() {
            "--tptp-root" if index + 1 < arguments.len() => {
                tptp = Some(PathBuf::from(&arguments[index + 1]));
                index += 2;
            }
            "--flat" if index + 1 < arguments.len() => {
                flat_path = Some(PathBuf::from(&arguments[index + 1]));
                index += 2;
            }
            value if top.is_none() && !value.starts_with("--") => {
                top = Some(PathBuf::from(value));
                index += 1;
            }
            _ => {
                eprintln!("usage: fang-bundle-candidate TOP [--tptp-root DIR] [--flat PATH]");
                return ExitCode::from(64);
            }
        }
    }
    let Some(top) = top else {
        eprintln!("usage: fang-bundle-candidate TOP [--tptp-root DIR] [--flat PATH]");
        return ExitCode::from(64);
    };
    // The values of the checker's limits record, `NativeLimits.lean`.
    let limits = native_limits();
    match produce_bundle(&top, tptp.as_deref(), &limits) {
        Ok(run) => {
            let digest: String = run
                .expanded
                .bundle
                .digest()
                .iter()
                .map(|b| format!("{b:02x}"))
                .collect();
            let files: Vec<String> = run
                .expanded
                .bundle
                .files
                .iter()
                .map(|file| {
                    format!(
                        "[{},{}]",
                        json(match file.key.root {
                            Root::Base => "base",
                            Root::Tptp => "tptp",
                        }),
                        json(&file.key.path.join("/"))
                    )
                })
                .collect();
            eprintln!(
                "{{\"bundle_sha256\":\"{digest}\",\"files\":[{}],\"declarations\":{},\"objects\":{}}}",
                files.join(","),
                run.expanded.parsed.declarations.len(),
                run.expanded.distinct_objects.len()
            );
            if let Some(path) = flat_path
                && std::fs::write(path, run.flat.as_bytes()).is_err()
            {
                eprintln!("io: flat output failed");
                return ExitCode::from(74);
            }
            match run.produced.outcome {
                Outcome::CandidateRefutation { text, .. } => {
                    if std::io::stdout().lock().write_all(text.as_bytes()).is_err() {
                        eprintln!("io: candidate output failed");
                        return ExitCode::from(74);
                    }
                    eprintln!("candidate-certificate: unchecked bundle input");
                    ExitCode::SUCCESS
                }
                Outcome::Unknown(statistics) => {
                    eprintln!(
                        "unknown: processed={} attempted={}",
                        statistics.processed_clauses, statistics.attempted_inferences
                    );
                    ExitCode::from(2)
                }
            }
        }
        Err(Error::Capture(error)) => {
            eprintln!(
                "capture: {:?} {:?} file={:?} offset={:?}",
                error.kind, error.reason, error.file, error.offset
            );
            ExitCode::from(3)
        }
        Err(Error::Render(message)) => {
            eprintln!("render: {message}");
            ExitCode::from(5)
        }
        Err(Error::Producer(fang_tptp_expanded_v8::Error::Adapter(error))) => {
            eprintln!("adapter: {error:?}");
            ExitCode::from(3)
        }
        Err(Error::Producer(fang_tptp_expanded_v8::Error::Serialization(error))) => {
            eprintln!("serialization: {error:?}");
            ExitCode::from(4)
        }
        Err(Error::Producer(fang_tptp_expanded_v8::Error::WrongTraceVersion)) => {
            eprintln!("internal: ordered serializer envelope mismatch");
            ExitCode::from(5)
        }
    }
}
