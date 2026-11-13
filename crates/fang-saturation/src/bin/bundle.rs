// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Diagnostic candidate transport. Exit 0 never means independently checked UNSAT.
#![forbid(unsafe_code)]

//! Drop-in for `fang-bundle-candidate` (crates/tptp-bundle-v8): fang-v3-bundle [FLAGS] TOP [--tptp-root DIR]
//! [--flat PATH], with the same output and exit codes. With `--search v2` (the default) it runs the reviewed
//! producer unchanged; with `--search v3` it runs the reviewed capture, rendering and preparation, then the
//! saturation search.

use fang_equality_search::{Error as SearchError, PreparedError};
use fang_saturation::producer::{self, FLAGS_USAGE, Mode, Outcome as V3};
use fang_tptp_bundle_v8::{Error, flat_limits, produce_bundle, render};
use fang_tptp_coverage_candidate::{Expanded, Root, capture};
use fang_tptp_expanded_integration::Error as AdapterError;
use fang_tptp_expanded_v8::{Outcome, native_limits};
use std::io::Write;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Instant;

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

/// The JSON line the reviewed producer prints first on standard error.
fn bundle_line(expanded: &Expanded) -> String {
    let digest: String = expanded
        .bundle
        .digest()
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect();
    let files: Vec<String> = expanded
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
    format!(
        "{{\"bundle_sha256\":\"{digest}\",\"files\":[{}],\"declarations\":{},\"objects\":{}}}",
        files.join(","),
        expanded.parsed.declarations.len(),
        expanded.distinct_objects.len()
    )
}

fn usage(message: &str) -> ExitCode {
    eprintln!(
        "usage: fang-v3-bundle {FLAGS_USAGE} TOP [--tptp-root DIR] [--flat PATH] ({message})"
    );
    ExitCode::from(64)
}

fn main() -> ExitCode {
    let started = Instant::now();
    let (flags, arguments) = match producer::split(std::env::args().skip(1).collect(), started) {
        Ok(split) => split,
        Err(message) => return usage(&message),
    };
    let options = match flags.options() {
        Ok(options) => options,
        Err(message) => return usage(&message),
    };
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
    let limits = native_limits();
    if flags.mode == Mode::V2 {
        return match produce_bundle(&top, tptp.as_deref(), &limits) {
            Ok(run) => {
                eprintln!("{}", bundle_line(&run.expanded));
                if let Some(path) = flat_path
                    && std::fs::write(path, run.flat.as_bytes()).is_err()
                {
                    eprintln!("io: flat output failed");
                    return ExitCode::from(74);
                }
                let prepared = Some(run.produced.prepared.clauses.len());
                match run.produced.outcome {
                    Outcome::CandidateRefutation {
                        text, statistics, ..
                    } => {
                        flags.v2_stats("candidate", Some(&statistics), prepared);
                        if std::io::stdout().lock().write_all(text.as_bytes()).is_err() {
                            eprintln!("io: candidate output failed");
                            return ExitCode::from(74);
                        }
                        eprintln!("candidate-certificate: unchecked bundle input");
                        ExitCode::SUCCESS
                    }
                    Outcome::Unknown(statistics) => {
                        flags.v2_stats("unknown", Some(&statistics), prepared);
                        eprintln!(
                            "unknown: processed={} attempted={}",
                            statistics.processed_clauses, statistics.attempted_inferences
                        );
                        ExitCode::from(2)
                    }
                }
            }
            Err(Error::Capture(error)) => {
                flags.v2_stats("capture-error", None, None);
                eprintln!(
                    "capture: {:?} {:?} file={:?} offset={:?}",
                    error.kind, error.reason, error.file, error.offset
                );
                ExitCode::from(3)
            }
            Err(Error::Render(message)) => {
                flags.v2_stats("render-error", None, None);
                eprintln!("render: {message}");
                ExitCode::from(5)
            }
            Err(Error::Producer(fang_tptp_expanded_v8::Error::Adapter(error))) => {
                flags.v2_stats("adapter-error", None, None);
                eprintln!("adapter: {error:?}");
                ExitCode::from(3)
            }
            Err(Error::Producer(fang_tptp_expanded_v8::Error::Serialization(error))) => {
                flags.v2_stats("serialization-error", None, None);
                eprintln!("serialization: {error:?}");
                ExitCode::from(4)
            }
            Err(Error::Producer(fang_tptp_expanded_v8::Error::WrongTraceVersion)) => {
                flags.v2_stats("internal-error", None, None);
                eprintln!("internal: ordered serializer envelope mismatch");
                ExitCode::from(5)
            }
        };
    }
    let coverage_limits = fang_tptp_coverage_candidate::Limits::default();
    let expanded = match capture(&top, tptp.as_deref(), &coverage_limits) {
        Ok(expanded) => expanded,
        Err(error) => {
            eprintln!(
                "capture: {:?} {:?} file={:?} offset={:?}",
                error.kind, error.reason, error.file, error.offset
            );
            return ExitCode::from(3);
        }
    };
    let flat = match render(&expanded) {
        Ok(flat) => flat,
        Err(Error::Render(message)) => {
            eprintln!("render: {message}");
            return ExitCode::from(5);
        }
        Err(_) => {
            eprintln!("render: unexpected rendering error");
            return ExitCode::from(5);
        }
    };
    let widened = flat_limits(&limits, &expanded, &flat);
    let prepared = match fang_tptp_expanded_integration::prepare(flat.as_bytes(), &widened) {
        Ok(prepared) => prepared,
        Err(error) => {
            eprintln!("adapter: {error:?}");
            return ExitCode::from(3);
        }
    };
    let charged = prepared
        .adapter_operations
        .saturating_add(prepared.functions.len() + prepared.predicates.len());
    if charged > widened.max_adapter_operations {
        eprintln!(
            "adapter: {:?}",
            AdapterError::Resource("equality adapter operation cap")
        );
        return ExitCode::from(3);
    }
    let functions: Vec<usize> = prepared
        .functions
        .iter()
        .map(|symbol| symbol.arity)
        .collect();
    let predicates: Vec<usize> = prepared
        .predicates
        .iter()
        .map(|symbol| symbol.arity)
        .collect();
    let outcome = producer::run(
        &flags,
        &options,
        &prepared.clauses,
        &functions,
        &predicates,
        None,
        None,
    );
    if matches!(outcome, V3::Candidate(_) | V3::Unknown { .. }) {
        eprintln!("{}", bundle_line(&expanded));
        if let Some(path) = flat_path
            && std::fs::write(path, flat.as_bytes()).is_err()
        {
            eprintln!("io: flat output failed");
            return ExitCode::from(74);
        }
    }
    match outcome {
        V3::Candidate(text) => {
            if std::io::stdout().lock().write_all(text.as_bytes()).is_err() {
                eprintln!("io: candidate output failed");
                return ExitCode::from(74);
            }
            eprintln!("candidate-certificate: unchecked bundle input");
            ExitCode::SUCCESS
        }
        V3::Unknown {
            processed,
            attempted,
        } => {
            eprintln!("unknown: processed={processed} attempted={attempted}");
            ExitCode::from(2)
        }
        V3::Stopped(message) => {
            let error = AdapterError::Search(PreparedError::Search(SearchError::Resource(message)));
            eprintln!("adapter: {error:?}");
            ExitCode::from(3)
        }
        V3::Invalid(kind) => {
            eprintln!(
                "adapter: {:?}",
                AdapterError::Search(PreparedError::Invalid(kind))
            );
            ExitCode::from(3)
        }
        V3::CertificateBytes => {
            eprintln!(
                "serialization: {:?}",
                SearchError::Resource("expanded certificate byte limit")
            );
            ExitCode::from(4)
        }
        V3::Internal(message) => {
            eprintln!("internal: {message}");
            ExitCode::from(5)
        }
    }
}
