// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Diagnostic candidate transport. Exit 0 never means independently checked UNSAT.
#![forbid(unsafe_code)]

//! Drop-in for `fang-expanded-candidate` (crates/fang-v8): input on stdin, the same output and exit codes.
//! With `--search v2` (the default) it runs the reviewed producer unchanged; with `--search v3` it runs the
//! reviewed preparation, then the saturation search. Search counters go only to the `--stats` file.

use fang_equality_search::{Error as SearchError, PreparedError};
use fang_saturation::producer::{self, FLAGS_USAGE, Mode, Outcome as V3};
use fang_tptp_expanded_integration::Error as AdapterError;
use fang_tptp_expanded_v8::{Error, Outcome, native_limits, produce};
use std::io::{Read, Write};
use std::process::ExitCode;
use std::time::Instant;

fn main() -> ExitCode {
    let started = Instant::now();
    let (flags, rest) = match producer::split(std::env::args().skip(1).collect(), started) {
        Ok(split) => split,
        Err(message) => {
            eprintln!("usage: fang-v3-single {FLAGS_USAGE} < input ({message})");
            return ExitCode::from(64);
        }
    };
    let options = match flags.options() {
        Ok(options) => options,
        Err(message) => {
            eprintln!("usage: fang-v3-single {FLAGS_USAGE} < input ({message})");
            return ExitCode::from(64);
        }
    };
    if !rest.is_empty() {
        eprintln!("usage: fang-v3-single {FLAGS_USAGE} < input");
        return ExitCode::from(64);
    }
    let limits = native_limits();
    let maximum = u64::try_from(limits.input.input.max_input_bytes)
        .unwrap_or(u64::MAX)
        .saturating_add(1);
    let mut input = Vec::new();
    if std::io::stdin()
        .take(maximum)
        .read_to_end(&mut input)
        .is_err()
    {
        eprintln!("io: input read failed");
        return ExitCode::from(74);
    }
    if flags.mode == Mode::V2 {
        return match produce(&input, &limits) {
            Ok(output) => {
                let prepared = Some(output.prepared.clauses.len());
                match output.outcome {
                    Outcome::CandidateRefutation {
                        text, statistics, ..
                    } => {
                        flags.v2_stats("candidate", Some(&statistics), prepared);
                        if std::io::stdout().lock().write_all(text.as_bytes()).is_err() {
                            eprintln!("io: candidate output failed");
                            return ExitCode::from(74);
                        }
                        eprintln!("candidate-certificate: unchecked original input");
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
            Err(Error::Adapter(error)) => {
                flags.v2_stats("adapter-error", None, None);
                eprintln!("adapter: {error:?}");
                ExitCode::from(3)
            }
            Err(Error::Serialization(error)) => {
                flags.v2_stats("serialization-error", None, None);
                eprintln!("serialization: {error:?}");
                ExitCode::from(4)
            }
            Err(Error::WrongTraceVersion) => {
                flags.v2_stats("internal-error", None, None);
                eprintln!("internal: ordered serializer envelope mismatch");
                ExitCode::from(5)
            }
        };
    }
    let prepared = match fang_tptp_expanded_integration::prepare(&input, &limits) {
        Ok(prepared) => prepared,
        Err(error) => {
            eprintln!("adapter: {error:?}");
            return ExitCode::from(3);
        }
    };
    // The reviewed entry charges both symbol tables to the adapter's operation cap before searching.
    let charged = prepared
        .adapter_operations
        .saturating_add(prepared.functions.len() + prepared.predicates.len());
    if charged > limits.max_adapter_operations {
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
    match producer::run(
        &flags,
        &options,
        &prepared.clauses,
        &functions,
        &predicates,
        None,
        None,
    ) {
        V3::Candidate(text) => {
            if std::io::stdout().lock().write_all(text.as_bytes()).is_err() {
                eprintln!("io: candidate output failed");
                return ExitCode::from(74);
            }
            eprintln!("candidate-certificate: unchecked original input");
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
