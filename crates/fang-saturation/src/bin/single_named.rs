// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Diagnostic candidate transport. Exit 0 never means independently checked UNSAT.
#![forbid(unsafe_code)]

//! `fang-v3-single` with naming: input on stdin, the same output and exit codes as its search
//! path. The preparation is the checker's expanded entry with naming at the record's threshold,
//! under the final limits record; then the saturation search runs on the prepared clauses.

use fang_equality_search::{Error as SearchError, PreparedError};
use fang_saturation::producer::{self, FLAGS_USAGE, Outcome as V3};
use fang_tptp_expanded_integration::Error as AdapterError;
use fang_tptp_expanded_integration::final_limits::{NAMING_THRESHOLD, final_limits};
use fang_tptp_expanded_integration::prepare_named;
use std::io::{Read, Write};
use std::process::ExitCode;
use std::time::Instant;

fn main() -> ExitCode {
    let started = Instant::now();
    let usage = format!("usage: fang-v3-single-named {FLAGS_USAGE} < input");
    let (flags, rest) = match producer::split(std::env::args().skip(1).collect(), started) {
        Ok(split) => split,
        Err(message) => {
            eprintln!("{usage} ({message})");
            return ExitCode::from(64);
        }
    };
    let options = match flags.options() {
        Ok(options) => options,
        Err(message) => {
            eprintln!("{usage} ({message})");
            return ExitCode::from(64);
        }
    };
    if !rest.is_empty() {
        eprintln!("{usage}");
        return ExitCode::from(64);
    }
    let limits = final_limits();
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
    let prepared = match prepare_named(&input, &limits, NAMING_THRESHOLD) {
        Ok(prepared) => prepared,
        Err(error) => {
            eprintln!("adapter: {error:?}");
            return ExitCode::from(3);
        }
    };
    // As the reviewed entry: both symbol tables are charged to the adapter's operation cap.
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
