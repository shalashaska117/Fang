// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Diagnostic candidate transport. Exit 0 never means an independently checked result.
#![forbid(unsafe_code)]

//! Single-file signed producer with naming:
//! `fang-v3-signed-named --search v3 [FLAGS] [--render] (--goal N | --inputs) < input`.
//! The task is prepared as the single-file signed checker with naming replays it, under the final limits record
//! and at its naming threshold, then the third version's portfolio searches the prepared clauses; the schedule
//! comes from `--set portfolio=...`. The certificate is bounded by the record's certificate limit. Exit 0 writes an
//! unchecked candidate certificate, 2 means the search gave up, 1 is a typed error, 64 a usage error and 74 an
//! input or output error; none of these is a checked result.

#[path = "../experimental/final_limits.rs"]
mod final_limits;

use fang_equality_search::{Error as SearchError, PreparedError};
use fang_saturation::producer::{self, FLAGS_USAGE, Mode, Refutation};
use fang_saturation::stats::Json;
use fang_tptp_signed_roles::{
    Error as SignedError, Selection, error_kind, prepare_task_named, render,
};
use std::io::{Read, Write};
use std::process::ExitCode;
use std::time::{Duration, Instant};

fn usage(detail: &str) -> ExitCode {
    eprintln!(
        "usage: fang-v3-signed-named --search v3 {FLAGS_USAGE} [--render] (--goal N | --inputs) < input{detail}"
    );
    ExitCode::from(64)
}

fn signed_error(error: SignedError) -> ExitCode {
    eprintln!("error: {} {error:?}", error_kind(&error));
    ExitCode::from(1)
}

fn main() -> ExitCode {
    let started = Instant::now();
    let (flags, mut arguments) = match producer::split(std::env::args().skip(1).collect(), started)
    {
        Ok(split) => split,
        Err(message) => return usage(&format!(" ({message})")),
    };
    if flags.mode != Mode::V3 {
        return usage(" (--search v3 is required)");
    }
    if flags.trace.is_some() {
        return usage(" (--trace is unavailable on this route)");
    }
    let mut options = match flags.options() {
        Ok(options) => options,
        Err(message) => return usage(&format!(" ({message})")),
    };
    let render_only = arguments.first().is_some_and(|flag| flag == "--render");
    if render_only {
        arguments.remove(0);
    }
    let selection = match arguments.as_slice() {
        [flag] if flag == "--inputs" => Selection::Inputs,
        [flag, value] if flag == "--goal" => match value.parse() {
            Ok(index) => Selection::Goal(index),
            Err(_) => return usage(""),
        },
        _ => return usage(""),
    };
    let limits = final_limits::replay_limits();
    options.max_certificate_bytes = options
        .max_certificate_bytes
        .min(final_limits::CERTIFICATE_BYTES);
    // The same reserve as the third version's single-file producer: a tenth of the limit, at most one second.
    let deadline = flags.time_limit.map(|seconds| {
        let reserve = (seconds * 0.1).min(1.0);
        started + Duration::from_secs_f64((seconds - reserve).max(0.0))
    });
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
    let prepared =
        match prepare_task_named(&input, selection, &limits, final_limits::NAMING_THRESHOLD) {
            Ok(prepared) => prepared,
            Err(error) => return signed_error(error),
        };
    let mut stdout = std::io::stdout().lock();
    if render_only {
        if stdout.write_all(render(&prepared).as_bytes()).is_err() {
            eprintln!("io: output failed");
            return ExitCode::from(74);
        }
        return ExitCode::SUCCESS;
    }
    let result =
        producer::refute_prepared_portfolio(&prepared, &options, deadline, flags.memory_mib);
    let mut stats = Json::new();
    stats
        .string("search", "v3")
        .string("route", "signed-named")
        .string(
            "outcome",
            match &result {
                Refutation::Candidate { .. } => "candidate",
                Refutation::Unknown { .. } => "unknown",
                Refutation::Stopped(_) => "resource",
                _ => "error",
            },
        )
        .number("prepared_clauses", prepared.clauses.len() as u64)
        .number("total_ms", flags.elapsed_ms())
        .number("naming_threshold", final_limits::NAMING_THRESHOLD as u64);
    if let Refutation::Candidate { text, .. } = &result {
        stats.number("certificate_bytes", text.len() as u64);
    }
    flags.write_stats(&stats.finish());
    match result {
        Refutation::Candidate { text, .. } => {
            if stdout.write_all(text.as_bytes()).is_err() {
                eprintln!("io: candidate output failed");
                return ExitCode::from(74);
            }
            eprintln!("candidate-certificate: unchecked signed task");
            ExitCode::SUCCESS
        }
        Refutation::Unknown {
            processed,
            attempted,
        } => {
            eprintln!("unknown: processed={processed} attempted={attempted}");
            ExitCode::from(2)
        }
        Refutation::Stopped(message) => signed_error(SignedError::Search(PreparedError::Search(
            SearchError::Resource(message),
        ))),
        Refutation::Invalid(kind) => {
            signed_error(SignedError::Search(PreparedError::Invalid(kind)))
        }
        Refutation::CertificateBytes { .. } => signed_error(SignedError::Serialization(
            SearchError::Resource("expanded certificate byte limit"),
        )),
        Refutation::Internal(message) => signed_error(SignedError::Internal(message)),
    }
}
