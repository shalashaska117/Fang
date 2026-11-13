// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Diagnostic candidate transport. Exit 0 never means an independently checked result.
#![forbid(unsafe_code)]

//! Experimental parameterised CLI for `signed-bundle-produce` (crates/tptp-signed-bundle): fang-v3-signed-bundle [FLAGS] [--render]
//! [--skolem-symbols N] (--goal N | --inputs | --goals) ROOT PATH FILE..., with the same output and exit codes.
//! With `--search v2` (the default) it runs the reviewed producer unchanged; with `--search v3` it runs the
//! named whole-task discovery and a separately prepared cited replay.
//! ReplayConfig is supplied by the matching checker record; this source fixes
//! no adoption values. --render prints the named whole task without search.
//! The experimental cited route rejects --trace explicitly because its search
//! API does not expose the actual given-clause trace.

#[path = "../cited_bundle_adapter.rs"]
mod cited_adapter;

pub struct ReplayConfig {
    pub discovery_limits: fang_tptp_signed_roles::Limits,
    pub replay_limits: fang_tptp_signed_roles::Limits,
    pub naming_threshold: usize,
    pub certificate_bytes: usize,
}

use fang_equality_search::{Error as SearchError, PreparedError};
use fang_saturation::cited;
use fang_saturation::producer::{self, FLAGS_USAGE, Mode, Refutation};
use fang_saturation::stats::Json;
use fang_tptp_coverage_candidate::Root;
use fang_tptp_signed_bundle::{
    Error as BundleError, error_kind, flatten, prepare_bundle_task, prepare_bundle_task_named,
    produce_bundle_task, sealed,
};
use fang_tptp_signed_roles::{Error as SignedError, Limits, Outcome, Selection, render};
use std::io::{Read, Write};
use std::process::ExitCode;
use std::time::{Duration, Instant};

const USAGE: &str = "usage: signed-bundle-produce [--render] [--skolem-symbols N] (--goal N | --inputs | --goals) ROOT PATH FILE [ROOT PATH FILE]...";
const FILE_BYTES: u64 = 1024 * 1024;

enum Mode2 {
    Goals,
    Task(Selection),
}

fn usage() -> ExitCode {
    eprintln!("{USAGE}");
    ExitCode::from(64)
}

fn read_files(arguments: &[String]) -> Result<Vec<(Root, String, Vec<u8>)>, ExitCode> {
    if arguments.is_empty() || !arguments.len().is_multiple_of(3) {
        return Err(usage());
    }
    let mut files = Vec::new();
    for triple in arguments.chunks(3) {
        let root = match triple[0].as_str() {
            "base" => Root::Base,
            "tptp" => Root::Tptp,
            _ => return Err(usage()),
        };
        let mut bytes = Vec::new();
        let read = std::fs::File::open(&triple[2])
            .and_then(|file| file.take(FILE_BYTES + 1).read_to_end(&mut bytes));
        if read.is_err() {
            eprintln!("io: bundle file read failed");
            return Err(ExitCode::from(74));
        }
        if bytes.len() as u64 > FILE_BYTES {
            eprintln!("error: resource bundle file");
            return Err(ExitCode::from(1));
        }
        files.push((root, triple[1].clone(), bytes));
    }
    Ok(files)
}

/// The signed producer's error line for a third-version search outcome, in the reviewed shapes.
fn signed_error(error: SignedError) -> ExitCode {
    let error = BundleError::Signed(error);
    eprintln!("error: {} {error:?}", error_kind(&error));
    ExitCode::from(1)
}

pub fn run_with_limits(
    arguments: Vec<String>,
    started: Instant,
    supplied: &ReplayConfig,
) -> ExitCode {
    let (flags, mut arguments) = match producer::split(arguments, started) {
        Ok(split) => split,
        Err(message) => {
            eprintln!("usage: fang-v3-signed-bundle {FLAGS_USAGE} ... ({message})");
            return ExitCode::from(64);
        }
    };
    let options = match flags.options() {
        Ok(options) => options,
        Err(message) => {
            eprintln!("usage: fang-v3-signed-bundle {FLAGS_USAGE} ... ({message})");
            return ExitCode::from(64);
        }
    };
    let render_only = arguments.first().is_some_and(|flag| flag == "--render");
    if render_only {
        arguments.remove(0);
    }
    if flags.mode == Mode::V3 && flags.trace.is_some() {
        eprintln!("usage: --trace is unavailable for the experimental two-pass cited route");
        return ExitCode::from(64);
    }
    let mut limits = if flags.mode == Mode::V2 {
        Limits::default()
    } else {
        supplied.replay_limits.clone()
    };
    let mut discovery_limits = supplied.discovery_limits.clone();
    if arguments
        .first()
        .is_some_and(|flag| flag == "--skolem-symbols")
    {
        match arguments.get(1).map(|value| value.parse()) {
            Some(Ok(count)) => {
                if flags.mode == Mode::V3
                    && count > supplied.replay_limits.skolem.max_skolem_symbols
                {
                    eprintln!("usage: --skolem-symbols exceeds the supplied replay record");
                    return ExitCode::from(64);
                }
                limits.skolem.max_skolem_symbols = count;
                discovery_limits.skolem.max_skolem_symbols = count;
            }
            _ => return usage(),
        }
        arguments.drain(..2);
    }
    let (mode, rest) = match arguments.as_slice() {
        [flag, rest @ ..] if flag == "--goals" => (Mode2::Goals, rest),
        [flag, rest @ ..] if flag == "--inputs" => (Mode2::Task(Selection::Inputs), rest),
        [flag, value, rest @ ..] if flag == "--goal" => match value.parse() {
            Ok(index) => (Mode2::Task(Selection::Goal(index)), rest),
            Err(_) => return usage(),
        },
        _ => return usage(),
    };
    let deadline = if flags.mode == Mode::V3 {
        match flags.time_limit {
            Some(seconds) => {
                let reserve = (seconds * 0.1).min(1.0);
                let Ok(duration) = Duration::try_from_secs_f64((seconds - reserve).max(0.0)) else {
                    return usage();
                };
                let Some(end) = started.checked_add(duration) else {
                    return usage();
                };
                Some(end)
            }
            None => None,
        }
    } else {
        None
    };
    if deadline.is_some_and(|end| Instant::now() >= end) {
        return signed_error(SignedError::Search(PreparedError::Search(
            SearchError::Resource("time limit"),
        )));
    }
    let files = match read_files(rest) {
        Ok(files) => files,
        Err(code) => return code,
    };
    if deadline.is_some_and(|end| Instant::now() >= end) {
        return signed_error(SignedError::Search(PreparedError::Search(
            SearchError::Resource("time limit"),
        )));
    }
    let bundle = sealed(files);
    let mut stdout = std::io::stdout().lock();
    let written = match mode {
        Mode2::Goals => match flatten(
            &bundle,
            if flags.mode == Mode::V2 {
                &limits
            } else {
                &discovery_limits
            },
        ) {
            Ok(flat) => {
                let mut text = format!("goals {}\n", flat.goals.len());
                for (index, (file, statement)) in flat.goals.iter().enumerate() {
                    text.push_str(&format!("goal {index} item {file} {statement}\n"));
                }
                if deadline.is_some_and(|end| Instant::now() >= end) {
                    return search_error(Refutation::Stopped("time limit"));
                }
                stdout.write_all(text.as_bytes())
            }
            Err(error) => {
                eprintln!("error: {} {error:?}", error_kind(&error));
                return ExitCode::from(1);
            }
        },
        Mode2::Task(selection) if render_only => {
            let prepared = if flags.mode == Mode::V2 {
                prepare_bundle_task(&bundle, selection, &limits)
            } else {
                prepare_bundle_task_named(
                    &bundle,
                    selection,
                    &discovery_limits,
                    supplied.naming_threshold,
                )
            };
            match prepared {
                Ok((_, prepared)) => {
                    let text = render(&prepared);
                    if deadline.is_some_and(|end| Instant::now() >= end) {
                        return signed_error(SignedError::Search(PreparedError::Search(
                            SearchError::Resource("time limit"),
                        )));
                    }
                    stdout.write_all(text.as_bytes())
                }
                Err(error) => {
                    eprintln!("error: {} {error:?}", error_kind(&error));
                    return ExitCode::from(1);
                }
            }
        }
        Mode2::Task(selection) if flags.mode == Mode::V2 => {
            match produce_bundle_task(&bundle, selection, &limits) {
                Ok((_, produced)) => {
                    let prepared = Some(produced.prepared.clauses.len());
                    match produced.outcome {
                        Outcome::CandidateRefutation {
                            text, statistics, ..
                        } => {
                            flags.v2_stats("candidate", Some(&statistics), prepared);
                            eprintln!("candidate-certificate: unchecked signed bundle task");
                            stdout.write_all(text.as_bytes())
                        }
                        Outcome::Unknown(statistics) => {
                            flags.v2_stats("unknown", Some(&statistics), prepared);
                            eprintln!(
                                "unknown: processed={} attempted={}",
                                statistics.processed_clauses, statistics.attempted_inferences
                            );
                            return ExitCode::from(2);
                        }
                    }
                }
                Err(error) => {
                    flags.v2_stats(error_kind(&error), None, None);
                    eprintln!("error: {} {error:?}", error_kind(&error));
                    return ExitCode::from(1);
                }
            }
        }
        Mode2::Task(selection) => {
            let now = Instant::now();
            let discovery_deadline =
                deadline.map(|end| now + end.saturating_duration_since(now) / 2);
            let config = cited_adapter::Config {
                discovery_limits: &discovery_limits,
                replay_limits: &limits,
                naming_threshold: supplied.naming_threshold,
                options: &options,
                discovery_deadline,
                deadline,
                memory_mib: flags.memory_mib,
                certificate_bytes: supplied
                    .certificate_bytes
                    .min(options.max_certificate_bytes),
            };
            let result = cited_adapter::produce(&bundle, selection, &config);
            let mut stats = Json::new();
            stats
                .string("search", "v3")
                .string("route", "cited")
                .string(
                    "outcome",
                    match &result {
                        Ok(_) => "candidate",
                        Err(error) => match cited_adapter::search_outcome(error) {
                            Some(Refutation::Unknown { .. }) => "unknown",
                            Some(Refutation::Stopped(_)) => "resource",
                            _ => "error",
                        },
                    },
                )
                .number("total_ms", flags.elapsed_ms())
                .number("naming_threshold", supplied.naming_threshold as u64);
            if let Ok(text) = &result {
                stats.number("certificate_bytes", text.len() as u64);
            }
            flags.write_stats(&stats.finish());
            match result {
                Ok(text) => {
                    if deadline.is_some_and(|end| Instant::now() >= end) {
                        return search_error(Refutation::Stopped("time limit"));
                    }
                    eprintln!("candidate-certificate: unchecked signed bundle task");
                    stdout.write_all(text.as_bytes())
                }
                Err(error) => return cited_error(error),
            }
        }
    };
    if written.is_err() {
        eprintln!("io: output failed");
        return ExitCode::from(74);
    }
    ExitCode::SUCCESS
}

fn bundle_error(error: BundleError) -> ExitCode {
    eprintln!("error: {} {error:?}", error_kind(&error));
    ExitCode::from(1)
}

fn search_error(outcome: Refutation) -> ExitCode {
    match outcome {
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
        Refutation::Candidate { .. } => {
            signed_error(SignedError::Internal("candidate returned as an error"))
        }
    }
}

fn adapter_error(error: cited_adapter::AdapterError) -> ExitCode {
    match error {
        cited_adapter::AdapterError::Preparation(error) => bundle_error(error),
        cited_adapter::AdapterError::Mapping(error) => {
            eprintln!("error: internal cited premise mapping {error:?}");
            ExitCode::from(1)
        }
        cited_adapter::AdapterError::CitationOrder => {
            signed_error(SignedError::Internal("cited premise order differs"))
        }
    }
}

fn cited_error(error: cited_adapter::Error) -> ExitCode {
    match error {
        cited_adapter::Error::Preparation(error) => bundle_error(error),
        cited_adapter::Error::Refutation(
            cited::Error::Discovery(outcome) | cited::Error::Replay(outcome),
        ) => search_error(outcome),
        cited_adapter::Error::Refutation(
            cited::Error::Mapping(error) | cited::Error::Preparation(error),
        ) => adapter_error(error),
        cited_adapter::Error::CertificateBytes => signed_error(SignedError::Serialization(
            SearchError::Resource("expanded certificate byte limit"),
        )),
        cited_adapter::Error::Deadline => search_error(Refutation::Stopped("time limit")),
    }
}
