// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Diagnostic candidate transport. Exit 0 never means an independently checked result.
#![forbid(unsafe_code)]

//! Drop-in for `signed-bundle-produce` (crates/tptp-signed-bundle): fang-v3-signed-bundle [FLAGS] [--render]
//! [--skolem-symbols N] (--goal N | --inputs | --goals) ROOT PATH FILE..., with the same output and exit codes.
//! With `--search v2` (the default) it runs the reviewed producer unchanged; with `--search v3` it runs the
//! reviewed task preparation, then the saturation search.

use fang_equality_search::{Error as SearchError, PreparedError};
use fang_saturation::producer::{self, FLAGS_USAGE, Mode, Outcome as V3};
use fang_tptp_coverage_candidate::Root;
use fang_tptp_full_frontend_candidate::Role;
use fang_tptp_signed_bundle::{
    Error as BundleError, error_kind, flatten, prepare_bundle_task, produce_bundle_task, sealed,
};
use fang_tptp_signed_roles::{Error as SignedError, Limits, Outcome, Selection, render};
use std::io::{Read, Write};
use std::process::ExitCode;
use std::time::Instant;

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

/// Symbol names for `--trace`: the flat text's function and predicate tables, then the Skolem functions. Only
/// read when a trace is requested; the numbering is the parser's and is assumed to match the prepared task.
fn names(
    flags: &producer::Flags,
    text: &str,
    limits: &Limits,
    functions: usize,
) -> Option<producer::Names> {
    flags.trace.as_ref()?;
    let mut wide = limits.input.clone();
    wide.input.max_input_bytes = text.len().max(wide.input.max_input_bytes);
    wide.input.max_clauses = 1 << 20;
    wide.input.max_term_nodes = 1 << 26;
    wide.max_formula_nodes = 1 << 26;
    wide.max_binders = 1 << 26;
    let parsed = fang_tptp_full_frontend_candidate::parse(text.as_bytes(), &wide).ok()?;
    let mut names = producer::Names {
        functions: parsed
            .functions
            .iter()
            .map(|symbol| symbol.name.clone())
            .collect(),
        predicates: parsed
            .predicates
            .iter()
            .map(|symbol| symbol.name.clone())
            .collect(),
    };
    for index in names.functions.len()..functions {
        names.functions.push(format!("sk{index}"));
    }
    Some(names)
}

/// The signed producer's error line for a third-version search outcome, in the reviewed shapes.
fn signed_error(error: SignedError) -> ExitCode {
    let error = BundleError::Signed(error);
    eprintln!("error: {} {error:?}", error_kind(&error));
    ExitCode::from(1)
}

fn main() -> ExitCode {
    let started = Instant::now();
    let (flags, mut arguments) = match producer::split(std::env::args().skip(1).collect(), started)
    {
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
    let mut limits = Limits::default();
    if arguments
        .first()
        .is_some_and(|flag| flag == "--skolem-symbols")
    {
        match arguments.get(1).map(|value| value.parse()) {
            Some(Ok(count)) => limits.skolem.max_skolem_symbols = count,
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
    let files = match read_files(rest) {
        Ok(files) => files,
        Err(code) => return code,
    };
    let bundle = sealed(files);
    let mut stdout = std::io::stdout().lock();
    let written = match mode {
        Mode2::Goals => match flatten(&bundle, &limits) {
            Ok(flat) => {
                let mut text = format!("goals {}\n", flat.goals.len());
                for (index, (file, statement)) in flat.goals.iter().enumerate() {
                    text.push_str(&format!("goal {index} item {file} {statement}\n"));
                }
                stdout.write_all(text.as_bytes())
            }
            Err(error) => {
                eprintln!("error: {} {error:?}", error_kind(&error));
                return ExitCode::from(1);
            }
        },
        Mode2::Task(selection) if render_only => {
            match prepare_bundle_task(&bundle, selection, &limits) {
                Ok((_, prepared)) => stdout.write_all(render(&prepared).as_bytes()),
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
            let (flat, prepared) = match prepare_bundle_task(&bundle, selection, &limits) {
                Ok(prepared) => prepared,
                Err(error) => {
                    eprintln!("error: {} {error:?}", error_kind(&error));
                    return ExitCode::from(1);
                }
            };
            // A goal is the selected conjecture, entered negated, or a negated_conjecture item.
            let groups: Vec<fang_saturation::sine::Group> = prepared
                .origins
                .iter()
                .map(|origin| fang_saturation::sine::Group {
                    clauses: origin.clauses.clone(),
                    goal: !origin.positive || origin.role == Role::NegatedConjecture,
                })
                .collect();
            match producer::run(
                &flags,
                &options,
                &prepared.clauses,
                &prepared.function_arities,
                &prepared.predicate_arities,
                Some(&groups),
                names(&flags, &flat.text, &limits, prepared.function_arities.len()).as_ref(),
            ) {
                V3::Candidate(text) => {
                    eprintln!("candidate-certificate: unchecked signed bundle task");
                    stdout.write_all(text.as_bytes())
                }
                V3::Unknown {
                    processed,
                    attempted,
                } => {
                    eprintln!("unknown: processed={processed} attempted={attempted}");
                    return ExitCode::from(2);
                }
                V3::Stopped(message) => {
                    return signed_error(SignedError::Search(PreparedError::Search(
                        SearchError::Resource(message),
                    )));
                }
                V3::Invalid(kind) => {
                    return signed_error(SignedError::Search(PreparedError::Invalid(kind)));
                }
                V3::CertificateBytes => {
                    return signed_error(SignedError::Serialization(SearchError::Resource(
                        "expanded certificate byte limit",
                    )));
                }
                V3::Internal(message) => return signed_error(SignedError::Internal(message)),
            }
        }
    };
    if written.is_err() {
        eprintln!("io: output failed");
        return ExitCode::from(74);
    }
    ExitCode::SUCCESS
}
