// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Diagnostic candidate transport. Exit 0 never means an independently checked result.
#![forbid(unsafe_code)]

//! Write one version-8 candidate certificate for one task. `--goal N` selects the original conjecture with index N among all conjectures in source order; `--inputs` selects the satisfiability task. Exit 0 means a candidate was written, 2 Unknown, 1 a typed error; none of these is a checked result.

use fang_tptp_signed_roles::{Limits, Outcome, Selection, produce_task};
use std::io::{Read, Write};
use std::process::ExitCode;

const USAGE: &str = "usage: signed-produce (--goal N | --inputs) < input";

fn main() -> ExitCode {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let selection = match arguments.as_slice() {
        [flag] if flag == "--inputs" => Selection::Inputs,
        [flag, value] if flag == "--goal" => match value.parse() {
            Ok(index) => Selection::Goal(index),
            Err(_) => {
                eprintln!("{USAGE}");
                return ExitCode::from(64);
            }
        },
        _ => {
            eprintln!("{USAGE}");
            return ExitCode::from(64);
        }
    };
    let limits = Limits::default();
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
    match produce_task(&input, selection, &limits) {
        Ok(produced) => match produced.outcome {
            Outcome::CandidateRefutation { text, .. } => {
                if std::io::stdout().lock().write_all(text.as_bytes()).is_err() {
                    eprintln!("io: candidate output failed");
                    return ExitCode::from(74);
                }
                eprintln!("candidate-certificate: unchecked signed task");
                ExitCode::SUCCESS
            }
            Outcome::Unknown(statistics) => {
                eprintln!(
                    "unknown: processed={} attempted={}",
                    statistics.processed_clauses, statistics.attempted_inferences
                );
                ExitCode::from(2)
            }
        },
        Err(error) => {
            eprintln!("error: {error:?}");
            ExitCode::from(1)
        }
    }
}
