// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Diagnostic candidate transport. Exit 0 never means independently checked UNSAT.
#![forbid(unsafe_code)]
use fang_tptp_expanded_v8::{Error, Outcome, native_limits, produce};
use std::io::{Read, Write};
use std::process::ExitCode;

fn main() -> ExitCode {
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
    match produce(&input, &limits) {
        Ok(output) => match output.outcome {
            Outcome::CandidateRefutation { text, .. } => {
                if std::io::stdout().lock().write_all(text.as_bytes()).is_err() {
                    eprintln!("io: candidate output failed");
                    return ExitCode::from(74);
                }
                eprintln!("candidate-certificate: unchecked original input");
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
        Err(Error::Adapter(error)) => {
            eprintln!("adapter: {error:?}");
            ExitCode::from(3)
        }
        Err(Error::Serialization(error)) => {
            eprintln!("serialization: {error:?}");
            ExitCode::from(4)
        }
        Err(Error::WrongTraceVersion) => {
            eprintln!("internal: ordered serializer envelope mismatch");
            ExitCode::from(5)
        }
    }
}
