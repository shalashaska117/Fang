// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// CLI adapted from Fang src/main.rs. Algorithm sources remain unchanged.
#![forbid(unsafe_code)]

use fang::{
    ErrorKind, Limits,
    search::{self, Outcome},
};
use fang_ground_fof_search::Error as PrepareError;
use std::{
    env, fs,
    io::{self, Read},
    path::PathBuf,
    process::ExitCode,
};

fn usage() -> &'static str {
    "usage: fang-ground-fof-driver INPUT --proof PATH [--max-steps N] [--max-clauses N] [--max-operations N]\n\
     Accepts strict CNF and ground FOF axioms without equality or quantifiers.\n\
     Outputs candidate-refutation only; version-2 certificates require independent checking.\n\
     Exit codes: 0 candidate, 2 unknown, 3 invalid input, 4 unsupported, 5 resource limit, 6 usage/I/O/internal error, 101 panic."
}

fn classify(error: fang::Error) -> (u8, String) {
    let code = match error.kind {
        ErrorKind::InvalidInput => 3,
        ErrorKind::Unsupported => 4,
        ErrorKind::ResourceLimit => 5,
    };
    (code, error.to_string())
}

fn preprocessing_error(error: PrepareError) -> (u8, String) {
    match error {
        PrepareError::Input(error) => classify(error),
        PrepareError::Preprocessing(fang_ground_fof_core::Error::Invalid(reason)) => (
            6,
            format!("InternalError: parser produced an invalid formula: {reason:?}"),
        ),
        PrepareError::Preprocessing(fang_ground_fof_core::Error::Resource(reason)) => (
            5,
            format!("ResourceLimit: preprocessing {reason:?} limit exceeded"),
        ),
        PrepareError::Resource(reason) => (5, format!("ResourceLimit: {reason}")),
    }
}

fn run() -> Result<u8, (u8, String)> {
    let mut args = env::args_os().skip(1);
    let Some(input) = args.next() else {
        return Err((6, usage().into()));
    };
    if input == "--help" || input == "-h" {
        println!("{}", usage());
        return Ok(0);
    }
    let mut proof = None;
    // The versioned checker accepts at most one MiB of certificate bytes.
    let mut limits = Limits {
        max_proof_bytes: 1 << 20,
        ..Default::default()
    };
    while let Some(flag) = args.next() {
        let value = args.next().ok_or_else(|| (6, usage().into()))?;
        if flag == "--proof" {
            if proof.is_some() {
                return Err((6, "duplicate --proof".into()));
            }
            proof = Some(PathBuf::from(value));
        } else {
            let number = value
                .to_str()
                .and_then(|s| s.parse::<usize>().ok())
                .ok_or_else(|| (6, "limit must be a nonnegative integer".into()))?;
            if flag == "--max-steps" {
                limits.max_steps = number;
            } else if flag == "--max-clauses" {
                limits.max_clauses = number;
            } else if flag == "--max-operations" {
                limits.max_operations = number;
            } else {
                return Err((6, format!("unknown option: {}", flag.to_string_lossy())));
            }
        }
    }
    let proof = proof.ok_or_else(|| (6, usage().into()))?;
    let file = fs::File::open(input).map_err(|e| (6, format!("input I/O error: {e}")))?;
    let mut bytes = Vec::new();
    file.take((limits.max_input_bytes + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|e| (6, format!("input I/O error: {e}")))?;

    // The parser, preprocessor and search each have an explicit work budget.
    // A shared wall-time/RSS budget belongs to the supervising ATP command.
    let input_limits = fang_ground_fof_frontend::Limits {
        input: limits.clone(),
        ..Default::default()
    };
    let core_limits = fang_ground_fof_core::Limits {
        max_clauses: limits.max_clauses,
        max_operations: limits.max_operations,
        ..Default::default()
    };
    let prepared = fang_ground_fof_search::prepare(&bytes, &input_limits, &core_limits)
        .map_err(preprocessing_error)?;
    match search::prove(&prepared.problem, &limits).map_err(classify)? {
        Outcome::CandidateRefutation(certificate) => {
            let text =
                fang_ground_fof_versioned::certificate_text(&certificate, limits.max_proof_bytes)
                    .map_err(classify)?;
            fs::write(proof, text).map_err(|e| (6, format!("certificate I/O error: {e}")))?;
            println!("candidate-refutation");
            eprintln!(
                "{} recorded search nodes; serialized proof keeps only refutation dependencies; independent checking required",
                certificate.node_count()
            );
            Ok(0)
        }
        Outcome::Unknown {
            processed_clauses,
            attempted_inferences,
        } => {
            println!("unknown");
            eprintln!(
                "queue exhausted after {processed_clauses} clauses and {attempted_inferences} inference attempts"
            );
            Ok(2)
        }
    }
}

fn main() -> ExitCode {
    match run() {
        Ok(code) => ExitCode::from(code),
        Err((code, message)) => {
            let _ = io::Write::write_all(&mut io::stderr(), format!("{message}\n").as_bytes());
            ExitCode::from(code)
        }
    }
}
