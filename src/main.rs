// Copyright (c) 2026 Pietro Pellegrino.
#![forbid(unsafe_code)]
use fang::{
    ErrorKind, Limits, parser,
    search::{self, Outcome},
};
use std::{
    env, fs,
    io::{self, Read},
    path::PathBuf,
    process::ExitCode,
};

fn usage() -> &'static str {
    "usage: fang INPUT --proof PATH [--max-steps N] [--max-clauses N] [--max-operations N]\n\
     Outputs candidate-refutation only; certificates require independent checking.\n\
     Exit codes: 0 candidate, 2 unknown, 3 invalid input, 4 unsupported, 5 resource limit, 6 usage/I/O, 101 panic."
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
    let mut limits = Limits::default();
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
    // Read at most one byte past the limit, including for pipes and changing files.
    let mut bytes = Vec::new();
    file.take((limits.max_input_bytes + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|e| (6, format!("input I/O error: {e}")))?;
    let classify = |error: fang::Error| {
        let code = match error.kind {
            ErrorKind::InvalidInput => 3,
            ErrorKind::Unsupported => 4,
            ErrorKind::ResourceLimit => 5,
        };
        (code, error.to_string())
    };
    let problem = parser::parse(&bytes, &limits).map_err(classify)?;
    match search::prove(&problem, &limits).map_err(classify)? {
        Outcome::CandidateRefutation(certificate) => {
            let text = certificate
                .to_text(limits.max_proof_bytes)
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
