// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Finite model search for one task. Prints a candidate model certificate; only the Lean model checker turns it into
//! a result.
//!
//! fang-model-find (--single | --bundle | --inputs | --goal N | --list) [--seconds S] [--memory-mib M]
//!     [--from-domain A] [--to-domain B] [--symmetry-terms K] [--symmetry-arity A] [--initial-conflicts C] [--self-check] [--no-split] [--no-sorts]
//!     [--trace]
//!     ROOT PATH FILE [ROOT PATH FILE]...
//!
//! `--list` prints `goals N`, the number of selected conjectures, and exits 0.
//!
//! Exit 0 with the certificate on standard output and `candidate-model: unchecked domain N` on standard error;
//! exit 2 with `no-model: ...` when no model was found within the bounds; exit 3 for an input the frontend or the
//! task refuses; exit 5 for an internal fault; exit 64 for a usage error.

use fang_models::problem::{self, Task};
use fang_models::{FindError, Found, Settings, find};
use fang_tptp_coverage_candidate::Root;
use std::io::Write;
use std::process::ExitCode;
use std::time::{Duration, Instant};

fn usage(message: &str) -> ExitCode {
    eprintln!("usage: {message}");
    ExitCode::from(64)
}

fn main() -> ExitCode {
    let started = Instant::now();
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let mut task = None;
    let mut seconds = 10.0f64;
    let mut memory_mib = 1024usize;
    let mut from = 1u32;
    let mut to = 64u32;
    let mut self_check = false;
    let mut split = true;
    let mut sorts = true;
    let mut list = false;
    let mut symmetry_terms = 16usize;
    let mut symmetry_arity = 4usize;
    let mut initial_conflicts = 1000u64;
    let mut trace = false;
    let mut index = 0;
    while index < arguments.len() && arguments[index].starts_with("--") {
        let option = arguments[index].as_str();
        let value = arguments.get(index + 1);
        match option {
            "--single" | "--bundle" => task = Some(Task::All),
            "--inputs" => task = Some(Task::Inputs),
            "--self-check" => self_check = true,
            "--no-split" => split = false,
            "--no-sorts" => sorts = false,
            "--list" => list = true,
            "--trace" => trace = true,
            "--goal"
            | "--seconds"
            | "--memory-mib"
            | "--from-domain"
            | "--to-domain"
            | "--symmetry-terms"
            | "--symmetry-arity"
            | "--initial-conflicts" => {
                let Some(value) = value else {
                    return usage("missing option value");
                };
                let ok = match option {
                    "--goal" => value
                        .parse()
                        .map(|goal| task = Some(Task::Goal(goal)))
                        .is_ok(),
                    "--seconds" => value.parse().map(|parsed| seconds = parsed).is_ok(),
                    "--memory-mib" => value.parse().map(|parsed| memory_mib = parsed).is_ok(),
                    "--from-domain" => value.parse().map(|parsed| from = parsed).is_ok(),
                    "--symmetry-terms" => {
                        value.parse().map(|parsed| symmetry_terms = parsed).is_ok()
                    }
                    "--symmetry-arity" => {
                        value.parse().map(|parsed| symmetry_arity = parsed).is_ok()
                    }
                    "--initial-conflicts" => value
                        .parse()
                        .map(|parsed| initial_conflicts = parsed)
                        .is_ok(),
                    _ => value.parse().map(|parsed| to = parsed).is_ok(),
                };
                if !ok {
                    return usage("invalid option value");
                }
                index += 1;
            }
            _ => return usage("unknown option"),
        }
        index += 1;
    }
    if task.is_none() && !list {
        return usage("one of --single, --bundle, --inputs, --goal N, --list");
    }
    if !(seconds.is_finite() && seconds > 0.0) || from == 0 || to < from {
        return usage("invalid bounds");
    }
    let rest = &arguments[index..];
    if rest.is_empty() || !rest.len().is_multiple_of(3) {
        return usage("bundle files come as ROOT PATH FILE triples");
    }
    let mut files = Vec::new();
    for triple in rest.chunks(3) {
        let root = match triple[0].as_str() {
            "base" => Root::Base,
            "tptp" => Root::Tptp,
            _ => return usage("unknown root"),
        };
        match std::fs::read(&triple[2]) {
            Ok(bytes) => files.push((root, triple[1].clone(), bytes)),
            Err(error) => {
                eprintln!("io-error: {error}");
                return ExitCode::from(74);
            }
        }
    }
    let problem = match problem::load(files) {
        Ok(problem) => problem,
        Err(error) => {
            eprintln!("refused: {error}");
            return ExitCode::from(3);
        }
    };
    let Some(task) = task else {
        let goals = problem
            .statements
            .iter()
            .filter(|statement| statement.role == problem::Role::Goal)
            .count();
        println!("goals {goals}");
        return ExitCode::SUCCESS;
    };
    let mut settings = Settings::new(started + Duration::from_secs_f64(seconds));
    settings.from = from;
    settings.to = to;
    settings.memory_bytes = memory_mib.saturating_mul(1 << 20);
    settings.self_check = self_check;
    settings.split = split;
    settings.sorts = sorts;
    settings.symmetry_terms = symmetry_terms;
    settings.symmetry_arity = symmetry_arity;
    settings.initial_conflicts = initial_conflicts;
    settings.trace = trace;
    match find(&problem, task, &settings) {
        Ok(Found::Certificate {
            size,
            text,
            self_checked,
            ..
        }) => {
            let mut stdout = std::io::stdout().lock();
            if stdout
                .write_all(text.as_bytes())
                .and_then(|_| stdout.flush())
                .is_err()
            {
                return ExitCode::from(74);
            }
            eprintln!("candidate-model: unchecked domain {size}");
            if self_check && !self_checked {
                eprintln!("self-check: skipped at its step limit");
            }
            ExitCode::SUCCESS
        }
        Ok(Found::Exhausted { last }) => {
            eprintln!("no-model: no model up to domain {last}");
            ExitCode::from(2)
        }
        Ok(Found::Stopped { size, reason }) => {
            eprintln!("no-model: stopped at domain {size} ({reason})");
            ExitCode::from(2)
        }
        Err(FindError::Task(error)) => {
            eprintln!("refused: task {error:?}");
            ExitCode::from(3)
        }
        Err(FindError::SelfCheck(message)) => {
            eprintln!("internal: self-check failed: {message}");
            ExitCode::from(5)
        }
    }
}
