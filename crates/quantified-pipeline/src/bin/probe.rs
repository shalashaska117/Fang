// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Diagnostic driver only. A candidate is not an accepted refutation.
#![forbid(unsafe_code)]

use fang::syntax::{Problem, Term};
use fang_quantified_pipeline::{Error, Limits, prepare};
use std::fmt::{self, Write};
use std::io::Read;

struct Text {
    value: String,
    cap: usize,
}

impl Write for Text {
    fn write_str(&mut self, value: &str) -> fmt::Result {
        if value.len() > self.cap.saturating_sub(self.value.len()) {
            return Err(fmt::Error);
        }
        self.value.push_str(value);
        Ok(())
    }
}

fn term(out: &mut Text, value: &Term, problem: &Problem) -> fmt::Result {
    match value {
        Term::Var(id) => write!(out, "X{id}"),
        Term::Fun(id, arguments) => {
            let symbol = problem.functions.get(*id as usize).ok_or(fmt::Error)?;
            write!(out, "{}", symbol.name)?;
            if !arguments.is_empty() {
                out.write_char('(')?;
                for (index, argument) in arguments.iter().enumerate() {
                    if index != 0 {
                        out.write_char(',')?;
                    }
                    term(out, argument, problem)?;
                }
                out.write_char(')')?;
            }
            Ok(())
        }
    }
}

fn cnf(problem: &Problem) -> Result<String, fmt::Error> {
    let mut out = Text {
        value: String::new(),
        cap: 8 << 20,
    };
    for (index, clause) in problem.clauses.iter().enumerate() {
        write!(out, "cnf(prepared_{index},axiom,(")?;
        if clause.is_empty() {
            out.write_str("$false")?;
        }
        for (position, literal) in clause.iter().enumerate() {
            if position != 0 {
                out.write_char('|')?;
            }
            if !literal.positive {
                out.write_char('~')?;
            }
            let symbol = problem
                .predicates
                .get(literal.predicate as usize)
                .ok_or(fmt::Error)?;
            out.write_str(&symbol.name)?;
            if !literal.arguments.is_empty() {
                out.write_char('(')?;
                for (index, argument) in literal.arguments.iter().enumerate() {
                    if index != 0 {
                        out.write_char(',')?;
                    }
                    term(&mut out, argument, problem)?;
                }
                out.write_char(')')?;
            }
        }
        out.write_str(")).\n")?;
    }
    Ok(out.value)
}

fn classify(error: &Error) -> (&'static str, u8) {
    use fang_quantified_fof_core::Error as QuantifiedError;
    match error {
        Error::Input(error) => match error.kind {
            fang::ErrorKind::InvalidInput => ("invalid", 2),
            fang::ErrorKind::Unsupported => ("unsupported", 3),
            fang::ErrorKind::ResourceLimit => ("resource", 4),
        },
        Error::Resource(_)
        | Error::Skolem(fang_skolem_core::Error::Resource(_))
        | Error::Skolem(fang_skolem_core::Error::Core(QuantifiedError::Resource(_)))
        | Error::Removal(fang_binder_removal_core::Error::Resource(_))
        | Error::Clausification(fang_fof_core::Error::Resource(_)) => ("resource", 4),
        Error::Skolem(fang_skolem_core::Error::Core(QuantifiedError::Unsupported(_))) => {
            ("unsupported", 3)
        }
        _ => ("internal", 5),
    }
}

fn run() -> Result<(), (&'static str, u8)> {
    let arguments: Vec<String> = std::env::args().collect();
    if arguments.len() != 3 || !matches!(arguments[1].as_str(), "prepare" | "search" | "cnf") {
        return Err(("usage", 64));
    }
    let limits = Limits::default();
    let mut input = Vec::new();
    std::fs::File::open(&arguments[2])
        .map_err(|_| ("io", 6))?
        .take(limits.input.input.max_input_bytes as u64 + 1)
        .read_to_end(&mut input)
        .map_err(|_| ("io", 6))?;
    let value = prepare(&input, &limits).map_err(|error| classify(&error))?;
    if arguments[1] == "cnf" {
        print!(
            "{}",
            cnf(&value.problem).map_err(|_| ("output-resource", 4))?
        );
        return Ok(());
    }
    let status = if arguments[1] == "search" {
        match fang::search::prove(&value.problem, &fang::Limits::default()).map_err(|error| {
            match error.kind {
                fang::ErrorKind::ResourceLimit => ("resource", 4),
                _ => ("internal", 5),
            }
        })? {
            fang::search::Outcome::CandidateRefutation(_) => "candidate",
            fang::search::Outcome::Unknown { .. } => "unknown",
        }
    } else {
        "prepared"
    };
    println!(
        "{{\"status\":\"{status}\",\"functions\":{},\"predicates\":{},\"clauses\":{},\"skolem_symbols\":{},\"operations\":{},\"stored_nodes\":{}}}",
        value.problem.functions.len(),
        value.problem.predicates.len(),
        value.problem.clauses.len(),
        value.introduced.len(),
        value.statistics.preprocessing_operations,
        value.statistics.stored_nodes
    );
    Ok(())
}

fn main() -> std::process::ExitCode {
    match run() {
        Ok(()) => std::process::ExitCode::SUCCESS,
        Err((status, code)) => {
            println!("{{\"status\":\"{status}\"}}");
            std::process::ExitCode::from(code)
        }
    }
}
