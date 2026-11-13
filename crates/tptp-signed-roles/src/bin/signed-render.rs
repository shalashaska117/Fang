// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
#![forbid(unsafe_code)]

//! Print every task of the standard input in the agreement-campaign format. This is a diagnostic printer, not a result or certificate producer.

use fang_tptp_signed_roles::{Limits, Selection, error_kind, goal_count, prepare_task, render};
use std::io::Read;
use std::process::ExitCode;

fn task(input: &[u8], label: &str, selection: Selection, limits: &Limits) {
    println!("task {label}");
    match prepare_task(input, selection, limits) {
        Ok(prepared) => print!("{}", render(&prepared)),
        Err(error) => println!("error {}", error_kind(&error)),
    }
}

fn main() -> ExitCode {
    let mut limits = Limits::default();
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    match arguments.as_slice() {
        [] => {}
        [flag, value] if flag == "--skolem-symbols" => match value.parse() {
            Ok(count) => limits.skolem.max_skolem_symbols = count,
            Err(_) => {
                eprintln!("invalid --skolem-symbols value");
                return ExitCode::from(2);
            }
        },
        _ => {
            eprintln!("usage: signed-render [--skolem-symbols N] < input");
            return ExitCode::from(2);
        }
    }
    let mut input = Vec::new();
    if std::io::stdin().read_to_end(&mut input).is_err() {
        eprintln!("cannot read standard input");
        return ExitCode::from(2);
    }
    match goal_count(&input, &limits) {
        Err(_) => println!("input error"),
        Ok(0) => task(&input, "inputs", Selection::Inputs, &limits),
        Ok(count) => {
            for index in 0..count {
                task(
                    &input,
                    &format!("goal {index}"),
                    Selection::Goal(index),
                    &limits,
                );
            }
        }
    }
    ExitCode::SUCCESS
}
