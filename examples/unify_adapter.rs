// Copyright (c) 2026 Pietro Pellegrino.
// Test transport only. The actual unifier is fang::unify::Unifier.
use fang::{
    Limits,
    syntax::{Substitution, Term, apply},
    unify::Unifier,
};
use std::{
    collections::BTreeMap,
    io::{self, BufRead},
    str::SplitWhitespace,
    time::Instant,
};

fn number(input: &mut SplitWhitespace<'_>) -> Result<u32, String> {
    input
        .next()
        .ok_or("missing number")?
        .parse()
        .map_err(|_| "invalid number".into())
}
fn term(input: &mut SplitWhitespace<'_>, depth: usize) -> Result<Term, String> {
    if depth > 64 {
        return Err("term depth limit".into());
    }
    let kind = input.next().ok_or("missing term")?;
    let id = number(input)?;
    if kind == "v" {
        return Ok(Term::Var(id));
    }
    if kind != "f" {
        return Err("invalid term".into());
    }
    let arity = number(input)?;
    if arity > 32 {
        return Err("arity limit".into());
    }
    let mut args = Vec::new();
    for _ in 0..arity {
        args.push(term(input, depth + 1)?);
    }
    Ok(Term::Fun(id, args))
}
fn write_term(term: &Term, names: &mut BTreeMap<u32, usize>, output: &mut String) {
    match term {
        Term::Var(variable) => {
            let next = names.len();
            let id = names.entry(*variable).or_insert(next);
            output.push_str(&format!("v {id}"));
        }
        Term::Fun(id, args) => {
            output.push_str(&format!("f {id} {}", args.len()));
            for arg in args {
                output.push(' ');
                write_term(arg, names, output);
            }
        }
    }
}
enum Operation {
    Reset,
    Unify(u32, (Term, Term)),
}

fn weight(term: &Term) -> u64 {
    match term {
        Term::Var(_) => 1,
        Term::Fun(_, args) => 1 + args.iter().map(weight).sum::<u64>(),
    }
}

fn benchmark(operations: &[Operation], samples: usize) -> Result<(), String> {
    let limits = Limits::default();
    println!("sample,phase,nanoseconds,successes,image_nodes");
    for phase in 0..2 {
        for sample in 0..samples + 2 {
            let mut unifier = Unifier::default();
            let mut successes = 0u64;
            let mut image_nodes = 0u64;
            let begin = Instant::now();
            for operation in operations {
                match operation {
                    Operation::Reset => unifier = Unifier::default(),
                    Operation::Unify(queries, pair) => {
                        successes += u64::from(
                            unifier
                                .unify(std::slice::from_ref(pair), &limits)
                                .map_err(|e| e.to_string())?,
                        );
                        if phase != 0 {
                            let substitution =
                                unifier.substitution(&limits).map_err(|e| e.to_string())?;
                            for variable in 0..*queries {
                                image_nodes += weight(&apply(&Term::Var(variable), &substitution));
                            }
                        }
                    }
                }
            }
            let elapsed = begin.elapsed().as_nanos();
            if sample >= 2 {
                println!(
                    "{},{},{},{},{}",
                    sample - 2,
                    if phase == 0 {
                        "unify"
                    } else {
                        "unify-and-images"
                    },
                    elapsed,
                    successes,
                    image_nodes
                );
            }
        }
    }
    Ok(())
}

fn main() -> Result<(), String> {
    let mut unifier = Unifier::default();
    let limits = Limits::default();
    let arguments: Vec<_> = std::env::args().skip(1).collect();
    let samples = if arguments.is_empty() {
        None
    } else if arguments.len() == 2 && arguments[0] == "--benchmark" {
        let number: usize = arguments[1].parse().map_err(|_| "invalid sample count")?;
        if number > 1000 {
            return Err("sample count limit".into());
        }
        Some(number)
    } else {
        return Err("invalid adapter arguments".into());
    };
    let mut operations = Vec::new();
    for line in io::stdin().lock().lines() {
        let line = line.map_err(|e| e.to_string())?;
        let mut input = line.split_whitespace();
        match input.next() {
            None => continue,
            Some("R") => {
                if samples.is_some() {
                    operations.push(Operation::Reset);
                } else {
                    unifier = Unifier::default();
                    println!("reset");
                }
                continue;
            }
            Some("U") => (),
            _ => return Err("invalid operation".into()),
        }
        let queries = number(&mut input)?;
        if queries > 64 {
            return Err("query limit".into());
        }
        let left = term(&mut input, 0)?;
        let right = term(&mut input, 0)?;
        if input.next().is_some() {
            return Err("trailing input".into());
        }
        if samples.is_some() {
            operations.push(Operation::Unify(queries, (left, right)));
            continue;
        }
        let success = unifier
            .unify(&[(left, right)], &limits)
            .map_err(|e| e.to_string())?;
        let substitution: Substitution =
            unifier.substitution(&limits).map_err(|e| e.to_string())?;
        let mut names = BTreeMap::new();
        let mut output = if success { "success" } else { "mismatch" }.to_owned();
        for variable in 0..queries {
            output.push_str(" | ");
            write_term(
                &apply(&Term::Var(variable), &substitution),
                &mut names,
                &mut output,
            );
        }
        println!("{output}");
    }
    if let Some(samples) = samples {
        benchmark(&operations, samples)?;
    }
    Ok(())
}
