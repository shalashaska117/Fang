// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Local differential driver. Prints an alpha-normal AST, never a logical result.
use fang::{
    ErrorKind,
    syntax::{Literal, Term},
};
use fang_quantified_fof_core::{Formula, Signature, rectify_closed};
use fang_quantified_fof_frontend::{Body, Parsed, parse};
use std::io::Read;

fn term(value: &Term, source: &Parsed) -> String {
    match value {
        Term::Var(id) => format!("v{id}"),
        Term::Fun(id, args) => format!(
            "{}({})",
            source.functions[*id as usize].name,
            args.iter()
                .map(|t| term(t, source))
                .collect::<Vec<_>>()
                .join(",")
        ),
    }
}

fn atom(predicate: u32, args: &[Term], source: &Parsed) -> String {
    format!(
        "{}({})",
        source.predicates[predicate as usize].name,
        args.iter()
            .map(|t| term(t, source))
            .collect::<Vec<_>>()
            .join(",")
    )
}

fn literal(value: &Literal, source: &Parsed) -> String {
    format!(
        "{}{}",
        if value.positive { "+" } else { "-" },
        atom(value.predicate, &value.arguments, source)
    )
}

fn formula(value: &Formula, source: &Parsed) -> String {
    match value {
        Formula::Atom(p, args) => atom(*p, args, source),
        Formula::True => "true".into(),
        Formula::False => "false".into(),
        Formula::Not(a) => format!("not({})", formula(a, source)),
        Formula::And(a, b) => format!("and({},{})", formula(a, source), formula(b, source)),
        Formula::Or(a, b) => format!("or({},{})", formula(a, source), formula(b, source)),
        Formula::Implies(a, b) => format!("implies({},{})", formula(a, source), formula(b, source)),
        Formula::Forall(id, a) => format!("all(v{id},{})", formula(a, source)),
        Formula::Exists(id, a) => format!("exists(v{id},{})", formula(a, source)),
    }
}

fn run() -> Result<(), u8> {
    let args = std::env::args_os().skip(1).collect::<Vec<_>>();
    if args.len() != 1 {
        eprintln!("usage: inspect INPUT");
        return Err(5);
    }
    let mut bytes = Vec::new();
    std::fs::File::open(&args[0])
        .and_then(|f| f.take((1 << 20) + 1).read_to_end(&mut bytes))
        .map_err(|e| {
            eprintln!("IO: {e}");
            5
        })?;
    let source = parse(&bytes, &Default::default()).map_err(|e| {
        eprintln!("{e}");
        match e.kind {
            ErrorKind::InvalidInput => 2,
            ErrorKind::Unsupported => 3,
            ErrorKind::ResourceLimit => 4,
        }
    })?;
    let signature = Signature {
        functions: source.functions.iter().map(|s| s.arity).collect(),
        predicates: source.predicates.iter().map(|s| s.arity).collect(),
    };
    // Buffer every row; a later failure must not leave a misleading partial AST.
    let mut output = Vec::new();
    for declaration in &source.declarations {
        let body = match &declaration.body {
            Body::Cnf(clause) => format!(
                "cnf[{}]",
                clause
                    .iter()
                    .map(|l| literal(l, &source))
                    .collect::<Vec<_>>()
                    .join(",")
            ),
            Body::Fof(f) => {
                let rectified =
                    rectify_closed(f, &signature, &Default::default()).map_err(|e| {
                        eprintln!("core: {e:?}");
                        match e {
                            fang_quantified_fof_core::Error::Resource(_) => 4,
                            // An invalid AST after successful parsing is a driver/
                            // parser inconsistency, not resource exhaustion.
                            _ => 5,
                        }
                    })?;
                formula(&rectified.formula, &source)
            }
        };
        output.push(format!("{} {body}", declaration.name));
    }
    for row in output {
        println!("{row}");
    }
    Ok(())
}

fn main() -> std::process::ExitCode {
    std::process::ExitCode::from(run().err().unwrap_or(0))
}
