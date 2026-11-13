// Copyright (c) 2026 Pietro Pellegrino.
// Bounded, reproducible state-machine fuzzing; no background service is installed.
use fang::{
    ErrorKind, Limits,
    parser::parse,
    search::{Outcome, prove},
    syntax::{Term, apply},
    unify::Unifier,
};
use std::{
    fmt::Write,
    fs,
    path::PathBuf,
    time::{Duration, Instant},
};

const GENERATOR: &str = "fang-state-fuzz-v1";
const ARITIES: [usize; 7] = [0, 0, 1, 1, 2, 2, 3];
fn next(state: &mut u64) -> u32 {
    *state ^= *state << 13;
    *state ^= *state >> 7;
    *state ^= *state << 17;
    (*state >> 16) as u32
}
fn term(state: &mut u64, depth: usize) -> Term {
    if next(state).is_multiple_of(3) {
        return Term::Var(next(state) % 8);
    }
    let id = next(state) as usize % if depth == 0 { 2 } else { ARITIES.len() };
    let mut args = Vec::new();
    for _ in 0..ARITIES[id] {
        args.push(term(state, depth - 1));
    }
    Term::Fun(id as u32, args)
}
fn tptp(term: &Term, out: &mut String) {
    match term {
        Term::Var(id) => {
            write!(out, "X{id}").unwrap();
        }
        Term::Fun(id, args) => {
            write!(out, "f{id}").unwrap();
            if !args.is_empty() {
                out.push('(');
                for (i, arg) in args.iter().enumerate() {
                    if i != 0 {
                        out.push(',');
                    }
                    tptp(arg, out);
                }
                out.push(')');
            }
        }
    }
}
#[derive(Default)]
struct Counts {
    rounds: u64,
    raw_bytes: u64,
    parsed: u64,
    searches: u64,
    candidates: u64,
    resources: u64,
    unifications: u64,
    ground_oracles: u64,
    boundary_cases: u64,
}
fn save(path: &PathBuf, counts: &Counts, elapsed: Duration, finished: bool) {
    let text = format!(
        "{{\n  \"generator\": \"{GENERATOR}\",\n  \"elapsed_seconds\": {},\n  \"finished\": {finished},\n  \"rounds\": {},\n  \"raw_byte_inputs\": {},\n  \"parsed_inputs\": {},\n  \"searches\": {},\n  \"candidate_refutations\": {},\n  \"resource_results\": {},\n  \"unification_calls\": {},\n  \"ground_truth_table_cases\": {},\n  \"boundary_cases\": {}\n}}\n",
        elapsed.as_secs(),
        counts.rounds,
        counts.raw_bytes,
        counts.parsed,
        counts.searches,
        counts.candidates,
        counts.resources,
        counts.unifications,
        counts.ground_oracles,
        counts.boundary_cases
    );
    fs::write(path, text).unwrap();
}
fn resource(error: fang::Error, counts: &mut Counts) {
    assert_eq!(
        error.kind,
        ErrorKind::ResourceLimit,
        "unexpected non-resource error: {error}"
    );
    counts.resources += 1;
}

fn main() {
    let args: Vec<_> = std::env::args().skip(1).collect();
    assert_eq!(args.len(), 2, "usage: state_fuzz SECONDS OUTPUT_DIRECTORY");
    let seconds: u64 = args[0].parse().unwrap();
    assert!((1..=86_400).contains(&seconds));
    let output = PathBuf::from(&args[1]);
    if let Some(parent) = output.parent() {
        fs::create_dir_all(parent).unwrap();
    }
    fs::create_dir(&output).unwrap();
    fs::write(output.join("seeds.txt"), "1\n2\n3\n4\n5\n6\n7\n8\n9\n10\n").unwrap();
    fs::write(
        output.join("starting-corpus.p"),
        "cnf(c0,axiom,(p(X)|p(Y)|p(X))).\ncnf(c1,axiom,(~p(f0))).\n",
    )
    .unwrap();
    let mut streams = [1u64, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    let limits = Limits {
        max_steps: 500,
        max_clauses: 128,
        max_operations: 25_000,
        max_term_nodes: 20_000,
        max_stored_nodes: 100_000,
        ..Limits::default()
    };
    let mut counts = Counts::default();
    let begin = Instant::now();
    let mut checkpoint = begin;
    while begin.elapsed().as_secs() < seconds {
        let round = counts.rounds;
        let state = &mut streams[round as usize % 10];
        let original_state = *state;
        let result =
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| match next(state) % 6 {
                0 => {
                    let size = next(state) as usize % 2048;
                    let bytes: Vec<_> = (0..size).map(|_| next(state) as u8).collect();
                    let _ = parse(&bytes, &limits);
                    counts.raw_bytes += 1;
                }
                1 => {
                    let mut unifier = Unifier::default();
                    let mut accepted = Vec::new();
                    for _ in 0..8 {
                        let pair = (term(state, 4), term(state, 4));
                        let before = unifier.clone();
                        counts.unifications += 1;
                        match unifier.unify(std::slice::from_ref(&pair), &limits) {
                            Ok(true) => {
                                accepted.push(pair);
                                match unifier.substitution(&limits) {
                                    Ok(witness) => {
                                        for (left, right) in &accepted {
                                            assert_eq!(
                                                apply(left, &witness),
                                                apply(right, &witness)
                                            );
                                        }
                                        for image in witness.values() {
                                            assert_eq!(apply(image, &witness), *image);
                                        }
                                    }
                                    Err(error) => resource(error, &mut counts),
                                }
                            }
                            Ok(false) => {
                                assert_eq!(unifier, before, "failed call mutated bindings")
                            }
                            Err(error) => {
                                resource(error, &mut counts);
                                assert_eq!(unifier, before, "resource failure mutated bindings");
                            }
                        }
                    }
                }
                2 => {
                    let mut text = "cnf(c0,axiom,(p(".to_owned();
                    tptp(&term(state, 4), &mut text);
                    text.push_str("))).cnf(c1,axiom,(~p(X))).");
                    let problem = parse(text.as_bytes(), &limits).unwrap();
                    counts.parsed += 1;
                    counts.searches += 1;
                    match prove(&problem, &limits) {
                        Ok(Outcome::CandidateRefutation(proof)) => {
                            proof.to_text(1 << 20).unwrap();
                            counts.candidates += 1;
                        }
                        Ok(Outcome::Unknown { .. }) => {
                            panic!("the witnessed unit contradiction was lost")
                        }
                        Err(error) => resource(error, &mut counts),
                    }
                }
                3 => {
                    let mut text = String::new();
                    let count = 1 + next(state) % 8;
                    for clause in 0..count {
                        write!(text, "cnf(c{clause},axiom,(").unwrap();
                        let literals = 1 + next(state) % 3;
                        for literal in 0..literals {
                            if literal != 0 {
                                text.push('|');
                            }
                            if next(state).is_multiple_of(2) {
                                text.push('~');
                            }
                            write!(text, "p{}", next(state) % 4).unwrap();
                        }
                        text.push_str(")).");
                    }
                    let problem = parse(text.as_bytes(), &limits).unwrap();
                    let satisfiable = (0..16).any(|assignment| {
                        problem.clauses.iter().all(|clause| {
                            clause.iter().any(|literal| {
                                ((assignment >> literal.predicate) & 1 != 0) == literal.positive
                            })
                        })
                    });
                    counts.parsed += 1;
                    counts.searches += 1;
                    counts.ground_oracles += 1;
                    match prove(&problem, &limits) {
                        Ok(Outcome::CandidateRefutation(proof)) => {
                            assert!(
                                !satisfiable,
                                "candidate contradicts the independent truth table"
                            );
                            proof.to_text(1 << 20).unwrap();
                            counts.candidates += 1;
                        }
                        Ok(Outcome::Unknown { .. }) => assert!(
                            satisfiable,
                            "finite propositional search missed a refutation"
                        ),
                        Err(error) => resource(error, &mut counts),
                    }
                }
                4 => {
                    let depth = next(state) as usize % 81;
                    let text = format!(
                        "cnf(c,axiom,(p({}a{}))).",
                        "f(".repeat(depth),
                        ")".repeat(depth)
                    );
                    if depth >= 64 {
                        assert_eq!(
                            parse(text.as_bytes(), &limits).unwrap_err().kind,
                            ErrorKind::ResourceLimit
                        );
                    } else {
                        parse(text.as_bytes(), &limits).unwrap();
                    }
                    counts.boundary_cases += 1;
                }
                _ => {
                    let mut problem =
                        parse(b"cnf(c0,axiom,(p(X))).cnf(c1,axiom,(~p(X))).", &limits).unwrap();
                    problem.clauses[0][0].arguments[0] = Term::Var(u32::MAX - next(state) % 16);
                    assert_eq!(
                        prove(&problem, &limits).unwrap_err().kind,
                        ErrorKind::ResourceLimit
                    );
                    counts.boundary_cases += 1;
                }
            }));
        if result.is_err() {
            fs::write(
                output.join("failure.txt"),
                format!(
                    "generator={GENERATOR}\nround={round}\nstream={}\nstate={original_state}\n",
                    round % 10
                ),
            )
            .unwrap();
            save(
                &output.join("progress.json"),
                &counts,
                begin.elapsed(),
                false,
            );
            panic!("fuzz invariant failed; retained exact generator state");
        }
        counts.rounds += 1;
        if checkpoint.elapsed().as_secs() >= 60 {
            save(
                &output.join("progress.json"),
                &counts,
                begin.elapsed(),
                false,
            );
            println!(
                "elapsed={} rounds={}",
                begin.elapsed().as_secs(),
                counts.rounds
            );
            checkpoint = Instant::now();
        }
    }
    save(
        &output.join("progress.json"),
        &counts,
        begin.elapsed(),
        true,
    );
    println!(
        "finished seconds={} rounds={}",
        begin.elapsed().as_secs(),
        counts.rounds
    );
}
