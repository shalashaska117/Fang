// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang::{
    ErrorKind, Limits,
    parser::parse,
    search::{Outcome, prove},
};

fn overflowing_index_limits() -> Limits {
    Limits {
        max_clauses: usize::MAX,
        max_literals: 2,
        max_steps: 0,
        max_operations: 0,
        ..Limits::default()
    }
}

#[test]
fn initial_empty_clause_precedes_index_capacity_checks() {
    let problem = parse(
        b"cnf(bottom,axiom,($false)). cnf(unused,axiom,(p)).",
        &Limits::default(),
    )
    .unwrap();
    let outcome = prove(&problem, &overflowing_index_limits()).unwrap();
    let Outcome::CandidateRefutation(certificate) = outcome else {
        panic!("an input empty clause must produce its input certificate");
    };
    assert_eq!(
        certificate.to_text(1024).unwrap(),
        "(fang-proof 1\n  (input 0 0)\n  (final 0))\n"
    );
}

#[test]
fn empty_problem_remains_unknown_before_index_capacity_checks() {
    let problem = parse(b"", &Limits::default()).unwrap();
    assert!(matches!(
        prove(&problem, &overflowing_index_limits()).unwrap(),
        Outcome::Unknown {
            processed_clauses: 0,
            attempted_inferences: 0,
        }
    ));
}

#[test]
fn nonempty_search_reports_index_capacity_overflow_as_resource() {
    let problem = parse(b"cnf(nonempty,axiom,(p)).", &Limits::default()).unwrap();
    let error = prove(&problem, &overflowing_index_limits()).unwrap_err();
    assert_eq!(error.kind, ErrorKind::ResourceLimit);
    assert_eq!(error.message, "index position-cap arithmetic overflow");
}
