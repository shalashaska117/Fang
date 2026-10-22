// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang::{
    ErrorKind, Limits, parser,
    search::{self, Certificate, Outcome},
};

fn certificate(input: &str) -> Certificate {
    let limits = Limits::default();
    let problem = parser::parse(input.as_bytes(), &limits).unwrap();
    match search::prove(&problem, &limits).unwrap() {
        Outcome::CandidateRefutation(certificate) => certificate,
        _ => panic!("expected a refutation"),
    }
}

#[test]
fn serialization_omits_unused_inferences_and_remaps_final_node() {
    let certificate = certificate("cnf(c0,axiom,(p(X)|p(Y)|p(X))).cnf(c1,axiom,(~p(a))).");
    assert!(certificate.node_count() > 4);
    let expected = "(fang-proof 1\n  (input 0 0)\n  (input 1 1)\n  (factor 2 0 0 1 (subst (1 (v 0))) (clause (pos 0 (v 0))))\n  (resolve 3 2 0 1 0 (subst (0 (f 0))) (clause))\n  (final 3))\n";
    assert_eq!(certificate.to_text(expected.len()).unwrap(), expected);
    assert_eq!(certificate.to_text(expected.len()).unwrap(), expected);
    assert_eq!(
        certificate.to_text(expected.len() - 1).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    // Serialization does not remove nodes from the search result itself.
    assert!(certificate.node_count() > 4);
}

#[test]
fn unused_input_nodes_are_removed_without_changing_source_clause_indices() {
    let proof = certificate("cnf(unused,axiom,(q)).cnf(pos,axiom,(p(a))).cnf(neg,axiom,(~p(a))).")
        .to_text(4096)
        .unwrap();
    assert!(proof.contains("(input 0 1)"), "{proof}");
    assert!(proof.contains("(input 1 2)"), "{proof}");
    assert!(!proof.contains("(input 2 "), "{proof}");
    assert!(proof.contains("(final 2)"), "{proof}");
}

#[test]
fn an_input_empty_clause_requires_only_its_own_source_index() {
    let proof = certificate("cnf(c0,axiom,(p)).cnf(c1,axiom,($false)).cnf(c2,axiom,(q)).")
        .to_text(4096)
        .unwrap();
    assert_eq!(proof, "(fang-proof 1\n  (input 0 1)\n  (final 0))\n");
}

#[test]
fn every_serialized_parent_precedes_its_sequential_node() {
    for input in [
        "cnf(c0,axiom,(p(X)|p(Y))).cnf(c1,axiom,(~p(a))).",
        "cnf(c0,axiom,(p|q)).cnf(c1,axiom,(~p)).cnf(c2,axiom,(~q)).",
        "cnf(c0,axiom,(unused)).cnf(c1,axiom,(p(X)|q(X))).cnf(c2,axiom,(~p(a))).cnf(c3,axiom,(~q(a))).",
    ] {
        let proof = certificate(input).to_text(16384).unwrap();
        let mut next = 0;
        for line in proof.lines().skip(1) {
            let fields: Vec<_> = line.split_whitespace().collect();
            let id = fields[1].trim_end_matches(')').parse::<usize>().unwrap();
            if fields[0] == "(final" {
                assert_eq!(id + 1, next);
                continue;
            }
            assert_eq!(id, next);
            next += 1;
            if fields[0] == "(factor" || fields[0] == "(resolve" {
                assert!(fields[2].parse::<usize>().unwrap() < id);
            }
            if fields[0] == "(resolve" {
                assert!(fields[4].parse::<usize>().unwrap() < id);
            }
        }
    }
}
