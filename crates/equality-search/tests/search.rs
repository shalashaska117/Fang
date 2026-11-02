use fang_equality_search::{Error, Limits, Outcome, prove_bytes};

fn certificate(text: &str) -> String {
    let Outcome::CandidateRefutation { certificate, .. } =
        prove_bytes(text.as_bytes(), &Limits::default()).unwrap()
    else {
        panic!("expected a candidate refutation")
    };
    certificate.to_text(1 << 20).unwrap()
}

#[test]
fn empty_clause_and_reflexive_disequality_emit_the_versioned_dialect() {
    let direct = certificate("cnf(c,axiom,($false)).");
    assert!(direct.contains("(input 0 0)"));
    assert!(!direct.contains("eq-resolve"));
    let reflexive = certificate("cnf(c,axiom,(X!=X)).");
    assert!(reflexive.starts_with("(fang-proof 4\n  (preprocessing identity-cnf-equality-v1)\n"));
    assert!(reflexive.contains("(eq-resolve 1 0 (clause) (clause) (v 0) (v 0) (subst) (clause))"));
}

#[test]
fn actual_unifier_witness_is_simultaneous_and_reconstructed() {
    let proof = certificate("cnf(c,axiom,(f(X)!=f(a))).");
    assert!(proof.contains("(subst (0 (f 1)))"));
    assert!(proof.contains("(final 1)"));
}

#[test]
fn duplicate_pivots_are_removed_one_position_at_a_time() {
    let proof = certificate("cnf(c,axiom,(X!=X|X!=X)).");
    assert_eq!(proof.matches("(eq-resolve ").count(), 2);
    assert!(proof.contains("(clause (neg (eq (v 0) (v 0))))"));
    assert!(proof.contains("(final 2)"));
}

#[test]
fn substitutions_reach_later_equality_pivots() {
    let proof = certificate("cnf(c,axiom,(X!=a|f(X)!=f(a))).");
    assert_eq!(proof.matches("(eq-resolve ").count(), 3);
    assert!(proof.contains("(final 3)"));
}

#[test]
fn exhaustion_is_unknown_and_occurs_failure_is_not_a_refutation() {
    for source in [
        "",
        "cnf(c,axiom,(a=b)).",
        "cnf(c,axiom,(X!=f(X))).",
        "cnf(c,axiom,(X!=X|p)).",
        "cnf(c,axiom,(a!=b)).",
    ] {
        assert!(
            matches!(
                prove_bytes(source.as_bytes(), &Limits::default()),
                Ok(Outcome::Unknown(_))
            ),
            "{source}"
        );
    }
}

#[test]
fn structural_and_attempt_limits_are_errors() {
    let limits = Limits {
        max_attempts: 0,
        ..Default::default()
    };
    assert!(matches!(
        prove_bytes(b"cnf(c,axiom,(X!=X)).", &limits),
        Err(Error::Resource("inference attempt limit"))
    ));
    let limits = Limits {
        max_stored_clauses: 1,
        ..Default::default()
    };
    assert!(matches!(
        prove_bytes(b"cnf(c,axiom,(X!=X)).", &limits),
        Err(Error::Resource("stored clause limit"))
    ));
    let limits = Limits {
        max_stored_term_nodes: 1,
        ..Default::default()
    };
    assert!(matches!(
        prove_bytes(b"cnf(c,axiom,(X!=X)).", &limits),
        Err(Error::Resource("stored term-node limit"))
    ));
}

#[test]
fn certificate_limit_is_exact_and_does_not_return_partial_text() {
    let Outcome::CandidateRefutation { certificate, .. } =
        prove_bytes(b"cnf(c,axiom,(X!=X)).", &Limits::default()).unwrap()
    else {
        panic!()
    };
    let text = certificate.to_text(1 << 20).unwrap();
    assert_eq!(certificate.to_text(text.len()).unwrap(), text);
    assert!(matches!(
        certificate.to_text(text.len() - 1),
        Err(Error::Resource("certificate byte limit"))
    ));
}

#[test]
fn source_rejection_and_reconstruction_resources_remain_typed() {
    assert!(
        matches!(prove_bytes(b"fof(c,axiom,(a=b)).", &Limits::default()), Err(Error::Source(error)) if error.kind == fang::ErrorKind::Unsupported)
    );
    let mut limits = Limits::default();
    limits.reconstruction.max_operations = 0;
    assert!(matches!(
        prove_bytes(b"cnf(c,axiom,(X!=X)).", &limits),
        Err(Error::Reconstruction(
            fang_equality_inference_core::Error::Operations
        ))
    ));
}

#[test]
fn resolution_standardizes_parents_apart_and_preserves_order() {
    let proof =
        certificate("cnf(a,axiom,(p(X)|q(X))).cnf(b,axiom,(~p(f(X)))).cnf(c,axiom,(~q(f(a)))).");
    assert!(proof.contains("(resolve "));
    assert!(proof.contains("(subst (1 (f 0 (v 0))))"));
    // With shared variable IDs the first pair would fail its occurs check.
    assert!(proof.contains("(clause (pos (pred 1 (f 0 (v 0)))))"));
}

#[test]
fn factoring_and_resolution_close_a_nonunit_problem() {
    let proof = certificate("cnf(a,axiom,(p(X)|p(Y))).cnf(b,axiom,(~p(U)|~p(V))).");
    assert!(proof.contains("(factor "));
    assert!(proof.contains("(resolve "));
}

#[test]
fn equality_and_predicate_namespaces_do_not_resolve_together() {
    for source in [
        "cnf(a,axiom,(p(a,b))).cnf(b,axiom,(a!=b)).",
        "cnf(a,axiom,(p(a))).cnf(b,axiom,(~q(a))).",
        "cnf(a,axiom,(p(a))).cnf(b,axiom,(p(a))).",
    ] {
        assert!(
            matches!(
                prove_bytes(source.as_bytes(), &Limits::default()),
                Ok(Outcome::Unknown(_))
            ),
            "{source}"
        );
    }
    assert!(certificate("cnf(a,axiom,(a=b)).cnf(b,axiom,(a!=b)).").contains("(resolve "));
}

#[test]
fn resolution_then_equality_resolution_uses_one_certificate() {
    let proof = certificate("cnf(a,axiom,(p(X)|X!=a)).cnf(b,axiom,(~p(a))).");
    assert!(proof.contains("(resolve "));
    assert!(proof.contains("(eq-resolve "));
}
