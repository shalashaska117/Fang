use fang_equality_search::{Error, Limits, Outcome, prove_bytes, prove_bytes_ordered};

fn proof(source: &str) -> String {
    let Outcome::CandidateRefutation { certificate, .. } =
        prove_bytes_ordered(source.as_bytes(), &Limits::default()).unwrap()
    else {
        panic!("expected ordered candidate")
    };
    certificate.to_text(1 << 20).unwrap()
}

#[test]
fn ordered_entrypoint_is_explicit_and_versioned() {
    let source = "cnf(e,axiom,(a=b)).cnf(n,axiom,(f(a)!=f(b))).";
    assert!(matches!(
        prove_bytes(source.as_bytes(), &Limits::default()),
        Ok(Outcome::Unknown(_))
    ));
    let text = proof(source);
    assert!(text.starts_with("(fang-proof 5\n"));
    assert!(text.contains("(paramodulate "));
    assert!(text.contains("(equality-left) (path 0) forward"));
    assert!(text.contains("(eq-resolve "));
    assert_eq!(text.matches("(input ").count(), 2);
    assert_eq!(text.matches("(paramodulate ").count(), 1);
    assert!(text.contains("(final 3)"));
}

#[test]
fn predicate_arguments_and_both_equality_orientations_work() {
    for source in [
        "cnf(e,axiom,(a=b)).cnf(p,axiom,(p(a))).cnf(n,axiom,(~p(b))).",
        "cnf(e,axiom,(b=a)).cnf(p,axiom,(p(a))).cnf(n,axiom,(~p(b))).",
        "cnf(e,axiom,(f(X)=X)).cnf(p,axiom,(p(f(a)))).cnf(n,axiom,(~p(a))).",
    ] {
        assert!(proof(source).contains("(argument 0)"));
    }
}

#[test]
fn source_residual_and_target_literal_order_reach_common_rules() {
    let text =
        proof("cnf(e,axiom,(q|a=b)).cnf(p,axiom,(p(a))).cnf(n,axiom,(~p(b))).cnf(q,axiom,(~q)).");
    assert!(text.contains("(paramodulate "));
    assert!(text.contains("(resolve "));
}

#[test]
fn unknown_and_resources_never_become_refutations() {
    assert!(matches!(
        prove_bytes_ordered(b"cnf(c,axiom,(p(a))).", &Limits::default()),
        Ok(Outcome::Unknown(_))
    ));
    let limits = Limits {
        max_attempts: 0,
        ..Default::default()
    };
    assert!(matches!(
        prove_bytes_ordered(b"cnf(e,axiom,(a=b)).", &limits),
        Err(Error::Resource("inference attempt limit"))
    ));
}

#[test]
fn ordered_certificate_has_the_same_exact_size_contract() {
    let Outcome::CandidateRefutation { certificate, .. } = prove_bytes_ordered(
        b"cnf(e,axiom,(a=b)).cnf(n,axiom,(f(a)!=f(b))).",
        &Limits::default(),
    )
    .unwrap() else {
        panic!()
    };
    let text = certificate.to_text(1 << 20).unwrap();
    assert_eq!(certificate.to_text(text.len()).unwrap(), text);
    assert!(matches!(
        certificate.to_text(text.len() - 1),
        Err(Error::Resource("certificate byte limit"))
    ));
}
