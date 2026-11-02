// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang::ErrorKind;
use fang_equality_inference_core::{Atom, Literal};
use fang_tptp_full_frontend_candidate::{Body, Limits, parse};

fn ordinary(value: &fang_tptp_full_frontend_candidate::CnfLiteral) -> &Literal {
    match value {
        fang_tptp_full_frontend_candidate::CnfLiteral::Ordinary(value) => value,
        _ => panic!("ordinary fixture"),
    }
}

#[test]
fn bare_and_recursively_wrapped_clauses_keep_order_and_ids() {
    for depth in 0..12 {
        let body = format!(
            "{}p(X)|~q(Y,X)|p(X){}",
            "(".repeat(depth),
            ")".repeat(depth)
        );
        let source = format!("cnf(a,axiom,{body}).");
        let parsed = parse(source.as_bytes(), &Limits::default()).unwrap();
        let expected = parse(b"cnf(a,axiom,(p(X)|~q(Y,X)|p(X))).", &Limits::default()).unwrap();
        assert_eq!(parsed.functions, expected.functions);
        assert_eq!(parsed.predicates, expected.predicates);
        assert_eq!(parsed.declarations[0].body, expected.declarations[0].body);
        assert_eq!(parsed.declarations[0].variables, ["X", "Y"]);
        assert_eq!(&source[parsed.declarations[0].body_bytes.clone()], body);
    }
}

#[test]
fn negative_atoms_and_equality_have_exact_polarity() {
    let parsed = parse(
        b"cnf(a,axiom,~(p(X))|~a=b|~(f(X)=g(Y))|a!=b).",
        &Limits::default(),
    )
    .unwrap();
    let Body::Cnf(clause) = &parsed.declarations[0].body else {
        panic!()
    };
    assert_eq!(clause.len(), 4);
    assert!(clause.iter().all(|literal| !ordinary(literal).positive));
    assert!(matches!(ordinary(&clause[0]).atom, Atom::Predicate(0, _)));
    assert!(
        clause[1..]
            .iter()
            .all(|literal| matches!(ordinary(literal).atom, Atom::Equal(_, _)))
    );
    let encoded = parsed.encode(100, 100).unwrap();
    assert_eq!(encoded.original_predicates.len(), 1);
}

#[test]
fn invalid_partial_parentheses_and_double_negation_fail() {
    for body in [
        "(p)|q", "p|(q)", "~((p))", "~~p", "~(a!=b)", "~a!=b", "()", "(p|)", "(p)&q",
    ] {
        let source = format!("cnf(a,axiom,{body}).");
        assert!(
            parse(source.as_bytes(), &Limits::default()).is_err(),
            "{source}"
        );
    }
}

#[test]
fn false_retains_empty_declaration_and_later_validation() {
    for body in ["$false", "($false)", "((($false)))"] {
        let source = format!("cnf(a,axiom,{body}).cnf(b,axiom,p(f(X))).");
        let parsed = parse(source.as_bytes(), &Limits::default()).unwrap();
        assert_eq!(parsed.declarations.len(), 2);
        assert!(
            matches!(&parsed.declarations[0].body, Body::Cnf(clause) if matches!(clause.as_slice(), [fang_tptp_full_frontend_candidate::CnfLiteral::Boolean { positive: true, value: false }]))
        );
        assert_eq!(parsed.functions[0].name, "f");
        assert!(
            parse(
                format!("cnf(a,axiom,{body}).cnf(b,axiom,p()).").as_bytes(),
                &Limits::default()
            )
            .is_err()
        );
    }
}

#[test]
fn grouping_literal_term_and_operation_caps_still_reject() {
    let mut limits = Limits {
        max_formula_depth: 3,
        ..Limits::default()
    };
    assert!(parse(b"cnf(a,axiom,((p))).", &limits).is_ok());
    assert_eq!(
        parse(b"cnf(a,axiom,(((p)))).", &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    limits.input.max_literals = 1;
    assert_eq!(
        parse(b"cnf(a,axiom,p|q).", &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    limits.input.max_term_nodes = 1;
    assert_eq!(
        parse(b"cnf(a,axiom,~(f(a)=b)).", &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    limits.input.max_operations = 1;
    assert_eq!(
        parse(b"cnf(a,axiom,p).", &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
}

#[test]
fn signed_boolean_literals_are_now_accepted() {
    for body in ["$true", "$true|p", "~$true", "p|$false"] {
        assert!(
            parse(
                format!("cnf(a,axiom,{body}).").as_bytes(),
                &Limits::default()
            )
            .is_ok()
        );
    }
}
