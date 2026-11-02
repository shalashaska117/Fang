// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang::syntax::Term;
use fang_equality_inference_core::Atom;
use fang_fof_equality_bridge::Error as BridgeError;
use fang_tptp_full_frontend_candidate::{Body, CnfLiteral, EncodedBody, Limits, parse};

#[test]
fn all_signed_constants_keep_raw_identity_and_zero_vs_empty_output() {
    for (text, positive, value, tautology) in [
        ("$true", true, true, true),
        ("$false", true, false, false),
        ("~$true", false, true, false),
        ("~$false", false, false, true),
        ("~($true)", false, true, false),
        ("~($false)", false, false, true),
    ] {
        let input = format!("cnf(a,axiom,{text}).");
        let parsed = parse(input.as_bytes(), &Limits::default()).unwrap();
        assert_eq!(
            parsed.declarations[0].body,
            Body::Cnf(vec![CnfLiteral::Boolean { positive, value }])
        );
        let encoded = parsed.encode(1, 1).unwrap();
        assert_eq!(encoded.declarations.len(), 1);
        assert_eq!(encoded.declarations[0].name, "a");
        assert_eq!(
            encoded.declarations[0].body,
            EncodedBody::Cnf(if tautology { None } else { Some(vec![]) })
        );
    }
}

#[test]
fn discarded_clauses_still_reserve_complete_original_tables() {
    let input = "cnf(t,axiom,$true|p(f(X))|q(g)|~(a=b)).fof(f,axiom,?[Z]:q(Z)).cnf(z,axiom,$false|p(c)|~$true|p(c)).";
    let parsed = parse(input.as_bytes(), &Limits::default()).unwrap();
    let metadata: Vec<_> = parsed
        .declarations
        .iter()
        .map(|d| {
            (
                d.name.clone(),
                d.variables.clone(),
                d.bytes.clone(),
                d.body_bytes.clone(),
            )
        })
        .collect();
    assert_eq!(
        parsed
            .functions
            .iter()
            .map(|s| s.name.as_str())
            .collect::<Vec<_>>(),
        ["f", "g", "a", "b", "c"]
    );
    assert_eq!(
        parsed
            .predicates
            .iter()
            .map(|s| (s.name.as_str(), s.arity))
            .collect::<Vec<_>>(),
        [("p", 1), ("q", 1)]
    );
    let encoded = parsed.encode(3, 5).unwrap();
    assert_eq!(encoded.reservation.equality_id(), 2);
    assert_eq!(
        encoded
            .declarations
            .iter()
            .map(|d| (
                d.name.clone(),
                d.variables.clone(),
                d.bytes.clone(),
                d.body_bytes.clone()
            ))
            .collect::<Vec<_>>(),
        metadata
    );
    assert_eq!(encoded.declarations[0].body, EncodedBody::Cnf(None));
    let EncodedBody::Cnf(Some(last)) = &encoded.declarations[2].body else {
        panic!()
    };
    assert_eq!(last.len(), 2);
    assert_eq!(last[0], last[1]);
    assert_eq!(last[0].arguments, [Term::Fun(4, vec![])]);
}

#[test]
fn truth_does_not_skip_parse_errors_late_declarations_or_head_validation() {
    for input in [
        "cnf(a,axiom,$true|p()).",
        "cnf(a,axiom,$true).cnf(b,axiom,~(a!=b)).",
        "cnf(a,axiom,$true).fof(b,axiom,p(X)).",
        "cnf(a,axiom,$true).cnf(a,axiom,p).",
        "cnf(a,axiom,$true(abc)).",
    ] {
        assert!(
            parse(input.as_bytes(), &Limits::default()).is_err(),
            "{input}"
        );
    }
    let mut parsed = parse(b"cnf(a,axiom,$true|p(a)).", &Limits::default()).unwrap();
    parsed.predicates.clear();
    assert_eq!(
        parsed.encode(1, 2).unwrap_err(),
        BridgeError::UnknownPredicate
    );
}

#[test]
fn literal_limits_count_the_unsimplified_input() {
    let limits = Limits {
        input: fang::Limits {
            max_literals: 2,
            ..Default::default()
        },
        ..Default::default()
    };
    assert!(parse(b"cnf(a,axiom,$true|$false|p).", &limits).is_err());
    let parsed = parse(b"cnf(a,axiom,$true|$false|p).", &Limits::default()).unwrap();
    assert_eq!(parsed.encode(2, 2).unwrap_err(), BridgeError::LiteralLimit);
    assert!(
        parse(
            b"cnf(a,axiom,$false).",
            &Limits {
                input: fang::Limits {
                    max_literals: 0,
                    ..Default::default()
                },
                ..Default::default()
            }
        )
        .is_err()
    );
}

fn term(input: &Term, valuation: [bool; 2], bits: usize) -> bool {
    match input {
        Term::Var(id) => valuation[*id as usize],
        Term::Fun(id, args) => args
            .iter()
            .fold(bits & (1 << (*id as usize % 3)) != 0, |value, arg| {
                value ^ term(arg, valuation, bits)
            }),
    }
}

fn predicate(id: u32, arguments: &[Term], valuation: [bool; 2], bits: usize) -> bool {
    arguments
        .iter()
        .fold(bits & (1 << (id as usize % 3)) != 0, |value, arg| {
            value ^ term(arg, valuation, bits)
        })
}

#[test]
fn finite_models_agree_before_and_after_boolean_normalization() {
    let literals = [
        "p(X)", "~p(X)", "q(a)", "a=b", "a!=b", "$true", "$false", "~$true", "~$false",
    ];
    for left in literals {
        for right in literals {
            let source = format!("cnf(a,axiom,{left}|{right}|{left}).");
            let parsed = parse(source.as_bytes(), &Limits::default()).unwrap();
            let Body::Cnf(raw) = &parsed.declarations[0].body else {
                panic!()
            };
            let mut expected = Vec::new();
            for bits in 0..8 {
                for valuation in [[false, false], [true, false], [false, true], [true, true]] {
                    expected.push(raw.iter().any(|literal| match literal {
                        CnfLiteral::Boolean { positive, value } => positive == value,
                        CnfLiteral::Ordinary(literal) => {
                            literal.positive
                                == match &literal.atom {
                                    Atom::Predicate(id, args) => {
                                        predicate(*id, args, valuation, bits)
                                    }
                                    Atom::Equal(a, b) => {
                                        term(a, valuation, bits) == term(b, valuation, bits)
                                    }
                                }
                        }
                    }));
                }
            }
            let encoded = parsed.encode(3, 3).unwrap();
            let EncodedBody::Cnf(clause) = &encoded.declarations[0].body else {
                panic!()
            };
            let mut actual = Vec::new();
            for bits in 0..8 {
                for valuation in [[false, false], [true, false], [false, true], [true, true]] {
                    actual.push(clause.as_ref().is_none_or(|clause| {
                        clause.iter().any(|literal| {
                            let value = if literal.predicate == encoded.reservation.equality_id() {
                                term(&literal.arguments[0], valuation, bits)
                                    == term(&literal.arguments[1], valuation, bits)
                            } else {
                                predicate(literal.predicate, &literal.arguments, valuation, bits)
                            };
                            literal.positive == value
                        })
                    }));
                }
            }
            assert_eq!(actual, expected, "{source}");
        }
    }
}
