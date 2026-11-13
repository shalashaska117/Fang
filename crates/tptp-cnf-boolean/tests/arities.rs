// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang::syntax::Term;
use fang_equality_inference_core::{Atom, Literal};
use fang_tptp_full_frontend_candidate::{Body, Limits, parse};

fn ordinary(value: &fang_tptp_full_frontend_candidate::CnfLiteral) -> &Literal {
    match value {
        fang_tptp_full_frontend_candidate::CnfLiteral::Ordinary(value) => value,
        _ => panic!("ordinary fixture"),
    }
}

#[test]
fn actual_skolem_ids_reserve_later_overloads_and_unused_dependencies() {
    let p = parse(b"fof(e,axiom,![U]:?[X]:p(X)).fof(later,axiom,(fang_skolem_0 = a & fang_skolem_0(a) = a)).fof(laterp,axiom,(p & p(a,a))).", &Limits::default()).unwrap();
    let e = p.encode(4, 100).unwrap();
    let signature = fang_quantified_fof_core::Signature {
        functions: e.functions.iter().map(|s| s.arity).collect(),
        predicates: e.reservation.extended_arities(),
    };
    let declarations: Vec<_> = e
        .declarations
        .into_iter()
        .map(|d| {
            let fang_tptp_full_frontend_candidate::EncodedBody::Fof(formula) = d.body else {
                panic!("FOF fixture")
            };
            fang_skolem_core::Declaration {
                formula,
                positive: true,
            }
        })
        .collect();
    let result =
        fang_skolem_core::skolemize_problem(&declarations, &signature, &Default::default())
            .unwrap();
    assert_eq!(signature.functions, [0, 0, 1]);
    assert_eq!(result.signature.functions, [0, 0, 1, 1]);
    assert_eq!(result.signature.predicates, signature.predicates);
    assert_eq!(result.introduced.len(), 1);
    assert_eq!(result.introduced[0].function, 3);
    assert_eq!(result.introduced[0].universals, [0]);
    assert_eq!(e.reservation.equality_id(), 3);
}

#[test]
fn overloaded_function_ids_follow_preorder_and_arity_identity() {
    let p = parse(b"cnf(a,axiom,(p(f(f),f(f,f)))).", &Limits::default()).unwrap();
    assert_eq!(
        p.functions
            .iter()
            .map(|s| (s.name.as_str(), s.arity))
            .collect::<Vec<_>>(),
        [("f", 1), ("f", 0), ("f", 2)]
    );
    let Body::Cnf(clause) = &p.declarations[0].body else {
        panic!("clause")
    };
    assert_eq!(
        ordinary(&clause[0]).atom,
        Atom::Predicate(
            0,
            vec![
                Term::Fun(0, vec![Term::Fun(1, vec![])]),
                Term::Fun(2, vec![Term::Fun(1, vec![]), Term::Fun(1, vec![])])
            ]
        )
    );
}

#[test]
fn overloaded_predicates_and_functions_keep_separate_namespaces() {
    let p = parse(b"cnf(a,axiom,(p|p(p)|p(p,p)|p(p(p)))).", &Limits::default()).unwrap();
    assert_eq!(
        p.predicates
            .iter()
            .map(|s| (s.name.as_str(), s.arity))
            .collect::<Vec<_>>(),
        [("p", 0), ("p", 1), ("p", 2)]
    );
    assert_eq!(
        p.functions
            .iter()
            .map(|s| (s.name.as_str(), s.arity))
            .collect::<Vec<_>>(),
        [("p", 0), ("p", 1)]
    );
    let Body::Cnf(clause) = &p.declarations[0].body else {
        panic!("clause")
    };
    let ids: Vec<_> = clause
        .iter()
        .map(|l| match ordinary(l).atom {
            Atom::Predicate(id, _) => id,
            _ => panic!("predicate"),
        })
        .collect();
    assert_eq!(ids, [0, 1, 2, 1]);
}

#[test]
fn quoted_aliases_use_the_same_name_and_arity_key() {
    let p = parse(
        b"cnf(a,axiom,(p(f)|'p'('f')|p(f(f))|'p'('f','f'))).",
        &Limits::default(),
    )
    .unwrap();
    assert_eq!(
        p.functions
            .iter()
            .map(|s| (s.name.as_str(), s.arity))
            .collect::<Vec<_>>(),
        [("f", 0), ("f", 1)]
    );
    assert_eq!(
        p.predicates
            .iter()
            .map(|s| (s.name.as_str(), s.arity))
            .collect::<Vec<_>>(),
        [("p", 1), ("p", 2)]
    );
    let Body::Cnf(clause) = &p.declarations[0].body else {
        panic!("clause")
    };
    assert_eq!(clause[0], clause[1]);
}

#[test]
fn equality_reservation_follows_all_overloaded_original_predicates() {
    let p = parse(
        b"fof(a,axiom,a = a).cnf(b,axiom,(p|p(a)|p(a,a))).",
        &Limits::default(),
    )
    .unwrap();
    let e = p.encode(4, 100).unwrap();
    assert_eq!(e.reservation.equality_id(), 3);
    assert_eq!(e.reservation.extended_arities(), [0, 1, 2, 2]);
    assert_eq!(e.original_predicates.len(), 3);
    let p = parse(b"cnf(a,axiom,(p|p(a)|p(a,a))).", &Limits::default()).unwrap();
    assert!(p.encode(3, 100).is_err());
    let p = parse(b"fof(a,axiom,(fang_skolem_0(a) = fang_skolem_0 & fang_equality)).cnf(b,axiom,(fang_equality(a)|fang_equality(a,a))).", &Limits::default()).unwrap();
    let e = p.encode(4, 100).unwrap();
    assert_eq!(
        e.functions
            .iter()
            .map(|s| (s.name.as_str(), s.arity))
            .collect::<Vec<_>>(),
        [("fang_skolem_0", 1), ("a", 0), ("fang_skolem_0", 0)]
    );
    assert_eq!(e.reservation.equality_id(), 3);
    assert_eq!(e.reservation.extended_arities(), [0, 1, 2, 2]);
    assert!(
        e.original_predicates
            .iter()
            .all(|s| s.name == "fang_equality")
    );
}

#[test]
fn old_single_arity_ids_and_repeated_literals_are_unchanged() {
    let p = parse(
        b"cnf(a,axiom,(p(f(a),b)|~q(f(a))|p(f(a),b))).",
        &Limits::default(),
    )
    .unwrap();
    assert_eq!(
        p.functions
            .iter()
            .map(|s| (s.name.as_str(), s.arity))
            .collect::<Vec<_>>(),
        [("f", 1), ("a", 0), ("b", 0)]
    );
    assert_eq!(
        p.predicates
            .iter()
            .map(|s| (s.name.as_str(), s.arity))
            .collect::<Vec<_>>(),
        [("p", 2), ("q", 1)]
    );
    let Body::Cnf(clause) = &p.declarations[0].body else {
        panic!("clause")
    };
    assert_eq!(clause.len(), 3);
    assert_eq!(clause[0], clause[2]);
}

#[test]
fn generated_overloads_have_one_id_per_distinct_arity() {
    for width in 1..16 {
        let atoms: Vec<_> = (0..width)
            .map(|arity| {
                if arity == 0 {
                    "p".into()
                } else {
                    format!("p({})", vec!["a"; arity].join(","))
                }
            })
            .collect();
        let source = format!("cnf(a,axiom,({})).", atoms.join("|"));
        let p = parse(source.as_bytes(), &Limits::default()).unwrap();
        assert_eq!(p.predicates.len(), width);
        assert_eq!(
            p.predicates.iter().map(|s| s.arity).collect::<Vec<_>>(),
            (0..width).collect::<Vec<_>>()
        );
    }
}
