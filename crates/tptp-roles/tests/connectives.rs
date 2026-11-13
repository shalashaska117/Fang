// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang::ErrorKind;
use fang_equality_inference_core::Atom;
use fang_tptp_full_frontend_candidate::{Body, Formula, Limits, Parsed, parse};

fn parsed(body: &str) -> Parsed {
    parse(
        format!("fof(a,axiom,{body}).").as_bytes(),
        &Limits::default(),
    )
    .unwrap()
}

fn atom(id: u32) -> Formula {
    Formula::Atom(Atom::Predicate(id, vec![]))
}

fn body(value: &Parsed) -> &Formula {
    let Body::Fof(formula) = &value.declarations[0].body else {
        panic!("FOF")
    };
    formula
}

fn truth(formula: &Formula, mask: u32) -> bool {
    match formula {
        Formula::Atom(Atom::Predicate(id, args)) => {
            assert!(args.is_empty());
            mask & (1 << id) != 0
        }
        Formula::True => true,
        Formula::False => false,
        Formula::Not(f) => !truth(f, mask),
        Formula::And(a, b) => truth(a, mask) && truth(b, mask),
        Formula::Or(a, b) => truth(a, mask) || truth(b, mask),
        Formula::Implies(a, b) => !truth(a, mask) || truth(b, mask),
        Formula::Forall(_, f) | Formula::Exists(_, f) => truth(f, mask),
        Formula::Atom(Atom::Equal(_, _)) => panic!("not a propositional fixture"),
    }
}

#[test]
fn bare_binary_and_homogeneous_lists_have_exact_left_association() {
    assert_eq!(
        *body(&parsed("p & q & p")),
        Formula::And(
            Box::new(Formula::And(Box::new(atom(0)), Box::new(atom(1)))),
            Box::new(atom(0))
        )
    );
    assert_eq!(
        *body(&parsed("p | q | r")),
        Formula::Or(
            Box::new(Formula::Or(Box::new(atom(0)), Box::new(atom(1)))),
            Box::new(atom(2))
        )
    );
    assert_eq!(
        *body(&parsed("p => q")),
        Formula::Implies(Box::new(atom(0)), Box::new(atom(1)))
    );
}

#[test]
fn reverse_implication_preserves_source_table_order_before_swapping() {
    let p = parsed("p(a) <= q(b)");
    assert_eq!(
        p.functions.iter().map(|s| &*s.name).collect::<Vec<_>>(),
        ["a", "b"]
    );
    assert_eq!(
        p.predicates.iter().map(|s| &*s.name).collect::<Vec<_>>(),
        ["p", "q"]
    );
    let Formula::Implies(left, right) = body(&p) else {
        panic!("implies")
    };
    assert!(matches!(&**left, Formula::Atom(Atom::Predicate(1, _))));
    assert!(matches!(&**right, Formula::Atom(Atom::Predicate(0, _))));
}

#[test]
fn nand_nor_exact_expansion_and_node_counts() {
    assert_eq!(
        *body(&parsed("p ~& q")),
        Formula::Not(Box::new(Formula::And(Box::new(atom(0)), Box::new(atom(1)))))
    );
    assert_eq!(
        *body(&parsed("p ~| q")),
        Formula::Not(Box::new(Formula::Or(Box::new(atom(0)), Box::new(atom(1)))))
    );
    assert_eq!(parsed("p ~& q").statistics.formula_nodes, 4);
    assert_eq!(parsed("p <= q").statistics.formula_nodes, 3);
}

#[test]
fn all_propositional_valuations_match_source_connective_meaning() {
    for operator in ["&", "|", "=>", "<=", "~&", "~|"] {
        let p = parsed(&format!("p {operator} q"));
        for mask in 0..4 {
            let a = mask & 1 != 0;
            let b = mask & 2 != 0;
            let expected = match operator {
                "&" => a && b,
                "|" => a || b,
                "=>" => !a || b,
                "<=" => !b || a,
                "~&" => !(a && b),
                "~|" => !(a || b),
                _ => unreachable!(),
            };
            assert_eq!(truth(body(&p), mask), expected, "{operator}/{mask}");
        }
    }
    for operator in ["&", "|"] {
        for width in 2..10 {
            let text = (0..width)
                .map(|i| format!("p{i}"))
                .collect::<Vec<_>>()
                .join(operator);
            let p = parsed(&text);
            for mask in 0..(1 << width) {
                let expected = if operator == "&" {
                    mask == (1 << width) - 1
                } else {
                    mask != 0
                };
                assert_eq!(truth(body(&p), mask), expected);
            }
        }
    }
}

#[test]
fn unit_scope_is_exact_for_negation_and_quantifiers() {
    assert_eq!(
        *body(&parsed("~p | q")),
        Formula::Or(Box::new(Formula::Not(Box::new(atom(0)))), Box::new(atom(1)))
    );
    assert_eq!(
        *body(&parsed("![Unused]:p | q")),
        Formula::Or(
            Box::new(Formula::Forall(0, Box::new(atom(0)))),
            Box::new(atom(1))
        )
    );
    assert_eq!(
        *body(&parsed("![Unused]:(p | q)")),
        Formula::Forall(
            0,
            Box::new(Formula::Or(Box::new(atom(0)), Box::new(atom(1))))
        )
    );
    for text in ["![X]:p(X) | q(X)", "?[X]:p(X) & q(X)", "~![X]:p(X) => q(X)"] {
        assert_eq!(
            parse(
                format!("fof(a,axiom,{text}).").as_bytes(),
                &Limits::default()
            )
            .unwrap_err()
            .kind,
            ErrorKind::InvalidInput
        );
    }
    parsed("![X]:(p(X) | ?[X]:q(X) | p(X))");
}

#[test]
fn grouping_permits_mixed_operators_but_no_implicit_precedence() {
    for text in [
        "p | (q & r)",
        "(p | q) & r",
        "p => (q => r)",
        "(p <= q) <= r",
        "p ~& (q ~| r)",
    ] {
        parsed(text);
    }
    for text in [
        "p | q & r",
        "p & q | r",
        "p => q => r",
        "p <= q <= r",
        "p ~& q ~& r",
        "p | q => r",
        "p => q | r",
        "p ~| q & r",
    ] {
        assert_eq!(
            parse(
                format!("fof(a,axiom,{text}).").as_bytes(),
                &Limits::default()
            )
            .unwrap_err()
            .kind,
            ErrorKind::InvalidInput,
            "{text}"
        );
    }
}

#[test]
fn comments_and_quoted_atoms_do_not_join_operator_bytes() {
    let p = parsed("'p <= q' /*x*/ <= /*y*/ 'r ~& s'");
    assert_eq!(
        p.predicates.iter().map(|s| &*s.name).collect::<Vec<_>>(),
        ["p <= q", "r ~& s"]
    );
    for text in ["p < = q", "p < /*x*/ = q", "p ~ /*x*/ & q", "p = /*x*/ > q"] {
        assert!(
            parse(
                format!("fof(a,axiom,{text}).").as_bytes(),
                &Limits::default()
            )
            .is_err(),
            "{text}"
        );
    }
}

#[test]
fn unfinished_pairs_and_list_tails_publish_no_partial_result() {
    for text in [
        "p &",
        "p | | q",
        "p <=",
        "p ~& )",
        "& p",
        "p q",
        "p & q , r",
        "p ~| ~& q",
    ] {
        assert!(
            parse(
                format!("fof(a,axiom,{text}).").as_bytes(),
                &Limits::default()
            )
            .is_err(),
            "{text}"
        );
    }
}

#[test]
fn actual_output_depth_and_lowering_nodes_are_bounded() {
    let mut limits = Limits {
        max_formula_depth: 3,
        ..Limits::default()
    };
    assert!(parse(b"fof(a,axiom,p&q&r).", &limits).is_ok());
    assert_eq!(
        parse(b"fof(a,axiom,p&q&r&s).", &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    assert!(parse(b"fof(a,axiom,p~&q).", &limits).is_ok());
    limits.max_formula_depth = 2;
    assert_eq!(
        parse(b"fof(a,axiom,p~&q).", &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    limits.max_formula_depth = 64;
    limits.max_formula_nodes = 3;
    assert_eq!(
        parse(b"fof(a,axiom,p~&q).", &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    limits.max_formula_nodes = 4;
    assert!(parse(b"fof(a,axiom,p~&q).", &limits).is_ok());
    let wide = format!("fof(a,axiom,{}).", vec!["p"; 65].join("|"));
    limits.max_formula_nodes = 1000;
    assert_eq!(
        parse(wide.as_bytes(), &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
}

#[test]
fn source_spans_names_arities_and_equality_reservation_survive() {
    let text = "cnf(1,axiom,(p)). fof('x',axiom,p(a) <= a=b). fof(z,axiom,p(a,a)|p).";
    let p = parse(text.as_bytes(), &Limits::default()).unwrap();
    assert_eq!(&text[p.declarations[1].body_bytes.clone()], "p(a) <= a=b");
    assert_eq!(
        p.predicates.iter().map(|s| s.arity).collect::<Vec<_>>(),
        [0, 1, 2]
    );
    let e = p.encode(4, 10).unwrap();
    assert_eq!(e.reservation.equality_id(), 3);
    assert_eq!(e.reservation.extended_arities(), [0, 1, 2, 2]);
    assert_eq!(
        e.declarations.iter().map(|d| &*d.name).collect::<Vec<_>>(),
        ["1", "x", "z"]
    );
}

#[test]
fn remaining_language_boundaries_reject_explicitly() {
    for text in [
        "fof(a,assumption,p).",
        "fof(a,axiom,$less(1,2)).",
        "include('x.p').",
    ] {
        assert_eq!(
            parse(text.as_bytes(), &Limits::default()).unwrap_err().kind,
            ErrorKind::Unsupported,
            "{text}"
        );
    }
}

#[test]
fn operator_byte_mutations_never_panic_or_bypass_complete_input() {
    let source = b"fof(a,axiom,p<=q). cnf(b,axiom,(r)).";
    for position in 0..source.len() {
        for byte in 0..=255 {
            let mut changed = source.to_vec();
            changed[position] = byte;
            if let Ok(value) = parse(&changed, &Limits::default()) {
                assert!(
                    value
                        .declarations
                        .iter()
                        .all(|d| d.bytes.end <= changed.len())
                );
                assert!(value.statistics.formula_nodes <= Limits::default().max_formula_nodes);
            }
        }
    }
}
