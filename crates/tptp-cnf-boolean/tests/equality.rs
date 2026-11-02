// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang::{ErrorKind, syntax::Term};
use fang_equality_inference_core::{Atom, Literal};
use fang_fof_equality_bridge::Error as BridgeError;
use fang_quantified_fof_core::{Formula as CoreFormula, Signature};
use fang_tptp_full_frontend_candidate::{Body, EncodedBody, Formula, Limits, Parsed, parse};

fn parsed(source: &str) -> Parsed {
    parse(source.as_bytes(), &Limits::default()).unwrap()
}

fn ordinary(value: &fang_tptp_full_frontend_candidate::CnfLiteral) -> &Literal {
    match value {
        fang_tptp_full_frontend_candidate::CnfLiteral::Ordinary(value) => value,
        _ => panic!("ordinary fixture"),
    }
}

#[test]
fn operands_get_function_ids_and_heads_have_separate_namespaces() {
    let p = parsed("fof(a,axiom,(f(a) = g(b) & f(c))).");
    assert_eq!(
        p.functions
            .iter()
            .map(|s| (&*s.name, s.arity))
            .collect::<Vec<_>>(),
        [("f", 1), ("a", 0), ("g", 1), ("b", 0), ("c", 0)]
    );
    assert_eq!(
        p.predicates
            .iter()
            .map(|s| (&*s.name, s.arity))
            .collect::<Vec<_>>(),
        [("f", 1)]
    );
    let Body::Fof(Formula::And(left, right)) = &p.declarations[0].body else {
        panic!("and")
    };
    assert_eq!(
        **left,
        Formula::Atom(Atom::Equal(
            Term::Fun(0, vec![Term::Fun(1, vec![])]),
            Term::Fun(2, vec![Term::Fun(3, vec![])])
        ))
    );
    assert_eq!(
        **right,
        Formula::Atom(Atom::Predicate(0, vec![Term::Fun(4, vec![])]))
    );
}

#[test]
fn reservation_follows_the_complete_original_table_without_a_spelling() {
    let p = parsed("fof(e,axiom,a = a). fof(p,axiom,p(a)). fof(q,axiom,fang_equality(a,a)).");
    let encoded = p.encode(3, 10).unwrap();
    assert_eq!(encoded.reservation.equality_id(), 2);
    assert_eq!(encoded.reservation.extended_arities(), [1, 2, 2]);
    assert_eq!(
        encoded
            .original_predicates
            .iter()
            .map(|s| &*s.name)
            .collect::<Vec<_>>(),
        ["p", "fang_equality"]
    );
    let EncodedBody::Fof(CoreFormula::Atom(id, args)) = &encoded.declarations[0].body else {
        panic!("equality")
    };
    assert_eq!((*id, args.len()), (2, 2));
    let EncodedBody::Fof(CoreFormula::Atom(id, _)) = &encoded.declarations[2].body else {
        panic!("predicate")
    };
    assert_eq!(*id, 1);
}

#[test]
fn equality_polarity_and_nested_negation_are_explicit() {
    let p = parsed("fof(a,axiom,~(a != b)). cnf(c,axiom,(a = b | a != b | ~p)).");
    let Body::Fof(Formula::Not(outer)) = &p.declarations[0].body else {
        panic!("not")
    };
    assert!(
        matches!(&**outer, Formula::Not(inner) if matches!(&**inner, Formula::Atom(Atom::Equal(_, _))))
    );
    assert_eq!(p.statistics.formula_nodes, 3);
    let Body::Cnf(clause) = &p.declarations[1].body else {
        panic!("cnf")
    };
    assert_eq!(
        clause
            .iter()
            .map(|l| ordinary(l).positive)
            .collect::<Vec<_>>(),
        [true, false, false]
    );
    let encoded = p.encode(2, 3).unwrap();
    let EncodedBody::Cnf(Some(clause)) = &encoded.declarations[1].body else {
        panic!("encoded")
    };
    assert_eq!(
        clause.iter().map(|l| l.predicate).collect::<Vec<_>>(),
        [1, 1, 0]
    );
}

#[test]
fn shadowing_unused_binders_and_scope_restoration_reach_actual_rectification() {
    let p = parsed("fof(a,axiom,![Unused,X]:((?[X]:X != a) & X = b)).");
    assert_eq!(p.declarations[0].variables, ["Unused", "X"]);
    assert_eq!(p.statistics.binders, 3);
    let e = p.encode(1, 1).unwrap();
    let signature = Signature {
        functions: e.functions.iter().map(|s| s.arity).collect(),
        predicates: e.reservation.extended_arities(),
    };
    let EncodedBody::Fof(formula) = &e.declarations[0].body else {
        panic!("fof")
    };
    let result =
        fang_quantified_fof_core::rectify_closed(formula, &signature, &Default::default()).unwrap();
    assert_eq!(result.binder_count, 3);
    let CoreFormula::Forall(0, unused) = result.formula else {
        panic!("unused")
    };
    let CoreFormula::Forall(1, body) = *unused else {
        panic!("outer")
    };
    let CoreFormula::And(left, right) = *body else {
        panic!("and")
    };
    assert!(matches!(*left, CoreFormula::Exists(2, _)));
    assert_eq!(
        *right,
        CoreFormula::Atom(0, vec![Term::Var(1), Term::Fun(1, vec![])])
    );
}

#[test]
fn mixed_source_spans_order_duplicates_and_local_variable_ids_survive_lowering() {
    let source =
        " \ncnf(c,axiom,(X = a | X = a)).\nfof(f,axiom,![Z]:Z = a). cnf(d,axiom,(Y != a)). ";
    let p = parsed(source);
    assert_eq!(
        p.declarations.iter().map(|d| &*d.name).collect::<Vec<_>>(),
        ["c", "f", "d"]
    );
    assert_eq!(
        p.declarations
            .iter()
            .map(|d| d.variables.clone())
            .collect::<Vec<_>>(),
        [vec!["X"], vec!["Z"], vec!["Y"]]
    );
    let spans: Vec<_> = p
        .declarations
        .iter()
        .map(|d| (d.bytes.clone(), d.body_bytes.clone()))
        .collect();
    assert_eq!(&source[spans[0].0.clone()], "cnf(c,axiom,(X = a | X = a)).");
    assert_eq!(&source[spans[1].1.clone()], "![Z]:Z = a");
    let e = p.encode(1, 2).unwrap();
    for (d, (bytes, body)) in e.declarations.iter().zip(spans) {
        assert_eq!(d.bytes, bytes);
        assert_eq!(d.body_bytes, body);
    }
    let EncodedBody::Cnf(Some(c)) = &e.declarations[0].body else {
        panic!("cnf")
    };
    assert_eq!(c.len(), 2);
    assert_eq!(c[0], c[1]);
    assert_eq!(c[0].arguments[0], Term::Var(0));
    let EncodedBody::Cnf(Some(d)) = &e.declarations[2].body else {
        panic!("cnf")
    };
    assert_eq!(d[0].arguments[0], Term::Var(0));
}

#[test]
fn malformed_scope_arity_and_trailing_inputs_return_no_problem() {
    for source in [
        "fof(a,axiom,X = a).",
        "fof(a,axiom,((![X]:X = a) & X = b)).",
        "fof(a,axiom,a = b = c).",
        "fof(a,axiom,p()).",
        "fof(a,axiom,p(a,)).",
        "fof(a,axiom,a = a). cnf(a,axiom,($false)).",
        "fof(a,axiom,a = a). garbage",
        "cnf(c,axiom,(a = b != c)).",
        "fof(a,axiom,![X]:X).",
    ] {
        assert_eq!(
            parse(source.as_bytes(), &Limits::default())
                .unwrap_err()
                .kind,
            ErrorKind::InvalidInput,
            "{source}"
        );
    }
    assert_eq!(
        parse(&[255], &Limits::default()).unwrap_err().kind,
        ErrorKind::InvalidInput
    );
}

#[test]
fn unsupported_forms_remain_explicit() {
    for source in [
        "fof(c,conjecture,a = a).",
        "fof(c,axiom,![X:$i]:X = X).",
        "fof(c,axiom,1 = a).",
        "fof(c,axiom,a = a,file(x,y)).",
        "tff(c,axiom,a = a).",
        "include(a).",
    ] {
        assert_eq!(
            parse(source.as_bytes(), &Limits::default())
                .unwrap_err()
                .kind,
            ErrorKind::Unsupported,
            "{source}"
        );
    }
}

#[test]
fn limits_count_both_equality_operands_and_inequality_ast_nodes() {
    let source = "fof(a,axiom,f(a) != b).";
    let accepted = parsed(source);
    assert_eq!(
        (
            accepted.statistics.term_nodes,
            accepted.statistics.formula_nodes
        ),
        (3, 2)
    );
    let mut limits = Limits::default();
    limits.input.max_term_nodes = 2;
    assert_eq!(
        parse(source.as_bytes(), &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    limits.input.max_term_nodes = 3;
    limits.max_formula_nodes = 1;
    assert_eq!(
        parse(source.as_bytes(), &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    limits.max_formula_nodes = 2;
    limits.max_formula_depth = 1;
    assert_eq!(
        parse(source.as_bytes(), &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    limits.max_formula_depth = 2;
    limits.input.max_term_depth = 1;
    assert_eq!(
        parse(source.as_bytes(), &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    limits.input.max_term_depth = 2;
    assert!(parse(source.as_bytes(), &limits).is_ok());
    limits.input.max_operations = accepted.statistics.operations - 1;
    assert_eq!(
        parse(source.as_bytes(), &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    limits.input.max_operations += 1;
    assert!(parse(source.as_bytes(), &limits).is_ok());
    limits.input.max_literals = 0;
    assert_eq!(
        parse(b"cnf(c,axiom,($false)).", &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    assert_eq!(
        parse(b"cnf(c,axiom,(a=a)).", &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
}

#[test]
fn equality_free_inputs_match_the_accepted_quantified_parser() {
    let bodies = [
        "z",
        "p(a)",
        "~p(f(a))",
        "$true",
        "$false",
        "![X]:p(X)",
        "?[X]:![Y]:(p(X) => q(Y))",
        "![X]:((?[X]:p(X)) & p(X))",
        "![Unused,X,X]:p(X)",
    ];
    for left in bodies {
        for right in bodies {
            let source = format!("fof(a,axiom,({left} | {right})). cnf(c,axiom,(p(a)|~p(a))).");
            let old = quantified_reference::parse(source.as_bytes(), &Default::default()).unwrap();
            let p = parsed(&source);
            assert_eq!(p.statistics.operations, old.statistics.operations);
            assert_eq!(p.statistics.term_nodes, old.statistics.term_nodes);
            assert_eq!(p.statistics.formula_nodes, old.statistics.formula_nodes);
            assert_eq!(p.statistics.binders, old.statistics.binders);
            let e = p.encode(100, 100).unwrap();
            assert_eq!(e.functions, old.functions);
            assert_eq!(e.original_predicates, old.predicates);
            for (new, old) in e.declarations.into_iter().zip(old.declarations) {
                assert_eq!(
                    (new.name, new.bytes, new.variables, new.body_bytes),
                    (old.name, old.bytes, old.variables, old.body_bytes)
                );
                match (new.body, old.body) {
                    (EncodedBody::Fof(a), quantified_reference::Body::Fof(b)) => assert_eq!(a, b),
                    (EncodedBody::Cnf(Some(a)), quantified_reference::Body::Cnf(b)) => {
                        assert_eq!(a, b)
                    }
                    _ => panic!("declaration kind"),
                }
            }
        }
    }
}

#[test]
fn cnf_inputs_match_the_accepted_equality_parser() {
    let literals = [
        "X = a",
        "X != f(a)",
        "f(X) = g(Y)",
        "a = a",
        "p(X)",
        "~p(a)",
        "q",
        "q != a",
    ];
    for left in literals {
        for right in literals {
            let source = format!("cnf(c,axiom,({left}|{right}|{left})). cnf(d,axiom,(Z != a)).");
            let old = equality_reference::parse(source.as_bytes(), &Default::default()).unwrap();
            let p = parsed(&source);
            assert_eq!(p.functions, old.functions);
            assert_eq!(p.predicates, old.predicates);
            for (new, old) in p.declarations.into_iter().zip(old.clauses) {
                let Body::Cnf(clause) = new.body else {
                    panic!("cnf")
                };
                assert_eq!(
                    clause
                        .into_iter()
                        .map(|value| match value {
                            fang_tptp_full_frontend_candidate::CnfLiteral::Ordinary(value) => value,
                            _ => panic!("ordinary fixture"),
                        })
                        .collect::<Vec<_>>(),
                    old
                );
            }
        }
    }
}

#[test]
fn reservation_and_mutated_ordinary_heads_fail_without_partial_output() {
    assert_eq!(
        parsed("fof(a,axiom,p).").encode(1, 1).unwrap_err(),
        BridgeError::PredicateLimit
    );
    let empty = parsed("").encode(1, 0).unwrap();
    assert_eq!(empty.reservation.equality_id(), 0);
    assert_eq!(empty.reservation.extended_arities(), [2]);
    let mut p = parsed("fof(a,axiom,p(a)).");
    p.predicates.clear();
    assert_eq!(p.encode(1, 1).unwrap_err(), BridgeError::UnknownPredicate);
    assert_eq!(
        parsed("cnf(a,axiom,(a=a|a=a)).").encode(1, 1).unwrap_err(),
        BridgeError::LiteralLimit
    );
}

fn term_value(term: &Term, valuation: &[bool], flip: bool) -> bool {
    match term {
        Term::Var(id) => valuation[*id as usize],
        Term::Fun(id, args) => args.iter().fold((*id % 2 == 1) ^ flip, |a, t| {
            a ^ term_value(t, valuation, flip)
        }),
    }
}

fn predicate_value(id: u32, args: &[Term], valuation: &[bool], flip: bool, mask: u32) -> bool {
    let parity = args
        .iter()
        .fold(false, |a, t| a ^ term_value(t, valuation, flip));
    parity ^ ((mask >> id) & 1 == 1)
}

fn holds(formula: &Formula, valuation: &mut [bool], flip: bool, mask: u32) -> bool {
    match formula {
        Formula::Atom(Atom::Equal(a, b)) => {
            term_value(a, valuation, flip) == term_value(b, valuation, flip)
        }
        Formula::Atom(Atom::Predicate(id, args)) => {
            predicate_value(*id, args, valuation, flip, mask)
        }
        Formula::True => true,
        Formula::False => false,
        Formula::Not(f) => !holds(f, valuation, flip, mask),
        Formula::And(a, b) => holds(a, valuation, flip, mask) && holds(b, valuation, flip, mask),
        Formula::Or(a, b) => holds(a, valuation, flip, mask) || holds(b, valuation, flip, mask),
        Formula::Implies(a, b) => {
            !holds(a, valuation, flip, mask) || holds(b, valuation, flip, mask)
        }
        Formula::Forall(id, body) | Formula::Exists(id, body) => {
            let old = valuation[*id as usize];
            valuation[*id as usize] = false;
            let left = holds(body, valuation, flip, mask);
            valuation[*id as usize] = true;
            let right = holds(body, valuation, flip, mask);
            valuation[*id as usize] = old;
            if matches!(formula, Formula::Forall(_, _)) {
                left && right
            } else {
                left || right
            }
        }
    }
}

fn encoded_holds(
    formula: &CoreFormula,
    equality: u32,
    valuation: &mut [bool],
    flip: bool,
    mask: u32,
) -> bool {
    match formula {
        CoreFormula::Atom(id, args) if *id == equality => {
            assert_eq!(args.len(), 2);
            term_value(&args[0], valuation, flip) == term_value(&args[1], valuation, flip)
        }
        CoreFormula::Atom(id, args) => predicate_value(*id, args, valuation, flip, mask),
        CoreFormula::True => true,
        CoreFormula::False => false,
        CoreFormula::Not(f) => !encoded_holds(f, equality, valuation, flip, mask),
        CoreFormula::And(a, b) => {
            encoded_holds(a, equality, valuation, flip, mask)
                && encoded_holds(b, equality, valuation, flip, mask)
        }
        CoreFormula::Or(a, b) => {
            encoded_holds(a, equality, valuation, flip, mask)
                || encoded_holds(b, equality, valuation, flip, mask)
        }
        CoreFormula::Implies(a, b) => {
            !encoded_holds(a, equality, valuation, flip, mask)
                || encoded_holds(b, equality, valuation, flip, mask)
        }
        CoreFormula::Forall(id, body) | CoreFormula::Exists(id, body) => {
            let old = valuation[*id as usize];
            valuation[*id as usize] = false;
            let left = encoded_holds(body, equality, valuation, flip, mask);
            valuation[*id as usize] = true;
            let right = encoded_holds(body, equality, valuation, flip, mask);
            valuation[*id as usize] = old;
            if matches!(formula, CoreFormula::Forall(_, _)) {
                left && right
            } else {
                left || right
            }
        }
    }
}

#[test]
fn finite_models_compare_builtin_equality_with_the_reserved_interpretation() {
    for body in [
        "a = b",
        "a != b",
        "~(a = b)",
        "![X]:X = X",
        "?[X]:X = a",
        "![X]:?[Y]:X = Y",
        "![X]:((?[X]:X != a) | X = a)",
        "![X]:((p(X) & X = a) => q(X))",
    ] {
        let source = format!("fof(a,axiom,{body}).");
        let p = parsed(&source);
        let e = parsed(&source).encode(100, 100).unwrap();
        let Body::Fof(original) = &p.declarations[0].body else {
            panic!("fof")
        };
        let EncodedBody::Fof(encoded) = &e.declarations[0].body else {
            panic!("encoded")
        };
        for flip in [false, true] {
            for mask in 0..4 {
                assert_eq!(
                    holds(original, &mut [false; 4], flip, mask),
                    encoded_holds(
                        encoded,
                        e.reservation.equality_id(),
                        &mut [false; 4],
                        flip,
                        mask
                    ),
                    "{body}"
                );
            }
        }
    }
}
