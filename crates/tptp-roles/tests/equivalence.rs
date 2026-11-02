// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang::ErrorKind;
use fang::syntax::Term;
use fang_equality_inference_core::Atom;
use fang_tptp_full_frontend_candidate::{Body, Formula, Limits, Parsed, parse};

fn source(body: &str) -> String {
    format!("fof(a,axiom,{body}).")
}

fn parsed(body: &str) -> Parsed {
    parse(source(body).as_bytes(), &Limits::default()).unwrap()
}

fn formula(parsed: &Parsed) -> &Formula {
    let Body::Fof(value) = &parsed.declarations[0].body else {
        panic!("FOF")
    };
    value
}

fn atom(id: u32) -> Formula {
    Formula::Atom(Atom::Predicate(id, vec![]))
}

fn term(value: &Term, values: &[bool], model: u32) -> bool {
    match value {
        Term::Var(id) => values[*id as usize],
        Term::Fun(_, args) => {
            let index = args
                .first()
                .map_or(0, |arg| usize::from(term(arg, values, model)));
            model & (1 << index) != 0
        }
    }
}

fn holds(value: &Formula, values: &[bool], model: u32) -> bool {
    match value {
        Formula::Atom(Atom::Predicate(id, args)) => {
            let argument = args
                .first()
                .map_or(0, |arg| usize::from(term(arg, values, model)));
            model & (1 << (2 + 2 * id + argument as u32)) != 0
        }
        Formula::Atom(Atom::Equal(a, b)) => term(a, values, model) == term(b, values, model),
        Formula::True => true,
        Formula::False => false,
        Formula::Not(body) => !holds(body, values, model),
        Formula::And(a, b) => holds(a, values, model) && holds(b, values, model),
        Formula::Or(a, b) => holds(a, values, model) || holds(b, values, model),
        Formula::Implies(a, b) => !holds(a, values, model) || holds(b, values, model),
        Formula::Forall(id, body) | Formula::Exists(id, body) => {
            let evaluate = |value| {
                let mut updated = values.to_vec();
                updated.resize(updated.len().max(*id as usize + 1), false);
                updated[*id as usize] = value;
                holds(body, &updated, model)
            };
            if matches!(value, Formula::Forall(_, _)) {
                evaluate(false) && evaluate(true)
            } else {
                evaluate(false) || evaluate(true)
            }
        }
    }
}

#[test]
fn exact_iff_and_xor_shape_counts() {
    let expected = || {
        Formula::And(
            Box::new(Formula::Implies(Box::new(atom(0)), Box::new(atom(1)))),
            Box::new(Formula::Implies(Box::new(atom(1)), Box::new(atom(0)))),
        )
    };
    let iff = parsed("p<=>q");
    let xor = parsed("p<~>q");
    assert_eq!(*formula(&iff), expected());
    assert_eq!(*formula(&xor), Formula::Not(Box::new(expected())));
    assert_eq!(iff.statistics.formula_nodes, 7);
    assert_eq!(xor.statistics.formula_nodes, 8);
}

#[test]
fn all_truth_assignments_match_equivalence_and_xor() {
    for model in 0..64 {
        let p = model & 4 != 0;
        let q = model & 16 != 0;
        assert_eq!(holds(formula(&parsed("p<=>q")), &[], model), p == q);
        assert_eq!(holds(formula(&parsed("p<~>q")), &[], model), p != q);
        assert_eq!(
            holds(formula(&parsed("(p<=>q)<~>(q=>p)")), &[], model),
            (p == q) != (!q || p)
        );
    }
}

#[test]
fn quantified_equality_copy_preserves_finite_model_meaning() {
    let a = parsed("(![X]:p(f(X)))<=> (?[X]:f(X)=X)");
    let b = parsed("(![X]:p(f(X)))<~> (?[X]:f(X)=X)");
    for model in 0..16 {
        let function = |x: bool| model & (1 << usize::from(x)) != 0;
        let predicate = |x: bool| model & (1 << (2 + usize::from(x))) != 0;
        let left = [false, true].into_iter().all(|x| predicate(function(x)));
        let right = [false, true].into_iter().any(|x| function(x) == x);
        assert_eq!(holds(formula(&a), &[], model), left == right);
        assert_eq!(holds(formula(&b), &[], model), left != right);
    }
}

#[test]
fn source_tables_and_shadowing_survive_duplication() {
    let p = parsed("(![Unused,X]:?[X]:p(f(X)))<=> (?[Y]:q(g(Y)))");
    assert_eq!(p.declarations[0].variables, ["Unused", "X", "Y"]);
    assert_eq!(
        p.functions
            .iter()
            .map(|s| (&*s.name, s.arity))
            .collect::<Vec<_>>(),
        [("f", 1), ("g", 1)]
    );
    assert_eq!(
        p.predicates
            .iter()
            .map(|s| (&*s.name, s.arity))
            .collect::<Vec<_>>(),
        [("p", 1), ("q", 1)]
    );
    assert_eq!(p.statistics.binders, 4);
    let Formula::And(first, second) = formula(&p) else {
        panic!("and")
    };
    let (Formula::Implies(a, b), Formula::Implies(c, d)) = (&**first, &**second) else {
        panic!("implications")
    };
    assert_eq!(a, d);
    assert_eq!(b, c);
    assert_eq!(
        parse(source("(![X]:p(X))<=>q(X)").as_bytes(), &Limits::default())
            .unwrap_err()
            .kind,
        ErrorKind::InvalidInput
    );
}

#[test]
fn formula_and_term_copy_caps_are_charged_exactly() {
    let text = source("p(f(a))<=>q(f(a))");
    let p = parse(text.as_bytes(), &Limits::default()).unwrap();
    assert_eq!(p.statistics.formula_nodes, 7);
    assert_eq!(p.statistics.term_nodes, 8);
    for (nodes, terms, success) in [(7, 8, true), (6, 8, false), (7, 7, false)] {
        let mut limits = Limits {
            max_formula_nodes: nodes,
            ..Limits::default()
        };
        limits.input.max_term_nodes = terms;
        let result = parse(text.as_bytes(), &limits);
        if success {
            assert!(result.is_ok());
        } else {
            assert_eq!(result.unwrap_err().kind, ErrorKind::ResourceLimit);
        }
    }
}

#[test]
fn duplicate_work_uses_the_same_operation_cap() {
    let text = source("p(f(a))<~>q(g(b))");
    let operations = parse(text.as_bytes(), &Limits::default())
        .unwrap()
        .statistics
        .operations;
    let mut limits = Limits::default();
    limits.input.max_operations = operations;
    assert!(parse(text.as_bytes(), &limits).is_ok());
    limits.input.max_operations = operations - 1;
    assert_eq!(
        parse(text.as_bytes(), &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
}

#[test]
fn resulting_depth_and_exponential_growth_stay_bounded() {
    let text = source("p<=>q");
    let mut limits = Limits {
        max_formula_depth: 2,
        ..Limits::default()
    };
    assert_eq!(
        parse(text.as_bytes(), &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    limits.max_formula_depth = 3;
    assert!(parse(text.as_bytes(), &limits).is_ok());
    let mut body = "p".to_owned();
    for _ in 0..15 {
        body = format!("({body}<=>q)");
    }
    assert_eq!(
        parse(source(&body).as_bytes(), &Limits::default())
            .unwrap_err()
            .kind,
        ErrorKind::ResourceLimit
    );
}

#[test]
fn pair_framing_quoted_heads_and_malformed_bytes() {
    for body in [
        "p<=>q<=>r",
        "p<~>q<~>r",
        "p<=>q|r",
        "p& q<~>r",
        "p< = >q",
        "p<~ >q",
    ] {
        assert!(
            parse(source(body).as_bytes(), &Limits::default()).is_err(),
            "{body}"
        );
    }
    let quoted = parsed("'p<=>q'<=> '<~>'");
    assert_eq!(
        quoted
            .predicates
            .iter()
            .map(|p| &*p.name)
            .collect::<Vec<_>>(),
        ["p<=>q", "<~>"]
    );
    let original = source("p<=>q").into_bytes();
    for index in 0..original.len() {
        for byte in 0..=255 {
            let mut altered = original.clone();
            altered[index] = byte;
            if let Ok(value) = parse(&altered, &Limits::default()) {
                assert!(value.statistics.formula_nodes <= Limits::default().max_formula_nodes);
                assert!(value.statistics.term_nodes <= Limits::default().input.max_term_nodes);
            }
        }
    }
}
