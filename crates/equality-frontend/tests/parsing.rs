use fang::syntax::Term;
use fang::{ErrorKind, Limits};
use fang_equality_frontend::parse;
use fang_equality_inference_core::Atom;

fn read(text: &str) -> fang_equality_frontend::Problem {
    parse(text.as_bytes(), &Limits::default()).unwrap()
}

#[test]
fn equality_does_not_allocate_a_predicate_id() {
    let parsed = read("cnf(e,axiom,(f(a) = b | X != f(a))).");
    assert!(parsed.predicates.is_empty());
    assert_eq!(
        parsed
            .functions
            .iter()
            .map(|s| (&*s.name, s.arity))
            .collect::<Vec<_>>(),
        [("f", 1), ("a", 0), ("b", 0)]
    );
    assert_eq!(
        parsed.clauses[0][0].atom,
        Atom::Equal(
            Term::Fun(0, vec![Term::Fun(1, vec![])]),
            Term::Fun(2, vec![])
        )
    );
    assert!(parsed.clauses[0][0].positive);
    assert!(!parsed.clauses[0][1].positive);
    assert_eq!(
        parsed.clauses[0][1].atom,
        Atom::Equal(Term::Var(0), Term::Fun(0, vec![Term::Fun(1, vec![])]))
    );
}

#[test]
fn predicate_and_function_heads_have_separate_namespaces() {
    let parsed = read("cnf(a,axiom,(f(a) | f(a) = a | ~f(f(a)))).");
    assert_eq!(
        parsed
            .predicates
            .iter()
            .map(|s| (&*s.name, s.arity))
            .collect::<Vec<_>>(),
        [("f", 1)]
    );
    assert_eq!(
        parsed
            .functions
            .iter()
            .map(|s| (&*s.name, s.arity))
            .collect::<Vec<_>>(),
        [("a", 0), ("f", 1)]
    );
    assert_eq!(
        parsed.clauses[0][2].atom,
        Atom::Predicate(0, vec![Term::Fun(1, vec![Term::Fun(0, vec![])])])
    );
    assert!(!parsed.clauses[0][2].positive);
}

#[test]
fn clause_variables_reset_and_duplicates_keep_positions() {
    let parsed = read("cnf(a,axiom,(Y != X | p(Y,X) | Y != X)). cnf(b,axiom,(X = Z)).");
    assert_eq!(parsed.clauses[0].len(), 3);
    assert_eq!(parsed.clauses[0][0], parsed.clauses[0][2]);
    assert_eq!(
        parsed.clauses[0][0].atom,
        Atom::Equal(Term::Var(0), Term::Var(1))
    );
    assert_eq!(
        parsed.clauses[1][0].atom,
        Atom::Equal(Term::Var(0), Term::Var(1))
    );
    assert_eq!(parsed.clause_names, ["a", "b"]);
}

#[test]
fn false_and_zero_arity_predicates_keep_their_meaning() {
    let parsed = read("cnf(a,axiom,($false)). cnf(b,axiom,(p | ~q | a = a)).");
    assert!(parsed.clauses[0].is_empty());
    assert_eq!(parsed.clauses[1][0].atom, Atom::Predicate(0, vec![]));
    assert_eq!(parsed.clauses[1][1].atom, Atom::Predicate(1, vec![]));
    assert_eq!(parsed.functions.len(), 1);
}

#[test]
fn both_function_and_predicate_arity_conflicts_are_invalid() {
    for text in [
        "cnf(c,axiom,(f = a | f(a) = a)).",
        "cnf(c,axiom,(p | p(a))).",
        "cnf(c,axiom,(p(f) | f(a) = a)).",
    ] {
        assert_eq!(
            parse(text.as_bytes(), &Limits::default()).unwrap_err().kind,
            ErrorKind::InvalidInput
        );
    }
}

#[test]
fn unsupported_forms_are_distinct_from_malformed_syntax() {
    for text in [
        "cnf(c,axiom,(~a = b)).",
        "cnf(c,axiom,(~a != b)).",
        "cnf(c,axiom,(!(a = b))).",
        "fof(c,axiom,(a = b)).",
        "cnf(c,conjecture,(a = b)).",
        "cnf(c,axiom,(a = 1)).",
        "cnf(c,axiom,(a ! = b)).",
        "cnf(c,axiom,(p),file(x)).",
    ] {
        assert_eq!(
            parse(text.as_bytes(), &Limits::default()).unwrap_err().kind,
            ErrorKind::Unsupported,
            "{text}"
        );
    }
    for text in [
        "cnf(c,axiom,(X)).",
        "cnf(c,axiom,(a =)).",
        "cnf(c,axiom,(a = b = c)).",
        "cnf(c,axiom,(p())).",
        "cnf(c,axiom,(f(a,) = b)).",
        "cnf(c,axiom,(p)). junk",
        "cnf(c,axiom,(p)). cnf(c,axiom,(q)).",
    ] {
        assert_eq!(
            parse(text.as_bytes(), &Limits::default()).unwrap_err().kind,
            ErrorKind::InvalidInput,
            "{text}"
        );
    }
}

#[test]
fn actual_term_limits_count_both_equality_sides_but_not_predicate_heads() {
    let mut limits = Limits {
        max_term_nodes: 2,
        ..Limits::default()
    };
    assert!(parse(b"cnf(c,axiom,(a = b)).", &limits).is_ok());
    assert!(parse(b"cnf(c,axiom,(p(a,b))).", &limits).is_ok());
    limits.max_term_nodes = 1;
    assert_eq!(
        parse(b"cnf(c,axiom,(a = b)).", &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    limits.max_term_nodes = 0;
    assert!(parse(b"cnf(c,axiom,(p)).", &limits).is_ok());
}

#[test]
fn term_depth_and_clause_literal_limits_fail_explicitly() {
    let mut limits = Limits {
        max_term_depth: 1,
        ..Limits::default()
    };
    assert!(parse(b"cnf(c,axiom,(p(a))).", &limits).is_ok());
    assert!(parse(b"cnf(c,axiom,(a = a)).", &limits).is_ok());
    assert_eq!(
        parse(b"cnf(c,axiom,(f(a) = a)).", &limits)
            .unwrap_err()
            .kind,
        ErrorKind::ResourceLimit
    );
    limits.max_literals = 1;
    assert_eq!(
        parse(b"cnf(c,axiom,(a = a | a = a)).", &limits)
            .unwrap_err()
            .kind,
        ErrorKind::ResourceLimit
    );
    limits.max_literals = 0;
    assert!(parse(b"cnf(c,axiom,($false)).", &limits).is_ok());
    assert_eq!(
        parse(b"cnf(c,axiom,(p)).", &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    limits.max_clauses = 0;
    assert_eq!(
        parse(b"cnf(c,axiom,(a = a)).", &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
}

#[test]
fn ascii_whitespace_and_exact_byte_offsets() {
    let parsed = read("\tcnf ( c , axiom , ( a\r\n!=\t b ) ) . \n");
    assert!(!parsed.clauses[0][0].positive);
    let error = parse(b"cnf(c,axiom,(a = \xff)).", &Limits::default()).unwrap_err();
    assert_eq!(error.kind, ErrorKind::InvalidInput);
    assert_eq!(error.offset, Some(17));
}

#[test]
fn input_limit_precedes_lexical_or_syntactic_diagnostics() {
    let limits = Limits {
        max_input_bytes: 0,
        ..Limits::default()
    };
    assert_eq!(
        parse(b"!", &limits).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
    assert!(parse(b"", &limits).is_ok());
}
