use fang::syntax::Term;
use fang_equality_inference_core::{Atom, Clause, Literal};
use fang_equality_search::{
    InvalidPrepared, Limits, Outcome, PreparedError, prove_bytes_ordered, prove_prepared_ordered,
};

fn predicate(id: u32, arguments: Vec<Term>) -> Literal {
    Literal {
        positive: true,
        atom: Atom::Predicate(id, arguments),
    }
}

fn outcome(result: Outcome) -> (Option<String>, usize, usize) {
    match result {
        Outcome::CandidateRefutation {
            certificate,
            statistics,
        } => (
            Some(certificate.to_text(1 << 20).unwrap()),
            statistics.processed_clauses,
            statistics.attempted_inferences,
        ),
        Outcome::Unknown(statistics) => (
            None,
            statistics.processed_clauses,
            statistics.attempted_inferences,
        ),
    }
}

#[test]
fn numeric_entry_preserves_exact_existing_candidates_and_unknowns() {
    let limits = Limits::default();
    for source in [
        "cnf(e,axiom,($false)).",
        "cnf(e,axiom,(a!=a)).",
        "cnf(e,axiom,(a=b)).cnf(n,axiom,(f(a)!=f(b))).",
        "cnf(e,axiom,(a=b)).cnf(p,axiom,(p(a))).cnf(n,axiom,(~p(b))).",
        "cnf(e,axiom,(b=a)).cnf(p,axiom,(p(a))).cnf(n,axiom,(~p(b))).",
        "cnf(e,axiom,(f(X)=X)).cnf(p,axiom,(p(f(a)))).cnf(n,axiom,(~p(a))).",
        "cnf(p,axiom,(p(X)|p(Y))).cnf(n,axiom,(~p(a))).",
        "cnf(p,axiom,(p(a))).",
        "",
    ] {
        let parsed = fang_equality_frontend::parse(source.as_bytes(), &limits.input).unwrap();
        let functions: Vec<_> = parsed.functions.iter().map(|symbol| symbol.arity).collect();
        let predicates: Vec<_> = parsed
            .predicates
            .iter()
            .map(|symbol| symbol.arity)
            .collect();
        let before = parsed.clauses.clone();
        let actual =
            prove_prepared_ordered(&parsed.clauses, &functions, &predicates, &limits).unwrap();
        let expected = prove_bytes_ordered(source.as_bytes(), &limits).unwrap();
        assert_eq!(outcome(actual), outcome(expected), "{source}");
        assert_eq!(parsed.clauses, before);
    }
}

#[test]
fn invalid_later_clause_cannot_hide_behind_empty_clause() {
    let clauses = vec![vec![], vec![predicate(0, vec![Term::Fun(1, vec![])])]];
    assert!(matches!(
        prove_prepared_ordered(&clauses, &[0], &[1], &Limits::default()),
        Err(PreparedError::Invalid(InvalidPrepared::UnknownFunction))
    ));
}

#[test]
fn every_function_and_predicate_head_and_arity_is_checked() {
    for (literal, functions, predicates, expected) in [
        (
            predicate(1, vec![]),
            vec![],
            vec![0],
            InvalidPrepared::UnknownPredicate,
        ),
        (
            predicate(0, vec![]),
            vec![],
            vec![1],
            InvalidPrepared::PredicateArity,
        ),
        (
            predicate(0, vec![Term::Fun(0, vec![])]),
            vec![],
            vec![1],
            InvalidPrepared::UnknownFunction,
        ),
        (
            predicate(0, vec![Term::Fun(0, vec![])]),
            vec![1],
            vec![1],
            InvalidPrepared::FunctionArity,
        ),
    ] {
        let clauses = vec![vec![literal]];
        let before = clauses.clone();
        assert!(
            matches!(prove_prepared_ordered(&clauses, &functions, &predicates, &Limits::default()),
            Err(PreparedError::Invalid(found)) if found == expected)
        );
        assert_eq!(clauses, before);
    }
}

#[test]
fn equality_operands_are_validated() {
    for (left, right) in [
        (Term::Fun(1, vec![]), Term::Var(0)),
        (Term::Var(0), Term::Fun(1, vec![])),
    ] {
        let clauses = vec![vec![Literal {
            positive: false,
            atom: Atom::Equal(left, right),
        }]];
        assert!(matches!(
            prove_prepared_ordered(&clauses, &[0], &[], &Limits::default()),
            Err(PreparedError::Invalid(InvalidPrepared::UnknownFunction))
        ));
    }
}

#[test]
fn complete_table_slots_are_preserved_and_charged() {
    let clauses: Vec<Clause> = vec![vec![]];
    let mut limits = Limits::default();
    limits.input.max_operations = 4;
    assert!(matches!(
        prove_prepared_ordered(&clauses, &[0, 3], &[2], &limits),
        Ok(Outcome::CandidateRefutation { .. })
    ));
    limits.input.max_operations = 3;
    assert!(matches!(
        prove_prepared_ordered(&clauses, &[0, 3], &[2], &limits),
        Err(PreparedError::Resource(
            "prepared validation operation limit"
        ))
    ));
}

#[test]
fn term_depth_boundary_is_exact() {
    let clauses = vec![vec![predicate(
        0,
        vec![Term::Fun(0, vec![Term::Fun(1, vec![])])],
    )]];
    let mut limits = Limits::default();
    limits.input.max_term_depth = 1;
    assert!(matches!(
        prove_prepared_ordered(&clauses, &[1, 0], &[1], &limits),
        Ok(Outcome::Unknown(_))
    ));
    limits.input.max_term_depth = 0;
    assert!(matches!(
        prove_prepared_ordered(&clauses, &[1, 0], &[1], &limits),
        Err(PreparedError::Resource("prepared term depth limit"))
    ));
}

#[test]
fn hard_depth_bound_cannot_be_raised_by_caller() {
    let mut term = Term::Var(0);
    for _ in 0..65 {
        term = Term::Fun(0, vec![term]);
    }
    let clauses = vec![vec![predicate(0, vec![term])]];
    let mut limits = Limits::default();
    limits.input.max_term_depth = usize::MAX;
    assert!(matches!(
        prove_prepared_ordered(&clauses, &[1], &[1], &limits),
        Err(PreparedError::Resource("prepared term depth limit"))
    ));
}

#[test]
fn total_term_node_budget_counts_across_clauses() {
    let clauses = vec![
        vec![predicate(0, vec![Term::Var(0)])],
        vec![predicate(0, vec![Term::Var(1)])],
    ];
    let mut limits = Limits::default();
    limits.input.max_term_nodes = 2;
    assert!(matches!(
        prove_prepared_ordered(&clauses, &[], &[1], &limits),
        Ok(Outcome::Unknown(_))
    ));
    limits.input.max_term_nodes = 1;
    assert!(matches!(
        prove_prepared_ordered(&clauses, &[], &[1], &limits),
        Err(PreparedError::Resource("prepared term-node limit"))
    ));
}

#[test]
fn clause_count_and_width_caps_apply_before_search() {
    let mut limits = Limits::default();
    limits.input.max_clauses = 0;
    assert!(matches!(
        prove_prepared_ordered(&[vec![]], &[], &[], &limits),
        Err(PreparedError::Resource("prepared clause limit"))
    ));
    limits.input.max_clauses = 1;
    limits.max_stored_clauses = 0;
    assert!(matches!(
        prove_prepared_ordered(&[vec![]], &[], &[], &limits),
        Err(PreparedError::Resource("prepared clause limit"))
    ));
    limits.max_stored_clauses = 1;
    limits.input.max_literals = 0;
    assert!(matches!(
        prove_prepared_ordered(&[vec![predicate(0, vec![])]], &[], &[0], &limits),
        Err(PreparedError::Resource("prepared clause width limit"))
    ));
}

#[test]
fn full_variable_ids_are_not_truncated() {
    let clauses = vec![
        vec![predicate(0, vec![Term::Var(u32::MAX)])],
        vec![Literal {
            positive: false,
            atom: Atom::Predicate(0, vec![Term::Var(u32::MAX)]),
        }],
    ];
    // Standardization apart has a smaller representable range and must report
    // its existing error rather than wrapping the identifier.
    assert!(matches!(
        prove_prepared_ordered(&clauses, &[], &[1], &Limits::default()),
        Err(PreparedError::Search(_))
    ));
}
