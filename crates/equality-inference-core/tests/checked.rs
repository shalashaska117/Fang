use fang::syntax::Term;
use fang_equality_inference_core::{Atom, Error, Limits, Literal, checked};

fn predicate(term: Term) -> Literal {
    Literal {
        positive: true,
        atom: Atom::Predicate(0, vec![term]),
    }
}

#[test]
fn finite_images_are_applied_once_and_duplicates_remain() {
    let premise = vec![
        predicate(Term::Var(0)),
        predicate(Term::Var(1)),
        predicate(Term::Var(0)),
    ];
    let image = Term::Fun(0, vec![Term::Var(1)]);
    let result = checked::instantiate(
        &premise,
        &[(0, Term::Var(1)), (1, image.clone())],
        &[1],
        &[1],
        &Limits::default(),
    )
    .unwrap();
    assert_eq!(
        result.clause,
        vec![
            predicate(Term::Var(1)),
            predicate(image),
            predicate(Term::Var(1))
        ]
    );
}

#[test]
fn unused_images_and_resource_errors_are_checked() {
    assert_eq!(
        checked::instantiate(
            &[],
            &[(9, Term::Fun(1, vec![]))],
            &[0],
            &[],
            &Limits::default()
        ),
        Err(Error::UnknownFunction)
    );
    let none = Limits {
        max_operations: 0,
        ..Limits::default()
    };
    assert_eq!(
        checked::terms_equal(&Term::Var(0), &Term::Var(1), &[], &none),
        Err(Error::Operations)
    );
    assert!(
        !checked::terms_equal(&Term::Var(0), &Term::Var(1), &[], &Limits::default())
            .unwrap()
            .equal
    );
}

#[test]
fn exact_counter_boundary_is_reproducible() {
    let premise = [predicate(Term::Var(0))];
    let images = [(0, Term::Fun(0, vec![]))];
    let result = checked::instantiate(&premise, &images, &[0], &[1], &Limits::default()).unwrap();
    let exact = Limits {
        max_operations: result.statistics.operations,
        max_output_nodes: result.statistics.output_nodes,
        ..Limits::default()
    };
    assert_eq!(
        checked::instantiate(&premise, &images, &[0], &[1], &exact),
        Ok(result)
    );
    let short = Limits {
        max_operations: exact.max_operations - 1,
        ..exact
    };
    assert_eq!(
        checked::instantiate(&premise, &images, &[0], &[1], &short),
        Err(Error::Operations)
    );
}
