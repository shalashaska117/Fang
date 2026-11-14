// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use super::*;

fn options(policy: &str) -> Options {
    Options::from_settings(&[
        ("preset".into(), "step2".into()),
        ("selection".into(), policy.into()),
    ])
    .unwrap()
}

fn negative(term: TermId) -> Lit {
    Lit {
        positive: false,
        atom: Atom::Pred(term),
    }
}

fn selected(search: &mut Search<'_>, literals: Vec<Lit>) -> Option<u16> {
    let id = search.push(
        literals,
        Rule::Input {
            index: 0,
            original: vec![],
        },
    );
    search.eligibility(id);
    search.clauses[id as usize]
        .eligibility
        .as_ref()
        .unwrap()
        .selected
}

#[test]
fn ground_negative_prefers_ground_over_heavier_nonground() {
    let options = options("ground-negative");
    let mut search = Search::new(&[], &[0, 1], &[1], &options, Limits::default()).unwrap();
    let a = search.bank.app(0, &[]);
    let x = search.bank.var(0);
    let fx = search.bank.app(1, &[x]);
    let ffx = search.bank.app(1, &[fx]);
    let nonground = search.bank.app(2, &[ffx]);
    let ground = search.bank.app(2, &[a]);
    assert_eq!(
        selected(&mut search, vec![negative(nonground), negative(ground)]),
        Some(1)
    );
}

#[test]
fn negative_equality_prefers_disequality_over_heavier_predicate() {
    let options = options("negative-equality");
    let mut search = Search::new(&[], &[0, 1], &[1], &options, Limits::default()).unwrap();
    let a = search.bank.app(0, &[]);
    let x = search.bank.var(0);
    let fx = search.bank.app(1, &[x]);
    let ffx = search.bank.app(1, &[fx]);
    let predicate = search.bank.app(2, &[ffx]);
    let equation = Lit {
        positive: false,
        atom: Atom::Eq(x, a),
    };
    assert_eq!(
        selected(&mut search, vec![negative(predicate), equation]),
        Some(1)
    );
}

#[test]
fn both_policies_ignore_positive_literals_and_break_ties_by_first_position() {
    for policy in ["ground-negative", "negative-equality"] {
        let options = options(policy);
        let mut search = Search::new(&[], &[0, 1], &[1], &options, Limits::default()).unwrap();
        let a = search.bank.app(0, &[]);
        let fa = search.bank.app(1, &[a]);
        let predicate = search.bank.app(2, &[a]);
        let positive = Lit {
            positive: true,
            atom: Atom::Eq(fa, a),
        };
        assert_eq!(
            selected(
                &mut search,
                vec![positive, negative(predicate), negative(predicate)]
            ),
            Some(1)
        );
        assert_eq!(selected(&mut search, vec![positive]), None);
    }
}

#[test]
fn both_policies_fall_back_to_weight_within_the_preferred_category() {
    for policy in ["ground-negative", "negative-equality"] {
        let options = options(policy);
        let mut search = Search::new(&[], &[0, 1], &[1], &options, Limits::default()).unwrap();
        let a = search.bank.app(0, &[]);
        let fa = search.bank.app(1, &[a]);
        let small = search.bank.app(2, &[a]);
        let large = search.bank.app(2, &[fa]);
        assert_eq!(
            selected(&mut search, vec![negative(small), negative(large)]),
            Some(1)
        );
    }
}

#[test]
fn ordering_off_preserves_unrestricted_eligibility() {
    for policy in ["ground-negative", "negative-equality"] {
        let mut options = options(policy);
        options.ordering = false;
        let mut search = Search::new(&[], &[0], &[1], &options, Limits::default()).unwrap();
        let a = search.bank.app(0, &[]);
        let predicate = search.bank.app(1, &[a]);
        assert_eq!(selected(&mut search, vec![negative(predicate)]), None);
    }
}
