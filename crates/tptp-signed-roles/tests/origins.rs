// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! `Prepared::origins` gives every declaration of a task its run of prepared clauses.

use fang_tptp_full_frontend_candidate::Role;
use fang_tptp_signed_roles::{Limits, Prepared, Selection, prepare_task};

/// The ranges follow each other from 0 to the clause count, the entries are in source order, and every FOF
/// declaration sent to the Skolem entry has an entry with the same sign.
fn check(prepared: &Prepared) {
    let mut next = 0;
    for origin in &prepared.origins {
        assert_eq!(origin.clauses.start, next);
        assert!(origin.clauses.start <= origin.clauses.end);
        next = origin.clauses.end;
    }
    assert_eq!(next, prepared.clauses.len());
    assert!(
        prepared
            .origins
            .windows(2)
            .all(|pair| pair[0].source_index < pair[1].source_index)
    );
    for &(index, positive) in &prepared.signs {
        assert!(
            prepared
                .origins
                .iter()
                .any(|origin| origin.source_index == index && origin.positive == positive)
        );
    }
}

fn shape(prepared: &Prepared) -> Vec<(usize, Role, bool, usize)> {
    prepared
        .origins
        .iter()
        .map(|origin| {
            (
                origin.source_index,
                origin.role,
                origin.positive,
                origin.clauses.len(),
            )
        })
        .collect()
}

#[test]
fn origins_follow_the_clause_layout() {
    let input = b"cnf(a,axiom,p|q).fof(b,axiom,r&s).fof(t,axiom,$true).cnf(u,axiom,$true|p).fof(g,conjecture,p).";
    let prepared = prepare_task(input, Selection::Goal(0), &Limits::default()).unwrap();
    check(&prepared);
    assert_eq!(
        shape(&prepared),
        vec![
            (0, Role::Axiom, true, 1),
            (1, Role::Axiom, true, 2),
            (2, Role::Axiom, true, 0),
            (3, Role::Axiom, true, 0),
            (4, Role::Conjecture, false, 1),
        ]
    );
}

#[test]
fn negated_conjecture_items_keep_their_role() {
    let input = b"cnf(n,negated_conjecture,~p).cnf(a,axiom,p).";
    let prepared = prepare_task(input, Selection::Inputs, &Limits::default()).unwrap();
    check(&prepared);
    assert_eq!(
        shape(&prepared),
        vec![
            (0, Role::NegatedConjecture, true, 1),
            (1, Role::Axiom, true, 1)
        ]
    );
}

#[test]
fn only_the_selected_conjecture_has_an_origin() {
    let input = b"fof(a,axiom,p).fof(g,conjecture,p).fof(h,conjecture,q).";
    for (index, source_index) in [(0, 1), (1, 2)] {
        let prepared = prepare_task(input, Selection::Goal(index), &Limits::default()).unwrap();
        check(&prepared);
        let goals: Vec<usize> = prepared
            .origins
            .iter()
            .filter(|origin| origin.role == Role::Conjecture)
            .map(|origin| origin.source_index)
            .collect();
        assert_eq!(goals, vec![source_index]);
        assert_eq!(prepared.origins.len(), 2);
    }
}
