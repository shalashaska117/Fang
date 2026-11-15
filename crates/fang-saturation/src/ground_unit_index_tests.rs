// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use super::*;

fn push(search: &mut Search<'_>, literals: Vec<Lit>) -> Id {
    search.push(
        literals,
        Rule::Input {
            index: 0,
            original: vec![],
        },
    )
}

fn activate(search: &mut Search<'_>, id: Id) {
    search.clauses[id as usize].state = State::Active;
    search.activations += 1;
    search.clauses[id as usize].activation = search.activations;
    search.active.push(id);
    search.eligibility(id);
    search.prepare_filter(id);
    search.index_insert(id);
}

fn literals(search: &mut Search<'_>) -> Vec<Lit> {
    let a = search.bank.app(0, &[]);
    let b = search.bank.app(1, &[]);
    let x = search.bank.var(0);
    let fa = search.bank.app(2, &[a]);
    let fx = search.bank.app(2, &[x]);
    let terms = [a, b, x, fa, fx];
    let mut atoms = Vec::new();
    for term in terms {
        atoms.push(Atom::Pred(search.bank.app(3, &[term])));
        atoms.push(Atom::Pred(search.bank.app(4, &[term, a])));
    }
    for left in terms {
        for right in terms {
            atoms.push(Atom::Eq(left, right));
        }
    }
    atoms
        .into_iter()
        .flat_map(|atom| {
            [
                Lit {
                    positive: true,
                    atom,
                },
                Lit {
                    positive: false,
                    atom,
                },
            ]
        })
        .collect()
}

#[test]
fn forward_queries_preserve_every_linear_subsumer_in_activation_order() {
    let mut options = Options::preset("step1").unwrap();
    options.index = true;
    let mut search = Search::new(&[], &[0, 0, 1], &[1, 2], &options, Limits::default()).unwrap();
    let pool = literals(&mut search);
    let mut clauses: Vec<Vec<Lit>> = pool.iter().map(|&literal| vec![literal]).collect();
    for (index, &literal) in pool.iter().enumerate() {
        clauses.push(vec![literal, pool[(index + 13) % pool.len()]]);
        clauses.push(vec![literal, literal]);
    }
    let ids: Vec<Id> = clauses
        .iter()
        .map(|clause| push(&mut search, clause.clone()))
        .collect();
    for &id in ids.iter().rev() {
        activate(&mut search, id);
    }
    // Leave stale entries in every index and exercise active filtering.
    for &id in ids.iter().step_by(9) {
        search.delete(id);
    }
    let active = search.active.clone();
    let mut filtered_any = false;
    for clause in clauses {
        let special = push(&mut search, clause);
        let candidates = search.subsumer_candidates(special);
        assert!(
            candidates
                .windows(2)
                .all(|ids| search.clauses[ids[0] as usize].activation
                    < search.clauses[ids[1] as usize].activation)
        );
        assert!(
            candidates
                .iter()
                .all(|&id| search.clauses[id as usize].state == State::Active)
        );
        filtered_any |= candidates.len() < active.len();
        let expected: Vec<_> = active
            .iter()
            .copied()
            .filter(|&id| search.subsumes(id, special))
            .collect();
        let actual: Vec<_> = candidates
            .into_iter()
            .filter(|&id| search.subsumes(id, special))
            .collect();
        assert_eq!(actual, expected);
        let candidates = search.subsumed_candidates(special);
        assert!(
            candidates
                .windows(2)
                .all(|ids| search.clauses[ids[0] as usize].activation
                    < search.clauses[ids[1] as usize].activation)
        );
        let expected: Vec<_> = active
            .iter()
            .copied()
            .filter(|&id| search.subsumes(special, id))
            .collect();
        let actual: Vec<_> = candidates
            .into_iter()
            .filter(|&id| search.subsumes(special, id))
            .collect();
        assert_eq!(actual, expected);
    }
    assert!(filtered_any);
}

fn unit_deletion(index: bool, unit_index: usize, target_index: usize) -> Option<String> {
    let mut options = Options::preset("step1").unwrap();
    options.index = index;
    let mut search = Search::new(&[], &[0, 0, 1], &[1, 2], &options, Limits::default()).unwrap();
    let pool = literals(&mut search);
    let unit = push(&mut search, vec![pool[unit_index]]);
    activate(&mut search, unit);
    let target = push(&mut search, vec![pool[target_index]]);
    search.subsumption_resolution(target).map(|result| {
        let clause = &search.clauses[result as usize];
        format!("{:?} {:?}", clause.lits, clause.rule)
    })
}

#[test]
fn ground_and_variable_unit_deletion_matches_linear_search() {
    // Includes both signs, both equation orientations, shared terms and variables
    // on either side of the one-way match. Compare the exact chosen proof rule.
    for unit in 0..70 {
        for target in 0..70 {
            assert_eq!(
                unit_deletion(true, unit, target),
                unit_deletion(false, unit, target),
                "unit {unit}, target {target}"
            );
        }
    }
}

#[test]
fn ground_units_do_not_match_variable_targets_and_keep_equation_symmetry() {
    let mut options = Options::preset("step1").unwrap();
    options.index = true;
    let mut search = Search::new(&[], &[0, 0, 1], &[1, 2], &options, Limits::default()).unwrap();
    let a = search.bank.app(0, &[]);
    let b = search.bank.app(1, &[]);
    let x = search.bank.var(0);
    let unit = push(
        &mut search,
        vec![Lit {
            positive: true,
            atom: Atom::Eq(a, b),
        }],
    );
    activate(&mut search, unit);
    let reversed = push(
        &mut search,
        vec![Lit {
            positive: true,
            atom: Atom::Eq(b, a),
        }],
    );
    let variable = push(
        &mut search,
        vec![Lit {
            positive: true,
            atom: Atom::Eq(x, b),
        }],
    );
    assert_eq!(search.subsumer_candidates(reversed), vec![unit]);
    assert!(search.subsumer_candidates(variable).is_empty());
    assert!(search.index.subsume_one.is_empty());
    search.delete(unit);
    assert!(search.subsumer_candidates(reversed).is_empty());
}
