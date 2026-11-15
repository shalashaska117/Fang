use super::*;

fn predicate(search: &mut Search<'_>, symbol: u32) -> Lit {
    Lit {
        positive: true,
        atom: Atom::Pred(search.bank.app(symbol, &[])),
    }
}

fn options(mode: usize) -> Options {
    let mut options = Options::preset("step1").unwrap();
    options.orphan_deletion = true;
    options.duplicates = false;
    match mode {
        0 => {
            options.age_ratio = 1;
            options.weight_ratio = 0;
        }
        1 => {
            options.age_ratio = 0;
            options.weight_ratio = 1;
        }
        2 => options.inputs_first = true,
        3 => options.horn_layer = true,
        4 => options.sine_layer = true,
        _ => unreachable!(),
    }
    options
}

#[test]
fn every_selection_queue_skips_an_orphan_once_and_preserves_inputs() {
    for mode in 0..5 {
        let options = options(mode);
        let mut search = Search::new(&[], &[], &[0, 0], &options, Limits::default()).unwrap();
        let p = predicate(&mut search, 0);
        let q = predicate(&mut search, 1);
        let parent = search.push(
            vec![p, p],
            Rule::Input {
                index: 0,
                original: vec![],
            },
        );
        search.clauses[parent as usize].state = State::Active;
        search.active.push(parent);
        assert!(!search.derived(
            vec![p],
            Rule::Factor {
                parent,
                first: 0,
                second: 1
            }
        ));
        let orphan = parent + 1;
        let survivor = search.push(
            vec![q],
            Rule::Input {
                index: 1,
                original: vec![],
            },
        );
        assert!(!search.admit(survivor));
        assert_eq!(search.passive, 2);
        search.delete(parent);
        assert_eq!(search.select(), Some(survivor), "queue mode {mode}");
        assert_eq!(search.select(), None);
        assert_eq!(search.passive, 0);
        assert_eq!(search.stats.orphaned, 1);
        assert_eq!(search.stats.pruned, 1);
        assert!(search.clauses[orphan as usize].lits.is_empty());
        assert_eq!(search.clauses[parent as usize].lits, vec![p, p]);
        assert_eq!(search.clauses[survivor as usize].lits, vec![q]);
    }
}

#[test]
fn disabled_option_keeps_old_selection_and_allocates_no_parent_records() {
    let mut options = options(0);
    options.orphan_deletion = false;
    let mut search = Search::new(&[], &[], &[0], &options, Limits::default()).unwrap();
    let p = predicate(&mut search, 0);
    let parent = search.push(
        vec![p, p],
        Rule::Input {
            index: 0,
            original: vec![],
        },
    );
    search.clauses[parent as usize].state = State::Deleted;
    assert!(!search.derived(
        vec![p],
        Rule::Factor {
            parent,
            first: 0,
            second: 1
        }
    ));
    assert_eq!(search.select(), Some(parent + 1));
    assert_eq!(search.stats.orphaned, 0);
    assert_eq!(search.stats.pruned, 0);
    assert_eq!(search.generating_parents.capacity(), 0);
}

#[test]
fn replacement_ignores_deleted_proof_parent_but_tracks_original_generating_parent() {
    for delete_generator in [false, true] {
        let options = options(0);
        let mut search = Search::new(&[], &[], &[0], &options, Limits::default()).unwrap();
        let p = predicate(&mut search, 0);
        let generator = search.push(
            vec![p, p, p],
            Rule::Input {
                index: 0,
                original: vec![],
            },
        );
        search.clauses[generator as usize].state = State::Active;
        let intermediate = search.push(
            vec![p, p],
            Rule::Factor {
                parent: generator,
                first: 0,
                second: 1,
            },
        );
        let replacement = search
            .push_simplified(
                vec![p],
                Rule::Factor {
                    parent: intermediate,
                    first: 0,
                    second: 1,
                },
                intermediate,
            )
            .unwrap();
        search.delete(intermediate);
        assert!(!search.admit(replacement));
        if delete_generator {
            search.delete(generator);
        }
        assert_eq!(
            search.select(),
            if delete_generator {
                None
            } else {
                Some(replacement)
            }
        );
        assert_eq!(search.stats.orphaned, u64::from(delete_generator));
        assert_eq!(search.clauses[intermediate as usize].lits, vec![p, p]);
    }
}

#[test]
fn either_deleted_binary_parent_causes_orphan_deletion() {
    for deleted in 0..2 {
        let options = options(0);
        let mut search = Search::new(&[], &[], &[0, 0], &options, Limits::default()).unwrap();
        let p = predicate(&mut search, 0);
        let q = predicate(&mut search, 1);
        let left = search.push(
            vec![p, q],
            Rule::Input {
                index: 0,
                original: vec![],
            },
        );
        let right = search.push(
            vec![Lit {
                positive: false,
                ..p
            }],
            Rule::Input {
                index: 1,
                original: vec![],
            },
        );
        for id in [left, right] {
            search.clauses[id as usize].state = State::Active;
        }
        assert!(!search.derived(
            vec![q],
            Rule::Resolve {
                left,
                left_lit: 0,
                right,
                right_lit: 0
            }
        ));
        search.delete([left, right][deleted]);
        assert_eq!(search.select(), None);
        assert_eq!(search.stats.orphaned, 1);
        assert_eq!(search.passive, 0);
    }
}

#[test]
fn option_parser_requires_explicit_boolean_value() {
    assert!(
        Options::from_settings(&[("orphan_deletion".into(), "on".into())])
            .unwrap()
            .orphan_deletion
    );
    assert!(
        !Options::from_settings(&[("orphan_deletion".into(), "off".into())])
            .unwrap()
            .orphan_deletion
    );
    assert!(Options::from_settings(&[("orphan_deletion".into(), "perhaps".into())]).is_err());
}

#[test]
fn passive_limit_bounds_all_queues_and_reuses_a_selected_slot() {
    for mode in 0..5 {
        let mut options = options(mode);
        options.max_passive = Some(1);
        let mut search = Search::new(&[], &[], &[0, 0, 0], &options, Limits::default()).unwrap();
        let mut ids = Vec::new();
        for symbol in 0..2 {
            let literal = predicate(&mut search, symbol);
            let id = search.push(
                vec![literal],
                Rule::Input {
                    index: symbol as usize,
                    original: vec![],
                },
            );
            assert!(!search.admit(id));
            ids.push(id);
        }
        assert_eq!(search.passive, 1);
        assert_eq!(search.stats.passive_limit_dropped, 1);
        assert_eq!(search.stats.pruned, 1);
        assert!(search.clauses[ids[1] as usize].lits.is_empty());
        assert_eq!(search.select(), Some(ids[0]));
        let literal = predicate(&mut search, 2);
        let next = search.push(
            vec![literal],
            Rule::Input {
                index: 2,
                original: vec![],
            },
        );
        assert!(!search.admit(next));
        assert_eq!(search.passive, 1);
        assert_eq!(search.select(), Some(next));
        assert_eq!(search.select(), None);
        assert_eq!(search.stats.passive_peak, 1);
        assert_eq!(search.stats.orphaned, 0);
    }
}

#[test]
fn zero_passive_limit_drops_nonempty_inputs_without_a_proof() {
    use fang_equality_inference_core::{Atom as InputAtom, Literal};
    let input = vec![vec![Literal {
        positive: true,
        atom: InputAtom::Predicate(0, vec![]),
    }]];
    for orphan_deletion in [false, true] {
        let mut options = options(0);
        options.orphan_deletion = orphan_deletion;
        options.max_passive = Some(0);
        let mut search = Search::new(&input, &[], &[0], &options, Limits::default()).unwrap();
        assert_eq!(search.run(), Stop::Saturated);
        assert_eq!(search.stats.passive_peak, 0);
        assert_eq!(search.stats.passive_limit_dropped, 1);
        assert_eq!(search.stats.pruned, 1);
        assert!(search.found.is_none());
    }
}

#[test]
fn zero_passive_limit_preserves_an_empty_input_refutation() {
    let mut options = options(0);
    options.max_passive = Some(0);
    let mut search = Search::new(&[vec![]], &[], &[], &options, Limits::default()).unwrap();
    let Stop::Proof(empty) = search.run() else {
        panic!("empty input must remain a refutation");
    };
    let proof = search.certificate(empty, 1 << 20).unwrap();
    assert_eq!(proof.unchecked, 0);
    assert_eq!(search.stats.passive_limit_dropped, 0);
    assert_eq!(search.stats.passive_peak, 0);
}

#[test]
fn passive_limit_parser_checks_the_full_unsigned_range() {
    for limit in [0, 1, u64::MAX] {
        assert_eq!(
            Options::from_settings(&[("max_passive".into(), limit.to_string())])
                .unwrap()
                .max_passive,
            Some(limit)
        );
    }
    for bad in ["-1", "1.5", "18446744073709551616", ""] {
        assert!(Options::from_settings(&[("max_passive".into(), bad.into())]).is_err());
    }
}
