// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Staged as a module of the research signed-bundle crate.
use super::{Flat, INPUT_ROLES, PREMISE_ROLES};
use fang_tptp_signed_roles::Prepared;
use std::collections::BTreeSet;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InputOriginError {
    InputOrder,
    InputIndex(usize),
    OriginLayout,
    SourceIndex(usize),
    UnexpectedNegative(usize),
    UncitableInput(usize),
    MissingObjectWitness(usize),
}

/// Map ascending used clause indices to premise items in expansion order.
/// The origin merge is linear; the ordered set only removes repeated bundle
/// items in the final expansion-order pass. A used synthetic disequality also
/// retains permitted declarations that introduce its objects. The selected
/// conjecture supplies its own objects and is never a premise citation.
pub fn cited_inputs(
    flat: &Flat,
    prepared: &Prepared,
    inputs: &[usize],
) -> Result<Vec<(usize, usize)>, InputOriginError> {
    if flat.roles.len() != flat.items.len()
        || flat.item_objects.len() != flat.items.len()
        || flat.distinct_pairs.len() != flat.distinct_clauses
        || prepared.goal.is_some_and(|goal| goal >= flat.items.len())
    {
        return Err(InputOriginError::OriginLayout);
    }
    if inputs.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(InputOriginError::InputOrder);
    }
    if let Some(&index) = inputs
        .last()
        .filter(|&&index| index >= prepared.clauses.len())
    {
        return Err(InputOriginError::InputIndex(index));
    }
    let source_count = flat
        .items
        .len()
        .checked_add(flat.distinct_clauses)
        .ok_or(InputOriginError::OriginLayout)?;
    let mut end = 0;
    for origin in &prepared.origins {
        if origin.clauses.start != end
            || origin.clauses.end < end
            || origin.clauses.end > prepared.clauses.len()
        {
            return Err(InputOriginError::OriginLayout);
        }
        if origin.source_index >= source_count {
            return Err(InputOriginError::SourceIndex(origin.source_index));
        }
        if !origin.positive && prepared.goal != Some(origin.source_index) {
            return Err(InputOriginError::UnexpectedNegative(origin.source_index));
        }
        end = origin.clauses.end;
    }
    if end != prepared.clauses.len() {
        return Err(InputOriginError::OriginLayout);
    }
    let mut needed = vec![false; flat.items.len()];
    let mut objects_needed = BTreeSet::new();
    let mut next = 0;
    for &index in inputs {
        while prepared.origins[next].clauses.end <= index {
            next += 1;
        }
        let source = prepared.origins[next].source_index;
        if prepared.goal != Some(source) && source < needed.len() {
            needed[source] = true;
        } else if source >= needed.len() {
            let (left, right) = flat.distinct_pairs[source - needed.len()];
            objects_needed.extend([left, right]);
        }
    }
    let allowed = if prepared.goal.is_some() {
        PREMISE_ROLES
    } else {
        INPUT_ROLES
    };
    let mut present = BTreeSet::new();
    for (index, selected) in needed.iter().enumerate() {
        if *selected && !allowed.contains(&flat.roles[index].as_str()) {
            return Err(InputOriginError::UncitableInput(index));
        }
        if *selected || prepared.goal == Some(index) {
            present.extend(flat.item_objects[index].iter().copied());
        }
    }
    for object in objects_needed {
        if present.contains(&object) {
            continue;
        }
        let witness = flat
            .item_objects
            .iter()
            .enumerate()
            .position(|(index, objects)| {
                allowed.contains(&flat.roles[index].as_str()) && objects.contains(&object)
            })
            .ok_or(InputOriginError::MissingObjectWitness(object))?;
        needed[witness] = true;
        present.extend(flat.item_objects[witness].iter().copied());
    }
    let mut selected: BTreeSet<_> = flat
        .items
        .iter()
        .zip(needed)
        .filter_map(|(&item, needed)| needed.then_some(item))
        .collect();
    Ok(flat
        .items
        .iter()
        .filter_map(|&item| selected.remove(&item).then_some(item))
        .collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use fang_tptp_full_frontend_candidate::Role;
    use fang_tptp_signed_roles::Origin;

    fn example() -> (Flat, Prepared) {
        let flat = Flat {
            text: String::new(),
            goals: vec![(0, 2)],
            items: vec![(1, 4), (1, 9), (0, 2), (1, 4), (0, 7)],
            roles: vec![
                "axiom".into(),
                "axiom".into(),
                "conjecture".into(),
                "axiom".into(),
                "axiom".into(),
            ],
            distinct_clauses: 1,
            item_objects: vec![vec![0, 1], vec![], vec![], vec![0, 1], vec![]],
            distinct_pairs: vec![(0, 1)],
        };
        let spans = [
            (0, 0..0),
            (1, 0..2),
            (2, 2..3),
            (3, 3..4),
            (4, 4..4),
            (5, 4..5),
        ];
        let prepared = Prepared {
            goal: Some(2),
            signs: vec![],
            clauses: vec![vec![]; 5],
            function_arities: vec![],
            predicate_arities: vec![],
            origins: spans
                .into_iter()
                .map(|(source_index, clauses)| Origin {
                    source_index,
                    role: if source_index == 2 {
                        Role::Conjecture
                    } else {
                        Role::Axiom
                    },
                    positive: source_index != 2,
                    clauses,
                })
                .collect(),
        };
        (flat, prepared)
    }

    #[test]
    fn merge_keeps_object_witnesses_without_citing_the_goal_or_synthetic_origins() {
        let (flat, prepared) = example();
        assert_eq!(
            cited_inputs(&flat, &prepared, &[0, 1, 2, 3, 4]),
            Ok(vec![(1, 4), (1, 9)])
        );
        assert_eq!(cited_inputs(&flat, &prepared, &[2, 4]), Ok(vec![(1, 4)]));
        assert_eq!(cited_inputs(&flat, &prepared, &[]), Ok(vec![]));
    }

    #[test]
    fn repeated_items_keep_first_expansion_order() {
        let (mut flat, mut prepared) = example();
        flat.items[1] = (1, 4);
        prepared.origins[0].clauses = 0..1;
        prepared.origins[1].clauses = 1..2;
        assert_eq!(cited_inputs(&flat, &prepared, &[0, 1, 3]), Ok(vec![(1, 4)]));
        assert_eq!(
            cited_inputs(&flat, &prepared, &[0, 1, 3, 4]),
            Ok(vec![(1, 4)])
        );
    }

    #[test]
    fn invalid_indices_and_origin_layouts_are_errors() {
        let (flat, mut prepared) = example();
        assert_eq!(
            cited_inputs(&flat, &prepared, &[1, 0]),
            Err(InputOriginError::InputOrder)
        );
        assert_eq!(
            cited_inputs(&flat, &prepared, &[0, 0]),
            Err(InputOriginError::InputOrder)
        );
        assert_eq!(
            cited_inputs(&flat, &prepared, &[5]),
            Err(InputOriginError::InputIndex(5))
        );
        prepared.origins[2].clauses.start = 3;
        assert_eq!(
            cited_inputs(&flat, &prepared, &[0]),
            Err(InputOriginError::OriginLayout)
        );
    }

    #[test]
    fn invalid_source_and_negative_origins_are_errors() {
        let (flat, mut prepared) = example();
        prepared.origins[0].source_index = 6;
        assert_eq!(
            cited_inputs(&flat, &prepared, &[]),
            Err(InputOriginError::SourceIndex(6))
        );
        prepared.origins[0].source_index = 0;
        prepared.origins[0].positive = false;
        assert_eq!(
            cited_inputs(&flat, &prepared, &[]),
            Err(InputOriginError::UnexpectedNegative(0))
        );
    }

    fn bundle(files: &[(&str, &[u8])]) -> fang_tptp_coverage_candidate::Bundle {
        super::super::sealed(
            files
                .iter()
                .map(|(path, bytes)| {
                    (
                        fang_tptp_coverage_candidate::Root::Base,
                        (*path).to_owned(),
                        bytes.to_vec(),
                    )
                })
                .collect(),
        )
    }

    fn check_kept(
        files: &[(&str, &[u8])],
        selection: fang_tptp_signed_roles::Selection,
        used: &[usize],
        expected: &[(usize, usize)],
    ) {
        let bundle = bundle(files);
        let limits = fang_tptp_signed_roles::Limits::default();
        let (flat, prepared) =
            super::super::prepare_bundle_task_named(&bundle, selection, &limits, 8).unwrap();
        let citations = cited_inputs(&flat, &prepared, used).unwrap();
        assert_eq!(citations, expected);
        let (canonical, kept, _) =
            super::super::prepare_cited_task_named(&bundle, selection, &citations, &limits, 8)
                .unwrap();
        assert_eq!(canonical, citations);
        assert_eq!(flat.distinct_clauses, 1);
        assert_eq!(kept.distinct_clauses, 1);
    }

    #[test]
    fn three_generative_regressions_retain_objects_used_by_discovery() {
        use fang_tptp_signed_roles::Selection;
        // Input indices are from the retained discovery proofs, not inferred from the new citation code.
        check_kept(
            &[(
                "top.p",
                include_bytes!("../tests/fixtures/cited-object-0044-top.p"),
            )],
            Selection::Goal(0),
            &[2, 5, 10],
            &[(0, 1), (0, 2), (0, 5)],
        );
        check_kept(
            &[
                (
                    "top.p",
                    include_bytes!("../tests/fixtures/cited-object-0057-top.p"),
                ),
                (
                    "ax.ax",
                    include_bytes!("../tests/fixtures/cited-object-0057-ax.ax"),
                ),
            ],
            Selection::Inputs,
            &[1, 8],
            &[(1, 1), (1, 6)],
        );
        check_kept(
            &[
                (
                    "top.p",
                    include_bytes!("../tests/fixtures/cited-object-0146-top.p"),
                ),
                (
                    "ax.ax",
                    include_bytes!("../tests/fixtures/cited-object-0146-ax.ax"),
                ),
            ],
            Selection::Goal(0),
            &[0, 11],
            &[(1, 0), (1, 3)],
        );
    }

    #[test]
    fn minimal_object_witness_is_added_only_for_a_used_disequality() {
        let bundle = bundle(&[(
            "top.p",
            b"fof(a,axiom,![X]:X=\"o1\"). fof(b,axiom,p(\"o2\")).",
        )]);
        let limits = fang_tptp_signed_roles::Limits::default();
        let selection = fang_tptp_signed_roles::Selection::Inputs;
        let (flat, prepared) =
            super::super::prepare_bundle_task_named(&bundle, selection, &limits, 8).unwrap();
        assert_eq!(cited_inputs(&flat, &prepared, &[0]), Ok(vec![(0, 0)]));
        assert_eq!(
            cited_inputs(&flat, &prepared, &[0, 2]),
            Ok(vec![(0, 0), (0, 1)])
        );
        assert_eq!(
            cited_inputs(&flat, &prepared, &[0, 1, 2]),
            Ok(vec![(0, 0), (0, 1)])
        );
    }

    #[test]
    fn selected_goal_supplies_objects_without_becoming_a_premise() {
        check_kept(
            &[(
                "top.p",
                b"fof(a,axiom,![X]:X=\"o1\"). fof(g,conjecture,p(\"o2\")).",
            )],
            fang_tptp_signed_roles::Selection::Goal(0),
            &[0, 2],
            &[(0, 0)],
        );
    }

    #[test]
    fn another_conjecture_cannot_supply_a_missing_object_as_a_premise() {
        let bundle = bundle(&[(
            "top.p",
            b"fof(a,axiom,![X]:X=\"o1\"). fof(g0,conjecture,p). fof(g1,conjecture,q(\"o2\")).",
        )]);
        let limits = fang_tptp_signed_roles::Limits::default();
        let (flat, prepared) = super::super::prepare_bundle_task_named(
            &bundle,
            fang_tptp_signed_roles::Selection::Goal(0),
            &limits,
            8,
        )
        .unwrap();
        let synthetic = prepared
            .origins
            .iter()
            .find(|origin| origin.source_index == flat.items.len())
            .unwrap()
            .clauses
            .start;
        assert_eq!(
            cited_inputs(&flat, &prepared, &[0, synthetic]),
            Err(InputOriginError::MissingObjectWitness(1))
        );
    }

    #[test]
    fn include_selection_excludes_uncited_object_declarations() {
        check_kept(
            &[("top.p", b"include('ax.ax',[a,b])."), ("ax.ax", b"fof(ignored,axiom,q(\"o2\")). fof(a,axiom,![X]:X=\"o1\"). fof(b,axiom,p(\"o2\")).")],
            fang_tptp_signed_roles::Selection::Inputs, &[0, 2], &[(1, 1), (1, 2)],
        );
    }

    #[test]
    fn malformed_object_metadata_is_refused() {
        let (mut flat, prepared) = example();
        flat.item_objects.pop();
        assert_eq!(
            cited_inputs(&flat, &prepared, &[4]),
            Err(InputOriginError::OriginLayout)
        );
        let (mut flat, prepared) = example();
        flat.distinct_pairs.clear();
        assert_eq!(
            cited_inputs(&flat, &prepared, &[4]),
            Err(InputOriginError::OriginLayout)
        );
    }

    #[test]
    fn multiple_used_pairs_share_a_witness_without_retaining_unneeded_objects() {
        let bundle = bundle(&[(
            "top.p",
            b"fof(a,axiom,![X]:X=\"o0\"). fof(b,axiom,p(\"o1\",\"o2\")). fof(c,axiom,q(\"o3\")).",
        )]);
        let limits = fang_tptp_signed_roles::Limits::default();
        let selection = fang_tptp_signed_roles::Selection::Inputs;
        let (flat, prepared) =
            super::super::prepare_bundle_task_named(&bundle, selection, &limits, 8).unwrap();
        let mut used = vec![0];
        for pair in [(0, 1), (0, 2)] {
            let source = flat.items.len()
                + flat
                    .distinct_pairs
                    .iter()
                    .position(|found| *found == pair)
                    .unwrap();
            used.push(
                prepared
                    .origins
                    .iter()
                    .find(|origin| origin.source_index == source)
                    .unwrap()
                    .clauses
                    .start,
            );
        }
        used.sort_unstable();
        let citations = cited_inputs(&flat, &prepared, &used).unwrap();
        assert_eq!(citations, vec![(0, 0), (0, 1)]);
        let (_, kept, _) =
            super::super::prepare_cited_task_named(&bundle, selection, &citations, &limits, 8)
                .unwrap();
        assert_eq!(flat.distinct_clauses, 6);
        assert_eq!(kept.distinct_clauses, 3);
    }

    #[test]
    fn a_permitted_witness_is_used_instead_of_another_conjecture() {
        let bundle = bundle(&[("top.p", b"fof(a,axiom,![X]:X=\"o1\"). fof(g0,conjecture,p). fof(g1,conjecture,q(\"o2\")). fof(b,axiom,r(\"o2\")).")]);
        let limits = fang_tptp_signed_roles::Limits::default();
        let (flat, prepared) = super::super::prepare_bundle_task_named(
            &bundle,
            fang_tptp_signed_roles::Selection::Goal(0),
            &limits,
            8,
        )
        .unwrap();
        let synthetic = prepared
            .origins
            .iter()
            .find(|origin| origin.source_index == flat.items.len())
            .unwrap()
            .clauses
            .start;
        assert_eq!(
            cited_inputs(&flat, &prepared, &[0, synthetic]),
            Ok(vec![(0, 0), (0, 3)])
        );
    }

    #[test]
    fn negated_conjecture_can_supply_an_object_in_an_inputs_task() {
        check_kept(
            &[(
                "top.p",
                b"fof(a,axiom,![X]:X=\"o1\"). fof(b,negated_conjecture,p(\"o2\")).",
            )],
            fang_tptp_signed_roles::Selection::Inputs,
            &[0, 2],
            &[(0, 0), (0, 1)],
        );
    }

    #[test]
    fn object_in_an_excluded_include_item_never_enters_the_flat_metadata() {
        let bundle = bundle(&[
            ("top.p", b"include('ax.ax',[a])."),
            (
                "ax.ax",
                b"fof(a,axiom,![X]:X=\"o1\"). fof(ignored,axiom,p(\"o2\")).",
            ),
        ]);
        let limits = fang_tptp_signed_roles::Limits::default();
        let (flat, prepared) = super::super::prepare_bundle_task_named(
            &bundle,
            fang_tptp_signed_roles::Selection::Inputs,
            &limits,
            8,
        )
        .unwrap();
        assert_eq!(flat.items, vec![(1, 0)]);
        assert_eq!(flat.item_objects.len(), 1);
        assert_eq!(flat.item_objects[0].len(), 1);
        assert!(flat.distinct_pairs.is_empty());
        assert_eq!(cited_inputs(&flat, &prepared, &[0]), Ok(vec![(1, 0)]));
    }
}
