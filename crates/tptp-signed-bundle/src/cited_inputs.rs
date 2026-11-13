// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Staged as a module of the research signed-bundle crate.
use super::Flat;
use fang_tptp_signed_roles::Prepared;
use std::collections::BTreeSet;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InputOriginError {
    InputOrder,
    InputIndex(usize),
    OriginLayout,
    SourceIndex(usize),
    UnexpectedNegative(usize),
}

/// Map ascending used clause indices to premise items in expansion order.
/// The origin merge is linear; the ordered set only removes repeated bundle
/// items in the final expansion-order pass. Synthetic object disequalities and
/// the selected conjecture do not become premise citations.
pub fn cited_inputs(
    flat: &Flat,
    prepared: &Prepared,
    inputs: &[usize],
) -> Result<Vec<(usize, usize)>, InputOriginError> {
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
    let mut next = 0;
    for &index in inputs {
        while prepared.origins[next].clauses.end <= index {
            next += 1;
        }
        let source = prepared.origins[next].source_index;
        if prepared.goal != Some(source) && source < needed.len() {
            needed[source] = true;
        }
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
    fn merge_skips_empty_goal_and_synthetic_origins() {
        let (flat, prepared) = example();
        assert_eq!(
            cited_inputs(&flat, &prepared, &[0, 1, 2, 3, 4]),
            Ok(vec![(1, 4), (1, 9)])
        );
        assert_eq!(cited_inputs(&flat, &prepared, &[2, 4]), Ok(vec![]));
        assert_eq!(cited_inputs(&flat, &prepared, &[]), Ok(vec![]));
    }

    #[test]
    fn repeated_items_keep_first_expansion_order() {
        let (mut flat, mut prepared) = example();
        flat.items[1] = (1, 4);
        prepared.origins[0].clauses = 0..1;
        prepared.origins[1].clauses = 1..2;
        assert_eq!(cited_inputs(&flat, &prepared, &[0, 1, 3]), Ok(vec![(1, 4)]));
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
}
