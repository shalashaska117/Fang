// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Candidate enumeration only. The actual checked reconstructor owns the rule.
use super::*;
use fang_equality_paramodulation_core::{Direction, Position, Root, Witness};

fn term_positions<'a>(
    term: &'a Term,
    position: &mut Position,
    found: &mut Vec<(Position, &'a Term)>,
    remaining: &mut usize,
    depth_limit: usize,
) -> Result<(), Error> {
    if position.path.len() > depth_limit {
        return Err(Error::Resource("occurrence enumeration depth limit"));
    }
    if *remaining == 0 {
        return Err(Error::Resource("occurrence enumeration operation limit"));
    }
    *remaining -= 1;
    if let Term::Fun(_, arguments) = term {
        // Restrict enumeration to original non-variable positions. Substitution
        // preserves every function ancestor, so these paths still designate
        // the corresponding term in the instantiated target.
        found.push((position.clone(), term));
        for (index, child) in arguments.iter().enumerate() {
            position.path.push(index);
            term_positions(child, position, found, remaining, depth_limit)?;
            position.path.pop();
        }
    }
    Ok(())
}

fn positions<'a>(clause: &'a Clause, limits: &Limits) -> Result<Vec<(Position, &'a Term)>, Error> {
    let mut found = Vec::new();
    let mut remaining = limits.input.max_operations;
    for (literal, value) in clause.iter().enumerate() {
        let mut position = Position {
            literal,
            root: Root::EqualityLeft,
            path: Vec::new(),
        };
        match &value.atom {
            Atom::Equal(left, right) => {
                term_positions(
                    left,
                    &mut position,
                    &mut found,
                    &mut remaining,
                    limits.input.max_term_depth,
                )?;
                position.root = Root::EqualityRight;
                term_positions(
                    right,
                    &mut position,
                    &mut found,
                    &mut remaining,
                    limits.input.max_term_depth,
                )?;
            }
            Atom::Predicate(_, arguments) => {
                for (index, term) in arguments.iter().enumerate() {
                    position.root = Root::Argument(index);
                    term_positions(
                        term,
                        &mut position,
                        &mut found,
                        &mut remaining,
                        limits.input.max_term_depth,
                    )?;
                }
            }
        }
    }
    Ok(found)
}

fn pair(
    nodes: &mut Vec<Node>,
    source_id: usize,
    target_id: usize,
    signature: (&[usize], &[usize]),
    limits: &Limits,
    statistics: &mut Statistics,
) -> Result<bool, Error> {
    // Standardize both entire parents apart, including a self-pair. Witnesses
    // use these exact even/odd identifiers, as does Ordered.infer.
    let source = rename_clause(&nodes[source_id].clause, 0, limits)?;
    let target = rename_clause(&nodes[target_id].clause, 1, limits)?;
    let targets = positions(&target, limits)?;
    for (source_pivot, literal) in source.iter().enumerate() {
        if !literal.positive {
            continue;
        }
        let Atom::Equal(left, right) = &literal.atom else {
            continue;
        };
        for direction in [Direction::LeftToRight, Direction::RightToLeft] {
            let from = match direction {
                Direction::LeftToRight => left,
                Direction::RightToLeft => right,
            };
            for (position, selected) in &targets {
                let Some(substitution) = witness(&[(from, selected)], limits, statistics)? else {
                    continue;
                };
                let result = fang_equality_paramodulation_core::paramodulate(
                    &source,
                    &target,
                    Witness {
                        source_pivot,
                        direction,
                        position,
                        substitution: &substitution,
                    },
                    signature.0,
                    signature.1,
                    &limits.reconstruction,
                )
                .map_err(Error::Paramodulation)?;
                if retain(
                    nodes,
                    result.clause,
                    Rule::Paramodulate {
                        source: source_id,
                        target: target_id,
                        source_pivot,
                        direction,
                        position: position.clone(),
                        substitution,
                    },
                    limits,
                    statistics,
                )? {
                    return Ok(true);
                }
            }
        }
    }
    Ok(false)
}

pub(super) fn derive(
    nodes: &mut Vec<Node>,
    parent: usize,
    signature: (&[usize], &[usize]),
    limits: &Limits,
    statistics: &mut Statistics,
) -> Result<bool, Error> {
    for other in 0..=parent {
        if pair(nodes, parent, other, signature, limits, statistics)? {
            return Ok(true);
        }
        if other != parent && pair(nodes, other, parent, signature, limits, statistics)? {
            return Ok(true);
        }
    }
    Ok(false)
}
