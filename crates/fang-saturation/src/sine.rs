// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! SInE premise selection (Hoder and Voronkov, 2011) over declarations: starting from the goal's symbols, a
//! premise is selected when one of its trigger symbols is reached, and its symbols are reached in turn. A
//! symbol triggers a premise when it occurs in at most `tolerance` times as many premises as the premise's
//! rarest symbol. Selection only decides which input clauses enter the search; a certificate still names
//! inputs by their index, so nothing here needs the checker.

use fang::syntax::Term;
use fang_equality_inference_core::{Atom, Clause};
use std::collections::{BTreeMap, BTreeSet};
use std::ops::Range;

/// A declaration's clauses and whether it is a goal (the negated conjecture or a negated_conjecture item).
pub struct Group {
    pub clauses: Range<usize>,
    pub goal: bool,
}

/// Symbols as (is predicate, number); equality is not a symbol.
fn symbols(clauses: &[Clause], range: Range<usize>) -> BTreeSet<(bool, u32)> {
    fn term(value: &Term, found: &mut BTreeSet<(bool, u32)>) {
        if let Term::Fun(symbol, arguments) = value {
            found.insert((false, *symbol));
            for argument in arguments {
                term(argument, found);
            }
        }
    }
    let mut found = BTreeSet::new();
    for clause in &clauses[range] {
        for literal in clause {
            match &literal.atom {
                Atom::Predicate(symbol, arguments) => {
                    found.insert((true, *symbol));
                    for argument in arguments {
                        term(argument, &mut found);
                    }
                }
                Atom::Equal(left, right) => {
                    term(left, &mut found);
                    term(right, &mut found);
                }
            }
        }
    }
    found
}

/// Which input clauses to keep: the goals' clauses and those of every premise reached within `depth` rounds
/// (all rounds when None). Without a goal every clause is kept.
pub fn select(
    clauses: &[Clause],
    groups: &[Group],
    tolerance: f64,
    depth: Option<u32>,
) -> Vec<bool> {
    run(clauses, groups, tolerance, depth, None)
}

/// The SInE level of every input clause: 0 for a goal, the round in which its premise is reached, u32::MAX when it
/// is never reached; all 0 without a goal.
pub fn levels(clauses: &[Clause], groups: &[Group], tolerance: f64) -> Vec<u32> {
    let mut levels = vec![u32::MAX; clauses.len()];
    run(clauses, groups, tolerance, None, Some(&mut levels));
    if !groups.iter().any(|group| group.goal) {
        levels.iter_mut().for_each(|level| *level = 0);
    }
    levels
}

fn run(
    clauses: &[Clause],
    groups: &[Group],
    tolerance: f64,
    depth: Option<u32>,
    mut levels: Option<&mut Vec<u32>>,
) -> Vec<bool> {
    let mut keep = vec![false; clauses.len()];
    if !groups.iter().any(|group| group.goal) {
        return vec![true; clauses.len()];
    }
    let group_symbols: Vec<BTreeSet<(bool, u32)>> = groups
        .iter()
        .map(|group| symbols(clauses, group.clauses.clone()))
        .collect();
    let mut occurrences: BTreeMap<(bool, u32), usize> = BTreeMap::new();
    for (group, found) in groups.iter().zip(&group_symbols) {
        if !group.goal {
            for symbol in found {
                *occurrences.entry(*symbol).or_default() += 1;
            }
        }
    }
    // Trigger symbols of each premise.
    let mut triggered_by: BTreeMap<(bool, u32), Vec<usize>> = BTreeMap::new();
    for (index, (group, found)) in groups.iter().zip(&group_symbols).enumerate() {
        if group.goal {
            continue;
        }
        let rarest = found
            .iter()
            .map(|symbol| occurrences[symbol])
            .min()
            .unwrap_or(0) as f64;
        for symbol in found {
            if (occurrences[symbol] as f64) <= tolerance * rarest {
                triggered_by.entry(*symbol).or_default().push(index);
            }
        }
    }
    let mut reached: BTreeSet<(bool, u32)> = BTreeSet::new();
    let mut frontier: Vec<(bool, u32)> = Vec::new();
    let mut selected = vec![false; groups.len()];
    for (index, (group, found)) in groups.iter().zip(&group_symbols).enumerate() {
        if group.goal {
            selected[index] = true;
            for symbol in found {
                if reached.insert(*symbol) {
                    frontier.push(*symbol);
                }
            }
        }
    }
    let mut round = 0;
    let mut reached_in = vec![u32::MAX; groups.len()];
    for (index, group) in groups.iter().enumerate() {
        if group.goal {
            reached_in[index] = 0;
        }
    }
    while !frontier.is_empty() && depth.is_none_or(|limit| round < limit) {
        round += 1;
        let mut next = Vec::new();
        for symbol in frontier {
            for &index in triggered_by.get(&symbol).map_or(&[][..], Vec::as_slice) {
                if selected[index] {
                    continue;
                }
                selected[index] = true;
                reached_in[index] = round;
                for found in &group_symbols[index] {
                    if reached.insert(*found) {
                        next.push(*found);
                    }
                }
            }
        }
        frontier = next;
    }
    // Clauses outside every group (there should be none) stay in.
    let mut covered = vec![false; clauses.len()];
    for (index, group) in groups.iter().enumerate() {
        for clause in group.clauses.clone() {
            covered[clause] = true;
            keep[clause] = selected[index];
            if let Some(levels) = levels.as_deref_mut() {
                levels[clause] = reached_in[index];
            }
        }
    }
    for (clause, is_covered) in covered.into_iter().enumerate() {
        if !is_covered {
            keep[clause] = true;
        }
    }
    keep
}
