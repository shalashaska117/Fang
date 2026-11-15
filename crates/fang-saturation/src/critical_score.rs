// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Optional queue scores for positive unit equations. These never filter clauses.
use crate::clause::{Atom, Lit};
use crate::term::{Bank, TermId};
use std::collections::HashSet;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Standard,
    MaxSide,
    SharedMaxSide,
}

impl Mode {
    pub fn parse(text: &str) -> Result<Self, String> {
        match text {
            "standard" => Ok(Self::Standard),
            "max-side" => Ok(Self::MaxSide),
            "shared-max-side" => Ok(Self::SharedMaxSide),
            _ => Err(format!("unknown critical-pair score {text}")),
        }
    }
}

/// Count each first subterm normally and each later occurrence as one symbol.
/// Stop before traversing an oversized DAG and fall back to the cached tree size.
fn shared_weight(bank: &Bank, term: TermId, budget: usize) -> Option<u32> {
    let mut seen = HashSet::new();
    let mut pending = vec![term];
    let mut count = 0u32;
    let mut remaining = budget;
    while let Some(at) = pending.pop() {
        remaining = remaining.checked_sub(1)?;
        count = count.checked_add(1)?;
        if seen.insert(at) {
            let args = bank.args(at);
            if args.len().saturating_add(pending.len()) > remaining {
                return None;
            }
            pending.extend(args.iter().rev().copied());
        }
    }
    Some(count)
}

fn combine(left: u32, right: u32) -> u64 {
    u64::from(left.max(right)) * 4 + u64::from(left.min(right))
}

pub fn weight(bank: &Bank, literals: &[Lit], standard: u32, mode: Mode) -> u64 {
    if mode == Mode::Standard || literals.len() != 1 || !literals[0].positive {
        return u64::from(standard);
    }
    let Atom::Eq(left, right) = literals[0].atom else {
        return u64::from(standard);
    };
    let (a, b) = if mode == Mode::SharedMaxSide {
        match (
            shared_weight(bank, left, 4096),
            shared_weight(bank, right, 4096),
        ) {
            (Some(a), Some(b)) => (a, b),
            _ => (bank.weight(left), bank.weight(right)),
        }
    } else {
        (bank.weight(left), bank.weight(right))
    };
    combine(a, b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::Head;

    // A separate recursive reference visits children without a work bound.
    fn reference(bank: &Bank, at: TermId, seen: &mut Vec<TermId>) -> u32 {
        if seen.contains(&at) {
            return 1;
        }
        seen.push(at);
        1 + bank
            .args(at)
            .iter()
            .map(|&child| reference(bank, child, seen))
            .sum::<u32>()
    }

    #[test]
    fn bounded_dag_scores_match_reference_and_fall_back() {
        let mut bank = Bank::new();
        let a = bank.app(0, &[]);
        let x = bank.var(0);
        let mut terms = vec![a, x];
        for _ in 0..4 {
            let old = terms.clone();
            for &left in &old {
                for &right in &old {
                    terms.push(bank.app(1, &[left, right]));
                }
            }
            terms.sort_unstable();
            terms.dedup();
            if terms.len() > 1000 {
                break;
            }
        }
        for &term in &terms {
            let expected = reference(&bank, term, &mut vec![]);
            assert_eq!(shared_weight(&bank, term, 4096), Some(expected));
            assert_eq!(shared_weight(&bank, term, (expected - 1) as usize), None);
            assert_eq!(
                shared_weight(&bank, term, expected as usize),
                Some(expected)
            );
        }
        let mut big = a;
        for _ in 0..40 {
            big = bank.app(1, &[big, big]);
        }
        assert_eq!(bank.weight(big), u32::MAX);
        assert_eq!(shared_weight(&bank, big, 4096), Some(81));
        let literal = Lit {
            positive: true,
            atom: Atom::Eq(big, a),
        };
        assert_eq!(
            weight(&bank, &[literal], u32::MAX, Mode::MaxSide),
            4 * u64::from(u32::MAX) + 1
        );
        assert_eq!(
            weight(&bank, &[literal], u32::MAX, Mode::SharedMaxSide),
            325
        );
        assert_eq!(bank.head(a), Head::Sym(0));
    }

    #[test]
    fn score_scope_symmetry_and_parser() {
        let mut bank = Bank::new();
        let a = bank.app(0, &[]);
        let fa = bank.app(1, &[a]);
        let left = Lit {
            positive: true,
            atom: Atom::Eq(a, fa),
        };
        let right = Lit {
            positive: true,
            atom: Atom::Eq(fa, a),
        };
        for mode in [Mode::Standard, Mode::MaxSide, Mode::SharedMaxSide] {
            assert_eq!(
                weight(&bank, &[left], 3, mode),
                weight(&bank, &[right], 3, mode)
            );
            assert_eq!(weight(&bank, &[], 7, mode), 7);
            assert_eq!(weight(&bank, &[left, right], 6, mode), 6);
            assert_eq!(
                weight(
                    &bank,
                    &[Lit {
                        positive: false,
                        ..left
                    }],
                    3,
                    mode
                ),
                3
            );
            assert_eq!(
                weight(
                    &bank,
                    &[Lit {
                        positive: true,
                        atom: Atom::Pred(fa)
                    }],
                    2,
                    mode
                ),
                2
            );
        }
        assert_eq!(weight(&bank, &[left], 3, Mode::Standard), 3);
        assert_eq!(weight(&bank, &[left], 3, Mode::MaxSide), 9);
        assert_eq!(Mode::parse("shared-max-side"), Ok(Mode::SharedMaxSide));
        assert!(Mode::parse("invalid").is_err());
    }
}
