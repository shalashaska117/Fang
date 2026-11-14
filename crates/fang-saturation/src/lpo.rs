// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Lexicographic path ordering for producer-side inference selection.
//! A comparison budget limits temporary storage and work; exhaustion leaves
//! terms incomparable. It never supplies a certificate inference.

use crate::kbo::Cmp;
use crate::term::{Bank, Head, TermId};
use std::collections::HashMap;

const PAIR_LIMIT: usize = 16_384;

struct Comparison<'a> {
    bank: &'a Bank,
    rank: &'a [u32],
    remaining: usize,
    memo: HashMap<(TermId, TermId), bool>,
}

impl Comparison<'_> {
    /// Strict LPO: a left argument dominates the right term, or the left
    /// dominates every right argument and wins by precedence/lexicography.
    fn greater(&mut self, left: TermId, right: TermId) -> Option<bool> {
        if left == right {
            return Some(false);
        }
        if let Some(&answer) = self.memo.get(&(left, right)) {
            return Some(answer);
        }
        self.remaining = self.remaining.checked_sub(1)?;
        let answer = self.compute(left, right)?;
        self.memo.insert((left, right), answer);
        Some(answer)
    }

    fn compute(&mut self, left: TermId, right: TermId) -> Option<bool> {
        let bank = self.bank;
        let Head::Sym(f) = bank.head(left) else {
            return Some(false);
        };
        for &argument in bank.args(left) {
            if argument == right || self.greater(argument, right)? {
                return Some(true);
            }
        }
        let Head::Sym(g) = bank.head(right) else {
            return Some(false);
        };
        if self.rank[f as usize] < self.rank[g as usize] {
            return Some(false);
        }
        for &argument in bank.args(right) {
            if !self.greater(left, argument)? {
                return Some(false);
            }
        }
        if f != g {
            return Some(self.rank[f as usize] > self.rank[g as usize]);
        }
        for (&a, &b) in bank.args(left).iter().zip(bank.args(right)) {
            if a != b {
                return self.greater(a, b);
            }
        }
        Some(false)
    }
}

fn compare_bounded(bank: &Bank, left: TermId, right: TermId, rank: &[u32], limit: usize) -> Cmp {
    if left == right {
        return Cmp::Equal;
    }
    // Give a pair the same evaluation order in both call directions, including
    // when its work budget expires.
    if left > right {
        return compare_bounded(bank, right, left, rank, limit).reverse();
    }
    let mut comparison = Comparison {
        bank,
        rank,
        remaining: limit,
        memo: HashMap::new(),
    };
    match comparison.greater(left, right) {
        Some(true) => Cmp::Greater,
        None => Cmp::Incomparable,
        Some(false) => match comparison.greater(right, left) {
            Some(true) => Cmp::Less,
            Some(false) | None => Cmp::Incomparable,
        },
    }
}

pub(crate) fn compare(bank: &Bank, left: TermId, right: TermId, rank: &[u32]) -> Cmp {
    compare_bounded(bank, left, right, rank, PAIR_LIMIT)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kbo::{Order, OrderKind, Precedence};
    use crate::options::Options;

    #[test]
    fn distribution_orients_oppositely_to_uniform_kbo() {
        let mut bank = Bank::new();
        let x = bank.var(0);
        let y = bank.var(1);
        let z = bank.var(2);
        let plus_yz = bank.app(0, &[y, z]);
        let left = bank.app(1, &[x, plus_yz]);
        let xy = bank.app(1, &[x, y]);
        let xz = bank.app(1, &[x, z]);
        let right = bank.app(0, &[xy, xz]);
        let kbo = Order::new(&[2, 2], &[1, 1], 2, Precedence::Arity);
        assert_eq!(kbo.compare(&bank, left, right), Cmp::Less);
        let lpo = kbo.with_kind(OrderKind::Lpo);
        assert_eq!(lpo.compare(&bank, left, right), Cmp::Greater);
        assert_eq!(lpo.compare(&bank, right, left), Cmp::Less);
    }

    #[test]
    fn lexicographic_comparison_requires_dominance_of_all_right_arguments() {
        let mut bank = Bank::new();
        let a = bank.app(0, &[]);
        let b = bank.app(1, &[]);
        let left = bank.app(2, &[b, a]);
        let bb = bank.app(2, &[b, b]);
        let right = bank.app(2, &[a, bb]);
        assert_eq!(compare(&bank, left, right, &[0, 1, 2]), Cmp::Less);
    }

    #[test]
    fn missing_variables_and_exhausted_budget_do_not_create_an_order() {
        let mut bank = Bank::new();
        let x = bank.var(0);
        let y = bank.var(1);
        let fx = bank.app(0, &[x]);
        assert_eq!(compare(&bank, fx, x, &[0]), Cmp::Greater);
        assert_eq!(compare(&bank, fx, y, &[0]), Cmp::Incomparable);
        assert_eq!(compare(&bank, x, y, &[0]), Cmp::Incomparable);
        assert_eq!(compare_bounded(&bank, fx, x, &[0], 0), Cmp::Incomparable);
        assert_eq!(compare_bounded(&bank, fx, fx, &[0], 0), Cmp::Equal);
        for limit in 0..5 {
            assert_eq!(
                compare_bounded(&bank, fx, x, &[0], limit),
                compare_bounded(&bank, x, fx, &[0], limit).reverse()
            );
        }
    }

    fn terms(bank: &mut Bank) -> Vec<TermId> {
        let mut result = vec![bank.var(0), bank.var(1), bank.app(0, &[]), bank.app(1, &[])];
        let leaves = result.clone();
        for &a in &leaves {
            result.push(bank.app(2, &[a]));
            result.push(bank.app(3, &[a]));
            for &b in &leaves {
                result.push(bank.app(4, &[a, b]));
            }
        }
        for a in result.clone() {
            result.push(bank.app(2, &[a]));
            result.push(bank.app(3, &[a]));
        }
        result.sort_unstable();
        result.dedup();
        result
    }

    fn substitute(bank: &mut Bank, term: TermId, values: &[TermId; 2]) -> TermId {
        match bank.head(term) {
            Head::Var(variable) => values[variable as usize],
            Head::Sym(symbol) => {
                let arguments = bank.args(term).to_vec();
                let substituted: Vec<_> = arguments
                    .into_iter()
                    .map(|a| substitute(bank, a, values))
                    .collect();
                bank.app(symbol, &substituted)
            }
        }
    }

    #[test]
    fn finite_term_census_checks_order_and_context_properties() {
        let mut bank = Bank::new();
        let terms = terms(&mut bank);
        let rank = [0, 1, 2, 3, 4];
        let matrix: Vec<Vec<_>> = terms
            .iter()
            .map(|&a| terms.iter().map(|&b| compare(&bank, a, b, &rank)).collect())
            .collect();
        for (i, &a) in terms.iter().enumerate() {
            assert_eq!(matrix[i][i], Cmp::Equal);
            for (j, &b) in terms.iter().enumerate() {
                assert_eq!(matrix[i][j], matrix[j][i].reverse());
                if bank.ground(a) && bank.ground(b) {
                    assert_ne!(matrix[i][j], Cmp::Incomparable);
                }
                if matrix[i][j] != Cmp::Greater {
                    continue;
                }
                let fa = bank.app(2, &[a]);
                let fb = bank.app(2, &[b]);
                assert_eq!(compare(&bank, fa, fb, &rank), Cmp::Greater);
                for k in 0..terms.len() {
                    if matrix[j][k] == Cmp::Greater {
                        assert_eq!(matrix[i][k], Cmp::Greater);
                    }
                }
            }
            for &argument in bank.args(a) {
                assert_eq!(compare(&bank, a, argument, &rank), Cmp::Greater);
            }
        }
        for values in [
            [terms[0], terms[1]],
            [terms[2], terms[2]],
            [terms[3], terms[2]],
        ] {
            let substituted: Vec<_> = terms
                .iter()
                .map(|&term| substitute(&mut bank, term, &values))
                .collect();
            for i in 0..terms.len() {
                for j in 0..terms.len() {
                    if matrix[i][j] == Cmp::Greater {
                        assert_eq!(
                            compare(&bank, substituted[i], substituted[j], &rank),
                            Cmp::Greater
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn option_selects_lpo_without_changing_the_default() {
        let options = Options::preset("step5").unwrap();
        assert_eq!(options.term_order, OrderKind::Kbo);
        let settings = |values: &[&str]| {
            Options::from_settings(
                &values
                    .iter()
                    .map(|value| ("ordering".into(), (*value).into()))
                    .collect::<Vec<_>>(),
            )
            .unwrap()
        };
        let options = settings(&["lpo"]);
        assert!(options.ordering);
        assert_eq!(options.term_order, OrderKind::Lpo);
        let options = settings(&["lpo", "off"]);
        assert!(!options.ordering);
        let options = settings(&["lpo", "off", "kbo"]);
        assert!(options.ordering);
        assert_eq!(options.term_order, OrderKind::Kbo);
    }
}
