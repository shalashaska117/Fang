// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Positive symbol weights for optional KBO strategies. Variables weigh one.
//! Overflow or a comparison-work limit leaves terms incomparable.

use crate::term::{Bank, Head, TermId};
use std::collections::HashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Scheme {
    Uniform,
    ConstantHeavy,
    InverseFrequency,
}

pub struct Weights {
    symbols: Vec<u64>,
}

impl Weights {
    /// Every constant weighs at least the variable weight, and every symbol
    /// has positive weight. Uniform keeps the existing cached bank weights.
    pub fn new(arities: &[usize], counts: &[u64], scheme: Scheme) -> Option<Self> {
        if scheme == Scheme::Uniform {
            return None;
        }
        let maximum = counts
            .iter()
            .copied()
            .max()
            .unwrap_or(0)
            .saturating_add(1)
            .ilog2();
        let symbols = arities
            .iter()
            .enumerate()
            .map(|(symbol, &arity)| match scheme {
                Scheme::Uniform => 1,
                Scheme::ConstantHeavy => {
                    if arity == 0 {
                        2
                    } else {
                        1
                    }
                }
                Scheme::InverseFrequency => {
                    u64::from(maximum - counts[symbol].saturating_add(1).ilog2()) + 1
                }
            })
            .collect();
        Some(Self { symbols })
    }

    pub fn pair(&self, bank: &Bank, left: TermId, right: TermId) -> Option<(u64, u64)> {
        self.pair_bounded(bank, left, right, 16_384)
    }

    fn pair_bounded(
        &self,
        bank: &Bank,
        left: TermId,
        right: TermId,
        limit: usize,
    ) -> Option<(u64, u64)> {
        let mut remaining = limit;
        let mut memo = HashMap::new();
        let left = self.weight(bank, left, &mut remaining, &mut memo)?;
        let right = self.weight(bank, right, &mut remaining, &mut memo)?;
        Some((left, right))
    }

    fn weight(
        &self,
        bank: &Bank,
        term: TermId,
        remaining: &mut usize,
        memo: &mut HashMap<TermId, u64>,
    ) -> Option<u64> {
        if let Some(&weight) = memo.get(&term) {
            return Some(weight);
        }
        *remaining = remaining.checked_sub(1)?;
        let mut weight = match bank.head(term) {
            Head::Var(_) => 1,
            Head::Sym(symbol) => self.symbols[symbol as usize],
        };
        for &argument in bank.args(term) {
            weight = weight.checked_add(self.weight(bank, argument, remaining, memo)?)?;
        }
        memo.insert(term, weight);
        Some(weight)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kbo::{Cmp, Order, Precedence};
    use crate::options::Options;

    #[test]
    fn constant_weight_can_change_the_orientation() {
        let mut bank = Bank::new();
        let a = bank.app(0, &[]);
        let ga = bank.app(1, &[a]);
        let gga = bank.app(1, &[ga]);
        let left = bank.app(1, &[gga]);
        let right = bank.app(2, &[a, a]);
        let arities = [0, 1, 2];
        let counts = [1, 1, 1];
        let order = Order::new(&arities, &counts, 3, Precedence::Arity);
        assert_eq!(order.compare(&bank, left, right), Cmp::Greater);
        let order = order.with_weights(Weights::new(&arities, &counts, Scheme::ConstantHeavy));
        assert_eq!(order.compare(&bank, left, right), Cmp::Less);
    }

    #[test]
    fn inverse_frequency_weights_are_positive_and_can_change_orientation() {
        let mut bank = Bank::new();
        let a = bank.app(0, &[]);
        let left = bank.app(1, &[a]);
        let right = bank.app(2, &[a]);
        let arities = [0, 1, 1];
        let counts = [100, 10, 1];
        let weights = Weights::new(&arities, &counts, Scheme::InverseFrequency).unwrap();
        assert!(weights.symbols.iter().all(|&weight| weight >= 1));
        let order = Order::new(&arities, &counts, 3, Precedence::Arity);
        assert_eq!(order.compare(&bank, left, right), Cmp::Greater);
        assert_eq!(
            order
                .with_weights(Some(weights))
                .compare(&bank, left, right),
            Cmp::Less
        );
        let edge = Weights::new(&arities, &[0, 1, u64::MAX], Scheme::InverseFrequency).unwrap();
        assert!(
            edge.symbols
                .iter()
                .all(|&weight| (1..=64).contains(&weight))
        );
    }

    #[test]
    fn memoized_weights_preserve_repeated_occurrences_and_refuse_overflow() {
        let mut bank = Bank::new();
        let x = bank.var(0);
        let twice = bank.app(0, &[x, x]);
        let four = bank.app(0, &[twice, twice]);
        let weights = Weights::new(&[2], &[1], Scheme::ConstantHeavy).unwrap();
        assert_eq!(weights.pair(&bank, twice, four), Some((3, 7)));
        assert_eq!(weights.pair_bounded(&bank, twice, four, 2), None);
        let mut huge = x;
        for _ in 0..65 {
            huge = bank.app(0, &[huge, huge]);
        }
        assert_eq!(weights.pair(&bank, huge, x), None);
        let order = Order::new(&[2], &[1], 1, Precedence::Arity).with_weights(Some(weights));
        assert_eq!(order.compare(&bank, huge, twice), Cmp::Incomparable);
    }

    #[test]
    fn variable_balance_still_restricts_weighted_comparisons() {
        let mut bank = Bank::new();
        let x = bank.var(0);
        let y = bank.var(1);
        let fx = bank.app(0, &[x]);
        let fy = bank.app(0, &[y]);
        for scheme in [Scheme::ConstantHeavy, Scheme::InverseFrequency] {
            let order = Order::new(&[1], &[10], 1, Precedence::Arity).with_weights(Weights::new(
                &[1],
                &[10],
                scheme,
            ));
            assert_eq!(order.compare(&bank, fx, fy), Cmp::Incomparable);
            assert_eq!(order.compare(&bank, fx, x), Cmp::Greater);
            assert_eq!(order.compare(&bank, fx, y), Cmp::Incomparable);
        }
    }

    #[test]
    fn finite_ground_census_checks_totality_transitivity_and_context_closure() {
        let mut bank = Bank::new();
        let a = bank.app(0, &[]);
        let b = bank.app(1, &[]);
        let mut terms = vec![a, b];
        for leaf in [a, b] {
            terms.push(bank.app(2, &[leaf]));
            for other in [a, b] {
                terms.push(bank.app(3, &[leaf, other]));
            }
        }
        for term in terms.clone() {
            terms.push(bank.app(2, &[term]));
        }
        terms.sort_unstable();
        terms.dedup();
        for scheme in [
            Scheme::Uniform,
            Scheme::ConstantHeavy,
            Scheme::InverseFrequency,
        ] {
            let arities = [0, 0, 1, 2];
            let counts = [100, 1, 30, 8];
            let order = Order::new(&arities, &counts, 4, Precedence::Arity)
                .with_weights(Weights::new(&arities, &counts, scheme));
            let matrix: Vec<Vec<_>> = terms
                .iter()
                .map(|&left| {
                    terms
                        .iter()
                        .map(|&right| order.compare(&bank, left, right))
                        .collect()
                })
                .collect();
            for (i, &left) in terms.iter().enumerate() {
                assert_eq!(matrix[i][i], Cmp::Equal);
                for (j, &right) in terms.iter().enumerate() {
                    assert_ne!(matrix[i][j], Cmp::Incomparable);
                    assert_eq!(matrix[i][j], matrix[j][i].reverse());
                    if matrix[i][j] != Cmp::Greater {
                        continue;
                    }
                    let fl = bank.app(2, &[left]);
                    let fr = bank.app(2, &[right]);
                    assert_eq!(order.compare(&bank, fl, fr), Cmp::Greater);
                    for k in 0..terms.len() {
                        if matrix[j][k] == Cmp::Greater {
                            assert_eq!(matrix[i][k], Cmp::Greater);
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn schemes_are_explicit_and_the_default_is_uniform() {
        assert_eq!(
            Options::preset("step5").unwrap().kbo_weights,
            Scheme::Uniform
        );
        for (name, scheme) in [
            ("uniform", Scheme::Uniform),
            ("constant-heavy", Scheme::ConstantHeavy),
            ("invfreq", Scheme::InverseFrequency),
        ] {
            let options = Options::from_settings(&[("kbo_weights".into(), name.into())]).unwrap();
            assert_eq!(options.kbo_weights, scheme);
        }
        assert!(Options::from_settings(&[("kbo_weights".into(), "negative".into())]).is_err());
    }
}
