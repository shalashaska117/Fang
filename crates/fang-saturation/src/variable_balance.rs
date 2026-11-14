// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Variable multiplicity differences without expanding shared subterms.

use crate::term::{Bank, Head, TermId};
use std::collections::BTreeMap;

pub(crate) fn balance(bank: &Bank, left: TermId, right: TermId) -> Option<(bool, bool)> {
    if bank.weight(left).saturating_add(bank.weight(right)) <= 128 {
        return Some(small_balance(bank, left, right));
    }
    bounded(bank, left, right, 16_384)
}

/// Bank parents have larger identifiers than their children. Descending traversal
/// collects all incoming multiplicities before visiting a node. A common subterm
/// can cancel before its children are visited. Overflow or excess work is unknown.
fn bounded(bank: &Bank, left: TermId, right: TermId, mut work: usize) -> Option<(bool, bool)> {
    if left == right || (bank.ground(left) && bank.ground(right)) {
        return Some((true, true));
    }
    // One canonical traversal also makes refusal symmetric at signed overflow.
    if left > right {
        return bounded(bank, right, left, work).map(|(left, right)| (right, left));
    }
    let mut pending = BTreeMap::<TermId, i128>::new();
    pending.insert(left, 1);
    pending.insert(right, -1);
    let (mut left_covers, mut right_covers) = (true, true);
    while let Some((term, difference)) = pending.pop_last() {
        work = work.checked_sub(1)?;
        if difference == 0 || bank.ground(term) {
            continue;
        }
        match bank.head(term) {
            Head::Var(_) => {
                // Bank interns each variable once, so no other node can add to it.
                left_covers &= difference >= 0;
                right_covers &= difference <= 0;
            }
            Head::Sym(_) => {
                for &child in bank.args(term) {
                    work = work.checked_sub(1)?;
                    if !bank.ground(child) {
                        let entry = pending.entry(child).or_default();
                        *entry = entry.checked_add(difference)?;
                    }
                }
            }
        }
    }
    Some((left_covers, right_covers))
}

// Small terms keep the original allocation and sorting path.
fn small_balance(bank: &Bank, left: TermId, right: TermId) -> (bool, bool) {
    let mut xs = Vec::new();
    let mut ys = Vec::new();
    bank.collect_vars(left, &mut xs);
    bank.collect_vars(right, &mut ys);
    xs.sort_unstable();
    ys.sort_unstable();
    let (mut left_covers, mut right_covers) = (true, true);
    let (mut i, mut j) = (0, 0);
    while i < xs.len() || j < ys.len() {
        let x = xs.get(i).copied().unwrap_or(u32::MAX);
        let y = ys.get(j).copied().unwrap_or(u32::MAX);
        let variable = x.min(y);
        let mut in_left = 0;
        while i < xs.len() && xs[i] == variable {
            in_left += 1;
            i += 1;
        }
        let mut in_right = 0;
        while j < ys.len() && ys[j] == variable {
            in_right += 1;
            j += 1;
        }
        left_covers &= in_left >= in_right;
        right_covers &= in_right >= in_left;
    }
    (left_covers, right_covers)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kbo::{Cmp, Order, Precedence};

    #[test]
    fn dag_counts_match_expanded_occurrences() {
        let mut bank = Bank::new();
        let mut terms = vec![bank.var(0), bank.var(1), bank.var(2), bank.app(0, &[])];
        // Repeated children, shared subgraphs, mixed variables and ground leaves.
        for _ in 0..2 {
            let available = terms.clone();
            for &a in &available {
                for &b in &available {
                    terms.push(bank.app(1, &[a, b]));
                }
            }
            terms.sort_unstable();
            terms.dedup();
        }
        assert_eq!(terms.len(), 404);
        for &left in &terms {
            for &right in &terms {
                let reference = small_balance(&bank, left, right);
                assert_eq!(bounded(&bank, left, right, 16_384), Some(reference));
                assert_eq!(balance(&bank, left, right), Some(reference));
            }
        }
    }

    #[test]
    fn repeated_occurrences_keep_their_multiplicity() {
        let mut bank = Bank::new();
        let x = bank.var(0);
        let y = bank.var(1);
        let mut many = x;
        for _ in 0..100 {
            many = bank.app(0, &[many, many]);
        }
        let with_y = bank.app(0, &[many, y]);
        assert_eq!(bounded(&bank, many, x, 16_384), Some((true, false)));
        assert_eq!(bounded(&bank, x, many, 16_384), Some((false, true)));
        assert_eq!(bounded(&bank, many, y, 16_384), Some((false, false)));
        assert_eq!(bounded(&bank, with_y, many, 16_384), Some((true, false)));
    }

    #[test]
    fn common_subterms_cancel_before_expansion_or_overflow() {
        let mut bank = Bank::new();
        let x = bank.var(0);
        let y = bank.var(1);
        let mut common = x;
        for _ in 0..256 {
            common = bank.app(0, &[common, common]);
        }
        let left = bank.app(0, &[common, x]);
        let right = bank.app(0, &[common, y]);
        assert_eq!(bounded(&bank, left, right, 20), Some((false, false)));
        assert_eq!(bounded(&bank, common, common, 0), Some((true, true)));
    }

    #[test]
    fn work_and_arithmetic_limits_refuse_symmetrically() {
        let mut bank = Bank::new();
        let mut left = bank.var(0);
        let mut right = bank.var(1);
        for _ in 0..128 {
            left = bank.app(0, &[left, left]);
            right = bank.app(0, &[right, right]);
        }
        for limit in [4, 16_384] {
            assert_eq!(bounded(&bank, left, right, limit), None);
            assert_eq!(bounded(&bank, right, left, limit), None);
        }
        let order = Order::new(&[2], &[1], 1, Precedence::Arity);
        assert_eq!(order.compare(&bank, left, right), Cmp::Incomparable);
        assert_eq!(order.compare(&bank, right, left), Cmp::Incomparable);
        let a = bank.app(1, &[]);
        let b = bank.app(2, &[]);
        assert_eq!(bounded(&bank, a, b, 0), Some((true, true)));
    }
}
