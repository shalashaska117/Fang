// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Knuth-Bendix ordering with every symbol and variable of weight 1, and the literal ordering built on it.
//! Nothing here affects soundness: the ordering only decides which inferences are tried.

use crate::clause::{Atom, Lit};
use crate::term::{Bank, Head, TermId};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cmp {
    Greater,
    Less,
    Equal,
    Incomparable,
}

impl Cmp {
    pub fn reverse(self) -> Self {
        match self {
            Cmp::Greater => Cmp::Less,
            Cmp::Less => Cmp::Greater,
            other => other,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OrderKind {
    Kbo,
    Lpo,
}

pub struct Order {
    kind: OrderKind,
    weights: Option<crate::weights::Weights>,
    /// Rank of each bank symbol; a higher rank is a greater symbol.
    rank: Vec<u32>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Precedence {
    /// Greater arity is greater, then more frequent is greater, then the larger number.
    Arity,
    /// Less frequent is greater, then greater arity, then the larger number.
    InverseFrequency,
}

impl Order {
    /// `arities` and `counts` are indexed by bank symbol (functions, then predicates); predicates rank above every
    /// function symbol.
    pub fn new(
        arities: &[usize],
        counts: &[u64],
        functions: usize,
        precedence: Precedence,
    ) -> Self {
        let mut symbols: Vec<usize> = (0..arities.len()).collect();
        symbols.sort_by_key(|&symbol| {
            let predicate = (symbol >= functions) as u64;
            let arity = arities[symbol] as u64;
            let count = counts[symbol];
            match precedence {
                Precedence::Arity => (predicate, arity, count, symbol as u64),
                Precedence::InverseFrequency => (predicate, u64::MAX - count, arity, symbol as u64),
            }
        });
        let mut rank = vec![0; arities.len()];
        for (position, symbol) in symbols.into_iter().enumerate() {
            rank[symbol] = position as u32;
        }
        Self {
            rank,
            kind: OrderKind::Kbo,
            weights: None,
        }
    }

    pub fn with_weights(mut self, weights: Option<crate::weights::Weights>) -> Self {
        self.weights = weights;
        self
    }

    pub fn with_kind(mut self, kind: OrderKind) -> Self {
        self.kind = kind;
        self
    }

    pub fn compare(&self, bank: &Bank, s: TermId, t: TermId) -> Cmp {
        if self.kind == OrderKind::Lpo {
            return crate::lpo::compare(bank, s, t, &self.rank);
        }
        if s == t {
            return Cmp::Equal;
        }
        match (bank.head(s), bank.head(t)) {
            (Head::Var(_), Head::Var(_)) => Cmp::Incomparable,
            (Head::Var(x), _) => {
                if bank.contains_var(t, x) {
                    Cmp::Less
                } else {
                    Cmp::Incomparable
                }
            }
            (_, Head::Var(y)) => {
                if bank.contains_var(s, y) {
                    Cmp::Greater
                } else {
                    Cmp::Incomparable
                }
            }
            (Head::Sym(f), Head::Sym(g)) => {
                let (ws, wt) = match &self.weights {
                    None => (u64::from(bank.weight(s)), u64::from(bank.weight(t))),
                    Some(weights) => match weights.pair(bank, s, t) {
                        Some(pair) => pair,
                        None => return Cmp::Incomparable,
                    },
                };
                let Some((s_covers, t_covers)) = crate::variable_balance::balance(bank, s, t)
                else {
                    return Cmp::Incomparable;
                };
                let greater = if s_covers {
                    Cmp::Greater
                } else {
                    Cmp::Incomparable
                };
                let less = if t_covers {
                    Cmp::Less
                } else {
                    Cmp::Incomparable
                };

                if ws > wt {
                    return greater;
                }
                if ws < wt {
                    return less;
                }
                let (rf, rg) = (self.rank[f as usize], self.rank[g as usize]);
                if rf > rg {
                    return greater;
                }
                if rf < rg {
                    return less;
                }
                let (xs, ys) = (bank.args(s), bank.args(t));
                for index in 0..xs.len().min(ys.len()) {
                    if xs[index] == ys[index] {
                        continue;
                    }
                    return match self.compare(bank, xs[index], ys[index]) {
                        Cmp::Greater => greater,
                        Cmp::Less => less,
                        _ => Cmp::Incomparable,
                    };
                }
                Cmp::Incomparable
            }
        }
    }

    fn element(&self, bank: &Bank, a: Option<TermId>, b: Option<TermId>) -> Cmp {
        match (a, b) {
            (None, None) => Cmp::Equal,
            (None, Some(_)) => Cmp::Less,
            (Some(_), None) => Cmp::Greater,
            (Some(x), Some(y)) => self.compare(bank, x, y),
        }
    }

    /// Literal ordering: the multiset extension over {s, t} for s = t, {s, s, t, t} for s != t, and P(u) read as
    /// P(u) = T with T below every term.
    pub fn compare_literals(&self, bank: &Bank, a: Lit, b: Lit) -> Cmp {
        if a == b {
            return Cmp::Equal;
        }
        let mut left = elements(a);
        let mut right = elements(b);
        // Remove the common elements, then each remaining element of the smaller side needs a greater one.
        let mut index = 0;
        while index < left.len() {
            if let Some(position) = right.iter().position(|&other| other == left[index]) {
                right.swap_remove(position);
                left.swap_remove(index);
            } else {
                index += 1;
            }
        }
        if left.is_empty() && right.is_empty() {
            return Cmp::Equal;
        }
        let dominates = |big: &[Option<TermId>], small: &[Option<TermId>]| {
            !big.is_empty()
                && small.iter().all(|&y| {
                    big.iter()
                        .any(|&x| self.element(bank, x, y) == Cmp::Greater)
                })
        };
        if dominates(&left, &right) {
            Cmp::Greater
        } else if dominates(&right, &left) {
            Cmp::Less
        } else {
            Cmp::Incomparable
        }
    }
}

fn elements(literal: Lit) -> Vec<Option<TermId>> {
    let (s, t) = match literal.atom {
        Atom::Eq(s, t) => (Some(s), Some(t)),
        Atom::Pred(atom) => (Some(atom), None),
    };
    if literal.positive {
        vec![s, t]
    } else {
        vec![s, s, t, t]
    }
}
