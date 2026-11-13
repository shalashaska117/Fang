// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Bindings over two variable banks, side 0 and side 1, which keep two parents apart without renaming them.
//! Unification binds either side; matching binds side 0 only and never looks through side 1.

use crate::term::{Bank, Head, TermId};

const UNBOUND: (TermId, u8) = (u32::MAX, 0);

#[derive(Default)]
pub struct Bindings {
    slots: [Vec<(TermId, u8)>; 2],
    trail: Vec<(u8, u32)>,
}

/// Numbers the variables of a conclusion 0, 1, 2, ... in the order they are first written.
#[derive(Default)]
pub struct Renamer {
    map: [Vec<u32>; 2],
    pub next: u32,
}

impl Renamer {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn assign(&mut self, side: u8, variable: u32) -> u32 {
        let slots = &mut self.map[side as usize];
        let index = variable as usize;
        if index >= slots.len() {
            slots.resize(index + 1, u32::MAX);
        }
        if slots[index] == u32::MAX {
            slots[index] = self.next;
            self.next += 1;
        }
        slots[index]
    }
}

impl Bindings {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn mark(&self) -> usize {
        self.trail.len()
    }

    pub fn undo(&mut self, mark: usize) {
        while self.trail.len() > mark {
            let (side, variable) = self.trail.pop().expect("trail entry");
            self.slots[side as usize][variable as usize] = UNBOUND;
        }
    }

    pub fn clear(&mut self) {
        self.undo(0);
    }

    pub fn get(&self, side: u8, variable: u32) -> Option<(TermId, u8)> {
        let value = *self.slots[side as usize].get(variable as usize)?;
        (value != UNBOUND).then_some(value)
    }

    fn bind(&mut self, side: u8, variable: u32, term: TermId, term_side: u8) {
        let slots = &mut self.slots[side as usize];
        let index = variable as usize;
        if index >= slots.len() {
            slots.resize(index + 1, UNBOUND);
        }
        slots[index] = (term, term_side);
        self.trail.push((side, variable));
    }

    pub fn deref(&self, bank: &Bank, mut term: TermId, mut side: u8) -> (TermId, u8) {
        while let Head::Var(variable) = bank.head(term) {
            match self.get(side, variable) {
                Some((next, next_side)) => {
                    term = next;
                    side = next_side;
                }
                None => break,
            }
        }
        (term, side)
    }

    fn occurs(&self, bank: &Bank, variable: u32, side: u8, term: TermId, term_side: u8) -> bool {
        let mut stack = vec![(term, term_side)];
        while let Some((current, current_side)) = stack.pop() {
            if bank.ground(current) {
                continue;
            }
            let (current, current_side) = self.deref(bank, current, current_side);
            match bank.head(current) {
                Head::Var(other) => {
                    if other == variable && current_side == side {
                        return true;
                    }
                }
                Head::Sym(_) => {
                    for &child in bank.args(current) {
                        stack.push((child, current_side));
                    }
                }
            }
        }
        false
    }

    /// Most general unifier with occurs check. On failure every binding made by this call is undone.
    pub fn unify(
        &mut self,
        bank: &Bank,
        left: TermId,
        left_side: u8,
        right: TermId,
        right_side: u8,
    ) -> bool {
        let mark = self.mark();
        let mut stack = vec![(left, left_side, right, right_side)];
        while let Some((a, side_a, b, side_b)) = stack.pop() {
            let (a, side_a) = self.deref(bank, a, side_a);
            let (b, side_b) = self.deref(bank, b, side_b);
            if a == b && (side_a == side_b || bank.ground(a)) {
                continue;
            }
            match (bank.head(a), bank.head(b)) {
                (Head::Var(variable), _) => {
                    if self.occurs(bank, variable, side_a, b, side_b) {
                        self.undo(mark);
                        return false;
                    }
                    self.bind(side_a, variable, b, side_b);
                }
                (_, Head::Var(variable)) => {
                    if self.occurs(bank, variable, side_b, a, side_a) {
                        self.undo(mark);
                        return false;
                    }
                    self.bind(side_b, variable, a, side_a);
                }
                (Head::Sym(f), Head::Sym(g)) => {
                    if f != g {
                        self.undo(mark);
                        return false;
                    }
                    let left_args = bank.args(a);
                    let right_args = bank.args(b);
                    for index in (0..left_args.len()).rev() {
                        stack.push((left_args[index], side_a, right_args[index], side_b));
                    }
                }
            }
        }
        true
    }

    /// One-sided matching: binds variables of `pattern` (side 0) so that it equals `target` (side 1, never bound).
    /// On failure every binding made by this call is undone.
    pub fn matches(&mut self, bank: &Bank, pattern: TermId, target: TermId) -> bool {
        let mark = self.mark();
        let mut stack = vec![(pattern, target)];
        while let Some((p, t)) = stack.pop() {
            if p == t && bank.ground(p) {
                continue;
            }
            match bank.head(p) {
                Head::Var(variable) => match self.get(0, variable) {
                    Some((bound, side)) => {
                        if side != 1 || bound != t {
                            self.undo(mark);
                            return false;
                        }
                    }
                    None => self.bind(0, variable, t, 1),
                },
                Head::Sym(f) => {
                    if bank.head(t) != Head::Sym(f) {
                        self.undo(mark);
                        return false;
                    }
                    let pattern_args = bank.args(p);
                    let target_args = bank.args(t);
                    for index in (0..pattern_args.len()).rev() {
                        stack.push((pattern_args[index], target_args[index]));
                    }
                }
            }
        }
        true
    }

    /// The instance of `term` (read on `side`), with unbound variables renamed by `renamer`.
    pub fn apply(&self, bank: &mut Bank, term: TermId, side: u8, renamer: &mut Renamer) -> TermId {
        if bank.ground(term) {
            return term;
        }
        match bank.head(term) {
            Head::Var(variable) => match self.get(side, variable) {
                Some((next, next_side)) => self.apply(bank, next, next_side, renamer),
                None => {
                    let number = renamer.assign(side, variable);
                    bank.var(number)
                }
            },
            Head::Sym(symbol) => {
                let children: Vec<TermId> = bank.args(term).to_vec();
                let mut applied = Vec::with_capacity(children.len());
                for child in children {
                    applied.push(self.apply(bank, child, side, renamer));
                }
                bank.app(symbol, &applied)
            }
        }
    }

    /// Whether every variable of `term` on side 0 is bound (used by demodulation's variable condition).
    pub fn side0_bound(&self, bank: &Bank, term: TermId) -> bool {
        let mut found = Vec::new();
        bank.collect_vars(term, &mut found);
        found
            .into_iter()
            .all(|variable| self.get(0, variable).is_some())
    }
}
