// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! A small CDCL solver: two watched literals, first-UIP learning with local minimization, VSIDS on a binary heap,
//! phase saving, Luby restarts and activity-based reduction of learned clauses. Deterministic. Its answers are
//! candidates: a satisfying assignment becomes a model only after the Lean checker accepts it.

use std::time::Instant;

/// A literal: variable `v` is `2v` (positive) or `2v + 1` (negative).
pub type Lit = u32;

pub fn positive(variable: u32) -> Lit {
    variable << 1
}

pub fn negative(variable: u32) -> Lit {
    (variable << 1) | 1
}

fn variable(literal: Lit) -> usize {
    (literal >> 1) as usize
}

fn negate(literal: Lit) -> Lit {
    literal ^ 1
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    Satisfiable,
    Unsatisfiable,
    /// The deadline or the literal budget was reached.
    Stopped,
}

#[derive(Clone, Copy)]
struct Header {
    start: u32,
    length: u32,
    learnt: bool,
    deleted: bool,
    activity: f32,
}

#[derive(Clone, Copy)]
struct Watch {
    clause: u32,
    blocker: Lit,
}

const UNASSIGNED: i8 = 0;
const NO_REASON: u32 = u32::MAX;

pub struct Solver {
    arena: Vec<Lit>,
    headers: Vec<Header>,
    watches: Vec<Vec<Watch>>,
    value: Vec<i8>,
    level: Vec<u32>,
    reason: Vec<u32>,
    phase: Vec<bool>,
    activity: Vec<f64>,
    heap: Vec<u32>,
    position: Vec<u32>,
    trail: Vec<Lit>,
    limits: Vec<usize>,
    head: usize,
    increment: f64,
    clause_increment: f32,
    seen: Vec<bool>,
    inconsistent: bool,
    learnts: usize,
    pub conflicts: u64,
    pub decisions: u64,
    pub propagations: u64,
    /// Stored literals above which the solver stops with `Stopped`.
    pub literal_budget: usize,
}

impl Solver {
    pub fn new(variables: usize) -> Self {
        let mut solver = Solver {
            arena: Vec::new(),
            headers: Vec::new(),
            watches: vec![Vec::new(); 2 * variables],
            value: vec![UNASSIGNED; variables],
            level: vec![0; variables],
            reason: vec![NO_REASON; variables],
            phase: vec![false; variables],
            activity: vec![0.0; variables],
            heap: Vec::with_capacity(variables),
            position: vec![u32::MAX; variables],
            trail: Vec::with_capacity(variables),
            limits: Vec::new(),
            head: 0,
            increment: 1.0,
            clause_increment: 1.0,
            seen: vec![false; variables],
            inconsistent: false,
            learnts: 0,
            conflicts: 0,
            decisions: 0,
            propagations: 0,
            literal_budget: usize::MAX,
        };
        for index in 0..variables as u32 {
            solver.heap_insert(index);
        }
        solver
    }

    pub fn variables(&self) -> usize {
        self.value.len()
    }

    pub fn stored_literals(&self) -> usize {
        self.arena.len()
    }

    /// Approximate heap bytes: the literal arena, clause headers, watch lists and the per-variable arrays.
    pub fn memory_bytes(&self) -> u64 {
        let watches: usize = self.watches.iter().map(|list| list.capacity()).sum();
        (self.arena.capacity() * 4
            + self.headers.capacity() * std::mem::size_of::<Header>()
            + watches * std::mem::size_of::<Watch>()
            + self.watches.len() * 24
            + self.value.len() * 40) as u64
    }

    fn literal_value(&self, literal: Lit) -> i8 {
        let value = self.value[variable(literal)];
        if literal & 1 == 1 { -value } else { value }
    }

    /// The truth value of a variable in the last satisfying assignment.
    pub fn model_value(&self, index: u32) -> bool {
        self.value[index as usize] > 0
    }

    fn decision_level(&self) -> u32 {
        self.limits.len() as u32
    }

    // Heap ordered by activity, largest first.
    fn heap_less(&self, left: u32, right: u32) -> bool {
        self.activity[left as usize] > self.activity[right as usize]
    }

    fn heap_up(&mut self, mut index: usize) {
        let item = self.heap[index];
        while index > 0 {
            let parent = (index - 1) / 2;
            if !self.heap_less(item, self.heap[parent]) {
                break;
            }
            self.heap[index] = self.heap[parent];
            self.position[self.heap[index] as usize] = index as u32;
            index = parent;
        }
        self.heap[index] = item;
        self.position[item as usize] = index as u32;
    }

    fn heap_down(&mut self, mut index: usize) {
        let item = self.heap[index];
        loop {
            let left = 2 * index + 1;
            if left >= self.heap.len() {
                break;
            }
            let right = left + 1;
            let child =
                if right < self.heap.len() && self.heap_less(self.heap[right], self.heap[left]) {
                    right
                } else {
                    left
                };
            if !self.heap_less(self.heap[child], item) {
                break;
            }
            self.heap[index] = self.heap[child];
            self.position[self.heap[index] as usize] = index as u32;
            index = child;
        }
        self.heap[index] = item;
        self.position[item as usize] = index as u32;
    }

    fn heap_insert(&mut self, item: u32) {
        if self.position[item as usize] != u32::MAX {
            return;
        }
        self.heap.push(item);
        let index = self.heap.len() - 1;
        self.position[item as usize] = index as u32;
        self.heap_up(index);
    }

    fn heap_pop(&mut self) -> Option<u32> {
        let top = *self.heap.first()?;
        let last = self.heap.pop().unwrap();
        self.position[top as usize] = u32::MAX;
        if !self.heap.is_empty() {
            self.heap[0] = last;
            self.position[last as usize] = 0;
            self.heap_down(0);
        }
        Some(top)
    }

    fn bump(&mut self, index: usize) {
        self.activity[index] += self.increment;
        if self.activity[index] > 1e100 {
            for value in &mut self.activity {
                *value *= 1e-100;
            }
            self.increment *= 1e-100;
        }
        let position = self.position[index];
        if position != u32::MAX {
            self.heap_up(position as usize);
        }
    }

    fn bump_clause(&mut self, clause: u32) {
        let header = &mut self.headers[clause as usize];
        header.activity += self.clause_increment;
        if header.activity > 1e20 {
            for header in &mut self.headers {
                header.activity *= 1e-20;
            }
            self.clause_increment *= 1e-20;
        }
    }

    fn assign(&mut self, literal: Lit, reason: u32) {
        let index = variable(literal);
        self.value[index] = if literal & 1 == 0 { 1 } else { -1 };
        self.level[index] = self.decision_level();
        self.reason[index] = reason;
        self.trail.push(literal);
    }

    fn attach(&mut self, literals: &[Lit], learnt: bool) -> u32 {
        let index = self.headers.len() as u32;
        self.headers.push(Header {
            start: self.arena.len() as u32,
            length: literals.len() as u32,
            learnt,
            deleted: false,
            activity: 0.0,
        });
        self.arena.extend_from_slice(literals);
        self.watches[negate(literals[0]) as usize].push(Watch {
            clause: index,
            blocker: literals[1],
        });
        self.watches[negate(literals[1]) as usize].push(Watch {
            clause: index,
            blocker: literals[0],
        });
        if learnt {
            self.learnts += 1;
        }
        index
    }

    /// Add a clause at decision level 0. Returns false once the formula is known unsatisfiable.
    pub fn add_clause(&mut self, input: &[Lit]) -> bool {
        if self.inconsistent {
            return false;
        }
        let mut literals: Vec<Lit> = input.to_vec();
        literals.sort_unstable();
        literals.dedup();
        let mut kept = Vec::with_capacity(literals.len());
        for (index, &literal) in literals.iter().enumerate() {
            if index + 1 < literals.len() && literals[index + 1] == negate(literal) {
                return true;
            }
            match self.literal_value(literal) {
                1 => return true,
                -1 => {}
                _ => kept.push(literal),
            }
        }
        match kept.len() {
            0 => {
                self.inconsistent = true;
                false
            }
            1 => {
                self.assign(kept[0], NO_REASON);
                if self.propagate().is_some() {
                    self.inconsistent = true;
                    return false;
                }
                true
            }
            _ => {
                self.attach(&kept, false);
                true
            }
        }
    }

    /// Unit propagation; returns a conflicting clause.
    fn propagate(&mut self) -> Option<u32> {
        while self.head < self.trail.len() {
            let literal = self.trail[self.head];
            self.head += 1;
            self.propagations += 1;
            let mut watchers = std::mem::take(&mut self.watches[literal as usize]);
            let false_literal = negate(literal);
            let mut keep = 0;
            let mut conflict = None;
            let mut index = 0;
            while index < watchers.len() {
                let watch = watchers[index];
                index += 1;
                if self.headers[watch.clause as usize].deleted {
                    continue;
                }
                if self.literal_value(watch.blocker) == 1 {
                    watchers[keep] = watch;
                    keep += 1;
                    continue;
                }
                let header = self.headers[watch.clause as usize];
                let start = header.start as usize;
                if self.arena[start] == false_literal {
                    self.arena.swap(start, start + 1);
                }
                let first = self.arena[start];
                if first != watch.blocker && self.literal_value(first) == 1 {
                    watchers[keep] = Watch {
                        clause: watch.clause,
                        blocker: first,
                    };
                    keep += 1;
                    continue;
                }
                let mut moved = false;
                for other in 2..header.length as usize {
                    let candidate = self.arena[start + other];
                    if self.literal_value(candidate) != -1 {
                        self.arena.swap(start + 1, start + other);
                        self.watches[negate(candidate) as usize].push(Watch {
                            clause: watch.clause,
                            blocker: first,
                        });
                        moved = true;
                        break;
                    }
                }
                if moved {
                    continue;
                }
                watchers[keep] = Watch {
                    clause: watch.clause,
                    blocker: first,
                };
                keep += 1;
                if self.literal_value(first) == -1 {
                    conflict = Some(watch.clause);
                    while index < watchers.len() {
                        watchers[keep] = watchers[index];
                        keep += 1;
                        index += 1;
                    }
                    break;
                }
                self.assign(first, watch.clause);
            }
            watchers.truncate(keep);
            self.watches[literal as usize] = watchers;
            if conflict.is_some() {
                return conflict;
            }
        }
        None
    }

    fn clause_literals(&self, clause: u32) -> &[Lit] {
        let header = self.headers[clause as usize];
        &self.arena[header.start as usize..(header.start + header.length) as usize]
    }

    /// First-UIP analysis; the asserting literal comes first. Returns the clause and the backjump level.
    fn analyze(&mut self, mut conflict: u32) -> (Vec<Lit>, u32) {
        let mut learnt: Vec<Lit> = vec![0];
        let mut pending = 0;
        let mut index = self.trail.len();
        let mut literal: Option<Lit> = None;
        let current = self.decision_level();
        loop {
            if self.headers[conflict as usize].learnt {
                self.bump_clause(conflict);
            }
            let literals: Vec<Lit> = self.clause_literals(conflict).to_vec();
            for &other in &literals {
                if Some(other) == literal {
                    continue;
                }
                let index = variable(other);
                if !self.seen[index] && self.level[index] > 0 {
                    self.seen[index] = true;
                    self.bump(index);
                    if self.level[index] >= current {
                        pending += 1;
                    } else {
                        learnt.push(other);
                    }
                }
            }
            loop {
                index -= 1;
                if self.seen[variable(self.trail[index])] {
                    break;
                }
            }
            let next = self.trail[index];
            self.seen[variable(next)] = false;
            pending -= 1;
            if pending == 0 {
                learnt[0] = negate(next);
                break;
            }
            literal = Some(next);
            conflict = self.reason[variable(next)];
        }
        // Local minimization: drop a literal whose reason is covered by the clause.
        let marked: Vec<usize> = learnt
            .iter()
            .skip(1)
            .map(|&other| variable(other))
            .collect();
        let mut kept = vec![learnt[0]];
        for &other in learnt.iter().skip(1) {
            let reason = self.reason[variable(other)];
            let redundant = reason != NO_REASON
                && self.clause_literals(reason).iter().all(|&inner| {
                    let index = variable(inner);
                    index == variable(other) || self.seen[index] || self.level[index] == 0
                });
            if !redundant {
                kept.push(other);
            }
        }
        for index in marked {
            self.seen[index] = false;
        }
        let mut level = 0;
        if kept.len() > 1 {
            let mut best = 1;
            for position in 2..kept.len() {
                if self.level[variable(kept[position])] > self.level[variable(kept[best])] {
                    best = position;
                }
            }
            kept.swap(1, best);
            level = self.level[variable(kept[1])];
        }
        (kept, level)
    }

    fn backtrack(&mut self, level: u32) {
        if self.decision_level() <= level {
            return;
        }
        let limit = self.limits[level as usize];
        for position in (limit..self.trail.len()).rev() {
            let literal = self.trail[position];
            let index = variable(literal);
            self.phase[index] = literal & 1 == 0;
            self.value[index] = UNASSIGNED;
            self.reason[index] = NO_REASON;
            self.heap_insert(index as u32);
        }
        self.trail.truncate(limit);
        self.head = limit;
        self.limits.truncate(level as usize);
    }

    fn locked(&self, clause: u32) -> bool {
        let first = self.clause_literals(clause)[0];
        let index = variable(first);
        self.reason[index] == clause && self.literal_value(first) == 1
    }

    fn reduce(&mut self) {
        let mut candidates: Vec<u32> = (0..self.headers.len() as u32)
            .filter(|&clause| {
                let header = self.headers[clause as usize];
                header.learnt && !header.deleted && header.length > 2 && !self.locked(clause)
            })
            .collect();
        candidates.sort_by(|left, right| {
            self.headers[*left as usize]
                .activity
                .total_cmp(&self.headers[*right as usize].activity)
        });
        for &clause in candidates.iter().take(candidates.len() / 2) {
            self.headers[clause as usize].deleted = true;
            self.learnts -= 1;
        }
        // Compact the arena when deleted clauses dominate it.
        let live: usize = self
            .headers
            .iter()
            .filter(|header| !header.deleted)
            .map(|header| header.length as usize)
            .sum();
        if live * 2 < self.arena.len() {
            let mut arena = Vec::with_capacity(live);
            for header in &mut self.headers {
                if header.deleted {
                    header.length = 0;
                    header.start = 0;
                    continue;
                }
                let start = arena.len() as u32;
                arena.extend_from_slice(
                    &self.arena[header.start as usize..(header.start + header.length) as usize],
                );
                header.start = start;
            }
            self.arena = arena;
        }
        for watchers in &mut self.watches {
            let headers = &self.headers;
            watchers.retain(|watch| !headers[watch.clause as usize].deleted);
        }
    }

    fn luby(mut index: u64) -> u64 {
        let mut size = 1u64;
        let mut sequence = 0u32;
        while size < index + 1 {
            sequence += 1;
            size = 2 * size + 1;
        }
        while size - 1 != index {
            size = (size - 1) >> 1;
            sequence -= 1;
            index %= size;
        }
        1u64 << sequence
    }

    /// Search until an answer, the deadline or the literal budget.
    pub fn solve(&mut self, deadline: Instant) -> Outcome {
        self.solve_limited(deadline, u64::MAX)
    }

    /// As `solve`, and also stop after `conflict_limit` more conflicts. A stopped search can be resumed; learned
    /// clauses stay.
    pub fn solve_limited(&mut self, deadline: Instant, conflict_limit: u64) -> Outcome {
        let stop_at = self.conflicts.saturating_add(conflict_limit);
        if self.inconsistent {
            return Outcome::Unsatisfiable;
        }
        if self.propagate().is_some() {
            self.inconsistent = true;
            return Outcome::Unsatisfiable;
        }
        let mut restart = 0u64;
        let mut maximum_learnts = (self.headers.len() / 3).max(5000);
        loop {
            let budget = 100 * Self::luby(restart);
            restart += 1;
            let mut conflicts = 0u64;
            loop {
                if let Some(conflict) = self.propagate() {
                    self.conflicts += 1;
                    conflicts += 1;
                    if self.decision_level() == 0 {
                        self.inconsistent = true;
                        return Outcome::Unsatisfiable;
                    }
                    let (learnt, level) = self.analyze(conflict);
                    self.backtrack(level);
                    if learnt.len() == 1 {
                        self.assign(learnt[0], NO_REASON);
                    } else {
                        let clause = self.attach(&learnt, true);
                        self.bump_clause(clause);
                        self.assign(learnt[0], clause);
                    }
                    self.increment /= 0.95;
                    self.clause_increment /= 0.999;
                    if self.conflicts >= stop_at
                        || self.conflicts.is_multiple_of(256)
                            && (Instant::now() >= deadline
                                || self.arena.len() > self.literal_budget)
                    {
                        self.backtrack(0);
                        return Outcome::Stopped;
                    }
                } else {
                    if conflicts >= budget {
                        self.backtrack(0);
                        break;
                    }
                    if self.learnts >= maximum_learnts + self.trail.len() {
                        self.reduce();
                        maximum_learnts += maximum_learnts / 10;
                    }
                    let mut next = None;
                    while let Some(candidate) = self.heap_pop() {
                        if self.value[candidate as usize] == UNASSIGNED {
                            next = Some(candidate);
                            break;
                        }
                    }
                    let Some(index) = next else {
                        return Outcome::Satisfiable;
                    };
                    self.decisions += 1;
                    if self.decisions.is_multiple_of(4096) && Instant::now() >= deadline {
                        self.backtrack(0);
                        return Outcome::Stopped;
                    }
                    self.limits.push(self.trail.len());
                    let literal = if self.phase[index as usize] {
                        positive(index)
                    } else {
                        negative(index)
                    };
                    self.assign(literal, NO_REASON);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    fn brute(variables: u32, clauses: &[Vec<Lit>]) -> bool {
        (0u64..1 << variables).any(|bits| {
            clauses.iter().all(|clause| {
                clause.iter().any(|&literal| {
                    let value = bits >> (literal >> 1) & 1 == 1;
                    if literal & 1 == 0 { value } else { !value }
                })
            })
        })
    }

    fn check(variables: u32, clauses: &[Vec<Lit>]) {
        let mut solver = Solver::new(variables as usize);
        let mut consistent = true;
        for clause in clauses {
            consistent &= solver.add_clause(clause);
        }
        let outcome = if consistent {
            solver.solve(Instant::now() + Duration::from_secs(10))
        } else {
            Outcome::Unsatisfiable
        };
        let expected = brute(variables, clauses);
        assert_eq!(outcome == Outcome::Satisfiable, expected, "{clauses:?}");
        if outcome == Outcome::Satisfiable {
            for clause in clauses {
                assert!(
                    clause
                        .iter()
                        .any(|&literal| solver.model_value(literal >> 1) == (literal & 1 == 0))
                );
            }
        }
    }

    #[test]
    fn random_formulas_agree_with_brute_force() {
        let mut state = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for round in 0..400 {
            let variables = 3 + (round % 10) as u32;
            let count = (variables as u64 * (2 + next() % 4)) as usize;
            let clauses: Vec<Vec<Lit>> = (0..count)
                .map(|_| {
                    let width = 1 + (next() % 3) as usize;
                    (0..width)
                        .map(|_| ((next() % variables as u64) as u32) << 1 | (next() & 1) as u32)
                        .collect()
                })
                .collect();
            check(variables, &clauses);
        }
    }

    #[test]
    fn pigeonhole_is_unsatisfiable() {
        // Five pigeons, four holes.
        let (pigeons, holes) = (5u32, 4u32);
        let index = |pigeon: u32, hole: u32| pigeon * holes + hole;
        let mut solver = Solver::new((pigeons * holes) as usize);
        for pigeon in 0..pigeons {
            solver.add_clause(
                &(0..holes)
                    .map(|hole| positive(index(pigeon, hole)))
                    .collect::<Vec<_>>(),
            );
        }
        for hole in 0..holes {
            for first in 0..pigeons {
                for second in first + 1..pigeons {
                    solver
                        .add_clause(&[negative(index(first, hole)), negative(index(second, hole))]);
                }
            }
        }
        assert_eq!(
            solver.solve(Instant::now() + Duration::from_secs(30)),
            Outcome::Unsatisfiable
        );
    }
}
