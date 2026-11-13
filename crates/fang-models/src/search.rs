// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Finite model search by increasing domain size: for each size, ground the flat clauses into propositional clauses
//! over function and predicate cells and solve them with the CDCL solver. Constants are ordered to break the symmetry
//! of renaming domain elements, separately in each inferred sort.

use crate::flatten::{Flat, FlatClause};
use crate::sat::{self, Outcome, Solver};
use std::time::Instant;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Model {
    pub size: u32,
    /// Row-major cells of every function symbol, first argument most significant.
    pub functions: Vec<Vec<u32>>,
    pub predicates: Vec<Vec<bool>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Search {
    Model(Model),
    /// Every size up to and including `last` has no model.
    Exhausted {
        last: u32,
    },
    /// The deadline or a size bound stopped the search at `size`; smaller sizes have no model.
    Stopped {
        size: u32,
        reason: &'static str,
    },
}

/// Arities of every function and predicate symbol of the clauses; inactive symbols occur in no clause and get no
/// cells.
pub struct Signature {
    pub functions: Vec<usize>,
    pub predicates: Vec<usize>,
    pub active_functions: Vec<bool>,
    pub active_predicates: Vec<bool>,
    /// The sort of each function symbol's value (`infer_sorts`); empty puts every constant in one sort.
    pub value_sorts: Vec<u32>,
}

/// Union-find over argument and value positions and clause variables.
struct Positions {
    parent: Vec<usize>,
}

impl Positions {
    fn find(&mut self, item: usize) -> usize {
        let mut root = item;
        while self.parent[root] != root {
            root = self.parent[root];
        }
        let mut current = item;
        while self.parent[current] != root {
            let next = self.parent[current];
            self.parent[current] = root;
            current = next;
        }
        root
    }

    fn join(&mut self, first: usize, second: usize) {
        let (first, second) = (self.find(first), self.find(second));
        if first != second {
            self.parent[first] = second;
        }
    }
}

/// The sort of each function symbol's value, as in Paradox: the positions one clause variable links share a sort,
/// namely a function's value and arguments, a predicate's arguments and the two sides of an equation. Every sort is
/// grounded at the same size, so a model of the sorted clauses is a model of the clauses, with element `i` of each
/// sort read as element `i`, and renaming the elements of one sort alone is a symmetry of the sorted clauses.
pub fn infer_sorts(signature: &Signature, clauses: &[FlatClause]) -> Vec<u32> {
    let mut next = 0usize;
    let mut function_start = Vec::with_capacity(signature.functions.len());
    for &arity in &signature.functions {
        function_start.push(next);
        next += 1 + arity;
    }
    let mut predicate_start = Vec::with_capacity(signature.predicates.len());
    for &arity in &signature.predicates {
        predicate_start.push(next);
        next += arity;
    }
    let total = next
        + clauses
            .iter()
            .map(|clause| clause.variables as usize)
            .sum::<usize>();
    let mut positions = Positions {
        parent: (0..total).collect(),
    };
    let mut offset = next;
    for clause in clauses {
        for literal in &clause.literals {
            match literal {
                Flat::Same { left, right, .. } => {
                    positions.join(offset + *left as usize, offset + *right as usize)
                }
                Flat::Predicate {
                    symbol, arguments, ..
                } => {
                    for (place, &argument) in arguments.iter().enumerate() {
                        positions.join(
                            predicate_start[*symbol as usize] + place,
                            offset + argument as usize,
                        );
                    }
                }
                Flat::Function {
                    symbol,
                    arguments,
                    value,
                    ..
                } => {
                    let start = function_start[*symbol as usize];
                    positions.join(start, offset + *value as usize);
                    for (place, &argument) in arguments.iter().enumerate() {
                        positions.join(start + 1 + place, offset + argument as usize);
                    }
                }
            }
        }
        offset += clause.variables as usize;
    }
    function_start
        .iter()
        .map(|&start| positions.find(start) as u32)
        .collect()
}

/// The active constants in symbol order, grouped by the sort of their value.
fn constant_groups(signature: &Signature) -> Vec<Vec<usize>> {
    let mut groups: Vec<(u32, Vec<usize>)> = Vec::new();
    for (symbol, &arity) in signature.functions.iter().enumerate() {
        if arity != 0 || !signature.active_functions[symbol] {
            continue;
        }
        let sort = signature.value_sorts.get(symbol).copied().unwrap_or(0);
        match groups.iter_mut().find(|(known, _)| *known == sort) {
            Some((_, members)) => members.push(symbol),
            None => groups.push((sort, vec![symbol])),
        }
    }
    groups.into_iter().map(|(_, members)| members).collect()
}

pub struct Options {
    /// Conflicts a size gets before it is set aside; the budget doubles on every pass.
    pub initial_conflicts: u64,
    /// Print one line per attempt on standard error.
    pub trace: bool,
    pub from: u32,
    pub to: u32,
    pub deadline: Instant,
    /// Ground and learned literals one solver may hold.
    pub literal_budget: usize,
    /// Bytes all grounded sizes together may hold.
    pub memory_bytes: u64,
}

pub fn power(base: u64, exponent: usize) -> Option<u64> {
    let mut result = 1u64;
    for _ in 0..exponent {
        result = result.checked_mul(base)?;
    }
    Some(result)
}

struct Layout {
    size: u32,
    function_base: Vec<u64>,
    predicate_base: Vec<u64>,
    variables: u64,
}

impl Layout {
    fn new(size: u32, signature: &Signature) -> Option<Layout> {
        let n = size as u64;
        let mut next = 0u64;
        let mut function_base = Vec::new();
        for (&arity, &active) in signature.functions.iter().zip(&signature.active_functions) {
            function_base.push(next);
            if active {
                next = next.checked_add(power(n, arity)?.checked_mul(n)?)?;
            }
        }
        let mut predicate_base = Vec::new();
        for (&arity, &active) in signature
            .predicates
            .iter()
            .zip(&signature.active_predicates)
        {
            predicate_base.push(next);
            if active {
                next = next.checked_add(power(n, arity)?)?;
            }
        }
        Some(Layout {
            size,
            function_base,
            predicate_base,
            variables: next,
        })
    }

    fn index(&self, arguments: &[u32], assignment: &[u32]) -> u64 {
        arguments.iter().fold(0u64, |index, &item| {
            index * self.size as u64 + assignment[item as usize] as u64
        })
    }
}

/// The largest value each constant may take under the least-number symmetry: its position among the active
/// constants of its sort. Other symbols have no ceiling.
fn ceilings(signature: &Signature) -> Vec<u32> {
    let mut ceiling = vec![u32::MAX; signature.functions.len()];
    for group in constant_groups(signature) {
        for (position, symbol) in group.into_iter().enumerate() {
            ceiling[symbol] = position as u32;
        }
    }
    ceiling
}

/// The values worth trying for each clause variable: a variable that a negated literal `c = x` binds to a constant
/// `c` ranges up to the constant's ceiling, since every larger value makes that literal true.
fn ranges(clause: &FlatClause, ceiling: &[u32], size: u32) -> Vec<u32> {
    let mut range = vec![size; clause.variables as usize];
    for literal in &clause.literals {
        if let Flat::Function {
            positive: false,
            symbol,
            arguments,
            value,
        } = literal
            && arguments.is_empty()
        {
            let bound = ceiling[*symbol as usize].saturating_add(1).min(size);
            range[*value as usize] = range[*value as usize].min(bound);
        }
    }
    range
}

fn estimate(size: u32, signature: &Signature, clauses: &[FlatClause]) -> Option<u64> {
    let n = size as u64;
    let mut total = 0u64;
    for (&arity, _) in signature
        .functions
        .iter()
        .zip(&signature.active_functions)
        .filter(|(_, active)| **active)
    {
        let cells = power(n, arity)?;
        total = total.checked_add(cells.checked_mul(n + n * n.saturating_sub(1))?)?;
    }
    let ceiling = ceilings(signature);
    for clause in clauses {
        let mut instances = 1u64;
        for range in ranges(clause, &ceiling, size) {
            instances = instances.checked_mul(range as u64)?;
        }
        total = total.checked_add(instances.checked_mul(clause.literals.len() as u64)?)?;
    }
    Some(total)
}

fn ground(
    layout: &Layout,
    signature: &Signature,
    clauses: &[FlatClause],
    solver: &mut Solver,
    deadline: Instant,
) -> Result<(), &'static str> {
    let n = layout.size;
    // Every function cell has exactly one value.
    for (symbol, &arity) in signature.functions.iter().enumerate() {
        if !signature.active_functions[symbol] {
            continue;
        }
        let cells = power(n as u64, arity).ok_or("cells")?;
        for cell in 0..cells {
            let base = layout.function_base[symbol] + cell * n as u64;
            let at_least: Vec<sat::Lit> = (0..n as u64)
                .map(|value| sat::positive((base + value) as u32))
                .collect();
            solver.add_clause(&at_least);
            for first in 0..n as u64 {
                for second in first + 1..n as u64 {
                    solver.add_clause(&[
                        sat::negative((base + first) as u32),
                        sat::negative((base + second) as u32),
                    ]);
                }
            }
        }
    }
    // Least-number symmetry over the constants of each sort in symbol order: renaming the elements of a sort maps
    // every model to one where each constant is either equal to an earlier one of its sort or the next unused
    // element. So constant number i of a sort is at most i, and value d > 0 needs an earlier constant of the sort
    // with value d - 1.
    for group in constant_groups(signature) {
        let constants: Vec<u64> = group
            .iter()
            .map(|&symbol| layout.function_base[symbol])
            .collect();
        for (position, &base) in constants.iter().enumerate() {
            for value in position as u64 + 1..n as u64 {
                solver.add_clause(&[sat::negative((base + value) as u32)]);
            }
            for value in 1..=(position as u64).min(n as u64 - 1) {
                let mut clause = vec![sat::negative((base + value) as u32)];
                clause.extend(
                    constants[..position]
                        .iter()
                        .map(|earlier| sat::positive((earlier + value - 1) as u32)),
                );
                solver.add_clause(&clause);
            }
        }
    }
    // The largest value each constant may take under that symmetry, for pruning ground instances below.
    let ceiling = ceilings(signature);
    let mut literals: Vec<sat::Lit> = Vec::new();
    for clause in clauses {
        let count = clause.variables as usize;
        let range = ranges(clause, &ceiling, n);
        if range.contains(&0) {
            continue;
        }
        let mut assignment = vec![0u32; count];
        let mut steps = 0u64;
        loop {
            steps += 1;
            if steps.is_multiple_of(65536) && Instant::now() >= deadline {
                return Err("time");
            }
            literals.clear();
            let mut satisfied = false;
            for literal in &clause.literals {
                match literal {
                    Flat::Same {
                        positive,
                        left,
                        right,
                    } => {
                        if (assignment[*left as usize] == assignment[*right as usize]) == *positive
                        {
                            satisfied = true;
                            break;
                        }
                    }
                    Flat::Predicate {
                        positive,
                        symbol,
                        arguments,
                    } => {
                        let variable = (layout.predicate_base[*symbol as usize]
                            + layout.index(arguments, &assignment))
                            as u32;
                        literals.push(if *positive {
                            sat::positive(variable)
                        } else {
                            sat::negative(variable)
                        });
                    }
                    Flat::Function {
                        positive,
                        symbol,
                        arguments,
                        value,
                    } => {
                        // A constant above its symmetry ceiling makes `c = a` false: drop the literal, or the
                        // whole instance when the literal is negated.
                        if arguments.is_empty()
                            && assignment[*value as usize] > ceiling[*symbol as usize]
                        {
                            if *positive {
                                continue;
                            }
                            satisfied = true;
                            break;
                        }
                        let variable = (layout.function_base[*symbol as usize]
                            + layout.index(arguments, &assignment) * n as u64
                            + assignment[*value as usize] as u64)
                            as u32;
                        literals.push(if *positive {
                            sat::positive(variable)
                        } else {
                            sat::negative(variable)
                        });
                    }
                }
            }
            if !satisfied && !solver.add_clause(&literals) {
                return Ok(());
            }
            // Next assignment.
            let mut position = 0;
            loop {
                if position == count {
                    break;
                }
                assignment[position] += 1;
                if assignment[position] < range[position] {
                    break;
                }
                assignment[position] = 0;
                position += 1;
            }
            if position == count {
                break;
            }
        }
    }
    Ok(())
}

fn extract(layout: &Layout, signature: &Signature, solver: &Solver) -> Model {
    let n = layout.size as u64;
    let functions = signature
        .functions
        .iter()
        .enumerate()
        .map(|(symbol, &arity)| {
            if !signature.active_functions[symbol] {
                return Vec::new();
            }
            let cells = power(n, arity).unwrap();
            (0..cells)
                .map(|cell| {
                    let base = layout.function_base[symbol] + cell * n;
                    (0..n)
                        .find(|&value| solver.model_value((base + value) as u32))
                        .unwrap_or(0) as u32
                })
                .collect()
        })
        .collect();
    let predicates = signature
        .predicates
        .iter()
        .enumerate()
        .map(|(symbol, &arity)| {
            if !signature.active_predicates[symbol] {
                return Vec::new();
            }
            let cells = power(n, arity).unwrap();
            (0..cells)
                .map(|cell| solver.model_value((layout.predicate_base[symbol] + cell) as u32))
                .collect()
        })
        .collect();
    Model {
        size: layout.size,
        functions,
        predicates,
    }
}

struct Open {
    size: u32,
    /// The grounded solver, or `None` when it was dropped to make room; it is grounded again when revisited.
    state: Option<(Layout, Solver)>,
    /// Conflicts of the next attempt; doubles after each.
    budget: u64,
}

enum Step {
    Model(Model),
    Refuted,
    Deferred,
    Stop(&'static str),
}

fn prepare(
    size: u32,
    signature: &Signature,
    clauses: &[FlatClause],
    options: &Options,
) -> Result<(Layout, Solver), &'static str> {
    let estimate = estimate(size, signature, clauses).ok_or("instance size")?;
    if estimate > options.literal_budget as u64 {
        return Err("instance size");
    }
    let layout = Layout::new(size, signature).ok_or("instance size")?;
    if layout.variables > u32::MAX as u64 / 2 {
        return Err("instance size");
    }
    let mut solver = Solver::new(layout.variables as usize);
    solver.literal_budget = options.literal_budget;
    ground(&layout, signature, clauses, &mut solver, options.deadline)?;
    Ok((layout, solver))
}

fn attempt(
    open: &mut Open,
    signature: &Signature,
    clauses: &[FlatClause],
    options: &Options,
    conflicts: u64,
) -> (Step, u64) {
    if open.state.is_none() {
        let started = Instant::now();
        match prepare(open.size, signature, clauses, options) {
            Ok(state) => open.state = Some(state),
            Err(reason) => return (Step::Stop(reason), 0),
        }
        if options.trace {
            eprintln!(
                "trace: size {} grounded in {:.3} s",
                open.size,
                started.elapsed().as_secs_f64()
            );
        }
    }
    let (layout, solver) = open.state.as_mut().unwrap();
    let started = Instant::now();
    let before = solver.conflicts;
    let outcome = solver.solve_limited(options.deadline, conflicts);
    let used = solver.conflicts - before;
    if options.trace {
        eprintln!(
            "trace: size {} budget {} outcome {:?} conflicts {} literals {} seconds {:.3}",
            open.size,
            conflicts,
            outcome,
            solver.conflicts,
            solver.stored_literals(),
            started.elapsed().as_secs_f64()
        );
    }
    let step = match outcome {
        Outcome::Satisfiable => Step::Model(extract(layout, signature, solver)),
        Outcome::Unsatisfiable => Step::Refuted,
        Outcome::Stopped if Instant::now() >= options.deadline => Step::Stop("time"),
        Outcome::Stopped => Step::Deferred,
    };
    (step, used)
}

/// Bytes held by the grounded sizes set aside.
fn held(pending: &[Open]) -> u64 {
    pending
        .iter()
        .filter_map(|open| open.state.as_ref().map(|(_, solver)| solver.memory_bytes()))
        .sum()
}

/// Planned bytes of a new size: about 16 bytes per ground literal with clause headers and watches.
fn planned(size: u32, signature: &Signature, clauses: &[FlatClause]) -> u64 {
    estimate(size, signature, clauses).map_or(u64::MAX, |literals| literals.saturating_mul(16))
}

/// Search sizes `from..=to` for a model of the flat clauses over the given signature. Each size starts with a small
/// conflict budget; a size that uses it up is set aside with a doubled budget, so a size that is hard to refute does
/// not block larger ones. Every pass opens new sizes until their first attempts have used as many conflicts as the
/// previous pass spent on the sizes set aside (at least one size is set aside per pass), then gives each size set
/// aside one more attempt. The schedule counts conflicts, not time, so a run does not depend on the machine's speed.
pub fn search(signature: &Signature, clauses: &[FlatClause], options: &Options) -> Search {
    let mut pending: Vec<Open> = Vec::new();
    let mut next = options.from.max(1);
    let mut blocked: Option<&'static str> = None;
    let initial = options.initial_conflicts.max(1);
    let mut revisit_conflicts = 0u64;
    let lowest =
        |pending: &Vec<Open>, next: u32| pending.iter().map(|open| open.size).min().unwrap_or(next);
    loop {
        let allowance = revisit_conflicts.max(initial);
        let mut opened = 0u64;
        let mut deferred = 0;
        while blocked.is_none() && next <= options.to && (deferred == 0 || opened < allowance) {
            if Instant::now() >= options.deadline {
                return Search::Stopped {
                    size: lowest(&pending, next),
                    reason: "time",
                };
            }
            let needed = planned(next, signature, clauses);
            if needed <= options.memory_bytes
                && held(&pending).saturating_add(needed) > options.memory_bytes
            {
                for open in pending.iter_mut() {
                    open.state = None;
                }
            }
            let mut open = Open {
                size: next,
                state: None,
                budget: initial,
            };
            let (step, used) = attempt(&mut open, signature, clauses, options, initial);
            opened += used;
            match step {
                Step::Model(model) => return Search::Model(model),
                Step::Refuted => next += 1,
                Step::Deferred => {
                    open.budget = initial.saturating_mul(2);
                    pending.push(open);
                    next += 1;
                    deferred += 1;
                }
                Step::Stop("time") => {
                    return Search::Stopped {
                        size: lowest(&pending, next),
                        reason: "time",
                    };
                }
                Step::Stop(reason) => blocked = Some(reason),
            }
        }
        if pending.is_empty() {
            return match blocked {
                Some(reason) => Search::Stopped { size: next, reason },
                None => Search::Exhausted { last: options.to },
            };
        }
        revisit_conflicts = 0;
        let mut index = 0;
        while index < pending.len() {
            if pending[index].state.is_none() {
                let needed = planned(pending[index].size, signature, clauses);
                if held(&pending).saturating_add(needed) > options.memory_bytes {
                    for open in pending.iter_mut() {
                        open.state = None;
                    }
                }
            }
            let budget = pending[index].budget;
            let (step, used) = attempt(&mut pending[index], signature, clauses, options, budget);
            revisit_conflicts += used;
            match step {
                Step::Model(model) => return Search::Model(model),
                Step::Refuted | Step::Stop("instance size") => {
                    pending.remove(index);
                }
                Step::Deferred => {
                    pending[index].budget = budget.saturating_mul(2);
                    index += 1;
                }
                Step::Stop(_) => {
                    return Search::Stopped {
                        size: lowest(&pending, next),
                        reason: "time",
                    };
                }
            }
        }
    }
}
