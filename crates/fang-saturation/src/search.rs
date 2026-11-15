// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Given-clause saturation (DISCOUNT loop): only active clauses simplify others, and a passive clause is
//! simplified when it is selected. Every derived clause is computed exactly as the checker computes the claimed
//! clause of its step; the search itself is untrusted and only decides which steps are tried.

use crate::clause::{
    Atom, ClauseRec, Eligibility, Filter, Id, Lit, Pos, Root, Rule, State, measure, positions,
    predicate_head, same_atom_symmetric, subterm,
};
use crate::index::{Index, Key, gather, ground_unit_key};
use crate::kbo::{Cmp, Order};
use crate::options::{Options, Selection};
use crate::stats::Stats;
use crate::subst::{Bindings, Renamer};
use crate::term::{Bank, Head, TermId};
use fang_equality_search::InvalidPrepared;
use std::cmp::Reverse;
use std::collections::hash_map::DefaultHasher;
use std::collections::{BinaryHeap, HashMap, VecDeque};
use std::hash::{Hash, Hasher};
use std::time::Instant;

#[path = "connected_search.rs"]
mod connected_search;
#[path = "ground_join_search.rs"]
mod ground_join_search;
#[path = "unit_join_search.rs"]
mod unit_join_search;

#[cfg(test)]
#[path = "count_limit_tests.rs"]
mod count_limit_tests;
#[cfg(test)]
#[path = "ground_unit_index_tests.rs"]
mod ground_unit_index_tests;
#[cfg(test)]
#[path = "orphan_tests.rs"]
mod orphan_tests;
#[cfg(test)]
#[path = "selection_tests.rs"]
mod selection_tests;
#[cfg(test)]
#[path = "storage_profile.rs"]
mod storage_profile;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stop {
    Proof(Id),
    Saturated,
    Time,
    Memory,
    GivenLimit,
    StoredLimit,
    GeneratedLimit,
}

#[derive(Clone, Copy, Debug, Default)]
pub struct Limits {
    pub deadline: Option<Instant>,
    pub memory_kib: Option<u64>,
}

/// A substitution for a certificate step: certificate variable numbers with their images.
pub type Sigma = Vec<(u32, TermId)>;

/// The age and weight queues of passive clauses.
type Queues = (VecDeque<Id>, BinaryHeap<Reverse<(u32, Id)>>);

/// Generating parents survive simplification of the conclusion. Proof parents
/// remain in Rule and must not be used to classify a replacement as an orphan.
#[derive(Clone, Copy, Debug)]
enum GeneratingParents {
    Input,
    One(Id),
    Two(Id, Id),
}

impl GeneratingParents {
    fn of_rule(rule: &Rule) -> Self {
        match *rule {
            Rule::Input { .. } => Self::Input,
            Rule::Factor { parent, .. }
            | Rule::EqRes { parent, .. }
            | Rule::EqFactor { parent, .. } => Self::One(parent),
            Rule::Resolve { left, right, .. } => Self::Two(left, right),
            Rule::Para { source, target, .. } | Rule::Demod { source, target, .. } => {
                Self::Two(source, target)
            }
        }
    }
}

/// A pattern and target for subsumption matching, and for equations the second pair.
type MatchPair = (TermId, TermId, Option<(TermId, TermId)>);

pub struct Search<'a> {
    pub(crate) bank: Bank,
    pub(crate) clauses: Vec<ClauseRec>,
    pub(crate) functions: usize,
    pub(crate) function_arities: Vec<usize>,
    pub(crate) predicate_arities: Vec<usize>,
    pub(crate) binds: Bindings,
    pub stats: Stats,
    /// The first `trace_given` given clauses, in order.
    pub given_trace: Vec<Id>,
    order: Order,
    options: &'a Options,
    active: Vec<Id>,
    units: Vec<Id>,
    age_queue: VecDeque<Id>,
    weight_queue: BinaryHeap<Reverse<(u32, Id)>>,
    passive: u64,
    /// Allocated only when orphan deletion is enabled; one entry per stored clause.
    generating_parents: Vec<GeneratingParents>,
    pick: u64,
    /// One clause per hash; a collision only lets a duplicate through.
    seen: HashMap<u64, Id>,
    limits: Limits,
    found: Option<Id>,
    interrupted: Option<Stop>,
    ground_join_tried: bool,
    unit_equality_problem: bool,
    /// Set by the memory check; the loop prunes passive before the next selection.
    pruning: bool,
    pruned_at_kib: u64,
    /// Goal flag of each input clause, by index.
    goal_inputs: Vec<bool>,
    /// SInE level of each input clause, by index.
    input_levels: Vec<u32>,
    /// Age and weight queues of the selection layers, narrowest first (`Options::layer_cutoffs`).
    layers: Vec<Queues>,
    layer_cutoffs: Vec<u32>,
    /// Running sums of the picks per layer; a pick number modulo the last sum chooses the first layer tried.
    layer_bounds: Vec<u64>,
    layer_pick: u64,
    /// Clauses admitted before the first given clause, for `inputs_first`.
    input_queue: VecDeque<Id>,
    /// Bank symbols that occur in a goal input.
    goal_symbol_set: Vec<bool>,
    index: Index,
    activations: u32,
}

fn resident_kib() -> Option<u64> {
    let text = std::fs::read_to_string("/proc/self/statm").ok()?;
    let pages: u64 = text.split_whitespace().nth(1)?.parse().ok()?;
    Some(pages * 4)
}

fn clause_hash(lits: &[Lit]) -> u64 {
    let mut hasher = DefaultHasher::new();
    lits.hash(&mut hasher);
    hasher.finish()
}

fn is_tautology(lits: &[Lit]) -> bool {
    for (index, literal) in lits.iter().enumerate() {
        if let Atom::Eq(left, right) = literal.atom
            && literal.positive
            && left == right
        {
            return true;
        }
        for other in &lits[index + 1..] {
            if literal.positive != other.positive && same_atom_symmetric(literal.atom, other.atom) {
                return true;
            }
        }
    }
    false
}

/// Validate the prepared clauses against the arity tables in the order the second release's entry checks them.
pub(crate) fn validate(
    clauses: &[fang_equality_inference_core::Clause],
    functions: &[usize],
    predicates: &[usize],
) -> Result<(), InvalidPrepared> {
    fn term(value: &fang::syntax::Term, functions: &[usize]) -> Result<(), InvalidPrepared> {
        if let fang::syntax::Term::Fun(symbol, arguments) = value {
            let arity = functions
                .get(*symbol as usize)
                .ok_or(InvalidPrepared::UnknownFunction)?;
            if *arity != arguments.len() {
                return Err(InvalidPrepared::FunctionArity);
            }
            for argument in arguments {
                term(argument, functions)?;
            }
        }
        Ok(())
    }
    for clause in clauses {
        for literal in clause {
            match &literal.atom {
                fang_equality_inference_core::Atom::Predicate(symbol, arguments) => {
                    let arity = predicates
                        .get(*symbol as usize)
                        .ok_or(InvalidPrepared::UnknownPredicate)?;
                    if *arity != arguments.len() {
                        return Err(InvalidPrepared::PredicateArity);
                    }
                    for argument in arguments {
                        term(argument, functions)?;
                    }
                }
                fang_equality_inference_core::Atom::Equal(left, right) => {
                    term(left, functions)?;
                    term(right, functions)?;
                }
            }
        }
    }
    Ok(())
}

fn mark_symbols(value: &fang::syntax::Term, set: &mut [bool]) {
    if let fang::syntax::Term::Fun(symbol, arguments) = value {
        set[*symbol as usize] = true;
        for argument in arguments {
            mark_symbols(argument, set);
        }
    }
}

fn count_symbols(value: &fang::syntax::Term, counts: &mut [u64]) {
    if let fang::syntax::Term::Fun(symbol, arguments) = value {
        counts[*symbol as usize] += 1;
        for argument in arguments {
            count_symbols(argument, counts);
        }
    }
}

impl<'a> Search<'a> {
    pub fn new(
        input: &[fang_equality_inference_core::Clause],
        functions: &[usize],
        predicates: &[usize],
        options: &'a Options,
        limits: Limits,
    ) -> Result<Self, InvalidPrepared> {
        Self::with_selection(input, functions, predicates, options, limits, None)
    }

    /// As `new`, entering only the inputs marked in `selected` (premise selection); certificates still name
    /// inputs by their index in `input`.
    pub fn with_selection(
        input: &[fang_equality_inference_core::Clause],
        functions: &[usize],
        predicates: &[usize],
        options: &'a Options,
        limits: Limits,
        selected: Option<&[bool]>,
    ) -> Result<Self, InvalidPrepared> {
        Self::with_inputs(
            input, functions, predicates, options, limits, selected, None,
        )
    }

    /// As `with_selection`, with the inputs that are goals (the negated conjecture), which goal-directed clause
    /// selection prefers; every input still enters unless `selected` leaves it out.
    pub fn with_inputs(
        input: &[fang_equality_inference_core::Clause],
        functions: &[usize],
        predicates: &[usize],
        options: &'a Options,
        limits: Limits,
        selected: Option<&[bool]>,
        goals: Option<&[bool]>,
    ) -> Result<Self, InvalidPrepared> {
        Self::with_levels(
            input, functions, predicates, options, limits, selected, goals, None,
        )
    }

    /// As `with_inputs`, with the SInE level of every input for layered clause selection.
    #[allow(clippy::too_many_arguments)]
    pub fn with_levels(
        input: &[fang_equality_inference_core::Clause],
        functions: &[usize],
        predicates: &[usize],
        options: &'a Options,
        limits: Limits,
        selected: Option<&[bool]>,
        goals: Option<&[bool]>,
        levels: Option<&[u32]>,
    ) -> Result<Self, InvalidPrepared> {
        validate(input, functions, predicates)?;
        let symbols = functions.len() + predicates.len();
        let mut counts = vec![0u64; symbols];
        for clause in input {
            for literal in clause {
                match &literal.atom {
                    fang_equality_inference_core::Atom::Predicate(symbol, arguments) => {
                        counts[functions.len() + *symbol as usize] += 1;
                        for argument in arguments {
                            count_symbols(argument, &mut counts);
                        }
                    }
                    fang_equality_inference_core::Atom::Equal(left, right) => {
                        count_symbols(left, &mut counts);
                        count_symbols(right, &mut counts);
                    }
                }
            }
        }
        let arities: Vec<usize> = functions.iter().chain(predicates).copied().collect();
        let order = Order::new(&arities, &counts, functions.len(), options.precedence)
            .with_kind(options.term_order)
            .with_weights(crate::weights::Weights::new(
                &arities,
                &counts,
                options.kbo_weights,
            ));
        let mut search = Search {
            bank: Bank::new(),
            clauses: Vec::new(),
            functions: functions.len(),
            function_arities: functions.to_vec(),
            predicate_arities: predicates.to_vec(),
            binds: Bindings::new(),
            stats: Stats::default(),
            given_trace: Vec::new(),
            order,
            options,
            active: Vec::new(),
            units: Vec::new(),
            age_queue: VecDeque::new(),
            weight_queue: BinaryHeap::new(),
            passive: 0,
            generating_parents: Vec::new(),
            pick: 0,
            seen: HashMap::new(),
            limits,
            found: None,
            interrupted: None,
            ground_join_tried: false,
            unit_equality_problem: input.iter().all(|clause| {
                clause.len() == 1
                    && matches!(
                        clause[0].atom,
                        fang_equality_inference_core::Atom::Equal(..)
                    )
            }),
            pruning: false,
            pruned_at_kib: 0,
            goal_inputs: goals.map(<[bool]>::to_vec).unwrap_or_default(),
            input_levels: levels.map(<[u32]>::to_vec).unwrap_or_default(),
            layers: options
                .layer_cutoffs()
                .iter()
                .map(|_| Queues::default())
                .collect(),
            layer_cutoffs: options.layer_cutoffs(),
            layer_bounds: options
                .layer_picks()
                .iter()
                .scan(0u64, |sum, &picks| {
                    *sum += picks as u64;
                    Some(*sum)
                })
                .collect(),
            layer_pick: 0,
            input_queue: VecDeque::new(),
            goal_symbol_set: Vec::new(),
            index: Index::default(),
            activations: 0,
        };
        if let Some(goals) = goals {
            let mut set = vec![false; functions.len() + predicates.len()];
            for (clause, _) in input.iter().zip(goals).filter(|(_, goal)| **goal) {
                for literal in clause {
                    match &literal.atom {
                        fang_equality_inference_core::Atom::Predicate(symbol, arguments) => {
                            set[functions.len() + *symbol as usize] = true;
                            for argument in arguments {
                                mark_symbols(argument, &mut set);
                            }
                        }
                        fang_equality_inference_core::Atom::Equal(left, right) => {
                            mark_symbols(left, &mut set);
                            mark_symbols(right, &mut set);
                        }
                    }
                }
            }
            search.goal_symbol_set = set;
        }
        for (index, clause) in input.iter().enumerate() {
            search.stats.input_clauses += 1;
            if selected.is_some_and(|keep| !keep[index]) {
                search.stats.inputs_unselected += 1;
                continue;
            }
            let mut original: Vec<u32> = Vec::new();
            let mut lits = Vec::with_capacity(clause.len());
            for literal in clause {
                let mut rename =
                    |variable: u32| match original.iter().position(|&seen| seen == variable) {
                        Some(position) => position as u32,
                        None => {
                            original.push(variable);
                            (original.len() - 1) as u32
                        }
                    };
                let atom = match &literal.atom {
                    fang_equality_inference_core::Atom::Predicate(symbol, arguments) => {
                        let mut children = Vec::with_capacity(arguments.len());
                        for argument in arguments {
                            children.push(search.bank.import(argument, &mut rename));
                        }
                        Atom::Pred(
                            search
                                .bank
                                .app((functions.len() + *symbol as usize) as u32, &children),
                        )
                    }
                    fang_equality_inference_core::Atom::Equal(left, right) => {
                        let left = search.bank.import(left, &mut rename);
                        let right = search.bank.import(right, &mut rename);
                        Atom::Eq(left, right)
                    }
                };
                lits.push(Lit {
                    positive: literal.positive,
                    atom,
                });
            }
            let (_, depth, _) = measure(&search.bank, &lits);
            // Binary steps rename input variable x to 2x or 2x+1, which must stay a u32 in the reconstruction.
            if depth > options.max_depth
                || lits.len() > options.max_literals
                || original.iter().any(|&v| v >= 1 << 30)
            {
                search.stats.inputs_dropped += 1;
                continue;
            }
            if options.tautologies && is_tautology(&lits) {
                search.stats.tautologies += 1;
                continue;
            }
            let Some(id) = search.try_push(lits, Rule::Input { index, original }) else {
                break;
            };
            if search.admit(id) {
                break;
            }
            if search.interrupted.is_some() {
                break;
            }
        }
        Ok(search)
    }

    fn try_push(&mut self, lits: Vec<Lit>, rule: Rule) -> Option<Id> {
        if self.interrupted.is_some() {
            return None;
        }
        if self
            .options
            .max_stored
            .is_some_and(|limit| self.clauses.len() as u64 >= limit)
        {
            self.interrupted = Some(Stop::StoredLimit);
            return None;
        }
        let (weight, depth, vars) = measure(&self.bank, &lits);
        let goal = match &rule {
            Rule::Input { index, .. } => self.goal_inputs.get(*index).copied().unwrap_or(false),
            _ => rule
                .parents()
                .iter()
                .any(|&parent| self.clauses[parent as usize].goal),
        };
        let level = if goal {
            0
        } else {
            match &rule {
                Rule::Input { index, .. } => self.input_levels.get(*index).copied().unwrap_or(0),
                _ => rule
                    .parents()
                    .iter()
                    .map(|&parent| self.clauses[parent as usize].level)
                    .min()
                    .unwrap_or(0),
            }
        };
        let id = self.clauses.len() as Id;
        if self.options.orphan_deletion {
            self.generating_parents
                .push(GeneratingParents::of_rule(&rule));
        }
        self.clauses.push(ClauseRec {
            lits: lits.into_boxed_slice(),
            rule,
            weight,
            depth,
            vars,
            state: State::New,
            eligibility: None,
            filter: None,
            activation: 0,
            goal,
            level,
        });
        self.stats.clauses_stored += 1;
        Some(id)
    }

    #[cfg(test)]
    fn push(&mut self, lits: Vec<Lit>, rule: Rule) -> Id {
        self.try_push(lits, rule).expect("test fixture storage")
    }

    fn generating_parents(&self, id: Id) -> Option<GeneratingParents> {
        self.options
            .orphan_deletion
            .then(|| self.generating_parents[id as usize])
    }

    fn push_simplified(&mut self, lits: Vec<Lit>, rule: Rule, target: Id) -> Option<Id> {
        let parents = self.generating_parents(target);
        let id = self.try_push(lits, rule)?;
        if let Some(parents) = parents {
            self.generating_parents[id as usize] = parents;
        }
        Some(id)
    }

    /// The key of the weight queue: symbol count (goal symbols at half when `goal_symbols` is on), plus the
    /// literal and depth penalties, times `nongoal_weight` percent for a clause with no goal ancestor.
    fn selection_weight(&self, id: Id) -> u32 {
        let record = &self.clauses[id as usize];
        let options = self.options;
        let mut weight = crate::critical_score::weight(
            &self.bank,
            &record.lits,
            record.weight,
            options.critical_pair_score,
        );
        if options.goal_symbols && !self.goal_symbol_set.is_empty() {
            let mut goal_occurrences = 0u64;
            for literal in &record.lits {
                let (left, right) = crate::clause::atom_terms(literal.atom);
                for term in std::iter::once(left).chain(right) {
                    goal_occurrences += self.count_goal_symbols(term);
                }
            }
            weight = weight.saturating_mul(2).saturating_sub(goal_occurrences);
        }
        weight += options.literal_weight as u64 * record.lits.len() as u64
            + options.depth_weight as u64 * record.depth as u64;
        if !record.goal && !self.goal_inputs.is_empty() {
            weight = weight.saturating_mul(options.nongoal_weight as u64) / 100;
        }
        weight.min(u32::MAX as u64) as u32
    }

    fn count_goal_symbols(&self, term: TermId) -> u64 {
        match self.bank.head(term) {
            Head::Var(_) => 0,
            Head::Sym(symbol) => {
                let own = self
                    .goal_symbol_set
                    .get(symbol as usize)
                    .copied()
                    .unwrap_or(false) as u64;
                own + self
                    .bank
                    .args(term)
                    .iter()
                    .map(|&child| self.count_goal_symbols(child))
                    .sum::<u64>()
            }
        }
    }

    fn lits(&self, id: Id) -> Vec<Lit> {
        self.clauses[id as usize].lits.to_vec()
    }

    pub(crate) fn certificate_var(&self, id: Id, variable: u32) -> u32 {
        match &self.clauses[id as usize].rule {
            Rule::Input { original, .. } => original[variable as usize],
            _ => variable,
        }
    }

    // ---- Conclusions: one function for search and for certificate extraction ----

    fn instance(&mut self, literal: Lit, side: u8, renamer: &mut Renamer) -> Lit {
        let atom = match literal.atom {
            Atom::Pred(term) => Atom::Pred(self.binds.apply(&mut self.bank, term, side, renamer)),
            Atom::Eq(left, right) => {
                let left = self.binds.apply(&mut self.bank, left, side, renamer);
                let right = self.binds.apply(&mut self.bank, right, side, renamer);
                Atom::Eq(left, right)
            }
        };
        Lit {
            positive: literal.positive,
            atom,
        }
    }

    /// The side-1 instance of `term` with the subterm at `path` replaced by the side-0 instance of `to`.
    fn replaced(
        &mut self,
        term: TermId,
        path: &[u16],
        to: TermId,
        renamer: &mut Renamer,
    ) -> TermId {
        if path.is_empty() {
            return self.binds.apply(&mut self.bank, to, 0, renamer);
        }
        let Head::Sym(symbol) = self.bank.head(term) else {
            unreachable!("paramodulation positions are non-variable");
        };
        let children = self.bank.args(term).to_vec();
        let mut built = Vec::with_capacity(children.len());
        for (index, child) in children.into_iter().enumerate() {
            if index == path[0] as usize {
                built.push(self.replaced(child, &path[1..], to, renamer));
            } else {
                built.push(self.binds.apply(&mut self.bank, child, 1, renamer));
            }
        }
        self.bank.app(symbol, &built)
    }

    fn replaced_literal(
        &mut self,
        literal: Lit,
        pos: &Pos,
        to: TermId,
        renamer: &mut Renamer,
    ) -> Lit {
        let atom = match (literal.atom, pos.root) {
            (Atom::Pred(term), Root::Argument(argument)) => {
                let Head::Sym(symbol) = self.bank.head(term) else {
                    unreachable!("predicate atom")
                };
                let children = self.bank.args(term).to_vec();
                let mut built = Vec::with_capacity(children.len());
                for (index, child) in children.into_iter().enumerate() {
                    if index == argument as usize {
                        built.push(self.replaced(child, &pos.path, to, renamer));
                    } else {
                        built.push(self.binds.apply(&mut self.bank, child, 1, renamer));
                    }
                }
                Atom::Pred(self.bank.app(symbol, &built))
            }
            (Atom::Eq(left, right), Root::Left) => {
                let left = self.replaced(left, &pos.path, to, renamer);
                let right = self.binds.apply(&mut self.bank, right, 1, renamer);
                Atom::Eq(left, right)
            }
            (Atom::Eq(left, right), Root::Right) => {
                let left = self.binds.apply(&mut self.bank, left, 1, renamer);
                let right = self.replaced(right, &pos.path, to, renamer);
                Atom::Eq(left, right)
            }
            _ => unreachable!("position root matches its atom"),
        };
        Lit {
            positive: literal.positive,
            atom,
        }
    }

    fn equation_sides(&self, source: Id, pivot: u16, reverse: bool) -> (TermId, TermId) {
        let Atom::Eq(left, right) = self.clauses[source as usize].lits[pivot as usize].atom else {
            unreachable!("paramodulation source is an equation");
        };
        if reverse {
            (right, left)
        } else {
            (left, right)
        }
    }

    /// The conclusion of `rule` under the current bindings, with variables numbered by first occurrence, and, on
    /// request, the step's certificate substitution over every variable of its parents.
    pub(crate) fn conclude(&mut self, rule: &Rule, want_sigma: bool) -> (Vec<Lit>, Option<Sigma>) {
        let mut renamer = Renamer::new();
        let mut out = Vec::new();
        match rule {
            Rule::Input { .. } => unreachable!("inputs have no conclusion"),
            Rule::Factor {
                parent,
                second: skip,
                ..
            }
            | Rule::EqRes {
                parent,
                pivot: skip,
            } => {
                for (index, literal) in self.lits(*parent).into_iter().enumerate() {
                    if index != *skip as usize {
                        out.push(self.instance(literal, 0, &mut renamer));
                    }
                }
            }
            Rule::EqFactor {
                parent,
                first,
                second,
            } => {
                let lits = self.lits(*parent);
                let (Atom::Eq(_, right), Atom::Eq(_, other)) =
                    (lits[*first as usize].atom, lits[*second as usize].atom)
                else {
                    unreachable!("equality factoring on equations");
                };
                let right = self.binds.apply(&mut self.bank, right, 0, &mut renamer);
                let other = self.binds.apply(&mut self.bank, other, 0, &mut renamer);
                out.push(Lit {
                    positive: false,
                    atom: Atom::Eq(right, other),
                });
                for (index, literal) in lits.into_iter().enumerate() {
                    if index != *first as usize {
                        out.push(self.instance(literal, 0, &mut renamer));
                    }
                }
            }
            Rule::Resolve {
                left,
                left_lit,
                right,
                right_lit,
            } => {
                for (index, literal) in self.lits(*left).into_iter().enumerate() {
                    if index != *left_lit as usize {
                        out.push(self.instance(literal, 0, &mut renamer));
                    }
                }
                for (index, literal) in self.lits(*right).into_iter().enumerate() {
                    if index != *right_lit as usize {
                        out.push(self.instance(literal, 1, &mut renamer));
                    }
                }
            }
            Rule::Para {
                source,
                pivot,
                reverse,
                target,
                pos,
            }
            | Rule::Demod {
                source,
                reverse,
                target,
                pos,
                pivot,
            } => {
                let (_, to) = self.equation_sides(*source, *pivot, *reverse);
                for (index, literal) in self.lits(*source).into_iter().enumerate() {
                    if index != *pivot as usize {
                        out.push(self.instance(literal, 0, &mut renamer));
                    }
                }
                for (index, literal) in self.lits(*target).into_iter().enumerate() {
                    if index == pos.literal as usize {
                        out.push(self.replaced_literal(literal, pos, to, &mut renamer));
                    } else {
                        out.push(self.instance(literal, 1, &mut renamer));
                    }
                }
            }
        }
        if !want_sigma {
            return (out, None);
        }
        let mut sigma = Vec::new();
        let parents: Vec<(Id, u8)> = match rule {
            Rule::Factor { parent, .. }
            | Rule::EqRes { parent, .. }
            | Rule::EqFactor { parent, .. } => vec![(*parent, 0)],
            Rule::Resolve { left, right, .. } => vec![(*left, 0), (*right, 1)],
            Rule::Para { source, target, .. } | Rule::Demod { source, target, .. } => {
                vec![(*source, 0), (*target, 1)]
            }
            Rule::Input { .. } => vec![],
        };
        let binary = parents.len() == 2;
        for (parent, side) in parents {
            for variable in 0..self.clauses[parent as usize].vars {
                let number = self.certificate_var(parent, variable);
                let key = if binary {
                    2 * number + side as u32
                } else {
                    number
                };
                let term = self.bank.var(variable);
                let image = self.binds.apply(&mut self.bank, term, side, &mut renamer);
                sigma.push((key, image));
            }
        }
        sigma.sort_by_key(|&(key, _)| key);
        (out, Some(sigma))
    }

    /// Redo the unification or match of `rule` from empty bindings, exactly as the search did.
    pub(crate) fn bind_rule(&mut self, rule: &Rule) -> bool {
        self.binds.clear();
        match rule {
            Rule::Input { .. } => true,
            Rule::Factor {
                parent,
                first,
                second,
            } => {
                let lits = self.lits(*parent);
                self.unify_atoms(
                    lits[*first as usize].atom,
                    0,
                    lits[*second as usize].atom,
                    0,
                )
            }
            Rule::EqRes { parent, pivot } => {
                let Atom::Eq(left, right) =
                    self.clauses[*parent as usize].lits[*pivot as usize].atom
                else {
                    return false;
                };
                self.binds.unify(&self.bank, left, 0, right, 0)
            }
            Rule::EqFactor {
                parent,
                first,
                second,
            } => {
                let lits = self.lits(*parent);
                let (Atom::Eq(left, _), Atom::Eq(other, _)) =
                    (lits[*first as usize].atom, lits[*second as usize].atom)
                else {
                    return false;
                };
                self.binds.unify(&self.bank, left, 0, other, 0)
            }
            Rule::Resolve {
                left,
                left_lit,
                right,
                right_lit,
            } => {
                let a = self.clauses[*left as usize].lits[*left_lit as usize].atom;
                let b = self.clauses[*right as usize].lits[*right_lit as usize].atom;
                self.unify_atoms(a, 0, b, 1)
            }
            Rule::Para {
                source,
                pivot,
                reverse,
                target,
                pos,
            } => {
                let (from, _) = self.equation_sides(*source, *pivot, *reverse);
                let literal = self.clauses[*target as usize].lits[pos.literal as usize];
                match subterm(&self.bank, literal, pos.root, &pos.path) {
                    Some(at) => self.binds.unify(&self.bank, from, 0, at, 1),
                    None => false,
                }
            }
            Rule::Demod {
                source,
                pivot,
                reverse,
                target,
                pos,
            } => {
                let (from, _) = self.equation_sides(*source, *pivot, *reverse);
                let literal = self.clauses[*target as usize].lits[pos.literal as usize];
                match subterm(&self.bank, literal, pos.root, &pos.path) {
                    Some(at) => self.binds.matches(&self.bank, from, at),
                    None => false,
                }
            }
        }
    }

    /// Positional unification of two atoms; equations are not tried the other way round.
    fn unify_atoms(&mut self, a: Atom, side_a: u8, b: Atom, side_b: u8) -> bool {
        match (a, b) {
            (Atom::Pred(x), Atom::Pred(y)) => self.binds.unify(&self.bank, x, side_a, y, side_b),
            (Atom::Eq(s, t), Atom::Eq(u, v)) => {
                let mark = self.binds.mark();
                if self.binds.unify(&self.bank, s, side_a, u, side_b)
                    && self.binds.unify(&self.bank, t, side_a, v, side_b)
                {
                    true
                } else {
                    self.binds.undo(mark);
                    false
                }
            }
            _ => false,
        }
    }

    fn compatible(&self, a: Atom, b: Atom) -> bool {
        match (a, b) {
            (Atom::Pred(_), Atom::Pred(_)) => {
                predicate_head(&self.bank, a) == predicate_head(&self.bank, b)
            }
            (Atom::Eq(..), Atom::Eq(..)) => true,
            _ => false,
        }
    }

    // ---- Admission of new clauses ----

    /// A new conclusion: bounds, tautology and duplicate tests, then storage and admission to passive.
    /// Returns true when the empty clause is found.
    fn derived(&mut self, lits: Vec<Lit>, rule: Rule) -> bool {
        self.derived_with_parents(lits, rule, None)
    }

    fn derived_with_parents(
        &mut self,
        lits: Vec<Lit>,
        rule: Rule,
        parents: Option<GeneratingParents>,
    ) -> bool {
        if self.interrupted.is_some() {
            return false;
        }
        if self
            .options
            .max_generated
            .is_some_and(|limit| self.stats.generated >= limit)
        {
            self.interrupted = Some(Stop::GeneratedLimit);
            return false;
        }
        self.stats.generated += 1;
        if lits.len() > self.options.max_literals {
            self.stats.dropped_literals += 1;
            return false;
        }
        let (weight, depth, _) = measure(&self.bank, &lits);
        if depth > self.options.max_depth {
            self.stats.dropped_depth += 1;
            return false;
        }
        if self
            .options
            .max_weight
            .is_some_and(|maximum| weight > maximum)
        {
            self.stats.dropped_weight += 1;
            return false;
        }
        if self.options.tautologies && is_tautology(&lits) {
            self.stats.tautologies += 1;
            return false;
        }
        if self.options.duplicates && self.is_duplicate(&lits) {
            self.stats.duplicates += 1;
            return false;
        }
        let Some(id) = self.try_push(lits, rule) else {
            return false;
        };
        if let Some(parents) = parents {
            self.generating_parents[id as usize] = parents;
        }
        self.admit(id)
    }

    fn is_duplicate(&self, lits: &[Lit]) -> bool {
        self.seen
            .get(&clause_hash(lits))
            .is_some_and(|&id| self.clauses[id as usize].lits.as_ref() == lits)
    }

    fn admit(&mut self, id: Id) -> bool {
        if self.interrupted.is_some() {
            return false;
        }
        if self.connected_redundant(id) {
            self.clauses[id as usize].state = State::Deleted;
            self.stats.connected_redundant += 1;
            return false;
        }
        if self.interrupted.is_some() {
            return false;
        }
        let mut current = id;
        if self.options.cleanup {
            while let Some(next) = self.cleanup_step(current) {
                self.clauses[current as usize].state = State::Deleted;
                current = next;
            }
        }
        if self.options.forward_demodulation && self.options.demodulate_new {
            let mut steps = 0;
            while steps < self.options.max_rewrites {
                let Some((lits, rule)) = self.rewrite_once(current, None) else {
                    break;
                };
                self.clauses[current as usize].state = State::Deleted;
                let Some(next) = self.push_simplified(lits, rule, current) else {
                    return false;
                };
                current = next;
                self.stats.forward_rewrites += 1;
                steps += 1;
            }
            if self.options.tautologies && is_tautology(&self.clauses[current as usize].lits) {
                self.stats.tautologies += 1;
                self.clauses[current as usize].state = State::Deleted;
                return false;
            }
        }
        // Simplify a new clause by the active set before it enters passive, as an Otter loop does.
        if self.options.simplify_new {
            let mut steps = 0;
            while steps < self.options.max_rewrites
                && !self.clauses[current as usize].lits.is_empty()
            {
                steps += 1;
                if self.options.cleanup
                    && let Some(next) = self.cleanup_step(current)
                {
                    self.clauses[current as usize].state = State::Deleted;
                    current = next;
                    continue;
                }
                if self.options.forward_demodulation
                    && let Some((lits, rule)) = self.rewrite_once(current, None)
                {
                    self.clauses[current as usize].state = State::Deleted;
                    let Some(next) = self.push_simplified(lits, rule, current) else {
                        return false;
                    };
                    current = next;
                    self.stats.forward_rewrites += 1;
                    continue;
                }
                if self.options.subsumption_resolution
                    && let Some(next) = self.subsumption_resolution(current)
                {
                    self.clauses[current as usize].state = State::Deleted;
                    current = next;
                    self.stats.subsumption_resolutions += 1;
                    continue;
                }
                break;
            }
            let lits = &self.clauses[current as usize].lits;
            if self.options.tautologies && is_tautology(lits) {
                self.stats.tautologies += 1;
                self.clauses[current as usize].state = State::Deleted;
                return false;
            }
            if self.options.forward_subsumption && !lits.is_empty() {
                for other in self.subsumer_candidates(current) {
                    if self.subsumes(other, current) {
                        self.stats.forward_subsumed += 1;
                        self.clauses[current as usize].state = State::Deleted;
                        return false;
                    }
                }
            }
        }
        if self.interrupted.is_some() {
            return false;
        }
        if self.unit_join_redundant(id, current) {
            self.clauses[current as usize].state = State::Deleted;
            self.stats.unit_join_redundant += 1;
            return false;
        }
        if self.interrupted.is_some() {
            return false;
        }
        if self.clauses[current as usize].lits.is_empty() {
            self.found = Some(current);
            return true;
        }
        if self
            .options
            .max_passive
            .is_some_and(|limit| self.passive >= limit)
        {
            // This candidate has not been admitted or used as a parent. Keep
            // proof records for its ancestors and release only its literals.
            self.clauses[current as usize].state = State::Deleted;
            self.clauses[current as usize].lits = Box::default();
            self.stats.passive_limit_dropped += 1;
            self.stats.pruned += 1;
            return false;
        }
        if self.options.duplicates {
            if current != id && self.is_duplicate(&self.clauses[current as usize].lits) {
                self.stats.duplicates += 1;
                self.clauses[current as usize].state = State::Deleted;
                return false;
            }
            let hash = clause_hash(&self.clauses[current as usize].lits);
            self.seen.entry(hash).or_insert(current);
        }
        let record = &mut self.clauses[current as usize];
        record.state = State::Passive;
        let weight = self.selection_weight(current);
        self.age_queue.push_back(current);
        self.weight_queue.push(Reverse((weight, current)));
        if self.options.inputs_first && self.stats.given == 0 {
            self.input_queue.push_back(current);
        }
        if !self.layers.is_empty() {
            let record = &self.clauses[current as usize];
            let feature = if self.options.sine_layer {
                record.level
            } else {
                record
                    .lits
                    .iter()
                    .filter(|literal| literal.positive)
                    .count() as u32
            };
            for layer in 0..self.layers.len() {
                if feature <= self.layer_cutoffs[layer] {
                    self.layers[layer].0.push_back(current);
                    self.layers[layer].1.push(Reverse((weight, current)));
                }
            }
        }
        self.passive += 1;
        self.stats.passive_added += 1;
        self.stats.passive_peak = self.stats.passive_peak.max(self.passive);
        false
    }

    /// One checked renaming step: drop a literal t != t, or the second of two identical literals.
    fn cleanup_step(&mut self, id: Id) -> Option<Id> {
        let lits = self.lits(id);
        let mut rule = None;
        for (index, literal) in lits.iter().enumerate() {
            if let Atom::Eq(left, right) = literal.atom
                && !literal.positive
                && left == right
            {
                rule = Some(Rule::EqRes {
                    parent: id,
                    pivot: index as u16,
                });
                break;
            }
        }
        // Destructive equality resolution: a clause with x != t, x not in t, is equivalent to its resolvent.
        if rule.is_none() && self.options.der {
            for (index, literal) in lits.iter().enumerate() {
                let Atom::Eq(left, right) = literal.atom else {
                    continue;
                };
                if literal.positive {
                    continue;
                }
                let solvable = |variable: TermId, other: TermId| {
                    self.bank
                        .as_var(variable)
                        .is_some_and(|x| !self.bank.contains_var(other, x))
                };
                if solvable(left, right) || solvable(right, left) {
                    rule = Some(Rule::EqRes {
                        parent: id,
                        pivot: index as u16,
                    });
                    break;
                }
            }
        }
        if rule.is_none() {
            'pairs: for first in 0..lits.len() {
                for second in first + 1..lits.len() {
                    if lits[first] == lits[second] {
                        rule = Some(Rule::Factor {
                            parent: id,
                            first: first as u16,
                            second: second as u16,
                        });
                        break 'pairs;
                    }
                }
            }
        }
        let rule = rule?;
        // The renaming steps need no unifier; destructive equality resolution binds its variable.
        if !self.bind_rule(&rule) {
            self.binds.clear();
            return None;
        }
        let (out, _) = self.conclude(&rule, false);
        self.binds.clear();
        self.stats.cleanup_steps += 1;
        self.push_simplified(out, rule, id)
    }

    // ---- Simplification by the active set ----

    fn delete(&mut self, id: Id) {
        let previous = self.clauses[id as usize].state;
        self.clauses[id as usize].state = State::Deleted;
        if previous == State::Active {
            self.active.retain(|&other| other != id);
            self.units.retain(|&other| other != id);
        }
    }

    fn is_unit_equation(&self, id: Id) -> bool {
        let lits = &self.clauses[id as usize].lits;
        lits.len() == 1 && lits[0].positive && matches!(lits[0].atom, Atom::Eq(..))
    }

    /// One demodulation step on `target` by an active unit equation (or only by `only`), as a conclusion and rule.
    fn rewrite_once(&mut self, target: Id, only: Option<Id>) -> Option<(Vec<Lit>, Rule)> {
        let lits = self.lits(target);
        if only.is_none() && self.units.is_empty() {
            return None;
        }
        for (index, literal) in lits.iter().enumerate() {
            for (pos, at) in positions(&self.bank, index as u16, *literal) {
                // The (unit, side) pairs in the order the linear scan tries them; the index keeps only those whose
                // side has the subterm's top symbol, the others cannot match.
                let tried: Vec<(Id, bool)> = match (only, self.options.index, self.bank.head(at)) {
                    (Some(unit), _, _) => vec![(unit, false), (unit, true)],
                    (None, true, Head::Sym(symbol)) => self
                        .index
                        .unit_from
                        .get(&symbol)
                        .map(|list| {
                            list.iter()
                                .copied()
                                .filter(|&(unit, _)| {
                                    self.clauses[unit as usize].state == State::Active
                                })
                                .collect()
                        })
                        .unwrap_or_default(),
                    (None, true, Head::Var(_)) => vec![],
                    (None, false, _) => self
                        .units
                        .iter()
                        .flat_map(|&unit| [(unit, false), (unit, true)])
                        .collect(),
                };
                for (unit, reverse) in tried {
                    if unit == target {
                        continue;
                    }
                    {
                        let (from, to) = self.equation_sides(unit, 0, reverse);
                        if self.bank.as_var(from).is_some() {
                            continue;
                        }
                        let oriented = self.order.compare(&self.bank, from, to);
                        if matches!(oriented, Cmp::Less | Cmp::Equal) {
                            continue;
                        }
                        self.binds.clear();
                        if !self.binds.matches(&self.bank, from, at)
                            || !self.binds.side0_bound(&self.bank, to)
                        {
                            self.binds.clear();
                            continue;
                        }
                        if oriented == Cmp::Incomparable {
                            let mut renamer = Renamer::new();
                            let from_instance =
                                self.binds.apply(&mut self.bank, from, 0, &mut renamer);
                            let to_instance = self.binds.apply(&mut self.bank, to, 0, &mut renamer);
                            if self.order.compare(&self.bank, from_instance, to_instance)
                                != Cmp::Greater
                            {
                                self.binds.clear();
                                continue;
                            }
                        }
                        let rule = Rule::Demod {
                            source: unit,
                            pivot: 0,
                            reverse,
                            target,
                            pos: pos.clone(),
                        };
                        let (out, _) = self.conclude(&rule, false);
                        self.binds.clear();
                        return Some((out, rule));
                    }
                }
            }
        }
        None
    }

    /// Multiset subsumption: some instance of `general` maps its literals to distinct literals of `special`.
    fn subsumes(&mut self, general: Id, special: Id) -> bool {
        let small = self.lits(general);
        let large = self.lits(special);
        if small.len() > large.len() {
            return false;
        }
        for literal in &small {
            if !large.iter().any(|other| {
                other.positive == literal.positive && self.compatible(literal.atom, other.atom)
            }) {
                return false;
            }
        }
        self.binds.clear();
        let mut used = vec![false; large.len()];
        let mut budget = self.options.subsumption_budget;
        let found = self.subsume_from(&small, &large, 0, &mut used, &mut budget);
        self.binds.clear();
        found
    }

    fn subsume_from(
        &mut self,
        small: &[Lit],
        large: &[Lit],
        index: usize,
        used: &mut [bool],
        budget: &mut u32,
    ) -> bool {
        if index == small.len() {
            return true;
        }
        let literal = small[index];
        for (position, other) in large.iter().enumerate() {
            if used[position] || other.positive != literal.positive {
                continue;
            }
            let pairs: Vec<MatchPair> = match (literal.atom, other.atom) {
                (Atom::Pred(a), Atom::Pred(b)) => vec![(a, b, None)],
                (Atom::Eq(s, t), Atom::Eq(u, v)) => {
                    vec![(s, u, Some((t, v))), (s, v, Some((t, u)))]
                }
                _ => continue,
            };
            for (pattern, target, second) in pairs {
                if *budget == 0 {
                    return false;
                }
                *budget -= 1;
                let mark = self.binds.mark();
                let matched = self.binds.matches(&self.bank, pattern, target)
                    && second.is_none_or(|(p, t)| self.binds.matches(&self.bank, p, t));
                if matched {
                    used[position] = true;
                    if self.subsume_from(small, large, index + 1, used, budget) {
                        return true;
                    }
                    used[position] = false;
                }
                self.binds.undo(mark);
            }
        }
        false
    }

    /// Positional one-sided match of `pattern` (side 0) onto `target` (side 1).
    fn match_atom(&mut self, pattern: Atom, target: Atom) -> bool {
        match (pattern, target) {
            (Atom::Pred(p), Atom::Pred(t)) => self.binds.matches(&self.bank, p, t),
            (Atom::Eq(s, t), Atom::Eq(u, v)) => {
                let mark = self.binds.mark();
                if self.binds.matches(&self.bank, s, u) && self.binds.matches(&self.bank, t, v) {
                    true
                } else {
                    self.binds.undo(mark);
                    false
                }
            }
            _ => false,
        }
    }

    /// Whether every literal of `rest` (side 0) matches, positionally, some literal of `target` with the same
    /// sign, under one substitution that extends the current bindings.
    fn match_into(&mut self, rest: &[Lit], target: &[Lit], budget: &mut u32) -> bool {
        let Some((first, others)) = rest.split_first() else {
            return true;
        };
        for literal in target {
            if literal.positive != first.positive {
                continue;
            }
            if *budget == 0 {
                return false;
            }
            *budget -= 1;
            let mark = self.binds.mark();
            if self.match_atom(first.atom, literal.atom) && self.match_into(others, target, budget)
            {
                return true;
            }
            self.binds.undo(mark);
        }
        false
    }

    /// Forward subsumption resolution by an active clause D = L' | E of the clause C = L | R, when L'σ is the
    /// complement of L and every literal of Eσ is in R. Returns R as a new clause.
    fn subsumption_resolution(&mut self, target: Id) -> Option<Id> {
        let c = self.lits(target);
        // With the index: D's one indexed key is one of its literals, which matches a literal of C either with the
        // same key or, for the resolved literal, with the complementary one.
        let candidates = if self.options.index {
            let keys = self.keys(target);
            let mut found = Vec::new();
            gather(&self.index.subsume_one, keys.iter().copied(), &mut found);
            gather(
                &self.index.subsume_one,
                keys.iter().map(|&(symbol, positive)| (symbol, !positive)),
                &mut found,
            );
            gather(
                &self.index.ground_units,
                c.iter().map(|literal| {
                    ground_unit_key(Lit {
                        positive: !literal.positive,
                        atom: literal.atom,
                    })
                }),
                &mut found,
            );
            self.in_activation_order(found)
        } else {
            self.active.clone()
        };
        for other in candidates {
            let d = self.lits(other);
            if other == target || d.len() > c.len() {
                continue;
            }
            if !d
                .iter()
                .all(|ld| c.iter().any(|lc| self.compatible(ld.atom, lc.atom)))
            {
                continue;
            }
            for (j, ld) in d.iter().enumerate() {
                let rest: Vec<Lit> = d
                    .iter()
                    .enumerate()
                    .filter(|(k, _)| *k != j)
                    .map(|(_, l)| *l)
                    .collect();
                for (i, lc) in c.iter().enumerate() {
                    if ld.positive == lc.positive || !self.compatible(ld.atom, lc.atom) {
                        continue;
                    }
                    let remaining: Vec<Lit> = c
                        .iter()
                        .enumerate()
                        .filter(|(k, _)| *k != i)
                        .map(|(_, l)| *l)
                        .collect();
                    self.binds.clear();
                    let mut budget = self.options.subsumption_budget;
                    let found = self.match_atom(ld.atom, lc.atom)
                        && self.match_into(&rest, &remaining, &mut budget);
                    self.binds.clear();
                    if found && let Some(result) = self.resolve_away(target, i, other, j) {
                        return Some(result);
                    }
                }
            }
        }
        None
    }

    /// Emit a subsumption resolution as the checker's steps: `resolve` of C (left) and D (right), then one
    /// `factor` for each literal of the instantiated E, which comes last, onto an equal literal of R. The result
    /// is kept only when it is exactly R with its variables renumbered; otherwise nothing is used.
    fn resolve_away(&mut self, target: Id, i: usize, other: Id, j: usize) -> Option<Id> {
        let size = self.clauses[target as usize].lits.len() - 1;
        self.binds.clear();
        let mut renamer = Renamer::new();
        let mut expected = Vec::with_capacity(size);
        for (index, literal) in self.lits(target).into_iter().enumerate() {
            if index != i {
                expected.push(self.instance(literal, 0, &mut renamer));
            }
        }
        let rule = Rule::Resolve {
            left: target,
            left_lit: i as u16,
            right: other,
            right_lit: j as u16,
        };
        if !self.bind_rule(&rule) {
            self.binds.clear();
            return None;
        }
        let (out, _) = self.conclude(&rule, false);
        self.binds.clear();
        let mut current = self.push_simplified(out, rule, target)?;
        let mut made = vec![current];
        while self.clauses[current as usize].lits.len() > size {
            let lits = self.lits(current);
            let last = lits.len() - 1;
            let mut partner = None;
            for (first, literal) in lits.iter().enumerate().take(size) {
                if literal.positive != lits[last].positive {
                    continue;
                }
                self.binds.clear();
                if self.unify_atoms(literal.atom, 0, lits[last].atom, 0) {
                    partner = Some(first);
                    break;
                }
            }
            self.binds.clear();
            let Some(first) = partner else { break };
            let rule = Rule::Factor {
                parent: current,
                first: first as u16,
                second: last as u16,
            };
            self.bind_rule(&rule);
            let (out, _) = self.conclude(&rule, false);
            self.binds.clear();
            current = self.push_simplified(out, rule, current)?;
            made.push(current);
        }
        if self.clauses[current as usize].lits.as_ref() != expected.as_slice() {
            for id in made {
                self.clauses[id as usize].state = State::Deleted;
            }
            return None;
        }
        for &id in &made[..made.len() - 1] {
            self.clauses[id as usize].state = State::Deleted;
        }
        Some(current)
    }

    /// Forward simplification of a selected clause: tautology deletion, renaming steps, demodulation, subsumption
    /// resolution and forward subsumption. Returns the simplified clause, or None when it was deleted.
    fn simplify_given(&mut self, id: Id) -> Option<Id> {
        let mut current = id;
        let mut rewrites = 0;
        loop {
            if self.interrupted.is_some() {
                return None;
            }
            if self.options.tautologies && is_tautology(&self.clauses[current as usize].lits) {
                self.stats.tautologies += 1;
                self.delete(current);
                return None;
            }
            if self.options.cleanup
                && let Some(next) = self.cleanup_step(current)
            {
                self.delete(current);
                current = next;
                continue;
            }
            if self.options.forward_demodulation
                && rewrites < self.options.max_rewrites
                && let Some((lits, rule)) = self.rewrite_once(current, None)
            {
                self.delete(current);
                current = self.push_simplified(lits, rule, current)?;
                self.stats.forward_rewrites += 1;
                rewrites += 1;
                continue;
            }
            if self.options.subsumption_resolution
                && let Some(next) = self.subsumption_resolution(current)
            {
                self.delete(current);
                current = next;
                self.stats.subsumption_resolutions += 1;
                continue;
            }
            break;
        }
        if self.options.forward_subsumption && !self.clauses[current as usize].lits.is_empty() {
            for other in self.subsumer_candidates(current) {
                if self.subsumes(other, current) {
                    self.stats.forward_subsumed += 1;
                    self.delete(current);
                    return None;
                }
            }
        }
        Some(current)
    }

    /// Backward subsumption and backward demodulation by the new given clause. Returns true on the empty clause.
    fn simplify_active(&mut self, given: Id) -> bool {
        if self.options.backward_subsumption {
            for other in self.subsumed_candidates(given) {
                if other != given && self.subsumes(given, other) {
                    self.stats.backward_subsumed += 1;
                    self.delete(other);
                }
            }
        }
        if self.options.backward_demodulation && self.is_unit_equation(given) {
            for other in self.rewrite_candidates(given) {
                if self.interrupted.is_some() {
                    return false;
                }
                if other == given || self.clauses[other as usize].state != State::Active {
                    continue;
                }
                if let Some((lits, rule)) = self.rewrite_once(other, Some(given)) {
                    self.stats.backward_rewrites += 1;
                    self.delete(other);
                    if self.derived_with_parents(lits, rule, self.generating_parents(other)) {
                        return true;
                    }
                }
            }
        }
        false
    }

    // ---- Selection and eligibility ----

    fn eligibility(&mut self, id: Id) {
        if self.clauses[id as usize].eligibility.is_some() {
            return;
        }
        let lits = self.lits(id);
        let count = lits.len();
        let mut result = Eligibility {
            selected: None,
            maximal: vec![true; count],
            strictly_maximal: vec![true; count],
        };
        if self.options.ordering {
            let lookahead: Vec<(usize, u64)> = if self.options.selection == Selection::Lookahead {
                let negative: Vec<(usize, Lit)> = lits
                    .iter()
                    .copied()
                    .enumerate()
                    .filter(|(_, literal)| !literal.positive)
                    .collect();
                negative
                    .into_iter()
                    .map(|(index, literal)| (index, self.lookahead_count(literal)))
                    .collect()
            } else {
                Vec::new()
            };
            let weight = |literal: &Lit| match literal.atom {
                Atom::Pred(term) => self.bank.weight(term),
                Atom::Eq(left, right) => self
                    .bank
                    .weight(left)
                    .saturating_add(self.bank.weight(right)),
            };
            let negatives = lits
                .iter()
                .enumerate()
                .filter(|(_, literal)| !literal.positive);
            let partners = &lookahead;
            result.selected = match self.options.selection {
                Selection::None => None,
                Selection::GroundNegative => negatives
                    .max_by_key(|(index, literal)| {
                        let ground = match literal.atom {
                            Atom::Pred(term) => self.bank.ground(term),
                            Atom::Eq(left, right) => {
                                self.bank.ground(left) && self.bank.ground(right)
                            }
                        };
                        (ground, weight(literal), Reverse(*index))
                    })
                    .map(|(index, _)| index as u16),
                Selection::NegativeEquality => negatives
                    .max_by_key(|(index, literal)| {
                        (
                            matches!(literal.atom, Atom::Eq(_, _)),
                            weight(literal),
                            Reverse(*index),
                        )
                    })
                    .map(|(index, _)| index as u16),
                Selection::HeaviestNegative => negatives
                    .max_by_key(|(index, literal)| (weight(literal), Reverse(*index)))
                    .map(|(index, _)| index as u16),
                Selection::LightestNegative => negatives
                    .min_by_key(|(index, literal)| (weight(literal), *index))
                    .map(|(index, _)| index as u16),
                // Fewest partners first; among equals the heavier literal, then the first one.
                Selection::Lookahead => partners
                    .iter()
                    .min_by_key(|&&(index, count)| (count, Reverse(weight(&lits[index])), index))
                    .map(|&(index, _)| index as u16),
            };
            for index in 0..count {
                for other in 0..count {
                    if other == index {
                        continue;
                    }
                    match self
                        .order
                        .compare_literals(&self.bank, lits[other], lits[index])
                    {
                        Cmp::Greater => {
                            result.maximal[index] = false;
                            result.strictly_maximal[index] = false;
                        }
                        Cmp::Equal => result.strictly_maximal[index] = false,
                        _ => {}
                    }
                }
            }
        }
        self.clauses[id as usize].eligibility = Some(Box::new(result));
    }

    /// Inference partners of a negative literal among the active clauses, counted up to a cap: for a predicate
    /// literal the eligible positive literals it unifies with, for an equation the active clauses with a
    /// rewriting side whose top symbol is that of one of its subterms. Selection only orders the search.
    fn lookahead_count(&mut self, literal: Lit) -> u64 {
        const CAP: u64 = 100_000;
        match literal.atom {
            Atom::Pred(term) => {
                let Head::Sym(symbol) = self.bank.head(term) else {
                    return 0;
                };
                let candidates: Vec<Id> = if self.options.index {
                    self.index
                        .resolution
                        .get(&(symbol, true))
                        .cloned()
                        .unwrap_or_default()
                } else {
                    self.active.clone()
                };
                let mut count = 0;
                for other in candidates {
                    if self.clauses[other as usize].state != State::Active {
                        continue;
                    }
                    for (position, other_literal) in self.lits(other).into_iter().enumerate() {
                        let Atom::Pred(other_term) = other_literal.atom else {
                            continue;
                        };
                        if !other_literal.positive
                            || self.bank.head(other_term) != Head::Sym(symbol)
                            || !self.positive_eligible(other, position)
                        {
                            continue;
                        }
                        self.binds.clear();
                        if self.binds.unify(&self.bank, term, 0, other_term, 1) {
                            count += 1;
                            if count >= CAP {
                                self.binds.clear();
                                return count;
                            }
                        }
                    }
                }
                self.binds.clear();
                count
            }
            Atom::Eq(left, right) => {
                if !self.options.index {
                    return self.active.len() as u64;
                }
                let mut heads = Vec::new();
                for side in [left, right] {
                    self.subterm_heads(side, &mut heads);
                }
                heads.sort_unstable();
                heads.dedup();
                let mut found = Vec::new();
                gather(&self.index.from, heads, &mut found);
                found.extend_from_slice(&self.index.from_variable);
                // Equality resolution is one more partner.
                self.in_activation_order(found).len() as u64 + 1
            }
        }
    }

    fn subterm_heads(&self, term: TermId, heads: &mut Vec<u32>) {
        if let Head::Sym(symbol) = self.bank.head(term) {
            heads.push(symbol);
            for &child in self.bank.args(term) {
                self.subterm_heads(child, heads);
            }
        }
    }

    fn info(&self, id: Id) -> &Eligibility {
        self.clauses[id as usize]
            .eligibility
            .as_ref()
            .expect("eligibility of an active clause")
    }

    /// A positive literal may take part: nothing is selected and it is strictly maximal.
    fn positive_eligible(&self, id: Id, index: usize) -> bool {
        if !self.options.ordering {
            return true;
        }
        let info = self.info(id);
        info.selected.is_none() && info.strictly_maximal[index]
    }

    /// A negative literal may take part: it is selected, or nothing is selected and it is maximal.
    fn negative_eligible(&self, id: Id, index: usize) -> bool {
        if !self.options.ordering {
            return true;
        }
        let info = self.info(id);
        match info.selected {
            Some(selected) => selected as usize == index,
            None => info.maximal[index],
        }
    }

    fn eligible(&self, id: Id, index: usize) -> bool {
        if self.clauses[id as usize].lits[index].positive {
            self.positive_eligible(id, index)
        } else {
            self.negative_eligible(id, index)
        }
    }

    fn take_passive(&mut self, id: Id) -> Option<Id> {
        if self.clauses[id as usize].state != State::Passive {
            return None;
        }
        let deleted = |parent: Id| self.clauses[parent as usize].state == State::Deleted;
        let orphan = match self.generating_parents(id) {
            Some(GeneratingParents::One(parent)) => deleted(parent),
            Some(GeneratingParents::Two(left, right)) => deleted(left) || deleted(right),
            Some(GeneratingParents::Input) | None => false,
        };
        self.passive -= 1;
        if orphan {
            let clause = &mut self.clauses[id as usize];
            clause.state = State::Deleted;
            // A passive clause has never generated children. Keep its rule and
            // identity; only its unreferenced literal allocation is released.
            clause.lits = Box::default();
            self.stats.orphaned += 1;
            self.stats.pruned += 1;
            None
        } else {
            self.clauses[id as usize].state = State::New;
            Some(id)
        }
    }

    fn select(&mut self) -> Option<Id> {
        while let Some(id) = self.input_queue.pop_front() {
            if let Some(id) = self.take_passive(id) {
                return Some(id);
            }
        }
        if !self.layers.is_empty() {
            return self.select_layered();
        }
        loop {
            if self.passive == 0 {
                return None;
            }
            let cycle = (self.options.age_ratio + self.options.weight_ratio) as u64;
            let by_age = (self.pick % cycle) < self.options.age_ratio as u64;
            self.pick += 1;
            let candidate = if by_age {
                self.age_queue.pop_front()
            } else {
                self.weight_queue.pop().map(|Reverse((_, id))| id)
            };
            if let Some(id) = candidate
                && let Some(id) = self.take_passive(id)
            {
                return Some(id);
            }
        }
    }

    /// Layered selection: pick a layer by the layer ratio, falling through to the next wider layer when it has no
    /// passive clause, then age or weight inside it. The widest layer holds every passive clause.
    fn select_layered(&mut self) -> Option<Id> {
        let cycle = (self.options.age_ratio + self.options.weight_ratio) as u64;
        let widest = self.layers.len() - 1;
        let picks = *self.layer_bounds.last().expect("one bound per layer");
        loop {
            if self.passive == 0 {
                return None;
            }
            let slot = self.layer_pick % picks;
            self.layer_pick += 1;
            let first = self
                .layer_bounds
                .iter()
                .position(|&bound| slot < bound)
                .expect("slot below the last bound");
            for layer in first..=widest {
                let by_age = (self.pick % cycle) < self.options.age_ratio as u64;
                self.pick += 1;
                let (ages, weights) = &mut self.layers[layer];
                let mut candidate = None;
                if by_age {
                    while let Some(id) = ages.pop_front() {
                        if self.clauses[id as usize].state == State::Passive {
                            candidate = Some(id);
                            break;
                        }
                    }
                } else {
                    while let Some(Reverse((_, id))) = weights.pop() {
                        if self.clauses[id as usize].state == State::Passive {
                            candidate = Some(id);
                            break;
                        }
                    }
                }
                if let Some(id) = candidate
                    && let Some(id) = self.take_passive(id)
                {
                    return Some(id);
                }
            }
        }
    }

    // ---- Limits ----

    fn over_limits(&mut self) -> Option<Stop> {
        if self
            .limits
            .deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
        {
            return Some(Stop::Time);
        }
        if let Some(limit) = self.limits.memory_kib
            && let Some(used) = resident_kib()
        {
            if used > limit {
                return Some(Stop::Memory);
            }
            // Freed memory is reused but rarely returned, so prune again only after further growth.
            if self.options.prune_passive
                && used > limit / 10 * 7
                && used > self.pruned_at_kib + limit / 20
            {
                self.pruned_at_kib = used;
                self.pruning = true;
            }
        }
        None
    }

    /// Checked every 4096 unification attempts inside one given clause's inferences.
    fn tick(&mut self) -> bool {
        if self.interrupted.is_some() {
            return true;
        }
        self.stats.attempts += 1;
        if self.stats.attempts.is_multiple_of(4096)
            && let Some(stop) = self.over_limits()
        {
            self.interrupted = Some(stop);
            return true;
        }
        false
    }

    // ---- Generating inferences ----

    fn unary(&mut self, given: Id) -> bool {
        let lits = self.lits(given);
        for (index, literal) in lits.iter().enumerate() {
            if let Atom::Eq(left, right) = literal.atom
                && !literal.positive
                && self.negative_eligible(given, index)
            {
                if self.tick() {
                    return false;
                }
                self.binds.clear();
                if self.binds.unify(&self.bank, left, 0, right, 0) {
                    let rule = Rule::EqRes {
                        parent: given,
                        pivot: index as u16,
                    };
                    let (out, _) = self.conclude(&rule, false);
                    self.binds.clear();
                    self.stats.equality_resolutions += 1;
                    if self.derived(out, rule) {
                        return true;
                    }
                }
            }
        }
        for first in 0..lits.len() {
            for second in first + 1..lits.len() {
                let (a, b) = (lits[first], lits[second]);
                if a.positive != b.positive || !self.compatible(a.atom, b.atom) {
                    continue;
                }
                if self.options.ordering || !self.options.unrestricted_rules {
                    if !a.positive {
                        continue;
                    }
                    let info = self.info(given);
                    if self.options.ordering
                        && (info.selected.is_some()
                            || !(info.maximal[first] || info.maximal[second]))
                    {
                        continue;
                    }
                }
                if self.tick() {
                    return false;
                }
                self.binds.clear();
                if self.unify_atoms(a.atom, 0, b.atom, 0) {
                    let rule = Rule::Factor {
                        parent: given,
                        first: first as u16,
                        second: second as u16,
                    };
                    let (out, _) = self.conclude(&rule, false);
                    self.binds.clear();
                    self.stats.factorings += 1;
                    if self.derived(out, rule) {
                        return true;
                    }
                }
            }
        }
        if self.options.equality_factoring {
            for first in 0..lits.len() {
                let Atom::Eq(left, _) = lits[first].atom else {
                    continue;
                };
                if !lits[first].positive {
                    continue;
                }
                if self.options.ordering {
                    let info = self.info(given);
                    if info.selected.is_some() || !info.maximal[first] {
                        continue;
                    }
                }
                for (second, literal) in lits.iter().enumerate() {
                    let Atom::Eq(other, _) = literal.atom else {
                        continue;
                    };
                    if second == first || !literal.positive {
                        continue;
                    }
                    if self.tick() {
                        return false;
                    }
                    self.binds.clear();
                    if self.binds.unify(&self.bank, left, 0, other, 0) {
                        let rule = Rule::EqFactor {
                            parent: given,
                            first: first as u16,
                            second: second as u16,
                        };
                        let (out, _) = self.conclude(&rule, false);
                        self.binds.clear();
                        self.stats.equality_factorings += 1;
                        if self.derived(out, rule) {
                            return true;
                        }
                    }
                }
            }
        }
        false
    }

    /// Binary resolution with `left` on side 0 and `right` on side 1.
    #[allow(clippy::needless_range_loop)]
    fn resolve(&mut self, left: Id, right: Id) -> bool {
        let a = self.lits(left);
        let b = self.lits(right);
        for i in 0..a.len() {
            for j in 0..b.len() {
                if a[i].positive == b[j].positive || !self.compatible(a[i].atom, b[j].atom) {
                    continue;
                }
                if matches!(a[i].atom, Atom::Eq(..)) && !self.options.unrestricted_rules {
                    continue;
                }
                if !self.eligible(left, i) || !self.eligible(right, j) {
                    continue;
                }
                if self.tick() {
                    return false;
                }
                self.binds.clear();
                if self.unify_atoms(a[i].atom, 0, b[j].atom, 1) {
                    let rule = Rule::Resolve {
                        left,
                        left_lit: i as u16,
                        right,
                        right_lit: j as u16,
                    };
                    let (out, _) = self.conclude(&rule, false);
                    self.binds.clear();
                    self.stats.resolutions += 1;
                    if self.derived(out, rule) {
                        return true;
                    }
                }
            }
        }
        false
    }

    /// Whether `big` stays not smaller than `small` after the current bindings (both read on `side`).
    fn not_smaller_instance(&mut self, big: TermId, small: TermId, side: u8, before: Cmp) -> bool {
        match before {
            Cmp::Greater => true,
            Cmp::Less | Cmp::Equal => false,
            Cmp::Incomparable => {
                let mut renamer = Renamer::new();
                let big = self.binds.apply(&mut self.bank, big, side, &mut renamer);
                let small = self.binds.apply(&mut self.bank, small, side, &mut renamer);
                !matches!(
                    self.order.compare(&self.bank, big, small),
                    Cmp::Less | Cmp::Equal
                )
            }
        }
    }

    /// Superposition from the equations of `source` (side 0) into `target` (side 1).
    fn superpose(&mut self, source: Id, target: Id) -> bool {
        let from_lits = self.lits(source);
        let into_lits = self.lits(target);
        for (pivot, literal) in from_lits.iter().enumerate() {
            let Atom::Eq(left, right) = literal.atom else {
                continue;
            };
            if !literal.positive || !self.positive_eligible(source, pivot) {
                continue;
            }
            for reverse in [false, true] {
                let (from, to) = if reverse {
                    (right, left)
                } else {
                    (left, right)
                };
                if self.bank.as_var(from).is_some() && !self.options.from_variables {
                    continue;
                }
                let oriented = if self.options.ordering {
                    self.order.compare(&self.bank, from, to)
                } else {
                    Cmp::Greater
                };
                if matches!(oriented, Cmp::Less | Cmp::Equal) {
                    continue;
                }
                for (index, target_literal) in into_lits.iter().enumerate() {
                    if !self.eligible(target, index) {
                        continue;
                    }
                    let sides = match target_literal.atom {
                        Atom::Eq(a, b) if self.options.ordering => {
                            Some((a, b, self.order.compare(&self.bank, a, b)))
                        }
                        _ => None,
                    };
                    let listed = match self.clauses[target as usize].filter.as_ref() {
                        Some(filter) => std::rc::Rc::clone(&filter.positions[index]),
                        None => {
                            std::rc::Rc::new(positions(&self.bank, index as u16, *target_literal))
                        }
                    };
                    for (pos, at) in listed.iter() {
                        let at = *at;
                        let side_order = sides.map(|(a, b, order)| match pos.root {
                            Root::Left => (a, b, order),
                            _ => (b, a, order.reverse()),
                        });
                        if let Some((_, _, order)) = side_order
                            && matches!(order, Cmp::Less | Cmp::Equal)
                        {
                            continue;
                        }
                        // Distinct top symbols cannot unify; skip without counting an attempt.
                        if self.options.filter
                            && let (Head::Sym(f), Head::Sym(g)) =
                                (self.bank.head(from), self.bank.head(at))
                            && f != g
                        {
                            continue;
                        }
                        if self.tick() {
                            return false;
                        }
                        self.binds.clear();
                        if !self.binds.unify(&self.bank, from, 0, at, 1) {
                            continue;
                        }
                        if self.options.ordering {
                            let keep_source = self.not_smaller_instance(from, to, 0, oriented);
                            let keep_target = match side_order {
                                Some((big, small, order)) => {
                                    self.not_smaller_instance(big, small, 1, order)
                                }
                                None => true,
                            };
                            if !keep_source || !keep_target {
                                self.binds.clear();
                                continue;
                            }
                        }
                        let rule = Rule::Para {
                            source,
                            pivot: pivot as u16,
                            reverse,
                            target,
                            pos: pos.clone(),
                        };
                        let (out, _) = self.conclude(&rule, false);
                        self.binds.clear();
                        self.stats.superpositions += 1;
                        if self.derived(out, rule) {
                            return true;
                        }
                    }
                }
            }
        }
        false
    }

    fn literal_key(&self, literal: Lit) -> Key {
        match literal.atom {
            Atom::Pred(term) => match self.bank.head(term) {
                Head::Sym(symbol) => (symbol, literal.positive),
                Head::Var(_) => (u32::MAX - 1, literal.positive),
            },
            Atom::Eq(..) => (u32::MAX, literal.positive),
        }
    }

    fn keys(&self, id: Id) -> Vec<Key> {
        let mut keys: Vec<Key> = self.clauses[id as usize]
            .lits
            .iter()
            .map(|&literal| self.literal_key(literal))
            .collect();
        keys.sort_unstable();
        keys.dedup();
        keys
    }

    /// Active clauses among `ids`, in activation order, each once.
    fn in_activation_order(&self, mut ids: Vec<Id>) -> Vec<Id> {
        ids.retain(|&id| self.clauses[id as usize].state == State::Active);
        ids.sort_unstable_by_key(|&id| self.clauses[id as usize].activation);
        ids.dedup();
        ids
    }

    fn index_insert(&mut self, id: Id) {
        let filter = self.filter(id);
        let (into, from, from_variable, resolution) = (
            filter.into_symbols.clone(),
            filter.from_symbols.clone(),
            filter.from_variable,
            filter.resolution_keys.clone(),
        );
        let mut symbols: Vec<u32> = filter
            .positions
            .iter()
            .flat_map(|list| list.iter().map(|&(_, at)| at))
            .filter_map(|at| match self.bank.head(at) {
                Head::Sym(symbol) => Some(symbol),
                Head::Var(_) => None,
            })
            .collect();
        symbols.sort_unstable();
        symbols.dedup();
        let keys = self.keys(id);
        let index = &mut self.index;
        for symbol in into {
            index.into.entry(symbol).or_default().push(id);
        }
        for symbol in from {
            index.from.entry(symbol).or_default().push(id);
        }
        if from_variable {
            index.from_variable.push(id);
        }
        for key in resolution {
            index.resolution.entry(key).or_default().push(id);
        }
        for symbol in symbols {
            index.symbols.entry(symbol).or_default().push(id);
        }
        for &key in &keys {
            index.subsume_all.entry(key).or_default().push(id);
        }
        let record = &self.clauses[id as usize];
        if record.lits.len() > 1 {
            for &literal in record.lits.iter() {
                let ground = match literal.atom {
                    Atom::Pred(term) => self.bank.ground(term),
                    Atom::Eq(left, right) => self.bank.ground(left) && self.bank.ground(right),
                };
                if ground {
                    let list = index
                        .ground_in_nonunits
                        .entry(ground_unit_key(literal))
                        .or_default();
                    // Repeated literals and reversed equalities share one posting.
                    if list.last() != Some(&id) {
                        list.push(id);
                    }
                }
            }
        }
        if record.lits.len() == 1 && record.vars == 0 {
            index
                .ground_units
                .entry(ground_unit_key(record.lits[0]))
                .or_default()
                .push(id);
        } else if let Some(&rarest) = keys
            .iter()
            .min_by_key(|key| (index.subsume_all.get(*key).map_or(0, Vec::len), **key))
        {
            index.subsume_one.entry(rarest).or_default().push(id);
        }
        if self.is_unit_equation(id) {
            let Atom::Eq(left, right) = self.clauses[id as usize].lits[0].atom else {
                unreachable!("unit equation");
            };
            for (side, reverse) in [(left, false), (right, true)] {
                if let Head::Sym(symbol) = self.bank.head(side) {
                    self.index
                        .unit_from
                        .entry(symbol)
                        .or_default()
                        .push((id, reverse));
                }
            }
        }
    }

    /// Active clauses that may share an inference with `given`: all of them without the index.
    fn partners(&self, given: Id) -> Vec<Id> {
        let filter = self.filter(given);
        if !self.options.index || filter.from_variable {
            return self.active.clone();
        }
        let mut found = vec![given];
        gather(
            &self.index.into,
            filter.from_symbols.iter().copied(),
            &mut found,
        );
        gather(
            &self.index.from,
            filter.into_symbols.iter().copied(),
            &mut found,
        );
        found.extend_from_slice(&self.index.from_variable);
        gather(
            &self.index.resolution,
            filter
                .resolution_keys
                .iter()
                .map(|&(symbol, positive)| (symbol, !positive)),
            &mut found,
        );
        self.in_activation_order(found)
    }

    /// Active clauses that may subsume `special`: each has its one indexed key among the keys of `special`.
    fn subsumer_candidates(&self, special: Id) -> Vec<Id> {
        if !self.options.index {
            return self.active.clone();
        }
        let mut found = Vec::new();
        gather(&self.index.subsume_one, self.keys(special), &mut found);
        gather(
            &self.index.ground_units,
            self.clauses[special as usize]
                .lits
                .iter()
                .copied()
                .map(ground_unit_key),
            &mut found,
        );
        self.in_activation_order(found)
    }

    /// Active clauses that `general` may subsume: each has every key of `general`; take the shortest list.
    fn subsumed_candidates(&self, general: Id) -> Vec<Id> {
        if !self.options.index {
            return self.active.clone();
        }
        let record = &self.clauses[general as usize];
        if record.lits.len() == 1 && record.vars == 0 {
            let key = ground_unit_key(record.lits[0]);
            let mut found = Vec::new();
            gather(&self.index.ground_units, [key], &mut found);
            gather(&self.index.ground_in_nonunits, [key], &mut found);
            return self.in_activation_order(found);
        }
        let shortest = self
            .keys(general)
            .into_iter()
            .min_by_key(|key| (self.index.subsume_all.get(key).map_or(0, Vec::len), *key));
        let found = shortest
            .and_then(|key| self.index.subsume_all.get(&key).cloned())
            .unwrap_or_default();
        self.in_activation_order(found)
    }

    /// Active clauses a unit equation may rewrite: each has a subterm with the top symbol of a side.
    fn rewrite_candidates(&self, unit: Id) -> Vec<Id> {
        if !self.options.index {
            return self.active.clone();
        }
        let Atom::Eq(left, right) = self.clauses[unit as usize].lits[0].atom else {
            return Vec::new();
        };
        let symbols = [left, right]
            .into_iter()
            .filter_map(|side| match self.bank.head(side) {
                Head::Sym(symbol) => Some(symbol),
                Head::Var(_) => None,
            });
        let mut found = Vec::new();
        gather(&self.index.symbols, symbols, &mut found);
        self.in_activation_order(found)
    }

    fn prepare_filter(&mut self, id: Id) {
        let lits = self.lits(id);
        let mut filter = Filter::default();
        for (index, literal) in lits.iter().enumerate() {
            let listed = std::rc::Rc::new(positions(&self.bank, index as u16, *literal));
            filter.positions.push(std::rc::Rc::clone(&listed));
            if let Atom::Eq(left, right) = literal.atom
                && literal.positive
                && self.positive_eligible(id, index)
            {
                for (from, to) in [(left, right), (right, left)] {
                    match self.bank.head(from) {
                        Head::Var(_) => filter.from_variable |= self.options.from_variables,
                        Head::Sym(symbol) => {
                            if !self.options.ordering
                                || !matches!(
                                    self.order.compare(&self.bank, from, to),
                                    Cmp::Less | Cmp::Equal
                                )
                            {
                                filter.from_symbols.push(symbol);
                            }
                        }
                    }
                }
            }
            if !self.eligible(id, index) {
                continue;
            }
            let sides = match literal.atom {
                Atom::Eq(a, b) if self.options.ordering => {
                    Some(self.order.compare(&self.bank, a, b))
                }
                _ => None,
            };
            for (pos, at) in listed.iter() {
                let order = sides.map(|order| {
                    if pos.root == Root::Left {
                        order
                    } else {
                        order.reverse()
                    }
                });
                if matches!(order, Some(Cmp::Less | Cmp::Equal)) {
                    continue;
                }
                if let Head::Sym(symbol) = self.bank.head(*at) {
                    filter.into_symbols.push(symbol);
                }
            }
            match literal.atom {
                Atom::Pred(term) => {
                    if let Head::Sym(symbol) = self.bank.head(term) {
                        filter.resolution_keys.push((symbol, literal.positive));
                    }
                }
                Atom::Eq(..) => {
                    if self.options.unrestricted_rules {
                        filter.resolution_keys.push((u32::MAX, literal.positive));
                    }
                }
            }
        }
        for list in [&mut filter.into_symbols, &mut filter.from_symbols] {
            list.sort_unstable();
            list.dedup();
        }
        filter.resolution_keys.sort_unstable();
        filter.resolution_keys.dedup();
        self.clauses[id as usize].filter = Some(Box::new(filter));
    }

    fn filter(&self, id: Id) -> &Filter {
        self.clauses[id as usize]
            .filter
            .as_ref()
            .expect("filter of an active clause")
    }

    /// False only when no superposition from `source` into `target` can unify.
    fn may_superpose(&self, source: Id, target: Id) -> bool {
        let (from, into) = (self.filter(source), self.filter(target));
        from.from_variable
            || from
                .from_symbols
                .iter()
                .any(|symbol| into.into_symbols.binary_search(symbol).is_ok())
    }

    /// False only when no resolution between `left` and `right` can unify.
    fn may_resolve(&self, left: Id, right: Id) -> bool {
        let (a, b) = (self.filter(left), self.filter(right));
        a.resolution_keys.iter().any(|&(symbol, positive)| {
            b.resolution_keys
                .binary_search(&(symbol, !positive))
                .is_ok()
        })
    }

    fn generate(&mut self, given: Id) -> bool {
        if self.unary(given) {
            return true;
        }
        let filter = self.options.filter || self.options.index;
        for partner in self.partners(given) {
            if self.interrupted.is_some() {
                return false;
            }
            if self.clauses[partner as usize].state != State::Active {
                continue;
            }
            if (!filter || self.may_resolve(given, partner)) && self.resolve(given, partner) {
                return true;
            }
            if (!filter || self.may_superpose(given, partner)) && self.superpose(given, partner) {
                return true;
            }
            if partner != given
                && (!filter || self.may_superpose(partner, given))
                && self.superpose(partner, given)
            {
                return true;
            }
        }
        false
    }

    /// Under memory pressure, drop the heavier half of passive. A passive clause has no children, so its
    /// literals can be freed; the search stays sound and loses only completeness.
    fn prune_passive(&mut self) {
        let mut entries: Vec<(u32, Id)> = std::mem::take(&mut self.weight_queue)
            .into_vec()
            .into_iter()
            .map(|Reverse(entry)| entry)
            .filter(|&(_, id)| self.clauses[id as usize].state == State::Passive)
            .collect();
        entries.sort_unstable();
        let keep = entries.len() / 2;
        for &(_, id) in &entries[keep..] {
            let record = &mut self.clauses[id as usize];
            record.state = State::Deleted;
            record.lits = Box::default();
            self.passive -= 1;
            self.stats.pruned += 1;
        }
        self.weight_queue = entries[..keep]
            .iter()
            .map(|&entry| Reverse(entry))
            .collect();
        self.age_queue
            .retain(|&id| self.clauses[id as usize].state == State::Passive);
    }

    // ---- The loop ----

    pub fn run(&mut self) -> Stop {
        if let Some(id) = self.found {
            return Stop::Proof(id);
        }
        loop {
            if let Some(stop) = self.interrupted {
                return stop;
            }
            if self.pick.is_multiple_of(32)
                && let Some(stop) = self.over_limits()
            {
                return stop;
            }
            if self
                .limits
                .deadline
                .is_some_and(|deadline| Instant::now() >= deadline)
            {
                return Stop::Time;
            }
            if self
                .options
                .given_limit
                .is_some_and(|limit| self.stats.given >= limit)
            {
                return Stop::GivenLimit;
            }
            if self.pruning {
                self.pruning = false;
                self.prune_passive();
            }
            if self.options.ground_joinability && !self.ground_join_tried {
                self.ground_join_tried = true;
                if let Some(empty) = self.ground_join_inputs() {
                    self.found = Some(empty);
                    return Stop::Proof(empty);
                }
                if let Some(stop) = self.interrupted {
                    return stop;
                }
            }
            let Some(selected) = self.select() else {
                return Stop::Saturated;
            };
            let Some(given) = self.simplify_given(selected) else {
                continue;
            };
            if let Some(stop) = self.interrupted {
                return stop;
            }
            if self.clauses[given as usize].lits.is_empty() {
                return Stop::Proof(given);
            }
            self.stats.given += 1;
            if (self.given_trace.len() as u32) < self.options.trace_given {
                self.given_trace.push(given);
            }
            self.eligibility(given);
            self.prepare_filter(given);
            if self.simplify_active(given) {
                return Stop::Proof(self.found.expect("empty clause"));
            }
            if let Some(stop) = self.interrupted {
                return stop;
            }
            self.clauses[given as usize].state = State::Active;
            self.activations += 1;
            self.clauses[given as usize].activation = self.activations;
            self.active.push(given);
            if self.is_unit_equation(given) {
                self.units.push(given);
            }
            if self.options.index {
                self.index_insert(given);
            }
            if self.generate(given) {
                return Stop::Proof(self.found.expect("empty clause"));
            }
            if let Some(stop) = self.interrupted {
                return stop;
            }
        }
    }

    pub fn finish_stats(&mut self) {
        self.stats.active_final = self.active.len() as u64;
        self.stats.terms_stored = self.bank.len() as u64;
    }
}
