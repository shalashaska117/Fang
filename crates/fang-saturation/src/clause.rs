// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Clauses keep the exact literal order, equation orientation and variable numbering the checker computes, so
//! every derived clause is the claimed clause of its certificate step. Variables are numbered 0, 1, 2, ... by
//! first occurrence; an input clause also records its original variable numbers.

use crate::term::{Bank, Head, TermId};

pub type Id = u32;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Atom {
    /// A predicate atom, stored as a bank term whose head is `functions + predicate`.
    Pred(TermId),
    /// An equation, left side first, as stated.
    Eq(TermId, TermId),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Lit {
    pub positive: bool,
    pub atom: Atom,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Root {
    Argument(u16),
    Left,
    Right,
}

/// A position in a literal: the predicate argument or equation side, then argument indexes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pos {
    pub literal: u16,
    pub root: Root,
    pub path: Vec<u16>,
}

#[derive(Clone, Debug)]
pub enum Rule {
    /// Clause `index` of the prepared problem; `original[x]` is the input's own number for internal variable x.
    Input { index: usize, original: Vec<u32> },
    /// The checker's `factor`: literal `second` removed after unifying it with literal `first`.
    Factor { parent: Id, first: u16, second: u16 },
    /// The checker's `eq-resolve` on negative equation `pivot`.
    EqRes { parent: Id, pivot: u16 },
    /// The checker's `resolve`, `left` renamed to even and `right` to odd variables.
    Resolve {
        left: Id,
        left_lit: u16,
        right: Id,
        right_lit: u16,
    },
    /// The checker's `paramodulate` with a unifier (superposition).
    Para {
        source: Id,
        pivot: u16,
        reverse: bool,
        target: Id,
        pos: Pos,
    },
    /// The checker's `paramodulate` with a match of a unit equation into the target (demodulation); `pivot` is 0.
    Demod {
        source: Id,
        pivot: u16,
        reverse: bool,
        target: Id,
        pos: Pos,
    },
    /// Equality factoring, which the version-8 format cannot state; used only to measure the missing rule.
    EqFactor { parent: Id, first: u16, second: u16 },
}

impl Rule {
    pub fn parents(&self) -> Vec<Id> {
        match self {
            Rule::Input { .. } => vec![],
            Rule::Factor { parent, .. }
            | Rule::EqRes { parent, .. }
            | Rule::EqFactor { parent, .. } => vec![*parent],
            Rule::Resolve { left, right, .. } => vec![*left, *right],
            Rule::Para { source, target, .. } | Rule::Demod { source, target, .. } => {
                vec![*source, *target]
            }
        }
    }

    pub fn name(&self) -> &'static str {
        match self {
            Rule::Input { .. } => "input",
            Rule::Factor { .. } => "factor",
            Rule::EqRes { .. } => "eq-resolve",
            Rule::Resolve { .. } => "resolve",
            Rule::Para { .. } => "superposition",
            Rule::Demod { .. } => "demodulation",
            Rule::EqFactor { .. } => "equality-factoring",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum State {
    New,
    Passive,
    Active,
    Deleted,
}

/// Selection and maximality, computed when a clause is selected as given clause.
#[derive(Clone, Debug, Default)]
pub struct Eligibility {
    pub selected: Option<u16>,
    pub maximal: Vec<bool>,
    pub strictly_maximal: Vec<bool>,
}

/// What a clause can take part in, computed when it becomes active, so that pairs where no unification can
/// succeed are skipped without changing which inferences are made.
#[derive(Clone, Debug, Default)]
pub struct Filter {
    /// Top symbols of the subterms superposition may rewrite, sorted.
    pub into_symbols: Vec<u32>,
    /// Top symbols of the equation sides superposition may rewrite with, sorted.
    pub from_symbols: Vec<u32>,
    /// Some equation side superposition may rewrite with is a variable.
    pub from_variable: bool,
    /// Predicate symbol (u32::MAX for an equation) and sign of each literal resolution may use, sorted.
    pub resolution_keys: Vec<(u32, bool)>,
    /// Every non-variable position of each literal, as `positions` lists them, shared with the inference loops.
    pub positions: Vec<std::rc::Rc<Vec<(Pos, TermId)>>>,
}

#[derive(Clone, Debug)]
pub struct ClauseRec {
    pub lits: Box<[Lit]>,
    pub rule: Rule,
    pub weight: u32,
    pub depth: u32,
    pub vars: u32,
    pub state: State,
    pub eligibility: Option<Box<Eligibility>>,
    pub filter: Option<Box<Filter>>,
    /// Position in the order of activation, from 1; 0 while never active.
    pub activation: u32,
    /// Some ancestor, or the clause itself, is a goal input.
    pub goal: bool,
    /// SInE level: 0 for a goal ancestor, else the least level of an input ancestor (u32::MAX when unreached).
    pub level: u32,
}

pub fn atom_terms(atom: Atom) -> (TermId, Option<TermId>) {
    match atom {
        Atom::Pred(term) => (term, None),
        Atom::Eq(left, right) => (left, Some(right)),
    }
}

/// Weight, the largest argument height (an argument of a predicate atom counts from its own root), and the number
/// of distinct variables (the largest variable plus one, since numbering is dense).
pub fn measure(bank: &Bank, lits: &[Lit]) -> (u32, u32, u32) {
    let mut weight: u32 = 0;
    let mut depth = 0;
    let mut vars = Vec::new();
    for literal in lits {
        match literal.atom {
            Atom::Pred(term) => {
                weight = weight.saturating_add(bank.weight(term));
                depth = depth.max(bank.depth(term).saturating_sub(1));
                bank.collect_vars(term, &mut vars);
            }
            Atom::Eq(left, right) => {
                weight = weight
                    .saturating_add(bank.weight(left))
                    .saturating_add(bank.weight(right));
                depth = depth.max(bank.depth(left)).max(bank.depth(right));
                bank.collect_vars(left, &mut vars);
                bank.collect_vars(right, &mut vars);
            }
        }
    }
    let count = vars.iter().max().map_or(0, |largest| largest + 1);
    (weight, depth, count)
}

/// Whether the atoms are equal, equations also up to symmetry.
pub fn same_atom_symmetric(a: Atom, b: Atom) -> bool {
    match (a, b) {
        (Atom::Eq(s, t), Atom::Eq(u, v)) => (s == u && t == v) || (s == v && t == u),
        _ => a == b,
    }
}

/// The predicate symbol of an atom, or None for an equation.
pub fn predicate_head(bank: &Bank, atom: Atom) -> Option<u32> {
    match atom {
        Atom::Pred(term) => match bank.head(term) {
            Head::Sym(symbol) => Some(symbol),
            Head::Var(_) => None,
        },
        Atom::Eq(..) => None,
    }
}

/// Every non-variable position of a literal with its subterm, in left-to-right preorder.
pub fn positions(bank: &Bank, index: u16, literal: Lit) -> Vec<(Pos, TermId)> {
    let mut found = Vec::new();
    let roots: Vec<(Root, TermId)> = match literal.atom {
        Atom::Pred(term) => bank
            .args(term)
            .iter()
            .enumerate()
            .map(|(argument, &child)| (Root::Argument(argument as u16), child))
            .collect(),
        Atom::Eq(left, right) => vec![(Root::Left, left), (Root::Right, right)],
    };
    for (root, term) in roots {
        let mut path = Vec::new();
        walk(bank, term, index, root, &mut path, &mut found);
    }
    found
}

fn walk(
    bank: &Bank,
    term: TermId,
    literal: u16,
    root: Root,
    path: &mut Vec<u16>,
    found: &mut Vec<(Pos, TermId)>,
) {
    if bank.as_var(term).is_some() {
        return;
    }
    found.push((
        Pos {
            literal,
            root,
            path: path.clone(),
        },
        term,
    ));
    for (index, &child) in bank.args(term).iter().enumerate() {
        path.push(index as u16);
        walk(bank, child, literal, root, path, found);
        path.pop();
    }
}

/// The subterm at `pos` below its root term.
pub fn subterm(bank: &Bank, literal: Lit, root: Root, path: &[u16]) -> Option<TermId> {
    let mut term = match (literal.atom, root) {
        (Atom::Pred(atom), Root::Argument(index)) => *bank.args(atom).get(index as usize)?,
        (Atom::Eq(left, _), Root::Left) => left,
        (Atom::Eq(_, right), Root::Right) => right,
        _ => return None,
    };
    for &index in path {
        term = *bank.args(term).get(index as usize)?;
    }
    Some(term)
}
