// Copyright (c) 2026 Pietro Pellegrino.
// Vampire is copyright (C) 2020 by its authors and contributors (see
// LICENSES/Vampire.AUTHORS) and their institutional affiliations. All rights reserved.
// Reference and retained notices: LICENSES/Vampire.txt; LICENSES/Vampire.ORIGIN.
use crate::{Budget, Error, Limits};
use std::ops::Index;

pub type Variable = u32;
pub type SymbolId = u32;

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Term {
    Var(Variable),
    Fun(SymbolId, Vec<Term>),
}

impl Term {
    pub fn copy_term(&self) -> Self {
        match self {
            Self::Var(variable) => Self::Var(*variable),
            Self::Fun(symbol, arguments) => {
                let mut copied = Vec::new();
                let mut index = 0;
                while index < arguments.len() {
                    copied.push(arguments[index].copy_term());
                    index += 1;
                }
                Self::Fun(*symbol, copied)
            }
        }
    }
}

impl Clone for Term {
    fn clone(&self) -> Self {
        self.copy_term()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Literal {
    pub positive: bool,
    pub predicate: SymbolId,
    pub arguments: Vec<Term>,
}

pub type Clause = Vec<Literal>;
/// Sorted, unique variable bindings. Linear lookup keeps the extracted core explicit.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Substitution {
    bindings: Vec<(Variable, Term)>,
}

impl Substitution {
    pub fn new() -> Self {
        Self {
            bindings: Vec::new(),
        }
    }

    pub fn get(&self, variable: &Variable) -> Option<&Term> {
        let mut index = 0;
        while index < self.bindings.len() {
            if self.bindings[index].0 == *variable {
                return Some(&self.bindings[index].1);
            }
            index += 1;
        }
        None
    }

    pub fn contains_key(&self, variable: &Variable) -> bool {
        self.get(variable).is_some()
    }

    pub fn insert(&mut self, variable: Variable, term: Term) -> Option<Term> {
        let mut index = 0;
        while index < self.bindings.len() {
            if self.bindings[index].0 == variable {
                return Some(std::mem::replace(&mut self.bindings[index].1, term));
            }
            if self.bindings[index].0 > variable {
                break;
            }
            index += 1;
        }
        // The pinned Aeneas Vec::insert model requires index < len, although
        // Rust also allows index == len. Use push for that append case.
        if index == self.bindings.len() {
            self.bindings.push((variable, term));
        } else {
            self.bindings.insert(index, (variable, term));
        }
        None
    }

    pub fn len(&self) -> usize {
        self.bindings.len()
    }
    pub fn is_empty(&self) -> bool {
        self.bindings.is_empty()
    }
    pub fn iter(&self) -> std::slice::Iter<'_, (Variable, Term)> {
        self.bindings.iter()
    }
    pub fn values(&self) -> impl Iterator<Item = &Term> {
        self.bindings.iter().map(|(_, term)| term)
    }
    pub(crate) fn entries(&self) -> &[(Variable, Term)] {
        &self.bindings
    }
}

impl<const N: usize> From<[(Variable, Term); N]> for Substitution {
    fn from(bindings: [(Variable, Term); N]) -> Self {
        bindings.into_iter().collect()
    }
}

impl FromIterator<(Variable, Term)> for Substitution {
    fn from_iter<T: IntoIterator<Item = (Variable, Term)>>(iter: T) -> Self {
        let mut result = Self::new();
        for (variable, term) in iter {
            result.insert(variable, term);
        }
        result
    }
}

impl<'a> IntoIterator for &'a Substitution {
    type Item = &'a (Variable, Term);
    type IntoIter = std::slice::Iter<'a, (Variable, Term)>;
    fn into_iter(self) -> Self::IntoIter {
        self.bindings.iter()
    }
}

impl Index<&Variable> for Substitution {
    type Output = Term;
    fn index(&self, variable: &Variable) -> &Self::Output {
        self.get(variable).expect("substitution key must exist")
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Symbol {
    pub name: String,
    pub arity: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Problem {
    pub functions: Vec<Symbol>,
    pub predicates: Vec<Symbol>,
    pub clause_names: Vec<String>,
    pub clauses: Vec<Clause>,
}

pub fn deduplicate(clause: &Clause) -> Clause {
    let mut seen = std::collections::BTreeSet::new();
    clause
        .iter()
        .filter(|literal| seen.insert(*literal))
        .cloned()
        .collect()
}

pub(crate) fn count_clause(clause: &Clause, limits: &Limits) -> Result<usize, Error> {
    if clause.len() > limits.max_literals {
        return Err(Error::resource("literal limit exceeded"));
    }
    let mut count = clause.len();
    let mut stack = Vec::new();
    for literal in clause {
        stack.extend(literal.arguments.iter().map(|term| (term, 1)));
    }
    while let Some((term, depth)) = stack.pop() {
        count = count
            .checked_add(1)
            .ok_or_else(|| Error::resource("term node count overflow"))?;
        if count > limits.max_term_nodes {
            return Err(Error::resource("term node limit exceeded"));
        }
        if depth > limits.max_term_depth.min(64) {
            return Err(Error::resource("term depth limit exceeded"));
        }
        if let Term::Fun(_, args) = term {
            stack.extend(args.iter().map(|arg| (arg, depth + 1)));
        }
    }
    Ok(count)
}

pub(crate) fn rename(clause: &Clause, side: u32, budget: &mut Budget) -> Result<Clause, Error> {
    fn term(t: &Term, side: u32, budget: &mut Budget) -> Result<Term, Error> {
        budget.tick()?;
        match t {
            Term::Var(v) => v
                .checked_mul(2)
                .and_then(|n| n.checked_add(side))
                .map(Term::Var)
                .ok_or_else(|| Error::resource("variable ID overflow during standardization")),
            Term::Fun(f, args) => Ok(Term::Fun(
                *f,
                args.iter()
                    .map(|t| term(t, side, budget))
                    .collect::<Result<_, _>>()?,
            )),
        }
    }
    clause
        .iter()
        .map(|l| {
            Ok(Literal {
                positive: l.positive,
                predicate: l.predicate,
                arguments: l
                    .arguments
                    .iter()
                    .map(|t| term(t, side, budget))
                    .collect::<Result<_, _>>()?,
            })
        })
        .collect()
}

/// Simultaneous application: substitution images are not substituted again.
pub fn apply(term: &Term, substitution: &Substitution) -> Term {
    match term {
        Term::Var(v) => match substitution.get(v) {
            Some(image) => image.copy_term(),
            None => Term::Var(*v),
        },
        Term::Fun(f, args) => {
            let mut result = Vec::new();
            let mut index = 0;
            while index < args.len() {
                result.push(apply(&args[index], substitution));
                index += 1;
            }
            Term::Fun(*f, result)
        }
    }
}

pub(crate) fn apply_clause(
    clause: &Clause,
    skip: usize,
    substitution: &Substitution,
    limits: &Limits,
    budget: &mut Budget,
) -> Result<Clause, Error> {
    fn term(
        t: &Term,
        subst: &Substitution,
        depth: usize,
        limits: &Limits,
        budget: &mut Budget,
        nodes: &mut usize,
    ) -> Result<Term, Error> {
        budget.tick()?;
        *nodes += 1;
        if *nodes > limits.max_term_nodes {
            return Err(Error::resource("substituted term node limit exceeded"));
        }
        if depth > limits.max_term_depth.min(64) {
            return Err(Error::resource("substituted term depth limit exceeded"));
        }
        match t {
            Term::Var(v) if subst.contains_key(v) => {
                // Validate the image at its actual insertion depth before cloning it.
                term(
                    &subst[v],
                    &Substitution::new(),
                    depth,
                    limits,
                    budget,
                    nodes,
                )
            }
            Term::Var(v) => Ok(Term::Var(*v)),
            Term::Fun(f, args) => Ok(Term::Fun(
                *f,
                args.iter()
                    .map(|t| term(t, subst, depth + 1, limits, budget, nodes))
                    .collect::<Result<_, _>>()?,
            )),
        }
    }
    let mut nodes = 0;
    clause
        .iter()
        .enumerate()
        .filter(|(i, _)| *i != skip)
        .map(|(_, l)| {
            Ok(Literal {
                positive: l.positive,
                predicate: l.predicate,
                arguments: l
                    .arguments
                    .iter()
                    .map(|t| term(t, substitution, 1, limits, budget, &mut nodes))
                    .collect::<Result<_, _>>()?,
            })
        })
        .collect()
}
