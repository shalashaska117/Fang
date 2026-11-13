// Copyright (c) 2026 Pietro Pellegrino.
// Vampire is copyright (C) 2020 by its authors and contributors (see
// LICENSES/Vampire.AUTHORS) and their institutional affiliations. All rights reserved.
// Vampire's unifier was consulted as a reference implementation.
// See LICENSES/Vampire.txt and LICENSES/Vampire.ORIGIN for source and scope.
use crate::syntax::{Substitution, Term};
use crate::{Budget, Error, Limits};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Unifier {
    bindings: Substitution,
}

enum ResourceFailure {
    Operations,
    ExpansionNodeOverflow,
    ExpansionNodeLimit,
    ExpansionDepthLimit,
    InputNodeOverflow,
    InputNodeLimit,
    InputDepthLimit,
}

impl ResourceFailure {
    fn into_error(self) -> Error {
        let message = match self {
            Self::Operations => "operation budget exhausted",
            Self::ExpansionNodeOverflow => "unifier expansion node count overflow",
            Self::ExpansionNodeLimit => "unifier expansion node limit exceeded",
            Self::ExpansionDepthLimit => "unifier expansion depth limit exceeded",
            Self::InputNodeOverflow => "unifier input node count overflow",
            Self::InputNodeLimit => "unifier input node limit exceeded",
            Self::InputDepthLimit => "unifier input depth limit exceeded",
        };
        Error::resource(message)
    }
}

fn tick(budget: &mut Budget) -> Result<(), ResourceFailure> {
    if budget.try_tick() {
        Ok(())
    } else {
        Err(ResourceFailure::Operations)
    }
}

struct EquationStack {
    entries: Vec<(Term, Term)>,
    used: usize,
}

impl EquationStack {
    fn new(pairs: &[(Term, Term)]) -> Self {
        let mut entries = pairs.to_vec();
        entries.reverse();
        Self {
            entries,
            used: pairs.len(),
        }
    }

    fn pop(&mut self) -> Option<(Term, Term)> {
        if self.used == 0 {
            return None;
        }
        self.used -= 1;
        Some(std::mem::replace(
            &mut self.entries[self.used],
            (Term::Var(0), Term::Var(0)),
        ))
    }

    fn push(&mut self, equation: (Term, Term)) {
        if self.used < self.entries.len() {
            self.entries[self.used] = equation;
        } else {
            self.entries.push(equation);
        }
        self.used += 1;
    }
}

fn same_term(left: &Term, right: &Term) -> bool {
    match (left, right) {
        (Term::Var(a), Term::Var(b)) => a == b,
        (Term::Fun(f, a), Term::Fun(g, b)) => {
            if f != g || a.len() != b.len() {
                return false;
            }
            let mut index = 0;
            let mut equal = true;
            while index < a.len() && equal {
                equal = same_term(&a[index], &b[index]);
                index += 1;
            }
            equal
        }
        _ => false,
    }
}

fn expand(
    term: &Term,
    bindings: &Substitution,
    depth: usize,
    count: &mut usize,
    limits: &Limits,
    budget: &mut Budget,
) -> Result<Term, ResourceFailure> {
    tick(budget)?;
    *count = match count.checked_add(1) {
        Some(next) => next,
        None => return Err(ResourceFailure::ExpansionNodeOverflow),
    };
    if *count > limits.max_term_nodes {
        return Err(ResourceFailure::ExpansionNodeLimit);
    }
    if depth > limits.max_term_depth.min(64) {
        return Err(ResourceFailure::ExpansionDepthLimit);
    }
    match term {
        Term::Var(v) => match bindings.get(v) {
            Some(image) => expand(image, bindings, depth + 1, count, limits, budget),
            None => Ok(Term::Var(*v)),
        },
        Term::Fun(f, args) => {
            let mut expanded = Vec::new();
            let mut index = 0;
            while index < args.len() {
                expanded.push(expand(
                    &args[index],
                    bindings,
                    depth + 1,
                    count,
                    limits,
                    budget,
                )?);
                index += 1;
            }
            Ok(Term::Fun(*f, expanded))
        }
    }
}

fn occurs(variable: u32, term: &Term, budget: &mut Budget) -> Option<bool> {
    if !budget.try_tick() {
        return None;
    }
    match term {
        Term::Var(v) => Some(*v == variable),
        Term::Fun(_, args) => {
            let mut index = 0;
            while index < args.len() {
                match occurs(variable, &args[index], budget) {
                    None => return None,
                    Some(true) => return Some(true),
                    Some(false) => (),
                }
                index += 1;
            }
            Some(false)
        }
    }
}

impl Unifier {
    /// The state is unchanged on a mismatch or a resource error.
    pub fn unify(&mut self, pairs: &[(Term, Term)], limits: &Limits) -> Result<bool, Error> {
        self.unify_with_budget(pairs, limits, &mut Budget::new(limits.max_operations))
    }

    pub(crate) fn unify_with_budget(
        &mut self,
        pairs: &[(Term, Term)],
        limits: &Limits,
        budget: &mut Budget,
    ) -> Result<bool, Error> {
        self.unify_core(pairs, limits, budget)
            .map_err(ResourceFailure::into_error)
    }

    // This production core is the direct Rust-to-Aeneas extraction root.
    // Public wrappers only allocate the existing diagnostic strings.
    fn unify_core(
        &mut self,
        pairs: &[(Term, Term)],
        limits: &Limits,
        budget: &mut Budget,
    ) -> Result<bool, ResourceFailure> {
        validate_inputs(pairs, &self.bindings, limits, budget)?;
        let mut pending = EquationStack::new(pairs);
        let mut bindings = self.bindings.clone();
        while let Some((left, right)) = pending.pop() {
            tick(budget)?;
            let left = expand(&left, &bindings, 1, &mut 0, limits, budget)?;
            let right = expand(&right, &bindings, 1, &mut 0, limits, budget)?;
            if same_term(&left, &right) {
                continue;
            }
            match (left, right) {
                (Term::Var(a), Term::Var(b)) => {
                    // Deterministic orientation also keeps common witnesses small.
                    bindings.insert(a.max(b), Term::Var(a.min(b)));
                }
                (Term::Var(v), term) | (term, Term::Var(v)) => {
                    match occurs(v, &term, budget) {
                        Some(true) => return Ok(false),
                        Some(false) => (),
                        None => return Err(ResourceFailure::Operations),
                    }
                    bindings.insert(v, term);
                }
                (Term::Fun(f, a), Term::Fun(g, b)) => {
                    if f != g || a.len() != b.len() {
                        return Ok(false);
                    }
                    append_equations(&mut pending, a, b);
                }
            }
        }
        self.bindings = bindings;
        Ok(true)
    }

    /// Turn transitive search bindings into the certificate's simultaneous map.
    pub fn substitution(&self, limits: &Limits) -> Result<Substitution, Error> {
        self.substitution_with_budget(limits, &mut Budget::new(limits.max_operations))
    }

    pub(crate) fn substitution_with_budget(
        &self,
        limits: &Limits,
        budget: &mut Budget,
    ) -> Result<Substitution, Error> {
        self.substitution_core(limits, budget)
            .map_err(ResourceFailure::into_error)
    }

    fn substitution_core(
        &self,
        limits: &Limits,
        budget: &mut Budget,
    ) -> Result<Substitution, ResourceFailure> {
        let mut count = 0;
        let entries = self.bindings.entries();
        let mut result = Substitution::new();
        let mut index = 0;
        while index < entries.len() {
            let (variable, term) = &entries[index];
            let image = expand(term, &self.bindings, 1, &mut count, limits, budget)?;
            result.insert(*variable, image);
            index += 1;
        }
        Ok(result)
    }
}

fn validate_inputs(
    pairs: &[(Term, Term)],
    bindings: &Substitution,
    limits: &Limits,
    budget: &mut Budget,
) -> Result<(), ResourceFailure> {
    // Validate borrowed terms before any recursive copy or comparison.
    let mut input_nodes = 0;
    let mut index = 0;
    while index < pairs.len() {
        let (left, right) = &pairs[index];
        validate_term(left, limits, budget, &mut input_nodes)?;
        validate_term(right, limits, budget, &mut input_nodes)?;
        index += 1;
    }
    validate_bindings(bindings, limits, budget, &mut input_nodes)
}

fn validate_bindings(
    bindings: &Substitution,
    limits: &Limits,
    budget: &mut Budget,
    count: &mut usize,
) -> Result<(), ResourceFailure> {
    let entries = bindings.entries();
    let mut index = 0;
    while index < entries.len() {
        validate_term(&entries[index].1, limits, budget, count)?;
        index += 1;
    }
    Ok(())
}

fn append_equations(pending: &mut EquationStack, mut left: Vec<Term>, mut right: Vec<Term>) {
    // Callers have checked equal arity. Reverse insertion preserves argument order.
    let mut index = left.len();
    while index > 0 {
        index -= 1;
        let a = std::mem::replace(&mut left[index], Term::Var(0));
        let b = std::mem::replace(&mut right[index], Term::Var(0));
        pending.push((a, b));
    }
}

fn validate_term(
    term: &Term,
    limits: &Limits,
    budget: &mut Budget,
    count: &mut usize,
) -> Result<(), ResourceFailure> {
    validate_term_at_depth(term, 1, limits, budget, count)
}

fn validate_term_at_depth(
    term: &Term,
    depth: usize,
    limits: &Limits,
    budget: &mut Budget,
    count: &mut usize,
) -> Result<(), ResourceFailure> {
    tick(budget)?;
    *count = match count.checked_add(1) {
        Some(next) => next,
        None => return Err(ResourceFailure::InputNodeOverflow),
    };
    if *count > limits.max_term_nodes {
        return Err(ResourceFailure::InputNodeLimit);
    }
    // Guard before recursion: even a caller-built deep term uses at most 65 frames.
    if depth > limits.max_term_depth.min(64) {
        return Err(ResourceFailure::InputDepthLimit);
    }
    match term {
        Term::Var(_) => Ok(()),
        Term::Fun(_, args) => {
            let mut index = 0;
            while index < args.len() {
                validate_term_at_depth(&args[index], depth + 1, limits, budget, count)?;
                index += 1;
            }
            Ok(())
        }
    }
}
