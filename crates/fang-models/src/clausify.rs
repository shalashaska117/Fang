// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Clausal form for the search only: negation normal form with fresh variables, Skolemization over the universal
//! variables free in each existential, and conjunctive normal form that names a disjunct by a new predicate when
//! distribution would grow past a bound. Every model of the result, restricted to the input symbols, is a model of
//! the input, so a wrong step here can only produce a model the checker rejects.

use crate::problem::{Formula, Term};
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Literal {
    Predicate(bool, u32, Vec<Term>),
    Equal(bool, Term, Term),
}

impl Literal {
    fn negated(&self) -> Literal {
        match self {
            Literal::Predicate(sign, symbol, arguments) => {
                Literal::Predicate(!sign, *symbol, arguments.clone())
            }
            Literal::Equal(sign, left, right) => Literal::Equal(!sign, left.clone(), right.clone()),
        }
    }
}

pub type Clause = Vec<Literal>;

#[derive(Debug)]
enum Nnf {
    Literal(Literal),
    True,
    False,
    And(Vec<Nnf>),
    Or(Vec<Nnf>),
    All(u32, Box<Nnf>),
    Ex(u32, Box<Nnf>),
}

/// Symbols added by the clausal form: Skolem functions after the input functions, definitions after the input
/// predicates.
pub struct Signature {
    pub functions: Vec<usize>,
    pub predicates: Vec<usize>,
}

fn rename(term: &Term, scope: &[(u32, u32)]) -> Term {
    match term {
        Term::Var(variable) => {
            let fresh = scope
                .iter()
                .rev()
                .find(|(old, _)| old == variable)
                .map(|(_, new)| *new);
            Term::Var(fresh.unwrap_or(*variable))
        }
        Term::App(symbol, arguments) => Term::App(
            *symbol,
            arguments.iter().map(|item| rename(item, scope)).collect(),
        ),
    }
}

fn nnf(formula: &Formula, positive: bool, scope: &mut Vec<(u32, u32)>, fresh: &mut u32) -> Nnf {
    let join = |children: Vec<Nnf>, conjunction: bool| -> Nnf {
        let mut kept = Vec::new();
        for child in children {
            match (child, conjunction) {
                (Nnf::True, true) | (Nnf::False, false) => {}
                (Nnf::False, true) => return Nnf::False,
                (Nnf::True, false) => return Nnf::True,
                (Nnf::And(inner), true) => kept.extend(inner),
                (Nnf::Or(inner), false) => kept.extend(inner),
                (other, _) => kept.push(other),
            }
        }
        match kept.len() {
            0 => {
                if conjunction {
                    Nnf::True
                } else {
                    Nnf::False
                }
            }
            1 => kept.pop().unwrap(),
            _ => {
                if conjunction {
                    Nnf::And(kept)
                } else {
                    Nnf::Or(kept)
                }
            }
        }
    };
    match formula {
        Formula::Atom(symbol, arguments) => Nnf::Literal(Literal::Predicate(
            positive,
            *symbol,
            arguments.iter().map(|item| rename(item, scope)).collect(),
        )),
        Formula::Equal(left, right) => Nnf::Literal(Literal::Equal(
            positive,
            rename(left, scope),
            rename(right, scope),
        )),
        Formula::Constant(value) => {
            if *value == positive {
                Nnf::True
            } else {
                Nnf::False
            }
        }
        Formula::Not(body) => nnf(body, !positive, scope, fresh),
        Formula::And(left, right) => {
            let children = vec![
                nnf(left, positive, scope, fresh),
                nnf(right, positive, scope, fresh),
            ];
            join(children, positive)
        }
        Formula::Or(left, right) => {
            let children = vec![
                nnf(left, positive, scope, fresh),
                nnf(right, positive, scope, fresh),
            ];
            join(children, !positive)
        }
        Formula::Implies(left, right) => {
            let children = vec![
                nnf(left, !positive, scope, fresh),
                nnf(right, positive, scope, fresh),
            ];
            join(children, !positive)
        }
        Formula::Forall(variable, body) | Formula::Exists(variable, body) => {
            let universal = matches!(formula, Formula::Forall(..)) == positive;
            let new = *fresh;
            *fresh += 1;
            scope.push((*variable, new));
            let inner = nnf(body, positive, scope, fresh);
            scope.pop();
            match inner {
                Nnf::True => Nnf::True,
                Nnf::False => Nnf::False,
                inner if universal => Nnf::All(new, Box::new(inner)),
                inner => Nnf::Ex(new, Box::new(inner)),
            }
        }
    }
}

fn term_variables(term: &Term, output: &mut Vec<u32>) {
    match term {
        Term::Var(variable) => {
            if !output.contains(variable) {
                output.push(*variable);
            }
        }
        Term::App(_, arguments) => arguments
            .iter()
            .for_each(|item| term_variables(item, output)),
    }
}

fn literal_variables(literal: &Literal, output: &mut Vec<u32>) {
    match literal {
        Literal::Predicate(_, _, arguments) => arguments
            .iter()
            .for_each(|item| term_variables(item, output)),
        Literal::Equal(_, left, right) => {
            term_variables(left, output);
            term_variables(right, output);
        }
    }
}

fn nnf_variables(node: &Nnf, output: &mut Vec<u32>) {
    match node {
        Nnf::Literal(literal) => literal_variables(literal, output),
        Nnf::True | Nnf::False => {}
        Nnf::And(children) | Nnf::Or(children) => children
            .iter()
            .for_each(|child| nnf_variables(child, output)),
        Nnf::All(_, body) | Nnf::Ex(_, body) => nnf_variables(body, output),
    }
}

fn substitute(term: &Term, map: &HashMap<u32, Term>) -> Term {
    match term {
        Term::Var(variable) => map.get(variable).cloned().unwrap_or(Term::Var(*variable)),
        Term::App(symbol, arguments) => Term::App(
            *symbol,
            arguments.iter().map(|item| substitute(item, map)).collect(),
        ),
    }
}

fn substitute_literal(literal: &Literal, map: &HashMap<u32, Term>) -> Literal {
    match literal {
        Literal::Predicate(sign, symbol, arguments) => Literal::Predicate(
            *sign,
            *symbol,
            arguments.iter().map(|item| substitute(item, map)).collect(),
        ),
        Literal::Equal(sign, left, right) => {
            Literal::Equal(*sign, substitute(left, map), substitute(right, map))
        }
    }
}

/// Remove quantifiers: universal variables stay as clause variables, existential ones become Skolem terms over the
/// universal variables the existential subformula depends on.
fn skolemize(
    node: Nnf,
    universals: &mut Vec<u32>,
    map: &mut HashMap<u32, Term>,
    signature: &mut Signature,
) -> Nnf {
    match node {
        Nnf::Literal(literal) => Nnf::Literal(substitute_literal(&literal, map)),
        Nnf::True | Nnf::False => node,
        Nnf::And(children) => Nnf::And(
            children
                .into_iter()
                .map(|child| skolemize(child, universals, map, signature))
                .collect(),
        ),
        Nnf::Or(children) => Nnf::Or(
            children
                .into_iter()
                .map(|child| skolemize(child, universals, map, signature))
                .collect(),
        ),
        Nnf::All(variable, body) => {
            universals.push(variable);
            let result = skolemize(*body, universals, map, signature);
            universals.pop();
            result
        }
        Nnf::Ex(variable, body) => {
            let mut occurring = Vec::new();
            nnf_variables(&body, &mut occurring);
            let mut depends = Vec::new();
            for found in occurring {
                if found == variable {
                    continue;
                }
                match map.get(&found) {
                    Some(term) => term_variables(term, &mut depends),
                    None => {
                        if !depends.contains(&found) {
                            depends.push(found);
                        }
                    }
                }
            }
            let arguments: Vec<Term> = universals
                .iter()
                .filter(|item| depends.contains(item))
                .map(|item| Term::Var(*item))
                .collect();
            let symbol = signature.functions.len() as u32;
            signature.functions.push(arguments.len());
            map.insert(variable, Term::App(symbol, arguments));
            let result = skolemize(*body, universals, map, signature);
            map.remove(&variable);
            result
        }
    }
}

/// Clauses of a quantifier-free node; a disjunct is named by a new predicate when the product would pass `bound`.
fn cnf(
    node: Nnf,
    bound: usize,
    signature: &mut Signature,
    definitions: &mut Vec<Clause>,
) -> Vec<Clause> {
    match node {
        Nnf::Literal(literal) => vec![vec![literal]],
        Nnf::True => Vec::new(),
        Nnf::False => vec![Vec::new()],
        Nnf::And(children) => children
            .into_iter()
            .flat_map(|child| cnf(child, bound, signature, definitions))
            .collect(),
        Nnf::Or(children) => {
            let mut parts: Vec<Vec<Clause>> = children
                .into_iter()
                .map(|child| cnf(child, bound, signature, definitions))
                .collect();
            parts.sort_by_key(|part| part.len());
            let mut product: Vec<Clause> = vec![Vec::new()];
            for part in parts {
                if part.is_empty() {
                    return Vec::new();
                }
                let part = if part.len() > 1 && product.len() * part.len() > bound {
                    let mut variables = Vec::new();
                    for clause in &part {
                        clause
                            .iter()
                            .for_each(|literal| literal_variables(literal, &mut variables));
                    }
                    let symbol = signature.predicates.len() as u32;
                    signature.predicates.push(variables.len());
                    let name = Literal::Predicate(
                        true,
                        symbol,
                        variables.iter().map(|item| Term::Var(*item)).collect(),
                    );
                    for clause in part {
                        let mut defined = vec![name.negated()];
                        defined.extend(clause);
                        definitions.push(defined);
                    }
                    vec![vec![name]]
                } else {
                    part
                };
                product = product
                    .iter()
                    .flat_map(|left| {
                        part.iter().map(move |right| {
                            let mut joined = left.clone();
                            joined.extend(right.iter().cloned());
                            joined
                        })
                    })
                    .collect();
            }
            product
        }
        Nnf::All(..) | Nnf::Ex(..) => unreachable!("quantifiers are removed before clausal form"),
    }
}

/// Sort, deduplicate and drop tautologies; `None` for a tautology.
pub fn simplify(mut clause: Clause) -> Option<Clause> {
    clause
        .retain(|literal| !matches!(literal, Literal::Equal(false, left, right) if left == right));
    if clause
        .iter()
        .any(|literal| matches!(literal, Literal::Equal(true, left, right) if left == right))
    {
        return None;
    }
    clause.sort();
    clause.dedup();
    for literal in &clause {
        if clause.contains(&literal.negated()) {
            return None;
        }
    }
    Some(clause)
}

/// Clausal form of closed formulas. `functions` and `predicates` are the input symbols' arities.
pub fn clausify(
    formulas: &[Formula],
    functions: &[usize],
    predicates: &[usize],
    bound: usize,
) -> (Vec<Clause>, Signature) {
    let mut signature = Signature {
        functions: functions.to_vec(),
        predicates: predicates.to_vec(),
    };
    let mut fresh = 0u32;
    let mut clauses = Vec::new();
    for formula in formulas {
        let node = nnf(formula, true, &mut Vec::new(), &mut fresh);
        let node = skolemize(node, &mut Vec::new(), &mut HashMap::new(), &mut signature);
        let mut definitions = Vec::new();
        let produced = cnf(node, bound, &mut signature, &mut definitions);
        clauses.extend(produced.into_iter().chain(definitions).filter_map(simplify));
    }
    (clauses, signature)
}
