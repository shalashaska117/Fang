// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Flat clauses: every literal is `p(x1..xk)`, `f(x1..xk) = y` or `x = y` over clause variables, possibly negated.
//! A nested term `t` in clause `C[t]` becomes a fresh variable `z` with the extra literal `t != z`; repeated subterms
//! share one variable. A negative `x != y` is removed by identifying `x` and `y`.

use crate::clausify::{Clause, Literal};
use crate::problem::Term;
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Flat {
    Predicate {
        positive: bool,
        symbol: u32,
        arguments: Vec<u32>,
    },
    Function {
        positive: bool,
        symbol: u32,
        arguments: Vec<u32>,
        value: u32,
    },
    Same {
        positive: bool,
        left: u32,
        right: u32,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FlatClause {
    pub literals: Vec<Flat>,
    pub variables: u32,
}

struct Builder {
    variables: HashMap<u32, u32>,
    count: u32,
    cache: HashMap<(u32, Vec<u32>), u32>,
    literals: Vec<Flat>,
}

impl Builder {
    fn variable(&mut self, source: u32) -> u32 {
        let count = &mut self.count;
        *self.variables.entry(source).or_insert_with(|| {
            *count += 1;
            *count - 1
        })
    }

    fn fresh(&mut self) -> u32 {
        self.count += 1;
        self.count - 1
    }

    fn term(&mut self, term: &Term) -> u32 {
        match term {
            Term::Var(source) => self.variable(*source),
            Term::App(symbol, arguments) => {
                let arguments: Vec<u32> = arguments.iter().map(|item| self.term(item)).collect();
                if let Some(&value) = self.cache.get(&(*symbol, arguments.clone())) {
                    return value;
                }
                let value = self.fresh();
                self.cache.insert((*symbol, arguments.clone()), value);
                self.literals.push(Flat::Function {
                    positive: false,
                    symbol: *symbol,
                    arguments,
                    value,
                });
                value
            }
        }
    }
}

fn find(parent: &mut [u32], item: u32) -> u32 {
    let mut root = item;
    while parent[root as usize] != root {
        root = parent[root as usize];
    }
    let mut current = item;
    while parent[current as usize] != root {
        let next = parent[current as usize];
        parent[current as usize] = root;
        current = next;
    }
    root
}

/// The flat form of a clause, or `None` when it became a tautology.
pub fn flatten(clause: &Clause) -> Option<FlatClause> {
    let mut builder = Builder {
        variables: HashMap::new(),
        count: 0,
        cache: HashMap::new(),
        literals: Vec::new(),
    };
    let mut main = Vec::new();
    for literal in clause {
        let flat = match literal {
            Literal::Predicate(positive, symbol, arguments) => Flat::Predicate {
                positive: *positive,
                symbol: *symbol,
                arguments: arguments.iter().map(|item| builder.term(item)).collect(),
            },
            Literal::Equal(positive, left, right) => match (left, right) {
                (Term::Var(a), Term::Var(b)) => {
                    let (left, right) = (builder.variable(*a), builder.variable(*b));
                    Flat::Same {
                        positive: *positive,
                        left,
                        right,
                    }
                }
                (Term::App(symbol, arguments), other)
                | (other @ Term::Var(_), Term::App(symbol, arguments)) => {
                    let value = builder.term(other);
                    let arguments: Vec<u32> =
                        arguments.iter().map(|item| builder.term(item)).collect();
                    Flat::Function {
                        positive: *positive,
                        symbol: *symbol,
                        arguments,
                        value,
                    }
                }
            },
        };
        main.push(flat);
    }
    let mut literals = builder.literals;
    literals.extend(main);
    // Identify the two sides of every negative variable equation.
    let mut parent: Vec<u32> = (0..builder.count).collect();
    literals.retain(|literal| match literal {
        Flat::Same {
            positive: false,
            left,
            right,
        } => {
            let (a, b) = (find(&mut parent, *left), find(&mut parent, *right));
            if a != b {
                parent[b as usize] = a;
            }
            false
        }
        _ => true,
    });
    let mut renumber: HashMap<u32, u32> = HashMap::new();
    let mut next = 0u32;
    let mut map = |item: u32, parent: &mut Vec<u32>| -> u32 {
        let root = find(parent, item);
        *renumber.entry(root).or_insert_with(|| {
            next += 1;
            next - 1
        })
    };
    let mut output = Vec::new();
    for literal in literals {
        let literal = match literal {
            Flat::Predicate {
                positive,
                symbol,
                arguments,
            } => Flat::Predicate {
                positive,
                symbol,
                arguments: arguments
                    .into_iter()
                    .map(|item| map(item, &mut parent))
                    .collect(),
            },
            Flat::Function {
                positive,
                symbol,
                arguments,
                value,
            } => {
                let arguments = arguments
                    .into_iter()
                    .map(|item| map(item, &mut parent))
                    .collect();
                Flat::Function {
                    positive,
                    symbol,
                    arguments,
                    value: map(value, &mut parent),
                }
            }
            Flat::Same {
                positive,
                left,
                right,
            } => {
                let (left, right) = (map(left, &mut parent), map(right, &mut parent));
                if left == right {
                    return None;
                }
                Flat::Same {
                    positive,
                    left,
                    right,
                }
            }
        };
        output.push(literal);
    }
    output.sort();
    output.dedup();
    for literal in &output {
        let opposite = match literal.clone() {
            Flat::Predicate {
                positive,
                symbol,
                arguments,
            } => Flat::Predicate {
                positive: !positive,
                symbol,
                arguments,
            },
            Flat::Function {
                positive,
                symbol,
                arguments,
                value,
            } => Flat::Function {
                positive: !positive,
                symbol,
                arguments,
                value,
            },
            Flat::Same {
                positive,
                left,
                right,
            } => Flat::Same {
                positive: !positive,
                left,
                right,
            },
        };
        if output.contains(&opposite) {
            return None;
        }
    }
    Some(FlatClause {
        literals: output,
        variables: next,
    })
}

fn literal_variables(literal: &Flat) -> Vec<u32> {
    let mut output = match literal {
        Flat::Predicate { arguments, .. } => arguments.clone(),
        Flat::Function {
            arguments, value, ..
        } => {
            let mut all = arguments.clone();
            all.push(*value);
            all
        }
        Flat::Same { left, right, .. } => vec![*left, *right],
    };
    output.sort_unstable();
    output.dedup();
    output
}

fn renumbered(literals: Vec<Flat>) -> FlatClause {
    let mut map: HashMap<u32, u32> = HashMap::new();
    let mut next = 0u32;
    let mut rename = |item: u32| -> u32 {
        *map.entry(item).or_insert_with(|| {
            next += 1;
            next - 1
        })
    };
    let literals = literals
        .into_iter()
        .map(|literal| match literal {
            Flat::Predicate {
                positive,
                symbol,
                arguments,
            } => Flat::Predicate {
                positive,
                symbol,
                arguments: arguments.into_iter().map(&mut rename).collect(),
            },
            Flat::Function {
                positive,
                symbol,
                arguments,
                value,
            } => {
                let arguments = arguments.into_iter().map(&mut rename).collect();
                Flat::Function {
                    positive,
                    symbol,
                    arguments,
                    value: rename(value),
                }
            }
            Flat::Same {
                positive,
                left,
                right,
            } => Flat::Same {
                positive,
                left: rename(left),
                right: rename(right),
            },
        })
        .collect();
    FlatClause {
        literals,
        variables: next,
    }
}

/// Split a clause along a variable to lower the number of variables per clause. For a variable `x`, the literals
/// with `x` form `A`, the others `B`, sharing the variables `s`; the clause `A | B` becomes `A | p(s)` and
/// `~p(s) | B` with a new predicate `p`. Every model of the two restricts to a model of the original, and a model of
/// the original extends to one of the two with `p(s)` meaning that `A` fails for some values of its own variables.
pub fn split(clause: FlatClause, predicates: &mut Vec<usize>, output: &mut Vec<FlatClause>) {
    if clause.variables <= 3 || clause.literals.len() < 2 {
        output.push(clause);
        return;
    }
    let variables: Vec<Vec<u32>> = clause.literals.iter().map(literal_variables).collect();
    let mut best: Option<(usize, usize, u32)> = None;
    for candidate in 0..clause.variables {
        let mut left = Vec::new();
        let mut right = Vec::new();
        let mut others = 0;
        for found in &variables {
            if found.contains(&candidate) {
                left.extend(found.iter().copied());
            } else {
                right.extend(found.iter().copied());
                others += 1;
            }
        }
        if others == 0 {
            continue;
        }
        left.sort_unstable();
        left.dedup();
        right.sort_unstable();
        right.dedup();
        let shared = left.iter().filter(|item| right.contains(item)).count();
        let larger = left.len().max(right.len().max(shared));
        if larger >= clause.variables as usize {
            continue;
        }
        let score = (larger, left.len() + right.len());
        if best.is_none_or(|(size, total, _)| score < (size, total)) {
            best = Some((score.0, score.1, candidate));
        }
    }
    let Some((_, _, chosen)) = best else {
        output.push(clause);
        return;
    };
    let mut first = Vec::new();
    let mut second = Vec::new();
    let mut left_variables = Vec::new();
    let mut right_variables = Vec::new();
    for (literal, found) in clause.literals.into_iter().zip(&variables) {
        if found.contains(&chosen) {
            left_variables.extend(found.iter().copied());
            first.push(literal);
        } else {
            right_variables.extend(found.iter().copied());
            second.push(literal);
        }
    }
    let mut shared: Vec<u32> = left_variables
        .into_iter()
        .filter(|item| right_variables.contains(item))
        .collect();
    shared.sort_unstable();
    shared.dedup();
    let symbol = predicates.len() as u32;
    predicates.push(shared.len());
    first.push(Flat::Predicate {
        positive: true,
        symbol,
        arguments: shared.clone(),
    });
    second.push(Flat::Predicate {
        positive: false,
        symbol,
        arguments: shared,
    });
    split(renumbered(first), predicates, output);
    split(renumbered(second), predicates, output);
}
