// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
#![forbid(unsafe_code)]

//! Finite model search for Fang. The input is read with the checkers' frontend, clausified and flattened for the
//! search only, grounded for one domain size at a time and solved with a CDCL solver. A found model is written as the
//! certificate the Lean model checker reads; it is a candidate until that checker accepts it.

pub mod certificate;
pub mod clausify;
pub mod evaluate;
pub mod flatten;
pub mod problem;
pub mod sat;
pub mod search;

use problem::{Formula, Problem, Task, TaskError, Term};
use std::time::Instant;

pub struct Settings {
    pub from: u32,
    pub to: u32,
    pub deadline: Instant,
    /// Bytes the ground problem and the learned clauses may take.
    pub memory_bytes: usize,
    /// Distribution in the clausal form may create at most this many clauses before a disjunct is named.
    pub distribution_bound: usize,
    /// Evaluate the original formulas on a found model before writing it.
    pub self_check: bool,
    /// Split flat clauses to lower their number of variables.
    pub split: bool,
    /// Ground terms over the constants named by new constants for the symmetry breaking.
    pub symmetry_terms: usize,
    /// Largest arity of the function symbols applied to constants in those terms.
    pub symmetry_arity: usize,
    /// Conflicts a domain size gets before the next size is tried; it doubles on every pass.
    pub initial_conflicts: u64,
    /// Print the search's attempts on standard error.
    pub trace: bool,
    /// Break the symmetry in each inferred sort separately.
    pub sorts: bool,
}

impl Settings {
    pub fn new(deadline: Instant) -> Self {
        Settings {
            from: 1,
            to: 64,
            deadline,
            memory_bytes: 1 << 30,
            distribution_bound: 32,
            self_check: false,
            split: true,
            symmetry_terms: 16,
            symmetry_arity: 4,
            initial_conflicts: 1000,
            trace: false,
            sorts: true,
        }
    }
}

#[derive(Debug)]
pub enum Found {
    /// The certificate text, its domain size and, for a goal task, the goal's bundle item.
    Certificate {
        size: u32,
        text: String,
        item: Option<(usize, usize)>,
        /// The self-check evaluated every original formula on the model (false when it was not asked for or passed
        /// its step limit).
        self_checked: bool,
    },
    /// No model: every size up to `last` was refuted, or the search stopped at `size`.
    Exhausted {
        last: u32,
    },
    /// All domains from one through the function-free small-model bound were
    /// exhausted. This is an unverified search outcome, not a refutation.
    FunctionFreeExhausted {
        last: u32,
    },
    Stopped {
        size: u32,
        reason: &'static str,
    },
}

#[derive(Debug)]
pub enum FindError {
    Task(TaskError),
    /// The model failed the evaluation of the original formulas; a producer fault.
    SelfCheck(String),
}

/// A universal, function-free clause set has a model on the interpretations of
/// its constants (or any one element when there are no constants). Restricting
/// predicates to that subdomain preserves every universal clause, including
/// equality. Count Skolem constants too, and refuse the bound as soon as any
/// active function has arguments. This bounds candidate search, not acceptance.
fn function_free_bound(signature: &search::Signature) -> Option<u32> {
    let mut constants = 0u32;
    for (&arity, &active) in signature.functions.iter().zip(&signature.active_functions) {
        if !active {
            continue;
        }
        if arity != 0 {
            return None;
        }
        constants = constants.checked_add(1)?;
    }
    Some(constants.max(1))
}

/// Search a model for the task.
pub fn find(problem: &Problem, task: Task, settings: &Settings) -> Result<Found, FindError> {
    let (formulas, item) = problem::task_formulas(problem, task).map_err(FindError::Task)?;
    let mut constrained = formulas.clone();
    for (index, &left) in problem.objects.iter().enumerate() {
        for &right in &problem.objects[index + 1..] {
            constrained.push(Formula::Not(Box::new(Formula::Equal(
                Term::App(left, Vec::new()),
                Term::App(right, Vec::new()),
            ))));
        }
    }
    let function_arities: Vec<usize> = problem
        .functions
        .iter()
        .map(|symbol| symbol.arity)
        .collect();
    let predicate_arities: Vec<usize> = problem
        .predicates
        .iter()
        .map(|symbol| symbol.arity)
        .collect();
    let (clauses, mut added) = clausify::clausify(
        &constrained,
        &function_arities,
        &predicate_arities,
        settings.distribution_bound,
    );
    let mut flat: Vec<flatten::FlatClause> = Vec::new();
    for clause in clauses.iter().filter_map(flatten::flatten) {
        if settings.split {
            flatten::split(clause, &mut added.predicates, &mut flat);
        } else {
            flat.push(clause);
        }
    }
    let (used_functions, used_predicates) = problem::used_symbols(problem);
    let active = |symbol: usize| {
        symbol >= function_arities.len() || used_functions.contains(&(symbol as u32))
    };
    // Name ground terms over the constants by new constants, so the least-number symmetry reaches them too.
    let mut named: Vec<u32> = (0..added.functions.len())
        .filter(|&symbol| added.functions[symbol] == 0 && active(symbol))
        .map(|symbol| symbol as u32)
        .collect();
    let operators: Vec<(u32, usize)> = (0..added.functions.len())
        .filter(|&symbol| {
            (1..=settings.symmetry_arity).contains(&added.functions[symbol]) && active(symbol)
        })
        .map(|symbol| (symbol as u32, added.functions[symbol]))
        .collect();
    let mut generated = 0;
    'naming: for _ in 0..2 {
        let base = named.clone();
        for &(operator, arity) in &operators {
            let mut tuples: Vec<Vec<u32>> = vec![Vec::new()];
            for _ in 0..arity {
                tuples = tuples
                    .iter()
                    .flat_map(|prefix| {
                        base.iter().map(move |&item| {
                            let mut tuple = prefix.clone();
                            tuple.push(item);
                            tuple
                        })
                    })
                    .take(settings.symmetry_terms + 1)
                    .collect();
            }
            for tuple in tuples {
                if generated >= settings.symmetry_terms {
                    break 'naming;
                }
                let symbol = added.functions.len() as u32;
                added.functions.push(0);
                let mut literals: Vec<flatten::Flat> = tuple
                    .iter()
                    .enumerate()
                    .map(|(position, &constant)| flatten::Flat::Function {
                        positive: false,
                        symbol: constant,
                        arguments: Vec::new(),
                        value: position as u32,
                    })
                    .collect();
                let value = tuple.len() as u32;
                literals.push(flatten::Flat::Function {
                    positive: false,
                    symbol,
                    arguments: Vec::new(),
                    value,
                });
                literals.push(flatten::Flat::Function {
                    positive: true,
                    symbol: operator,
                    arguments: (0..tuple.len() as u32).collect(),
                    value,
                });
                flat.push(flatten::FlatClause {
                    literals,
                    variables: value + 1,
                });
                named.push(symbol);
                generated += 1;
            }
        }
    }
    let mut signature = search::Signature {
        active_functions: (0..added.functions.len())
            .map(|symbol| {
                symbol >= function_arities.len() || used_functions.contains(&(symbol as u32))
            })
            .collect(),
        active_predicates: (0..added.predicates.len())
            .map(|symbol| {
                symbol >= predicate_arities.len() || used_predicates.contains(&(symbol as u32))
            })
            .collect(),
        functions: added.functions,
        predicates: added.predicates,
        value_sorts: Vec::new(),
    };
    if settings.sorts {
        signature.value_sorts = search::infer_sorts(&signature, &flat);
    }
    let bound = function_free_bound(&signature);
    let to = bound.map_or(settings.to, |bound| {
        // An explicit lower bound can request a larger domain. Try that size,
        // while still avoiding a scan through all larger sizes on exhaustion.
        settings.to.min(bound.max(settings.from))
    });
    if settings.trace && to < settings.to {
        eprintln!("trace: function-free clauses cap candidate search at domain {to}");
    }
    let options = search::Options {
        initial_conflicts: settings.initial_conflicts,
        trace: settings.trace,
        from: settings.from,
        to,
        deadline: settings.deadline,
        literal_budget: settings.memory_bytes / 24,
        memory_bytes: settings.memory_bytes as u64 / 4 * 3,
    };
    Ok(match search::search(&signature, &flat, &options) {
        search::Search::Model(model) => {
            let self_checked = settings.self_check
                && evaluate::check(&model, &formulas, &problem.objects)
                    .map_err(FindError::SelfCheck)?;
            let text = certificate::render(problem, &model, &used_functions, &used_predicates);
            Found::Certificate {
                size: model.size,
                text,
                item,
                self_checked,
            }
        }
        search::Search::Exhausted { last }
            if settings.from <= 1 && bound.is_some_and(|bound| last >= bound) =>
        {
            Found::FunctionFreeExhausted { last }
        }
        search::Search::Exhausted { last } => Found::Exhausted { last },
        search::Search::Stopped { size, reason } => Found::Stopped { size, reason },
    })
}
