// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Evaluation of the original statements over a found model, for tests and the harness. It is not part of any
//! result: the Lean checker decides.

use crate::problem::{Formula, Term};
use crate::search::Model;

/// Node evaluations a self-check may spend; a larger check is skipped, not failed.
pub const STEP_LIMIT: u64 = 200_000_000;

struct Evaluator<'a> {
    model: &'a Model,
    steps: u64,
}

impl Evaluator<'_> {
    fn term(&mut self, valuation: &[(u32, u32)], value: &Term) -> u32 {
        match value {
            Term::Var(variable) => valuation
                .iter()
                .rev()
                .find(|(name, _)| name == variable)
                .map(|(_, value)| *value)
                .unwrap_or(0),
            Term::App(symbol, arguments) => {
                let size = self.model.size as usize;
                let mut index = 0usize;
                for argument in arguments {
                    index = index * size + self.term(valuation, argument) as usize;
                }
                self.model.functions[*symbol as usize][index]
            }
        }
    }

    /// The truth value, or `None` once the step limit is reached.
    fn holds(&mut self, valuation: &mut Vec<(u32, u32)>, formula: &Formula) -> Option<bool> {
        self.steps += 1;
        if self.steps > STEP_LIMIT {
            return None;
        }
        Some(match formula {
            Formula::Atom(symbol, arguments) => {
                let size = self.model.size as usize;
                let mut index = 0usize;
                for argument in arguments {
                    index = index * size + self.term(valuation, argument) as usize;
                }
                self.model.predicates[*symbol as usize][index]
            }
            Formula::Equal(left, right) => {
                self.term(valuation, left) == self.term(valuation, right)
            }
            Formula::Constant(value) => *value,
            Formula::Not(body) => !self.holds(valuation, body)?,
            Formula::And(left, right) => {
                self.holds(valuation, left)? && self.holds(valuation, right)?
            }
            Formula::Or(left, right) => {
                self.holds(valuation, left)? || self.holds(valuation, right)?
            }
            Formula::Implies(left, right) => {
                !self.holds(valuation, left)? || self.holds(valuation, right)?
            }
            Formula::Forall(variable, body) | Formula::Exists(variable, body) => {
                let universal = matches!(formula, Formula::Forall(..));
                for value in 0..self.model.size {
                    valuation.push((*variable, value));
                    let result = self.holds(valuation, body);
                    valuation.pop();
                    if result? != universal {
                        return Some(!universal);
                    }
                }
                universal
            }
        })
    }
}

/// Every formula holds and the distinct objects are pairwise different. `Ok(false)` when the evaluation would pass
/// `STEP_LIMIT` node evaluations and was skipped.
pub fn check(model: &Model, formulas: &[Formula], objects: &[u32]) -> Result<bool, String> {
    let mut evaluator = Evaluator { model, steps: 0 };
    for (index, formula) in formulas.iter().enumerate() {
        match evaluator.holds(&mut Vec::new(), formula) {
            Some(true) => {}
            Some(false) => return Err(format!("formula {index} is false in the model")),
            None => return Ok(false),
        }
    }
    let values: Vec<u32> = objects
        .iter()
        .map(|&object| model.functions[object as usize][0])
        .collect();
    for (left, first) in values.iter().enumerate() {
        if values[left + 1..].contains(first) {
            return Err("two distinct objects share an element".into());
        }
    }
    Ok(true)
}
