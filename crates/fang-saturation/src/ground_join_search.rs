// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use super::*;
use crate::ground_join::{self, Bounds, Equation, Refusal};

impl Search<'_> {
    pub(super) fn ground_join_inputs(&mut self) -> Option<Id> {
        // Bound the scan independently of the total stored-record count. A
        // refused shortcut leaves the ordinary saturation search available.
        if self.clauses.len() > 65_536 || self.options.max_rewrites == 0 {
            return None;
        }
        let mut equations = vec![];
        let mut goals = vec![];
        for (index, record) in self.clauses.iter().enumerate() {
            if record.vars != 0 || record.lits.len() != 1 {
                continue;
            }
            let literal = record.lits[0];
            let Atom::Eq(left, right) = literal.atom else {
                continue;
            };
            let equation = Equation {
                clause: index as Id,
                left,
                right,
            };
            if literal.positive {
                equations.push(equation);
            } else {
                goals.push(equation);
            }
        }
        let bounds = Bounds {
            proof_steps: (self.options.max_rewrites as usize).min(4096),
            ..Bounds::default()
        };
        let plan =
            match ground_join::find(&self.bank, &equations, &goals, bounds, self.limits.deadline) {
                Ok(Some(plan)) => plan,
                Err(Refusal::Deadline) => {
                    self.interrupted = Some(Stop::Time);
                    return None;
                }
                _ => return None,
            };
        let mut current = plan.target;
        for step in plan.steps {
            if let Some(stop) = self.over_limits() {
                self.interrupted = Some(stop);
                return None;
            }
            let rule = Rule::Para {
                source: step.source,
                pivot: 0,
                reverse: step.reverse,
                target: current,
                pos: Pos {
                    literal: 0,
                    root: Root::Left,
                    path: step.path,
                },
            };
            if !self.bind_rule(&rule) {
                self.binds.clear();
                return None;
            }
            let (literals, _) = self.conclude(&rule, false);
            self.binds.clear();
            current = self.push_simplified(literals, rule, current)?;
            self.stats.forward_rewrites += 1;
        }
        if let Some(stop) = self.over_limits() {
            self.interrupted = Some(stop);
            return None;
        }
        let rule = Rule::EqRes {
            parent: current,
            pivot: 0,
        };
        if !self.bind_rule(&rule) {
            self.binds.clear();
            return None;
        }
        let (literals, _) = self.conclude(&rule, false);
        self.binds.clear();
        if !literals.is_empty() {
            return None;
        }
        let empty = self.push_simplified(literals, rule, current)?;
        self.stats.equality_resolutions += 1;
        Some(empty)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fang::syntax::Term;
    use fang_equality_inference_core::{Atom as InputAtom, Literal};

    fn a() -> Term {
        Term::Fun(0, vec![])
    }
    fn b() -> Term {
        Term::Fun(1, vec![])
    }
    fn f(term: Term) -> Term {
        Term::Fun(2, vec![term])
    }
    fn eq(positive: bool, left: Term, right: Term) -> Vec<Literal> {
        vec![Literal {
            positive,
            atom: InputAtom::Equal(left, right),
        }]
    }

    #[test]
    fn ground_congruence_emits_existing_checked_rules_before_saturation() {
        let clauses = vec![eq(true, a(), b()), eq(false, f(f(a())), f(f(b())))];
        let mut options = Options::preset("step1").unwrap();
        options.ground_joinability = true;
        options.given_limit = Some(1);
        let mut search =
            Search::new(&clauses, &[0, 0, 1], &[], &options, Limits::default()).unwrap();
        let Stop::Proof(empty) = search.run() else {
            panic!("ground contradiction")
        };
        assert_eq!(search.stats.given, 0);
        assert!(search.stats.forward_rewrites > 0);
        let certificate = search.certificate(empty, 1 << 20).unwrap();
        assert_eq!(certificate.unchecked, 0);
        assert!(!certificate.text.is_empty());
        assert_eq!(search.run(), Stop::Proof(empty));
    }

    #[test]
    fn zero_given_or_stored_limits_are_not_bypassed() {
        let clauses = vec![eq(true, a(), b()), eq(false, f(a()), f(b()))];
        for stored in [false, true] {
            let mut options = Options::preset("step1").unwrap();
            options.ground_joinability = true;
            if stored {
                options.max_stored = Some(2);
            } else {
                options.given_limit = Some(0);
            }
            let mut search =
                Search::new(&clauses, &[0, 0, 1], &[], &options, Limits::default()).unwrap();
            let expected = if stored {
                Stop::StoredLimit
            } else {
                Stop::GivenLimit
            };
            assert_eq!(search.run(), expected);
            assert_eq!(search.run(), expected);
            assert_eq!(search.clauses.len(), 2);
        }
    }

    #[test]
    fn nonground_equations_and_multi_literal_clauses_cannot_be_used_as_units() {
        let mut clauses = vec![eq(true, f(Term::Var(0)), a()), eq(false, f(b()), a())];
        let mut options = Options::preset("step1").unwrap();
        options.ground_joinability = true;
        let mut search =
            Search::new(&clauses, &[0, 0, 1], &[], &options, Limits::default()).unwrap();
        assert!(search.ground_join_inputs().is_none());
        clauses[0] = vec![
            eq(true, f(b()), a())[0].clone(),
            eq(true, a(), b())[0].clone(),
        ];
        let mut search =
            Search::new(&clauses, &[0, 0, 1], &[], &options, Limits::default()).unwrap();
        assert!(search.ground_join_inputs().is_none());
    }
}
