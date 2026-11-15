// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use super::*;

impl Search<'_> {
    pub(super) fn unit_join_redundant(&mut self, original: Id, current: Id) -> bool {
        if !self.options.unit_ground_joinability
            || !self.unit_equality_problem
            || !self.options.ordering
            || self.options.term_order != crate::kbo::OrderKind::Kbo
            || self.options.kbo_weights != crate::weights::Scheme::Uniform
        {
            return false;
        }
        // Only critical-pair conclusions are considered. Inputs remain available.
        let Rule::Para { source, target, .. } = self.clauses[original as usize].rule else {
            return false;
        };
        let positive_unit = |id: Id| {
            matches!(
                self.clauses[id as usize].lits.as_ref(),
                [Lit {
                    positive: true,
                    atom: Atom::Eq(..)
                }]
            )
        };
        if !positive_unit(source) || !positive_unit(target) || !positive_unit(current) {
            return false;
        }
        let Atom::Eq(left, right) = self.clauses[current as usize].lits[0].atom else {
            return false;
        };
        let equations: Vec<_> = self
            .units
            .iter()
            .rev()
            .take(256)
            .filter_map(|&id| {
                let clause = &self.clauses[id as usize];
                if clause.state != State::Active {
                    return None;
                }
                match clause.lits.as_ref() {
                    [
                        Lit {
                            positive: true,
                            atom: Atom::Eq(a, b),
                        },
                    ] => Some((*a, *b)),
                    _ => None,
                }
            })
            .take(64)
            .collect();
        if equations.is_empty() {
            return false;
        }
        self.stats.unit_join_attempts += 1;
        match crate::unit_join::joinable(
            &self.bank,
            left,
            right,
            &equations,
            self.order.symbol_ranks(),
            self.limits.deadline,
        ) {
            Ok(answer) => answer,
            Err(reason) => {
                self.stats.unit_join_refused += 1;
                if reason == crate::unit_join::Refusal::Deadline {
                    self.interrupted = Some(Stop::Time);
                }
                false
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fang::syntax::Term;
    use fang_equality_inference_core::{Atom as InputAtom, Literal};

    fn v(x: u32) -> Term {
        Term::Var(x)
    }
    fn c(x: u32) -> Term {
        Term::Fun(x, vec![])
    }
    fn f(a: Term, b: Term) -> Term {
        Term::Fun(2, vec![a, b])
    }
    fn eq(positive: bool, a: Term, b: Term) -> Vec<Literal> {
        vec![Literal {
            positive,
            atom: InputAtom::Equal(a, b),
        }]
    }
    fn inputs() -> Vec<Vec<Literal>> {
        vec![
            eq(true, f(v(0), v(1)), f(v(1), v(0))),
            eq(true, f(f(v(0), v(1)), v(2)), f(v(0), f(v(1), v(2)))),
            eq(true, f(v(0), f(v(1), v(2))), f(v(1), f(v(0), v(2)))),
            eq(false, c(0), c(1)),
        ]
    }

    #[test]
    fn ac_critical_pairs_use_the_bounded_redundancy_test_without_a_false_proof() {
        let input = inputs();
        let mut options = Options::preset("step5").unwrap();
        options.index = true;
        options.unit_ground_joinability = true;
        options.given_limit = Some(30);
        let mut search = Search::new(&input, &[0, 0, 2], &[], &options, Limits::default()).unwrap();
        let result = search.run();
        assert!(!matches!(result, Stop::Proof(_)));
        assert!(search.stats.unit_join_attempts > 0);
        assert!(search.stats.unit_join_redundant > 0, "{:?}", search.stats);
    }

    #[test]
    fn mixed_clause_inputs_and_alternative_orders_do_not_use_unit_redundancy() {
        for mode in 0..3 {
            let mut input = inputs();
            let mut options = Options::preset("step5").unwrap();
            options.index = true;
            options.unit_ground_joinability = true;
            options.given_limit = Some(8);
            match mode {
                0 => input.push(vec![input[0][0].clone(), input[3][0].clone()]),
                1 => options.term_order = crate::kbo::OrderKind::Lpo,
                _ => options.kbo_weights = crate::weights::Scheme::ConstantHeavy,
            }
            let mut search =
                Search::new(&input, &[0, 0, 2], &[], &options, Limits::default()).unwrap();
            search.run();
            assert_eq!(search.stats.unit_join_attempts, 0);
        }
    }
}
