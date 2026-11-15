// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use super::*;

impl Search<'_> {
    fn connected_target_image(
        &mut self,
        target: Id,
        at: TermId,
        sigma: &Sigma,
        depth: usize,
    ) -> Option<TermId> {
        if depth > 64 || self.bank.weight(at) > 4096 {
            return None;
        }
        match self.bank.head(at) {
            Head::Var(x) => {
                let key = self
                    .certificate_var(target, x)
                    .checked_mul(2)?
                    .checked_add(1)?;
                sigma
                    .binary_search_by_key(&key, |&(k, _)| k)
                    .ok()
                    .map(|i| sigma[i].1)
            }
            Head::Sym(symbol) => {
                let args = self.bank.args(at).to_vec();
                let args = args
                    .into_iter()
                    .map(|arg| self.connected_target_image(target, arg, sigma, depth + 1))
                    .collect::<Option<Vec<_>>>()?;
                Some(self.bank.app(symbol, &args))
            }
        }
    }

    pub(super) fn connected_redundant(&mut self, id: Id) -> bool {
        if !self.options.connectedness
            || !self.unit_equality_problem
            || !self.options.ordering
            || self.options.term_order != crate::kbo::OrderKind::Kbo
            || self.options.kbo_weights != crate::weights::Scheme::Uniform
        {
            return false;
        }
        let rule = self.clauses[id as usize].rule.clone();
        let Rule::Para {
            source,
            target,
            ref pos,
            ..
        } = rule
        else {
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
        if !positive_unit(id) || !positive_unit(source) || !positive_unit(target) {
            return false;
        }
        let Atom::Eq(a, b) = self.clauses[target as usize].lits[0].atom else {
            return false;
        };
        let peak = match pos.root {
            Root::Left => a,
            Root::Right => b,
            _ => return false,
        };
        // Reconstruct the original conclusion before cleanup can rename variables.
        if !self.bind_rule(&rule) {
            self.binds.clear();
            return false;
        }
        let (out, sigma) = self.conclude(&rule, true);
        self.binds.clear();
        if out.as_slice() != self.clauses[id as usize].lits.as_ref() {
            return false;
        }
        let Some(sigma) = sigma else { return false };
        let Some(peak) = self.connected_target_image(target, peak, &sigma, 0) else {
            return false;
        };
        let Atom::Eq(left, right) = out[0].atom else {
            return false;
        };
        let equations: Vec<_> = self
            .units
            .iter()
            .rev()
            .take(256)
            .filter_map(|&other| {
                let record = &self.clauses[other as usize];
                if record.state != State::Active {
                    return None;
                }
                match record.lits.as_ref() {
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
        self.stats.connected_attempts += 1;
        match crate::unit_join::connected::connected(
            &self.bank,
            left,
            right,
            peak,
            &equations,
            self.order.symbol_ranks(),
            self.limits.deadline,
        ) {
            Ok(answer) => answer,
            Err(reason) => {
                self.stats.connected_refused += 1;
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

    #[test]
    fn inference_local_deletion_keeps_the_global_duplicate_cache_clear() {
        let c = |x| Term::Fun(x, vec![]);
        let h = |x| Term::Fun(4, vec![x]);
        let eq = |a, b| {
            vec![Literal {
                positive: true,
                atom: InputAtom::Equal(a, b),
            }]
        };
        // Constant b has higher precedence than a and c, so the joining path rises.
        let input = vec![
            eq(h(c(3)), c(0)),
            eq(h(c(3)), c(1)),
            eq(c(0), c(2)),
            eq(c(2), c(1)),
        ];
        let mut options = Options::preset("step3").unwrap();
        options.connectedness = true;
        let mut search =
            Search::new(&input, &[0, 0, 0, 0, 1], &[], &options, Limits::default()).unwrap();
        assert_eq!(search.clauses.len(), 4);
        for id in [2, 3] {
            search.clauses[id].state = State::Active;
        }
        search.units = vec![2, 3];
        let rule = Rule::Para {
            source: 0,
            pivot: 0,
            reverse: false,
            target: 1,
            pos: Pos {
                literal: 0,
                root: Root::Left,
                path: vec![],
            },
        };
        assert!(search.bind_rule(&rule));
        let (out, _) = search.conclude(&rule, false);
        search.binds.clear();
        let id = search.push(out.clone(), rule);
        assert!(!search.admit(id));
        assert_eq!(search.clauses[id as usize].state, State::Deleted);
        assert_eq!(search.stats.connected_redundant, 1);
        assert!(!search.is_duplicate(&out));
        assert!(!search.connected_redundant(0));
    }
}
