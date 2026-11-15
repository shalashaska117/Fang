// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Bounded ground congruence closure with explanations in existing unit equations.
//! Every explanation is expanded to ordinary paramodulation steps by the caller.
use crate::clause::Id;
use crate::term::{Bank, Head, TermId};
use std::collections::{HashMap, VecDeque};
use std::time::Instant;

#[derive(Clone, Copy, Debug)]
pub struct Bounds {
    pub terms: usize,
    pub operations: u64,
    pub proof_steps: usize,
    pub path_depth: usize,
}

impl Default for Bounds {
    fn default() -> Self {
        Self {
            terms: 16_384,
            operations: 1_000_000,
            proof_steps: 4096,
            path_depth: 64,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Refusal {
    Work,
    Terms,
    Arity,
    Proof,
    Deadline,
    Nonground,
}

#[derive(Clone, Copy, Debug)]
pub struct Equation {
    pub clause: Id,
    pub left: TermId,
    pub right: TermId,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Rewrite {
    pub source: Id,
    pub reverse: bool,
    pub path: Vec<u16>,
}

#[derive(Debug)]
pub struct Plan {
    pub target: Id,
    pub steps: Vec<Rewrite>,
}

struct Budget {
    remaining: u64,
    deadline: Option<Instant>,
}

impl Budget {
    fn tick(&mut self) -> Result<(), Refusal> {
        self.remaining = self.remaining.checked_sub(1).ok_or(Refusal::Work)?;
        if self.remaining.is_multiple_of(256)
            && self.deadline.is_some_and(|end| Instant::now() >= end)
        {
            return Err(Refusal::Deadline);
        }
        Ok(())
    }
}

#[derive(Clone, Copy)]
enum Reason {
    Input(Id),
    Congruence,
}
struct Edge {
    left: usize,
    right: usize,
    reason: Reason,
}
struct Graph {
    terms: Vec<TermId>,
    index: HashMap<TermId, usize>,
    parent: Vec<usize>,
    size: Vec<usize>,
    edges: Vec<Edge>,
    adjacent: Vec<Vec<usize>>,
}

impl Graph {
    fn collect(
        bank: &Bank,
        roots: impl Iterator<Item = TermId>,
        bounds: Bounds,
        budget: &mut Budget,
    ) -> Result<Self, Refusal> {
        let mut terms = Vec::new();
        let mut index = HashMap::new();
        for root in roots {
            let mut pending = vec![root];
            while let Some(term) = pending.pop() {
                budget.tick()?;
                if !bank.ground(term) {
                    return Err(Refusal::Nonground);
                }
                if index.contains_key(&term) {
                    continue;
                }
                if terms.len() >= bounds.terms {
                    return Err(Refusal::Terms);
                }
                if bank.args(term).len() > 256 {
                    return Err(Refusal::Arity);
                }
                index.insert(term, terms.len());
                terms.push(term);
                for &child in bank.args(term).iter().rev() {
                    budget.tick()?;
                    pending.push(child);
                }
            }
        }
        let len = terms.len();
        Ok(Self {
            terms,
            index,
            parent: (0..len).collect(),
            size: vec![1; len],
            edges: vec![],
            adjacent: vec![vec![]; len],
        })
    }

    fn root(&mut self, mut node: usize, budget: &mut Budget) -> Result<usize, Refusal> {
        loop {
            budget.tick()?;
            let parent = self.parent[node];
            if parent == node {
                return Ok(node);
            }
            self.parent[node] = self.parent[parent];
            node = parent;
        }
    }

    fn merge(
        &mut self,
        left: usize,
        right: usize,
        reason: Reason,
        budget: &mut Budget,
    ) -> Result<bool, Refusal> {
        let mut a = self.root(left, budget)?;
        let mut b = self.root(right, budget)?;
        if a == b {
            return Ok(false);
        }
        if self.size[a] < self.size[b] {
            std::mem::swap(&mut a, &mut b);
        }
        self.parent[b] = a;
        self.size[a] += self.size[b];
        let edge = self.edges.len();
        self.edges.push(Edge {
            left,
            right,
            reason,
        });
        self.adjacent[left].push(edge);
        self.adjacent[right].push(edge);
        Ok(true)
    }

    fn close(&mut self, bank: &Bank, budget: &mut Budget) -> Result<(), Refusal> {
        loop {
            let mut signatures = HashMap::new();
            let mut changed = false;
            for node in 0..self.terms.len() {
                budget.tick()?;
                let term = self.terms[node];
                let Head::Sym(symbol) = bank.head(term) else {
                    return Err(Refusal::Nonground);
                };
                let mut args = Vec::with_capacity(bank.args(term).len());
                for child in bank.args(term) {
                    args.push(self.root(self.index[child], budget)?);
                }
                if let Some(&other) = signatures.get(&(symbol, args.clone())) {
                    changed |= self.merge(other, node, Reason::Congruence, budget)?;
                } else {
                    signatures.insert((symbol, args), node);
                }
            }
            if !changed {
                return Ok(());
            }
        }
    }

    // The explanation edges form a forest. A congruence edge may use only older
    // edges to explain its arguments; this prevents circular proof explanations.
    fn path(
        &self,
        from: usize,
        to: usize,
        before: usize,
        budget: &mut Budget,
    ) -> Result<Vec<(usize, bool)>, Refusal> {
        if from == to {
            return Ok(vec![]);
        }
        let mut seen = vec![false; self.terms.len()];
        let mut parent = vec![None; self.terms.len()];
        let mut pending = VecDeque::from([from]);
        seen[from] = true;
        while let Some(node) = pending.pop_front() {
            budget.tick()?;
            for &index in &self.adjacent[node] {
                budget.tick()?;
                if index >= before {
                    continue;
                }
                let edge = &self.edges[index];
                let reverse = edge.right == node;
                let next = if reverse { edge.left } else { edge.right };
                if seen[next] {
                    continue;
                }
                parent[next] = Some((node, index, reverse));
                seen[next] = true;
                if next == to {
                    let mut route = vec![];
                    let mut at = to;
                    while at != from {
                        budget.tick()?;
                        let (previous, edge, reverse) = parent[at].ok_or(Refusal::Proof)?;
                        route.push((edge, reverse));
                        at = previous;
                    }
                    route.reverse();
                    return Ok(route);
                }
                pending.push_back(next);
            }
        }
        Err(Refusal::Proof)
    }

    fn explain(
        &self,
        bank: &Bank,
        left: usize,
        right: usize,
        bounds: Bounds,
        budget: &mut Budget,
    ) -> Result<Vec<Rewrite>, Refusal> {
        enum Task {
            Pair(usize, usize, usize, Vec<u16>),
            Edge(usize, bool, Vec<u16>),
        }
        let mut pending = vec![Task::Pair(left, right, self.edges.len(), vec![])];
        let mut output = vec![];
        while let Some(task) = pending.pop() {
            budget.tick()?;
            if pending.len() > bounds.proof_steps {
                return Err(Refusal::Proof);
            }
            match task {
                Task::Pair(a, b, before, prefix) => {
                    let route = self.path(a, b, before, budget)?;
                    if pending.len().saturating_add(route.len()) > bounds.proof_steps {
                        return Err(Refusal::Proof);
                    }
                    for (edge, reverse) in route.into_iter().rev() {
                        pending.push(Task::Edge(edge, reverse, prefix.clone()));
                    }
                }
                Task::Edge(index, reverse, prefix) => {
                    let edge = &self.edges[index];
                    match edge.reason {
                        Reason::Input(source) => {
                            if output.len() >= bounds.proof_steps {
                                return Err(Refusal::Proof);
                            }
                            output.push(Rewrite {
                                source,
                                reverse,
                                path: prefix,
                            });
                        }
                        Reason::Congruence => {
                            let (a, b) = if reverse {
                                (edge.right, edge.left)
                            } else {
                                (edge.left, edge.right)
                            };
                            let left = bank.args(self.terms[a]);
                            let right = bank.args(self.terms[b]);
                            if bank.head(self.terms[a]) != bank.head(self.terms[b])
                                || left.len() != right.len()
                            {
                                return Err(Refusal::Proof);
                            }
                            for (position, (&a, &b)) in left.iter().zip(right).enumerate().rev() {
                                budget.tick()?;
                                if a == b {
                                    continue;
                                }
                                if prefix.len() >= bounds.path_depth
                                    || pending.len() >= bounds.proof_steps
                                {
                                    return Err(Refusal::Proof);
                                }
                                let mut path = prefix.clone();
                                path.push(u16::try_from(position).map_err(|_| Refusal::Arity)?);
                                pending.push(Task::Pair(
                                    self.index[&a],
                                    self.index[&b],
                                    index,
                                    path,
                                ));
                            }
                        }
                    }
                }
            }
        }
        Ok(output)
    }
}

/// Only positive ground unit equations may enter `equations`; `goals` are
/// negative ground unit equations. IDs are returned unchanged for reconstruction.
pub fn find(
    bank: &Bank,
    equations: &[Equation],
    goals: &[Equation],
    bounds: Bounds,
    deadline: Option<Instant>,
) -> Result<Option<Plan>, Refusal> {
    if deadline.is_some_and(|end| Instant::now() >= end) {
        return Err(Refusal::Deadline);
    }
    if goals.is_empty() {
        return Ok(None);
    }
    let mut budget = Budget {
        remaining: bounds.operations,
        deadline,
    };
    let roots = equations
        .iter()
        .chain(goals)
        .flat_map(|eq| [eq.left, eq.right]);
    let mut graph = Graph::collect(bank, roots, bounds, &mut budget)?;
    for eq in equations {
        graph.merge(
            graph.index[&eq.left],
            graph.index[&eq.right],
            Reason::Input(eq.clause),
            &mut budget,
        )?;
    }
    graph.close(bank, &mut budget)?;
    for goal in goals {
        let left = graph.index[&goal.left];
        let right = graph.index[&goal.right];
        if graph.root(left, &mut budget)? == graph.root(right, &mut budget)? {
            let steps = graph.explain(bank, left, right, bounds, &mut budget)?;
            if deadline.is_some_and(|end| Instant::now() >= end) {
                return Err(Refusal::Deadline);
            }
            return Ok(Some(Plan {
                target: goal.clause,
                steps,
            }));
        }
    }
    Ok(None)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn replace(bank: &mut Bank, at: TermId, path: &[u16], from: TermId, to: TermId) -> TermId {
        let Some((&first, rest)) = path.split_first() else {
            assert_eq!(at, from);
            return to;
        };
        let Head::Sym(symbol) = bank.head(at) else {
            panic!("ground term")
        };
        let mut children = bank.args(at).to_vec();
        let slot = usize::from(first);
        assert!(slot < children.len());
        children[slot] = replace(bank, children[slot], rest, from, to);
        bank.app(symbol, &children)
    }

    fn replay(bank: &mut Bank, equations: &[Equation], left: TermId, right: TermId, plan: Plan) {
        let mut at = left;
        for step in plan.steps {
            let eq = equations
                .iter()
                .find(|eq| eq.clause == step.source)
                .unwrap();
            let (from, to) = if step.reverse {
                (eq.right, eq.left)
            } else {
                (eq.left, eq.right)
            };
            at = replace(bank, at, &step.path, from, to);
        }
        assert_eq!(at, right);
    }

    fn reference(bank: &Bank, terms: &[TermId], equations: &[Equation]) -> Vec<Vec<bool>> {
        let n = terms.len();
        let mut related = vec![vec![false; n]; n];
        for (i, row) in related.iter_mut().enumerate() {
            row[i] = true;
        }
        for eq in equations {
            let a = terms.iter().position(|&t| t == eq.left).unwrap();
            let b = terms.iter().position(|&t| t == eq.right).unwrap();
            related[a][b] = true;
            related[b][a] = true;
        }
        loop {
            let previous = related.clone();
            for k in 0..n {
                for i in 0..n {
                    for j in 0..n {
                        related[i][j] |= related[i][k] && related[k][j];
                    }
                }
            }
            for i in 0..n {
                for j in 0..n {
                    let a = terms[i];
                    let b = terms[j];
                    if bank.head(a) != bank.head(b) || bank.args(a).len() != bank.args(b).len() {
                        continue;
                    }
                    let congruent = bank.args(a).iter().zip(bank.args(b)).all(|(a, b)| {
                        let a = terms.iter().position(|t| t == a).unwrap();
                        let b = terms.iter().position(|t| t == b).unwrap();
                        related[a][b]
                    });
                    if congruent {
                        related[i][j] = true;
                        related[j][i] = true;
                    }
                }
            }
            if related == previous {
                return related;
            }
        }
    }

    #[test]
    fn closure_and_expanded_explanations_match_independent_relation_census() {
        let mut bank = Bank::new();
        let a = bank.app(0, &[]);
        let b = bank.app(1, &[]);
        let c = bank.app(2, &[]);
        let fa = bank.app(3, &[a]);
        let fb = bank.app(3, &[b]);
        let fc = bank.app(3, &[c]);
        let gab = bank.app(4, &[a, b]);
        let gbc = bank.app(4, &[b, c]);
        let gca = bank.app(4, &[c, a]);
        let fgab = bank.app(3, &[gab]);
        let fgbc = bank.app(3, &[gbc]);
        let terms = [a, b, c, fa, fb, fc, gab, gbc, gca, fgab, fgbc];
        let choices = [
            (a, b),
            (b, c),
            (fa, a),
            (fb, b),
            (gab, c),
            (gbc, fa),
            (fgab, fc),
        ];
        for subset in 0..(1 << choices.len()) {
            let equations: Vec<_> = choices
                .iter()
                .enumerate()
                .filter(|(i, _)| subset & (1 << i) != 0)
                .map(|(i, &(left, right))| Equation {
                    clause: i as Id,
                    left,
                    right,
                })
                .collect();
            let expected = reference(&bank, &terms, &equations);
            for (i, &left) in terms.iter().enumerate() {
                for (j, &right) in terms.iter().enumerate() {
                    let goal = Equation {
                        clause: 100,
                        left,
                        right,
                    };
                    let plan = find(&bank, &equations, &[goal], Bounds::default(), None).unwrap();
                    assert_eq!(
                        plan.is_some(),
                        expected[i][j],
                        "subset {subset}, pair {i}/{j}"
                    );
                    if let Some(plan) = plan {
                        assert_eq!(plan.target, 100);
                        replay(&mut bank, &equations, left, right, plan);
                    }
                }
            }
        }
    }

    #[test]
    fn resource_refusals_and_variables_never_become_joinability_claims() {
        let mut bank = Bank::new();
        let a = bank.app(0, &[]);
        let b = bank.app(1, &[]);
        let fa = bank.app(2, &[a]);
        let fb = bank.app(2, &[b]);
        let equations = [Equation {
            clause: 0,
            left: a,
            right: b,
        }];
        let goals = [Equation {
            clause: 1,
            left: fa,
            right: fb,
        }];
        assert!(matches!(
            find(
                &bank,
                &equations,
                &goals,
                Bounds {
                    terms: 1,
                    ..Bounds::default()
                },
                None
            ),
            Err(Refusal::Terms)
        ));
        assert!(matches!(
            find(
                &bank,
                &equations,
                &goals,
                Bounds {
                    operations: 0,
                    ..Bounds::default()
                },
                None
            ),
            Err(Refusal::Work)
        ));
        assert!(matches!(
            find(
                &bank,
                &equations,
                &goals,
                Bounds {
                    proof_steps: 0,
                    ..Bounds::default()
                },
                None
            ),
            Err(Refusal::Proof)
        ));
        assert!(matches!(
            find(
                &bank,
                &equations,
                &goals,
                Bounds {
                    path_depth: 0,
                    ..Bounds::default()
                },
                None
            ),
            Err(Refusal::Proof)
        ));
        assert!(matches!(
            find(
                &bank,
                &equations,
                &goals,
                Bounds::default(),
                Some(Instant::now())
            ),
            Err(Refusal::Deadline)
        ));
        let variable = bank.var(0);
        assert!(matches!(
            find(
                &bank,
                &equations,
                &[Equation {
                    clause: 2,
                    left: variable,
                    right: a
                }],
                Bounds::default(),
                None
            ),
            Err(Refusal::Nonground)
        ));
    }
}
