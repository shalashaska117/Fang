// Copyright (c) 2026 Pietro Pellegrino.
// Vampire is copyright (C) 2020 by its authors and contributors (see
// LICENSES/Vampire.AUTHORS) and their institutional affiliations. All rights reserved.
// Reference for resolution and factoring: Vampire; see LICENSES/Vampire.txt and
// LICENSES/Vampire.ORIGIN. No Vampire strategy or completeness claim is made.
use crate::syntax::{Clause, Problem, Substitution, Term, apply_clause, count_clause, rename};
use crate::unify::Unifier;
use crate::{Budget, Error, ErrorKind, Limits};
use std::fmt::{self, Write};

#[derive(Clone, Debug)]
enum Rule {
    Input(usize),
    Factor {
        parent: usize,
        first: usize,
        second: usize,
        substitution: Substitution,
    },
    Resolve {
        left: usize,
        left_pos: usize,
        right: usize,
        right_pos: usize,
        substitution: Substitution,
    },
}

#[derive(Clone, Debug)]
struct Node {
    clause: Clause,
    rule: Rule,
}

struct EmissionPlan {
    order: Vec<usize>,
    remap: Vec<usize>,
}

#[derive(Clone, Debug)]
pub struct Certificate {
    nodes: Vec<Node>,
    final_node: usize,
}

#[derive(Clone, Debug)]
pub enum Outcome {
    CandidateRefutation(Certificate),
    Unknown {
        processed_clauses: usize,
        attempted_inferences: usize,
    },
}

struct Search<'a> {
    nodes: Vec<Node>,
    limits: &'a Limits,
    budget: Budget,
    steps: usize,
    stored_nodes: usize,
}

impl Search<'_> {
    fn step(&mut self) -> Result<(), Error> {
        self.budget.tick()?;
        self.steps += 1;
        if self.steps > self.limits.max_steps {
            return Err(Error::resource("inference step budget exhausted"));
        }
        Ok(())
    }

    fn append(&mut self, clause: Clause, rule: Rule) -> Result<Option<usize>, Error> {
        let clause_size = count_clause(&clause, self.limits)?;
        // Exact structural equality; no hash or alpha-equivalence is trusted here.
        for node in &self.nodes {
            self.budget.tick()?;
            if node.clause == clause {
                return Ok(None);
            }
        }
        if self.nodes.len() >= self.limits.max_clauses {
            return Err(Error::resource("stored clause limit exceeded"));
        }
        let subst_size = match &rule {
            Rule::Input(_) => 0,
            Rule::Factor { substitution, .. } | Rule::Resolve { substitution, .. } => {
                let mut size = substitution.len();
                let mut pending: Vec<_> = substitution.values().collect();
                while let Some(term) = pending.pop() {
                    size += 1;
                    if let Term::Fun(_, args) = term {
                        pending.extend(args);
                    }
                }
                size
            }
        };
        self.stored_nodes = self
            .stored_nodes
            .checked_add(clause_size)
            .and_then(|n| n.checked_add(subst_size))
            .ok_or_else(|| Error::resource("stored node count overflow"))?;
        if self.stored_nodes > self.limits.max_stored_nodes {
            return Err(Error::resource("stored term node limit exceeded"));
        }
        let id = self.nodes.len();
        self.nodes.push(Node { clause, rule });
        Ok(Some(id))
    }

    fn factor(
        &mut self,
        parent: usize,
        first: usize,
        second: usize,
    ) -> Result<Option<usize>, Error> {
        self.step()?;
        let clause = &self.nodes[parent].clause;
        let a = &clause[first];
        let b = &clause[second];
        if a.positive != b.positive || a.predicate != b.predicate {
            return Ok(None);
        }
        let pairs: Vec<_> = a
            .arguments
            .iter()
            .cloned()
            .zip(b.arguments.iter().cloned())
            .collect();
        let mut unifier = Unifier::default();
        if !unifier.unify_with_budget(&pairs, self.limits, &mut self.budget)? {
            return Ok(None);
        }
        let substitution = unifier.substitution_with_budget(self.limits, &mut self.budget)?;
        let result = apply_clause(clause, second, &substitution, self.limits, &mut self.budget)?;
        self.append(
            result,
            Rule::Factor {
                parent,
                first,
                second,
                substitution,
            },
        )
    }

    fn resolve(
        &mut self,
        left: usize,
        left_pos: usize,
        right: usize,
        right_pos: usize,
    ) -> Result<Option<usize>, Error> {
        self.step()?;
        let a = &self.nodes[left].clause[left_pos];
        let b = &self.nodes[right].clause[right_pos];
        if a.positive == b.positive || a.predicate != b.predicate {
            return Ok(None);
        }
        let left_clause = rename(&self.nodes[left].clause, 0, &mut self.budget)?;
        let right_clause = rename(&self.nodes[right].clause, 1, &mut self.budget)?;
        let pairs: Vec<_> = left_clause[left_pos]
            .arguments
            .iter()
            .cloned()
            .zip(right_clause[right_pos].arguments.iter().cloned())
            .collect();
        let mut unifier = Unifier::default();
        if !unifier.unify_with_budget(&pairs, self.limits, &mut self.budget)? {
            return Ok(None);
        }
        let substitution = unifier.substitution_with_budget(self.limits, &mut self.budget)?;
        let mut result = apply_clause(
            &left_clause,
            left_pos,
            &substitution,
            self.limits,
            &mut self.budget,
        )?;
        result.extend(apply_clause(
            &right_clause,
            right_pos,
            &substitution,
            self.limits,
            &mut self.budget,
        )?);
        self.append(
            result,
            Rule::Resolve {
                left,
                left_pos,
                right,
                right_pos,
                substitution,
            },
        )
    }
}

/// A deterministic, bounded FIFO search. Exhaustion is always Unknown.
pub fn prove(problem: &Problem, limits: &Limits) -> Result<Outcome, Error> {
    validate_problem(problem, limits)?;
    let mut search = Search {
        nodes: Vec::new(),
        limits,
        budget: Budget::new(limits.max_operations),
        steps: 0,
        stored_nodes: 0,
    };
    if problem.clauses.len() > limits.max_clauses {
        return Err(Error::resource("input clause limit exceeded"));
    }
    // Preserve all input positions, including duplicate clauses.
    for (i, clause) in problem.clauses.iter().enumerate() {
        search.stored_nodes = search
            .stored_nodes
            .checked_add(count_clause(clause, limits)?)
            .ok_or_else(|| Error::resource("stored node count overflow"))?;
        if search.stored_nodes > limits.max_stored_nodes {
            return Err(Error::resource("stored term node limit exceeded"));
        }
        search.nodes.push(Node {
            clause: clause.clone(),
            rule: Rule::Input(i),
        });
    }
    if let Some(final_node) = search.nodes.iter().position(|node| node.clause.is_empty()) {
        // The protocol requires the selected final node to be the last node.
        search.nodes.truncate(final_node + 1);
        return Ok(Outcome::CandidateRefutation(Certificate {
            nodes: search.nodes,
            final_node,
        }));
    }
    // Keep P0's zero-work result before index capacity arithmetic.
    if search.nodes.is_empty() {
        return Ok(Outcome::Unknown {
            processed_clauses: 0,
            attempted_inferences: 0,
        });
    }
    let mut predicate_index = crate::predicate_index::new_index(problem.predicates.len(), limits)?;
    let mut given = 0;
    while given < search.nodes.len() {
        search.budget.tick()?;
        let length = search.nodes[given].clause.len();
        for first in 0..length {
            for second in first + 1..length {
                // Distinct factoring positions leave at least one literal.
                search.factor(given, first, second)?;
            }
        }
        let schedule = crate::predicate_index::schedule(
            &mut predicate_index,
            given,
            &search.nodes[given].clause,
            problem.predicates.len(),
            &mut search.budget,
        )?;
        for candidate in schedule {
            if let Some(id) =
                search.resolve(given, candidate.left, candidate.other, candidate.right)?
                && search.nodes[id].clause.is_empty()
            {
                return Ok(Outcome::CandidateRefutation(Certificate {
                    nodes: search.nodes,
                    final_node: id,
                }));
            }
        }
        given += 1;
    }
    Ok(Outcome::Unknown {
        processed_clauses: given,
        attempted_inferences: search.steps,
    })
}

fn validate_problem(problem: &Problem, limits: &Limits) -> Result<(), Error> {
    let invalid = |message: &str| Error {
        kind: ErrorKind::InvalidInput,
        offset: None,
        message: message.into(),
    };
    if problem.clause_names.len() != problem.clauses.len() {
        return Err(invalid(
            "clause names and clauses must have the same length",
        ));
    }
    for clause in &problem.clauses {
        count_clause(clause, limits)?;
        if crate::syntax::deduplicate(clause) != *clause {
            return Err(invalid("prove requires stably deduplicated input clauses"));
        }
        let mut terms = Vec::new();
        for literal in clause {
            let Some(symbol) = problem.predicates.get(literal.predicate as usize) else {
                return Err(invalid("unknown predicate ID"));
            };
            if literal.arguments.len() != symbol.arity {
                return Err(invalid("predicate arity mismatch"));
            }
            terms.extend(&literal.arguments);
        }
        while let Some(term) = terms.pop() {
            if let Term::Fun(id, arguments) = term {
                let Some(symbol) = problem.functions.get(*id as usize) else {
                    return Err(invalid("unknown function ID"));
                };
                if arguments.len() != symbol.arity {
                    return Err(invalid("function arity mismatch"));
                }
                terms.extend(arguments);
            }
        }
    }
    Ok(())
}

struct BoundedString {
    text: String,
    limit: usize,
}
impl Write for BoundedString {
    fn write_str(&mut self, value: &str) -> fmt::Result {
        if value.len() > self.limit.saturating_sub(self.text.len()) {
            return Err(fmt::Error);
        }
        self.text.push_str(value);
        Ok(())
    }
}

fn write_term(out: &mut impl Write, term: &Term) -> fmt::Result {
    match term {
        Term::Var(v) => write!(out, "(v {v})"),
        Term::Fun(f, args) => {
            write!(out, "(f {f}")?;
            for arg in args {
                out.write_char(' ')?;
                write_term(out, arg)?;
            }
            out.write_char(')')
        }
    }
}

fn write_substitution(out: &mut impl Write, substitution: &Substitution) -> fmt::Result {
    out.write_str("(subst")?;
    for (variable, term) in substitution {
        write!(out, " ({variable} ")?;
        write_term(out, term)?;
        out.write_char(')')?;
    }
    out.write_char(')')
}

fn write_clause(out: &mut impl Write, clause: &Clause) -> fmt::Result {
    out.write_str("(clause")?;
    for literal in clause {
        write!(
            out,
            " ({} {}",
            if literal.positive { "pos" } else { "neg" },
            literal.predicate
        )?;
        for term in &literal.arguments {
            out.write_char(' ')?;
            write_term(out, term)?;
        }
        out.write_char(')')?;
    }
    out.write_char(')')
}

impl Certificate {
    /// Recorded search nodes, including nodes omitted from the serialized refutation.
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    fn emission_plan(&self) -> Result<EmissionPlan, Error> {
        let invalid = |message: &str| Error {
            kind: ErrorKind::InvalidInput,
            offset: None,
            message: format!("invalid internal certificate: {message}"),
        };
        let final_node = self
            .nodes
            .get(self.final_node)
            .ok_or_else(|| invalid("final node is out of range"))?;
        if !final_node.clause.is_empty() {
            return Err(invalid("final node is not the empty clause"));
        }
        let mut needed = vec![false; self.nodes.len()];
        needed[self.final_node] = true;
        // Parents must precede their child. A reverse scan therefore visits the entire
        // dependency closure without recursion or changing the recorded search history.
        for id in (0..=self.final_node).rev() {
            if !needed[id] {
                continue;
            }
            let mut require_parent = |parent: usize| {
                if parent >= id {
                    return Err(invalid("parent does not precede its child"));
                }
                needed[parent] = true;
                Ok(())
            };
            match self.nodes[id].rule {
                Rule::Input(_) => {}
                Rule::Factor { parent, .. } => require_parent(parent)?,
                Rule::Resolve { left, right, .. } => {
                    require_parent(left)?;
                    require_parent(right)?;
                }
            }
        }
        let mut order = Vec::new();
        let mut remap = vec![0; self.nodes.len()];
        for (old, required) in needed.into_iter().enumerate() {
            if required {
                remap[old] = order.len();
                order.push(old);
            }
        }
        Ok(EmissionPlan { order, remap })
    }

    pub fn to_text(&self, max_bytes: usize) -> Result<String, Error> {
        let plan = self.emission_plan()?;
        let mut out = BoundedString {
            text: String::new(),
            limit: max_bytes,
        };
        self.write(&mut out, &plan)
            .map_err(|_| Error::resource("certificate byte limit exceeded"))?;
        Ok(out.text)
    }

    fn write(&self, out: &mut impl Write, plan: &EmissionPlan) -> fmt::Result {
        out.write_str("(fang-proof 1\n")?;
        for (id, &old) in plan.order.iter().enumerate() {
            let node = &self.nodes[old];
            match &node.rule {
                Rule::Input(index) => writeln!(out, "  (input {id} {index})")?,
                Rule::Factor {
                    parent,
                    first,
                    second,
                    substitution,
                } => {
                    let parent = plan.remap[*parent];
                    write!(out, "  (factor {id} {parent} {first} {second} ")?;
                    write_substitution(out, substitution)?;
                    out.write_char(' ')?;
                    write_clause(out, &node.clause)?;
                    out.write_str(")\n")?;
                }
                Rule::Resolve {
                    left,
                    left_pos,
                    right,
                    right_pos,
                    substitution,
                } => {
                    let left = plan.remap[*left];
                    let right = plan.remap[*right];
                    write!(
                        out,
                        "  (resolve {id} {left} {left_pos} {right} {right_pos} "
                    )?;
                    write_substitution(out, substitution)?;
                    out.write_char(' ')?;
                    write_clause(out, &node.clause)?;
                    out.write_str(")\n")?;
                }
            }
        }
        writeln!(out, "  (final {}))", plan.remap[self.final_node])
    }
}

#[cfg(test)]
mod certificate_invariant_tests {
    use super::*;

    #[test]
    fn reachable_forward_and_self_references_are_rejected() {
        for parent in [0, 1, usize::MAX] {
            let certificate = Certificate {
                nodes: vec![Node {
                    clause: vec![],
                    rule: Rule::Factor {
                        parent,
                        first: 0,
                        second: 1,
                        substitution: Substitution::default(),
                    },
                }],
                final_node: 0,
            };
            assert!(
                certificate
                    .to_text(1024)
                    .unwrap_err()
                    .message
                    .contains("parent")
            );
        }
    }

    #[test]
    fn missing_final_node_is_rejected_without_indexing() {
        let certificate = Certificate {
            nodes: vec![],
            final_node: usize::MAX,
        };
        assert!(
            certificate
                .to_text(1024)
                .unwrap_err()
                .message
                .contains("final node")
        );
    }
}
