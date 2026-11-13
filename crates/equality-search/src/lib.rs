// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Isolated equality-CNF search. Every result remains a candidate until
// the independent original-byte checker accepts its certificate.
#![forbid(unsafe_code)]

use fang::syntax::Term;
use fang::unify::Unifier;
use fang_equality_inference_core::{Atom, Clause, Substitution};
use std::fmt::{self, Write};

mod ordered;
mod prepared;
pub use prepared::{InvalidPrepared, PreparedError, prove_prepared_ordered};
#[cfg(test)]
mod serialization_tests;

#[derive(Clone, Debug)]
pub struct Limits {
    pub input: fang::Limits,
    pub reconstruction: fang_equality_inference_core::Limits,
    pub max_attempts: usize,
    pub max_stored_clauses: usize,
    pub max_stored_term_nodes: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            input: Default::default(),
            reconstruction: Default::default(),
            max_attempts: 10_000,
            max_stored_clauses: 1_000,
            max_stored_term_nodes: 1_000_000,
        }
    }
}

#[derive(Debug)]
pub enum Error {
    Source(fang::Error),
    Unification(fang::Error),
    Reconstruction(fang_equality_inference_core::Error),
    Paramodulation(fang_equality_paramodulation_core::Error),
    Resource(&'static str),
    Certificate(&'static str),
}

#[derive(Clone, Debug, Default)]
pub struct Statistics {
    pub processed_clauses: usize,
    pub attempted_inferences: usize,
    pub derived_clauses: usize,
    pub stored_term_nodes: usize,
}

#[derive(Clone, Debug)]
enum Rule {
    Input(usize),
    Paramodulate {
        source: usize,
        target: usize,
        source_pivot: usize,
        direction: fang_equality_paramodulation_core::Direction,
        position: fang_equality_paramodulation_core::Position,
        substitution: Substitution,
    },
    EqualityResolution {
        parent: usize,
        pivot: usize,
        substitution: Substitution,
    },
    Factor {
        parent: usize,
        first: usize,
        second: usize,
        substitution: Substitution,
    },
    Resolve {
        left: usize,
        left_position: usize,
        right: usize,
        right_position: usize,
        substitution: Substitution,
    },
}

#[derive(Clone, Debug)]
struct Node {
    clause: Clause,
    rule: Rule,
}

#[derive(Clone, Debug)]
pub struct Certificate {
    ordered: bool,
    nodes: Vec<Node>,
    final_node: usize,
}

#[derive(Debug)]
pub enum Outcome {
    CandidateRefutation {
        certificate: Certificate,
        statistics: Statistics,
    },
    Unknown(Statistics),
}

fn account_term(term: &Term, total: &mut usize, cap: usize) -> Result<(), Error> {
    if *total >= cap {
        return Err(Error::Resource("stored term-node limit"));
    }
    *total += 1;
    if let Term::Fun(_, arguments) = term {
        for child in arguments {
            account_term(child, total, cap)?;
        }
    }
    Ok(())
}

fn account_clause(clause: &Clause, total: &mut usize, cap: usize) -> Result<(), Error> {
    for literal in clause {
        match &literal.atom {
            Atom::Equal(left, right) => {
                account_term(left, total, cap)?;
                account_term(right, total, cap)?;
            }
            Atom::Predicate(_, arguments) => {
                for term in arguments {
                    account_term(term, total, cap)?;
                }
            }
        }
    }
    Ok(())
}

fn matching_arguments<'a>(left: &'a Atom, right: &'a Atom) -> Option<Vec<(&'a Term, &'a Term)>> {
    match (left, right) {
        (Atom::Equal(a, b), Atom::Equal(c, d)) => Some(vec![(a, c), (b, d)]),
        (Atom::Predicate(p, a), Atom::Predicate(q, b)) if p == q && a.len() == b.len() => {
            Some(a.iter().zip(b).collect())
        }
        _ => None,
    }
}

fn witness(
    pairs: &[(&Term, &Term)],
    limits: &Limits,
    statistics: &mut Statistics,
) -> Result<Option<Substitution>, Error> {
    if statistics.attempted_inferences >= limits.max_attempts {
        return Err(Error::Resource("inference attempt limit"));
    }
    statistics.attempted_inferences += 1;
    let equations: Vec<_> = pairs
        .iter()
        .map(|(a, b)| ((*a).clone(), (*b).clone()))
        .collect();
    let mut unifier = Unifier::default();
    if !unifier
        .unify(&equations, &limits.input)
        .map_err(Error::Unification)?
    {
        return Ok(None);
    }
    Ok(Some(
        unifier
            .substitution(&limits.input)
            .map_err(Error::Unification)?
            .iter()
            .cloned()
            .collect(),
    ))
}

fn retain(
    nodes: &mut Vec<Node>,
    clause: Clause,
    rule: Rule,
    limits: &Limits,
    statistics: &mut Statistics,
) -> Result<bool, Error> {
    if nodes.iter().any(|node| node.clause == clause) {
        return Ok(false);
    }
    if nodes.len() >= limits.max_stored_clauses {
        return Err(Error::Resource("stored clause limit"));
    }
    if clause.len() > limits.reconstruction.max_literals {
        return Err(Error::Reconstruction(
            fang_equality_inference_core::Error::Literals,
        ));
    }
    // Bound the assembled conclusion as well as each helper's separate result.
    let mut result_nodes = 0;
    account_clause(
        &clause,
        &mut result_nodes,
        limits.reconstruction.max_output_nodes,
    )?;
    account_clause(
        &clause,
        &mut statistics.stored_term_nodes,
        limits.max_stored_term_nodes,
    )?;
    let substitution = match &rule {
        Rule::Input(_) => &[][..],
        Rule::EqualityResolution { substitution, .. }
        | Rule::Factor { substitution, .. }
        | Rule::Resolve { substitution, .. }
        | Rule::Paramodulate { substitution, .. } => substitution.as_slice(),
    };
    for (_, image) in substitution {
        account_term(
            image,
            &mut statistics.stored_term_nodes,
            limits.max_stored_term_nodes,
        )?;
    }
    let empty = clause.is_empty();
    nodes.push(Node { clause, rule });
    statistics.derived_clauses += 1;
    Ok(empty)
}

// The independent resolution checker uses exactly 2*x and 2*x+1.
// Overflow is a typed resource failure; it never aliases variable IDs.
fn rename_term(
    term: &Term,
    side: u32,
    depth: usize,
    remaining: &mut usize,
    limit: usize,
) -> Result<Term, Error> {
    if depth > limit {
        return Err(Error::Resource("renaming depth limit"));
    }
    if *remaining == 0 {
        return Err(Error::Resource("renaming operation limit"));
    }
    *remaining -= 1;
    match term {
        Term::Var(id) => Ok(Term::Var(
            id.checked_mul(2)
                .and_then(|n| n.checked_add(side))
                .ok_or(Error::Resource("renamed variable identifier limit"))?,
        )),
        Term::Fun(id, arguments) => {
            let mut result = Vec::new();
            for child in arguments {
                result.push(rename_term(child, side, depth + 1, remaining, limit)?);
            }
            Ok(Term::Fun(*id, result))
        }
    }
}

fn rename_clause(clause: &Clause, side: u32, limits: &Limits) -> Result<Clause, Error> {
    let mut remaining = limits.input.max_operations;
    let mut result = Vec::new();
    for literal in clause {
        let atom = match &literal.atom {
            Atom::Equal(a, b) => Atom::Equal(
                rename_term(a, side, 0, &mut remaining, limits.input.max_term_depth)?,
                rename_term(b, side, 0, &mut remaining, limits.input.max_term_depth)?,
            ),
            Atom::Predicate(id, arguments) => {
                let mut renamed = Vec::new();
                for term in arguments {
                    renamed.push(rename_term(
                        term,
                        side,
                        0,
                        &mut remaining,
                        limits.input.max_term_depth,
                    )?);
                }
                Atom::Predicate(*id, renamed)
            }
        };
        result.push(fang_equality_inference_core::Literal {
            positive: literal.positive,
            atom,
        });
    }
    Ok(result)
}

/// Parses original bytes, then explores equality resolution, factoring and
/// binary resolution. The actual unifier produces witnesses. Checked helpers
/// validate simultaneous instantiation; exact pivot conditions are checked
/// before ordered residual assembly. Every refutation remains a candidate.
/// Unification/substitution/reconstruction have per-call budgets. The separate
/// attempt cap bounds their number; it is not one shared operation counter.
pub fn prove_bytes(input: &[u8], limits: &Limits) -> Result<Outcome, Error> {
    prove(input, limits, false)
}

/// Add positional paramodulation and emit version 5. The accepted version-4
/// command does not call this candidate entrypoint. Every result still requires
/// the independent original-byte checker. No fairness/completeness is claimed.
pub fn prove_bytes_ordered(input: &[u8], limits: &Limits) -> Result<Outcome, Error> {
    prove(input, limits, true)
}

fn prove(input: &[u8], limits: &Limits, ordered: bool) -> Result<Outcome, Error> {
    let problem = fang_equality_frontend::parse(input, &limits.input).map_err(Error::Source)?;
    let functions: Vec<_> = problem
        .functions
        .iter()
        .map(|symbol| symbol.arity)
        .collect();
    let predicates: Vec<_> = problem
        .predicates
        .iter()
        .map(|symbol| symbol.arity)
        .collect();
    prove_clauses(problem.clauses, functions, predicates, limits, ordered)
}

fn prove_clauses(
    clauses: Vec<Clause>,
    functions: Vec<usize>,
    predicates: Vec<usize>,
    limits: &Limits,
    ordered: bool,
) -> Result<Outcome, Error> {
    let mut nodes: Vec<Node> = Vec::new();
    let mut statistics = Statistics::default();
    for (index, clause) in clauses.into_iter().enumerate() {
        if nodes.len() >= limits.max_stored_clauses {
            return Err(Error::Resource("stored clause limit"));
        }
        account_clause(
            &clause,
            &mut statistics.stored_term_nodes,
            limits.max_stored_term_nodes,
        )?;
        let empty = clause.is_empty();
        nodes.push(Node {
            clause,
            rule: Rule::Input(index),
        });
        if empty {
            let final_node = nodes.len() - 1;
            return Ok(Outcome::CandidateRefutation {
                certificate: Certificate {
                    ordered,
                    nodes,
                    final_node,
                },
                statistics,
            });
        }
    }
    let mut parent = 0;
    while parent < nodes.len() {
        statistics.processed_clauses += 1;
        for pivot in 0..nodes[parent].clause.len() {
            let literal = &nodes[parent].clause[pivot];
            if literal.positive {
                continue;
            }
            let Atom::Equal(left, right) = &literal.atom else {
                continue;
            };
            let Some(substitution) = witness(&[(left, right)], limits, &mut statistics)? else {
                continue;
            };
            let reconstructed = fang_equality_inference_core::equality_resolution(
                &nodes[parent].clause,
                pivot,
                &substitution,
                &functions,
                &predicates,
                &limits.reconstruction,
            )
            .map_err(Error::Reconstruction)?;
            if retain(
                &mut nodes,
                reconstructed.clause,
                Rule::EqualityResolution {
                    parent,
                    pivot,
                    substitution,
                },
                limits,
                &mut statistics,
            )? {
                let final_node = nodes.len() - 1;
                return Ok(Outcome::CandidateRefutation {
                    certificate: Certificate {
                        ordered,
                        nodes,
                        final_node,
                    },
                    statistics,
                });
            }
        }
        for first in 0..nodes[parent].clause.len() {
            for second in first + 1..nodes[parent].clause.len() {
                let a = &nodes[parent].clause[first];
                let b = &nodes[parent].clause[second];
                if a.positive != b.positive {
                    continue;
                }
                let Some(pairs) = matching_arguments(&a.atom, &b.atom) else {
                    continue;
                };
                let Some(substitution) = witness(&pairs, limits, &mut statistics)? else {
                    continue;
                };
                let mut reconstructed = fang_equality_inference_core::checked::instantiate(
                    &nodes[parent].clause,
                    &substitution,
                    &functions,
                    &predicates,
                    &limits.reconstruction,
                )
                .map_err(Error::Reconstruction)?
                .clause;
                if reconstructed[first] != reconstructed[second] {
                    return Err(Error::Reconstruction(
                        fang_equality_inference_core::Error::NotEqualized,
                    ));
                }
                reconstructed.remove(second);
                // A factor cannot make a nonempty clause empty, but retain still
                // has the same result contract as every other inference.
                if retain(
                    &mut nodes,
                    reconstructed,
                    Rule::Factor {
                        parent,
                        first,
                        second,
                        substitution,
                    },
                    limits,
                    &mut statistics,
                )? {
                    let final_node = nodes.len() - 1;
                    return Ok(Outcome::CandidateRefutation {
                        certificate: Certificate {
                            ordered,
                            nodes,
                            final_node,
                        },
                        statistics,
                    });
                }
            }
        }
        // Each pair is considered when its later parent is processed. A self
        // pair uses two disjoint variable banks, just like two distinct parents.
        for other in 0..=parent {
            let left = rename_clause(&nodes[parent].clause, 0, limits)?;
            let right = rename_clause(&nodes[other].clause, 1, limits)?;
            for left_position in 0..left.len() {
                for right_position in 0..right.len() {
                    let a = &left[left_position];
                    let b = &right[right_position];
                    if a.positive == b.positive {
                        continue;
                    }
                    let Some(pairs) = matching_arguments(&a.atom, &b.atom) else {
                        continue;
                    };
                    let Some(substitution) = witness(&pairs, limits, &mut statistics)? else {
                        continue;
                    };
                    let mut result = fang_equality_inference_core::checked::instantiate(
                        &left,
                        &substitution,
                        &functions,
                        &predicates,
                        &limits.reconstruction,
                    )
                    .map_err(Error::Reconstruction)?
                    .clause;
                    let mut right_result = fang_equality_inference_core::checked::instantiate(
                        &right,
                        &substitution,
                        &functions,
                        &predicates,
                        &limits.reconstruction,
                    )
                    .map_err(Error::Reconstruction)?
                    .clause;
                    if result[left_position].positive == right_result[right_position].positive
                        || result[left_position].atom != right_result[right_position].atom
                    {
                        return Err(Error::Reconstruction(
                            fang_equality_inference_core::Error::NotEqualized,
                        ));
                    }
                    result.remove(left_position);
                    right_result.remove(right_position);
                    if right_result.len()
                        > limits
                            .reconstruction
                            .max_literals
                            .saturating_sub(result.len())
                    {
                        return Err(Error::Reconstruction(
                            fang_equality_inference_core::Error::Literals,
                        ));
                    }
                    result.extend(right_result);
                    if retain(
                        &mut nodes,
                        result,
                        Rule::Resolve {
                            left: parent,
                            left_position,
                            right: other,
                            right_position,
                            substitution,
                        },
                        limits,
                        &mut statistics,
                    )? {
                        let final_node = nodes.len() - 1;
                        return Ok(Outcome::CandidateRefutation {
                            certificate: Certificate {
                                ordered,
                                nodes,
                                final_node,
                            },
                            statistics,
                        });
                    }
                }
            }
        }
        if ordered
            && ordered::derive(
                &mut nodes,
                parent,
                (&functions, &predicates),
                limits,
                &mut statistics,
            )?
        {
            let final_node = nodes.len() - 1;
            return Ok(Outcome::CandidateRefutation {
                certificate: Certificate {
                    ordered,
                    nodes,
                    final_node,
                },
                statistics,
            });
        }
        parent += 1;
    }
    Ok(Outcome::Unknown(statistics))
}

struct BoundedText {
    text: String,
    maximum: usize,
}
impl Write for BoundedText {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        if text.len() > self.maximum.saturating_sub(self.text.len()) {
            return Err(fmt::Error);
        }
        self.text.push_str(text);
        Ok(())
    }
}

fn term_text(value: &Term, out: &mut BoundedText) -> fmt::Result {
    match value {
        Term::Var(id) => write!(out, "(v {id})"),
        Term::Fun(id, arguments) => {
            write!(out, "(f {id}")?;
            for value in arguments {
                out.write_char(' ')?;
                term_text(value, out)?;
            }
            out.write_char(')')
        }
    }
}

fn clause_text(
    clause: &[fang_equality_inference_core::Literal],
    out: &mut BoundedText,
) -> fmt::Result {
    out.write_str("(clause")?;
    for literal in clause {
        write!(out, " ({} ", if literal.positive { "pos" } else { "neg" })?;
        match &literal.atom {
            Atom::Equal(left, right) => {
                out.write_str("(eq ")?;
                term_text(left, out)?;
                out.write_char(' ')?;
                term_text(right, out)?;
            }
            Atom::Predicate(id, arguments) => {
                write!(out, "(pred {id}")?;
                for value in arguments {
                    out.write_char(' ')?;
                    term_text(value, out)?;
                }
            }
        }
        out.write_str("))")?;
    }
    out.write_char(')')
}

fn substitution_text(substitution: &Substitution, out: &mut BoundedText) -> fmt::Result {
    out.write_str("(subst")?;
    for (variable, image) in substitution {
        write!(out, " ({variable} ")?;
        term_text(image, out)?;
        out.write_char(')')?;
    }
    out.write_char(')')
}

impl Certificate {
    // Version 5 omits unused search history. The sequence remains in original
    // order, so remapped parents precede their child. No clause is changed.
    fn serialization_order(&self, ancestors_only: bool) -> Result<(Vec<usize>, Vec<usize>), Error> {
        let mut selected = vec![!ancestors_only; self.nodes.len()];
        if self.final_node >= self.nodes.len() {
            return Err(Error::Certificate("final node is out of range"));
        }
        if ancestors_only {
            let mut pending = vec![self.final_node];
            while let Some(index) = pending.pop() {
                if selected[index] {
                    continue;
                }
                selected[index] = true;
                let parents: &[usize] = match &self.nodes[index].rule {
                    Rule::Input(_) => &[],
                    Rule::EqualityResolution { parent, .. } | Rule::Factor { parent, .. } => {
                        &[*parent]
                    }
                    Rule::Resolve { left, right, .. } => &[*left, *right],
                    Rule::Paramodulate { source, target, .. } => &[*source, *target],
                };
                for &parent in parents {
                    if parent >= index {
                        return Err(Error::Certificate("parent does not precede child"));
                    }
                    pending.push(parent);
                }
            }
        }
        let order: Vec<_> = selected
            .iter()
            .enumerate()
            .filter_map(|(index, keep)| keep.then_some(index))
            .collect();
        let mut ids = vec![usize::MAX; self.nodes.len()];
        for (id, &index) in order.iter().enumerate() {
            ids[index] = id;
        }
        Ok((order, ids))
    }

    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    pub fn to_text(&self, maximum: usize) -> Result<String, Error> {
        self.serialize(maximum, self.ordered)
    }

    /// Retain complete candidate search history for local diagnosis. This uses
    /// the same dialect and clauses, without removing unreferenced nodes.
    pub fn to_text_with_history(&self, maximum: usize) -> Result<String, Error> {
        self.serialize(maximum, false)
    }

    fn serialize(&self, maximum: usize, ancestors_only: bool) -> Result<String, Error> {
        let (order, ids) = self.serialization_order(ancestors_only)?;
        let mut out = BoundedText {
            text: String::new(),
            maximum,
        };
        let result = (|| -> fmt::Result {
            write!(
                out,
                "(fang-proof {}\n  (preprocessing identity-cnf-equality-v1)\n",
                if self.ordered { 5 } else { 4 }
            )?;
            for (id, &original) in order.iter().enumerate() {
                let node = &self.nodes[original];
                match &node.rule {
                    Rule::Input(index) => writeln!(out, "  (input {id} {index})")?,
                    Rule::Paramodulate {
                        source,
                        target,
                        source_pivot,
                        direction,
                        position,
                        substitution,
                    } => {
                        let source = ids[*source];
                        let target = ids[*target];
                        write!(
                            out,
                            "  (paramodulate {id} {source} {target} {source_pivot} {} ",
                            position.literal
                        )?;
                        match position.root {
                            fang_equality_paramodulation_core::Root::Argument(index) => {
                                write!(out, "(argument {index})")?
                            }
                            fang_equality_paramodulation_core::Root::EqualityLeft => {
                                out.write_str("(equality-left)")?
                            }
                            fang_equality_paramodulation_core::Root::EqualityRight => {
                                out.write_str("(equality-right)")?
                            }
                        }
                        out.write_str(" (path")?;
                        for index in &position.path {
                            write!(out, " {index}")?;
                        }
                        write!(
                            out,
                            ") {} ",
                            match direction {
                                fang_equality_paramodulation_core::Direction::LeftToRight =>
                                    "forward",
                                fang_equality_paramodulation_core::Direction::RightToLeft =>
                                    "reverse",
                            }
                        )?;
                        substitution_text(substitution, &mut out)?;
                        out.write_char(' ')?;
                        clause_text(&node.clause, &mut out)?;
                        out.write_str(")\n")?;
                    }
                    Rule::EqualityResolution {
                        parent,
                        pivot,
                        substitution,
                    } => {
                        let premise = &self.nodes[*parent].clause;
                        let Atom::Equal(left, right) = &premise[*pivot].atom else {
                            return Err(fmt::Error);
                        };
                        let parent = ids[*parent];
                        write!(out, "  (eq-resolve {id} {parent} ")?;
                        clause_text(&premise[..*pivot], &mut out)?;
                        out.write_char(' ')?;
                        clause_text(&premise[*pivot + 1..], &mut out)?;
                        out.write_char(' ')?;
                        term_text(left, &mut out)?;
                        out.write_char(' ')?;
                        term_text(right, &mut out)?;
                        out.write_char(' ')?;
                        substitution_text(substitution, &mut out)?;
                        out.write_char(' ')?;
                        clause_text(&node.clause, &mut out)?;
                        out.write_str(")\n")?;
                    }
                    Rule::Factor {
                        parent,
                        first,
                        second,
                        substitution,
                    } => {
                        let parent = ids[*parent];
                        write!(out, "  (factor {id} {parent} {first} {second} ")?;
                        substitution_text(substitution, &mut out)?;
                        out.write_char(' ')?;
                        clause_text(&node.clause, &mut out)?;
                        out.write_str(")\n")?;
                    }
                    Rule::Resolve {
                        left,
                        left_position,
                        right,
                        right_position,
                        substitution,
                    } => {
                        let left = ids[*left];
                        let right = ids[*right];
                        write!(
                            out,
                            "  (resolve {id} {left} {left_position} {right} {right_position} "
                        )?;
                        substitution_text(substitution, &mut out)?;
                        out.write_char(' ')?;
                        clause_text(&node.clause, &mut out)?;
                        out.write_str(")\n")?;
                    }
                }
            }
            writeln!(out, "  (final {}))", ids[self.final_node])
        })();
        result.map_err(|_| Error::Resource("certificate byte limit"))?;
        Ok(out.text)
    }
}
