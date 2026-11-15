// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Proof extraction and the version-8 certificate. Only the ancestors of the empty clause are written, in
//! creation order and renumbered, the empty clause last. Each step is recomputed from its rule and replayed
//! through the reviewed Rust reconstruction before it is written; the Lean checker still decides.

use crate::clause::{Atom, Id, Root, Rule};
use crate::search::Search;
use fang::syntax::Term;
use fang_equality_inference_core::{self as inference, Clause, Literal, Substitution, checked};
use fang_equality_paramodulation_core as para;
use std::fmt::Write;

/// The certificate cap of the final limits record (`certificateLimit`, 5,081,233 bytes, from certificate measurement
/// v3), which the first install round ships. The header counts toward it, since the text written here starts with it,
/// so a written certificate never exceeds the cap. Change it only here.
pub const MAX_CERTIFICATE_BYTES: usize = 5_081_233;

pub const HEADER: &str =
    "(fang-proof 8\n  (preprocessing expanded-fof-equality-skolem-distributive-v1)\n";

#[derive(Debug)]
pub enum ProofError {
    /// The refutation uses equality factoring, which the version-8 format cannot state.
    NeedsEqualityFactoring,
    /// The certificate would exceed its byte cap.
    Bytes { needed: usize },
    /// A recomputed step differs from the search, or the reconstruction disagrees: a producer bug.
    Internal(&'static str),
}

pub struct Certificate {
    pub text: String,
    pub nodes: usize,
    pub by_rule: Vec<(String, u64)>,
    /// Steps whose replay hit a reconstruction resource bound (term depth 64 and the like) and were written
    /// without that replay.
    pub unchecked: u64,
    /// Indices of the prepared input clauses the refutation uses, ascending.
    pub inputs: Vec<usize>,
}

fn reconstruction_limits() -> inference::Limits {
    inference::Limits {
        max_depth: 64,
        max_literals: 256,
        max_bindings: 1 << 16,
        max_output_nodes: 1 << 26,
        max_operations: 1 << 28,
    }
}

fn term_text(value: &Term, out: &mut String) {
    match value {
        Term::Var(id) => {
            let _ = write!(out, "(v {id})");
        }
        Term::Fun(id, arguments) => {
            let _ = write!(out, "(f {id}");
            for argument in arguments {
                out.push(' ');
                term_text(argument, out);
            }
            out.push(')');
        }
    }
}

fn clause_text(clause: &[Literal], out: &mut String) {
    out.push_str("(clause");
    for literal in clause {
        let _ = write!(out, " ({} ", if literal.positive { "pos" } else { "neg" });
        match &literal.atom {
            inference::Atom::Equal(left, right) => {
                out.push_str("(eq ");
                term_text(left, out);
                out.push(' ');
                term_text(right, out);
            }
            inference::Atom::Predicate(id, arguments) => {
                let _ = write!(out, "(pred {id}");
                for argument in arguments {
                    out.push(' ');
                    term_text(argument, out);
                }
            }
        }
        out.push_str("))");
    }
    out.push(')');
}

fn substitution_text(substitution: &Substitution, out: &mut String) {
    out.push_str("(subst");
    for (variable, image) in substitution {
        let _ = write!(out, " ({variable} ");
        term_text(image, out);
        out.push(')');
    }
    out.push(')');
}

fn rename(clause: &Clause, side: u32) -> Clause {
    fn term(value: &Term, side: u32) -> Term {
        match value {
            Term::Var(id) => Term::Var(2 * id + side),
            Term::Fun(symbol, arguments) => {
                Term::Fun(*symbol, arguments.iter().map(|a| term(a, side)).collect())
            }
        }
    }
    clause
        .iter()
        .map(|literal| Literal {
            positive: literal.positive,
            atom: match &literal.atom {
                inference::Atom::Predicate(id, arguments) => inference::Atom::Predicate(
                    *id,
                    arguments.iter().map(|a| term(a, side)).collect(),
                ),
                inference::Atom::Equal(left, right) => {
                    inference::Atom::Equal(term(left, side), term(right, side))
                }
            },
        })
        .collect()
}

enum Replay {
    Same,
    Resource,
    Different,
}

fn core_error(error: inference::Error) -> Replay {
    use inference::Error::*;
    match error {
        Depth | Literals | Bindings | OutputNodes | Operations => Replay::Resource,
        _ => Replay::Different,
    }
}

fn para_error(error: para::Error) -> Replay {
    match error {
        para::Error::Resource(_) => Replay::Resource,
        para::Error::Input(inner) => core_error(inner),
        _ => Replay::Different,
    }
}

fn compare(result: Clause, claimed: &Clause) -> Replay {
    if result == *claimed {
        Replay::Same
    } else {
        Replay::Different
    }
}

impl Search<'_> {
    /// The clause as the certificate states it: input clauses with their own variable numbers.
    fn certificate_clause(&self, id: Id) -> Clause {
        let record = &self.clauses[id as usize];
        let original = match &record.rule {
            Rule::Input { original, .. } => Some(original),
            _ => None,
        };
        let rename =
            |variable: u32| original.map_or(variable, |numbers| numbers[variable as usize]);
        record
            .lits
            .iter()
            .map(|literal| Literal {
                positive: literal.positive,
                atom: match literal.atom {
                    Atom::Pred(term) => {
                        let crate::term::Head::Sym(symbol) = self.bank.head(term) else {
                            unreachable!("predicate atom")
                        };
                        inference::Atom::Predicate(
                            symbol - self.functions as u32,
                            self.bank
                                .args(term)
                                .iter()
                                .map(|&a| self.bank.export(a, &rename))
                                .collect(),
                        )
                    }
                    Atom::Eq(left, right) => inference::Atom::Equal(
                        self.bank.export(left, &rename),
                        self.bank.export(right, &rename),
                    ),
                },
            })
            .collect()
    }

    fn replay(
        &self,
        rule: &Rule,
        parents: &[Clause],
        sigma: &Substitution,
        claimed: &Clause,
    ) -> Replay {
        let (functions, predicates, limits) = (
            &self.function_arities,
            &self.predicate_arities,
            reconstruction_limits(),
        );
        match rule {
            Rule::Factor { first, second, .. } => {
                match checked::instantiate(&parents[0], sigma, functions, predicates, &limits) {
                    Ok(result) => {
                        let mut clause = result.clause;
                        if clause[*first as usize] != clause[*second as usize] {
                            return Replay::Different;
                        }
                        clause.remove(*second as usize);
                        compare(clause, claimed)
                    }
                    Err(error) => core_error(error),
                }
            }
            Rule::EqRes { pivot, .. } => {
                match inference::equality_resolution(
                    &parents[0],
                    *pivot as usize,
                    sigma,
                    functions,
                    predicates,
                    &limits,
                ) {
                    Ok(result) => compare(result.clause, claimed),
                    Err(error) => core_error(error),
                }
            }
            Rule::Resolve {
                left_lit,
                right_lit,
                ..
            } => {
                let left = checked::instantiate(
                    &rename(&parents[0], 0),
                    sigma,
                    functions,
                    predicates,
                    &limits,
                );
                let right = checked::instantiate(
                    &rename(&parents[1], 1),
                    sigma,
                    functions,
                    predicates,
                    &limits,
                );
                match (left, right) {
                    (Ok(left), Ok(right)) => {
                        let (mut left, mut right) = (left.clause, right.clause);
                        let (i, j) = (*left_lit as usize, *right_lit as usize);
                        if left[i].positive == right[j].positive || left[i].atom != right[j].atom {
                            return Replay::Different;
                        }
                        left.remove(i);
                        right.remove(j);
                        left.extend(right);
                        compare(left, claimed)
                    }
                    (Err(error), _) | (_, Err(error)) => core_error(error),
                }
            }
            Rule::Para {
                pivot,
                reverse,
                pos,
                ..
            }
            | Rule::Demod {
                pivot,
                reverse,
                pos,
                ..
            } => {
                let position = para::Position {
                    literal: pos.literal as usize,
                    root: match pos.root {
                        Root::Argument(index) => para::Root::Argument(index as usize),
                        Root::Left => para::Root::EqualityLeft,
                        Root::Right => para::Root::EqualityRight,
                    },
                    path: pos.path.iter().map(|&index| index as usize).collect(),
                };
                let witness = para::Witness {
                    source_pivot: *pivot as usize,
                    direction: if *reverse {
                        para::Direction::RightToLeft
                    } else {
                        para::Direction::LeftToRight
                    },
                    position: &position,
                    substitution: sigma,
                };
                match para::paramodulate(
                    &rename(&parents[0], 0),
                    &rename(&parents[1], 1),
                    witness,
                    functions,
                    predicates,
                    &limits,
                ) {
                    Ok(result) => compare(result.clause, claimed),
                    Err(error) => para_error(error),
                }
            }
            Rule::Input { .. } | Rule::EqFactor { .. } => Replay::Different,
        }
    }

    /// Write the certificate for the refutation ending in `empty`.
    pub fn certificate(&mut self, empty: Id, max_bytes: usize) -> Result<Certificate, ProofError> {
        let mut keep = vec![false; self.clauses.len()];
        let mut pending = vec![empty];
        while let Some(id) = pending.pop() {
            if keep[id as usize] {
                continue;
            }
            keep[id as usize] = true;
            for parent in self.clauses[id as usize].rule.parents() {
                if parent >= id {
                    return Err(ProofError::Internal("parent does not precede its clause"));
                }
                pending.push(parent);
            }
        }
        let order: Vec<Id> = (0..self.clauses.len() as Id)
            .filter(|&id| keep[id as usize])
            .collect();
        if order
            .iter()
            .any(|&id| matches!(self.clauses[id as usize].rule, Rule::EqFactor { .. }))
        {
            return Err(ProofError::NeedsEqualityFactoring);
        }
        let mut number = vec![u32::MAX; self.clauses.len()];
        for (node, &id) in order.iter().enumerate() {
            number[id as usize] = node as u32;
        }
        let mut text = String::from(HEADER);
        let mut by_rule: Vec<(String, u64)> = Vec::new();
        let mut unchecked = 0;
        let mut inputs = Vec::new();
        for (node, &id) in order.iter().enumerate() {
            let rule = self.clauses[id as usize].rule.clone();
            match by_rule.iter_mut().find(|entry| entry.0 == rule.name()) {
                Some(entry) => entry.1 += 1,
                None => by_rule.push((rule.name().to_owned(), 1)),
            }
            if let Rule::Input { index, .. } = &rule {
                inputs.push(*index);
                let _ = writeln!(text, "  (input {node} {index})");
                continue;
            }
            if !self.bind_rule(&rule) {
                return Err(ProofError::Internal("recomputed unification failed"));
            }
            let (lits, sigma) = self.conclude(&rule, true);
            self.binds.clear();
            if lits.as_slice() != self.clauses[id as usize].lits.as_ref() {
                return Err(ProofError::Internal(
                    "recomputed conclusion differs from the search",
                ));
            }
            let sigma: Substitution = sigma
                .expect("substitution requested")
                .into_iter()
                .map(|(key, image)| (key, self.bank.export(image, &|variable| variable)))
                .collect();
            let claimed = self.certificate_clause(id);
            let parents: Vec<Clause> = rule
                .parents()
                .iter()
                .map(|&parent| self.certificate_clause(parent))
                .collect();
            match self.replay(&rule, &parents, &sigma, &claimed) {
                Replay::Same => {}
                Replay::Resource => unchecked += 1,
                Replay::Different => {
                    return Err(ProofError::Internal(
                        "reconstruction differs from the claimed clause",
                    ));
                }
            }
            let parent_numbers: Vec<u32> = rule
                .parents()
                .iter()
                .map(|&parent| number[parent as usize])
                .collect();
            match &rule {
                Rule::Factor { first, second, .. } => {
                    let _ = write!(
                        text,
                        "  (factor {node} {} {first} {second} ",
                        parent_numbers[0]
                    );
                }
                Rule::EqRes { pivot, .. } => {
                    let premise = &parents[0];
                    let inference::Atom::Equal(left, right) = &premise[*pivot as usize].atom else {
                        return Err(ProofError::Internal(
                            "equality resolution pivot is not an equation",
                        ));
                    };
                    let _ = write!(text, "  (eq-resolve {node} {} ", parent_numbers[0]);
                    clause_text(&premise[..*pivot as usize], &mut text);
                    text.push(' ');
                    clause_text(&premise[*pivot as usize + 1..], &mut text);
                    text.push(' ');
                    term_text(left, &mut text);
                    text.push(' ');
                    term_text(right, &mut text);
                    text.push(' ');
                }
                Rule::Resolve {
                    left_lit,
                    right_lit,
                    ..
                } => {
                    let _ = write!(
                        text,
                        "  (resolve {node} {} {left_lit} {} {right_lit} ",
                        parent_numbers[0], parent_numbers[1]
                    );
                }
                Rule::Para {
                    pivot,
                    reverse,
                    pos,
                    ..
                }
                | Rule::Demod {
                    pivot,
                    reverse,
                    pos,
                    ..
                } => {
                    let _ = write!(
                        text,
                        "  (paramodulate {node} {} {} {pivot} {} ",
                        parent_numbers[0], parent_numbers[1], pos.literal
                    );
                    match pos.root {
                        Root::Argument(index) => {
                            let _ = write!(text, "(argument {index})");
                        }
                        Root::Left => text.push_str("(equality-left)"),
                        Root::Right => text.push_str("(equality-right)"),
                    }
                    text.push_str(" (path");
                    for index in &pos.path {
                        let _ = write!(text, " {index}");
                    }
                    let _ = write!(text, ") {} ", if *reverse { "reverse" } else { "forward" });
                }
                Rule::Input { .. } | Rule::EqFactor { .. } => unreachable!("handled above"),
            }
            substitution_text(&sigma, &mut text);
            text.push(' ');
            clause_text(&claimed, &mut text);
            text.push_str(")\n");
        }
        let _ = writeln!(text, "  (final {}))", order.len() - 1);
        // The whole text is built first, so an oversize proof reports how much it needs.
        if text.len() > max_bytes {
            return Err(ProofError::Bytes { needed: text.len() });
        }
        inputs.sort_unstable();
        inputs.dedup();
        Ok(Certificate {
            text,
            nodes: order.len(),
            by_rule,
            unchecked,
            inputs,
        })
    }
}
