// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Erase auxiliary goal constants by rewriting the original negative goal.
use super::*;
use crate::clause::Pos;
use crate::goal_transform::Transform;
use crate::subst::{Bindings, Renamer};
use crate::term::{Bank, Head, TermId};
use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

type Env = BTreeMap<u32, Term>;

fn bound_replacement_depth(
    term: &Term,
    env: &Env,
    depth: usize,
    work: &mut Work,
) -> Result<(), ProofError> {
    work.tick()?;
    if depth > 64 {
        return Err(ProofError::TransformLimit);
    }
    match term {
        Term::Var(variable) => {
            let image = env.get(variable).ok_or(ProofError::TransformUnsupported)?;
            // Images are ground original terms. Reject a variable image instead
            // of following a potentially cyclic environment.
            bound_replacement_depth(image, &Env::new(), depth, work)
        }
        Term::Fun(_, args) => {
            for arg in args {
                bound_replacement_depth(arg, env, depth + 1, work)?;
            }
            Ok(())
        }
    }
}

struct Work {
    left: usize,
    deadline: Option<Instant>,
}

fn instance(
    bank: &Bank,
    bindings: &Bindings,
    mut at: TermId,
    mut side: u8,
    renamer: &mut Renamer,
    depth: usize,
    work: &mut Work,
) -> Result<Term, ProofError> {
    work.tick()?;
    if depth > 64 {
        return Err(ProofError::TransformLimit);
    }
    while let Head::Var(variable) = bank.head(at) {
        work.tick()?;
        if let Some((next, next_side)) = bindings.get(side, variable) {
            at = next;
            side = next_side;
        } else {
            return Ok(Term::Var(renamer.assign(side, variable)));
        }
    }
    let Head::Sym(symbol) = bank.head(at) else {
        unreachable!()
    };
    Ok(Term::Fun(
        symbol,
        bank.args(at)
            .iter()
            .map(|&arg| instance(bank, bindings, arg, side, renamer, depth + 1, work))
            .collect::<Result<_, _>>()?,
    ))
}

#[allow(clippy::too_many_arguments)]
fn replaced(
    bank: &Bank,
    bindings: &Bindings,
    at: TermId,
    path: &[u16],
    to: TermId,
    renamer: &mut Renamer,
    depth: usize,
    work: &mut Work,
) -> Result<Term, ProofError> {
    work.tick()?;
    if depth > 64 {
        return Err(ProofError::TransformLimit);
    }
    if path.is_empty() {
        return instance(bank, bindings, to, 0, renamer, depth, work);
    }
    let Head::Sym(symbol) = bank.head(at) else {
        return Err(ProofError::TransformUnsupported);
    };
    let args = bank.args(at);
    if path[0] as usize >= args.len() {
        return Err(ProofError::TransformUnsupported);
    }
    let mut out = Vec::with_capacity(args.len());
    for (index, &arg) in args.iter().enumerate() {
        out.push(if index == path[0] as usize {
            replaced(
                bank,
                bindings,
                arg,
                &path[1..],
                to,
                renamer,
                depth + 1,
                work,
            )?
        } else {
            instance(bank, bindings, arg, 1, renamer, depth + 1, work)?
        });
    }
    Ok(Term::Fun(symbol, out))
}
impl Work {
    fn tick(&mut self) -> Result<(), ProofError> {
        self.left = self.left.checked_sub(1).ok_or(ProofError::TransformLimit)?;
        if self.left.is_multiple_of(256) && self.deadline.is_some_and(|end| Instant::now() >= end) {
            return Err(ProofError::TransformLimit);
        }
        Ok(())
    }
}

fn expand(
    term: &Term,
    env: &Env,
    transform: &Transform,
    depth: usize,
    work: &mut Work,
) -> Result<Term, ProofError> {
    work.tick()?;
    if depth > 64 {
        return Err(ProofError::TransformLimit);
    }
    match term {
        Term::Var(x) => {
            // Parent variables absent from the conclusion may be grounded freely.
            // Environment images and the fallback are ground original terms.
            expand(
                env.get(x).unwrap_or(&transform.fallback),
                &Env::new(),
                transform,
                depth,
                work,
            )
        }
        Term::Fun(f, args) if *f as usize >= transform.original_functions => {
            if !args.is_empty() {
                return Err(ProofError::TransformUnsupported);
            }
            let term = transform
                .definitions
                .get(*f as usize - transform.original_functions)
                .ok_or(ProofError::TransformUnsupported)?;
            expand(term, &Env::new(), transform, depth, work)
        }
        Term::Fun(f, args) => Ok(Term::Fun(
            *f,
            args.iter()
                .map(|t| expand(t, env, transform, depth + 1, work))
                .collect::<Result<_, _>>()?,
        )),
    }
}

fn unit_equation(clause: &Clause, positive: bool) -> Result<(&Term, &Term), ProofError> {
    match clause.as_slice() {
        [
            Literal {
                positive: p,
                atom: inference::Atom::Equal(a, b),
            },
        ] if *p == positive => Ok((a, b)),
        _ => Err(ProofError::TransformUnsupported),
    }
}

fn context_term<'a>(clause: &'a Clause, position: &Pos) -> Result<&'a Term, ProofError> {
    if position.literal != 0 {
        return Err(ProofError::TransformUnsupported);
    }
    let (a, b) = unit_equation(clause, false)?;
    let mut at = match position.root {
        Root::Left => a,
        Root::Right => b,
        _ => return Err(ProofError::TransformUnsupported),
    };
    for &index in &position.path {
        let Term::Fun(_, args) = at else {
            return Err(ProofError::TransformUnsupported);
        };
        at = args
            .get(index as usize)
            .ok_or(ProofError::TransformUnsupported)?;
    }
    Ok(at)
}

struct Writer<'a> {
    original: &'a [Clause],
    functions: &'a [usize],
    text: String,
    nodes: usize,
    inputs: BTreeMap<usize, usize>,
    definitions: BTreeSet<usize>,
    current: Clause,
    current_node: usize,
    rewrites: u64,
    max_bytes: usize,
}

impl Writer<'_> {
    fn bound(&self) -> Result<(), ProofError> {
        if self.text.len() > self.max_bytes {
            return Err(ProofError::Bytes {
                needed: self.text.len(),
            });
        }
        if self.nodes > 8192 {
            return Err(ProofError::TransformLimit);
        }
        Ok(())
    }
    fn input(&mut self, index: usize) -> Result<usize, ProofError> {
        if let Some(&node) = self.inputs.get(&index) {
            return Ok(node);
        }
        if index >= self.original.len() {
            return Err(ProofError::TransformUnsupported);
        }
        let node = self.nodes;
        self.nodes += 1;
        let _ = writeln!(self.text, "  (input {node} {index})");
        self.inputs.insert(index, node);
        self.bound()?;
        Ok(node)
    }
    fn rewrite(
        &mut self,
        input: usize,
        env: &Env,
        reverse: bool,
        position: &Pos,
        work: &mut Work,
    ) -> Result<(), ProofError> {
        work.tick()?;
        let source = self
            .original
            .get(input)
            .ok_or(ProofError::TransformUnsupported)?;
        let (left, right) = unit_equation(source, true)?;
        // The replacement's depth includes the context above the selected term.
        // Check before reconstruction so this is an explicit resource refusal.
        bound_replacement_depth(
            if reverse { left } else { right },
            env,
            position.path.len(),
            work,
        )?;
        let sigma: Substitution = env
            .iter()
            .map(|(&key, term)| {
                Ok((
                    key.checked_mul(2).ok_or(ProofError::TransformLimit)?,
                    term.clone(),
                ))
            })
            .collect::<Result<_, ProofError>>()?;
        let place = para::Position {
            literal: 0,
            root: match position.root {
                Root::Left => para::Root::EqualityLeft,
                Root::Right => para::Root::EqualityRight,
                _ => return Err(ProofError::TransformUnsupported),
            },
            path: position.path.iter().map(|&n| n as usize).collect(),
        };
        let limits = inference::Limits {
            max_depth: 64,
            max_literals: 1,
            max_bindings: 1 << 16,
            max_output_nodes: 1 << 17,
            max_operations: 1_000_000,
        };
        let result = para::paramodulate(
            &rename(source, 0),
            &self.current,
            para::Witness {
                source_pivot: 0,
                direction: if reverse {
                    para::Direction::RightToLeft
                } else {
                    para::Direction::LeftToRight
                },
                position: &place,
                substitution: &sigma,
            },
            self.functions,
            &[],
            &limits,
        )
        .map_err(|error| match para_error(error) {
            Replay::Resource => ProofError::TransformLimit,
            _ => ProofError::TransformUnsupported,
        })?;
        unit_equation(&result.clause, false)?;
        let source_node = self.input(input)?;
        let node = self.nodes;
        self.nodes += 1;
        let _ = write!(
            self.text,
            "  (paramodulate {node} {source_node} {} 0 0 ",
            self.current_node
        );
        self.text.push_str(match position.root {
            Root::Left => "(equality-left)",
            Root::Right => "(equality-right)",
            _ => unreachable!(),
        });
        self.text.push_str(" (path");
        for index in &position.path {
            let _ = write!(self.text, " {index}");
        }
        let _ = write!(
            self.text,
            ") {} ",
            if reverse { "reverse" } else { "forward" }
        );
        substitution_text(&sigma, &mut self.text);
        self.text.push(' ');
        clause_text(&result.clause, &mut self.text);
        self.text.push_str(")\n");
        self.current = result.clause;
        self.current_node = node;
        self.rewrites += 1;
        self.bound()
    }
    fn finish(mut self) -> Result<Certificate, ProofError> {
        let (left, right) = unit_equation(&self.current, false)?;
        if left != right {
            return Err(ProofError::TransformUnsupported);
        }
        let result = inference::equality_resolution(
            &self.current,
            0,
            &[],
            self.functions,
            &[],
            &reconstruction_limits(),
        )
        .map_err(|error| match core_error(error) {
            Replay::Resource => ProofError::TransformLimit,
            _ => ProofError::TransformUnsupported,
        })?;
        if !result.clause.is_empty() {
            return Err(ProofError::TransformUnsupported);
        }
        let node = self.nodes;
        self.nodes += 1;
        let _ = write!(
            self.text,
            "  (eq-resolve {node} {} (clause) (clause) ",
            self.current_node
        );
        term_text(left, &mut self.text);
        self.text.push(' ');
        term_text(right, &mut self.text);
        self.text.push_str(" (subst) (clause))\n");
        let _ = writeln!(self.text, "  (final {node}))");
        self.bound()?;
        Ok(Certificate {
            text: self.text,
            nodes: self.nodes,
            by_rule: vec![
                ("input".into(), self.inputs.len() as u64),
                ("superposition".into(), self.rewrites),
                ("eq-resolve".into(), 1),
            ],
            unchecked: 0,
            goal_definition_inputs: self.definitions.len(),
            inputs: self.inputs.into_keys().collect(),
        })
    }
}

enum Frame {
    Apply {
        id: Id,
        env: Env,
        reverse: bool,
        position: Pos,
    },
    Check {
        term: Term,
        position: Pos,
    },
}

impl Search<'_> {
    fn bounded_expansion_clause(&self, id: Id, work: &mut Work) -> Result<Clause, ProofError> {
        work.tick()?;
        let record = self
            .clauses
            .get(id as usize)
            .ok_or(ProofError::TransformUnsupported)?;
        if record.lits.len() != 1 {
            return Err(ProofError::TransformUnsupported);
        }
        let Atom::Eq(a, b) = record.lits[0].atom else {
            return Err(ProofError::TransformUnsupported);
        };
        for term in [a, b] {
            if self.bank.weight(term) > 4096 || self.bank.depth(term) > 65 {
                return Err(ProofError::TransformLimit);
            }
        }
        Ok(self.certificate_clause(id))
    }

    fn expansion_sigma(&mut self, id: Id, work: &mut Work) -> Result<Substitution, ProofError> {
        let rule = self.clauses[id as usize].rule.clone();
        let expected = self.bounded_expansion_clause(id, work)?;
        let (source, target, reverse, pos) = match &rule {
            Rule::Para {
                source,
                pivot: 0,
                target,
                reverse,
                pos,
            }
            | Rule::Demod {
                source,
                pivot: 0,
                target,
                reverse,
                pos,
            } => (*source, *target, *reverse, pos.clone()),
            _ => return Err(ProofError::TransformUnsupported),
        };
        self.bounded_expansion_clause(source, work)?;
        self.bounded_expansion_clause(target, work)?;
        if !self.bind_rule(&rule) {
            self.binds.clear();
            return Err(ProofError::TransformUnsupported);
        }
        let result = (|| {
            let Atom::Eq(a, b) = self.clauses[source as usize].lits[0].atom else {
                return Err(ProofError::TransformUnsupported);
            };
            let to = if reverse { a } else { b };
            let target_lit = self.clauses[target as usize].lits[0];
            let Atom::Eq(left, right) = target_lit.atom else {
                return Err(ProofError::TransformUnsupported);
            };
            if pos.literal != 0 {
                return Err(ProofError::TransformUnsupported);
            }
            let mut renamer = Renamer::new();
            let left = match pos.root {
                Root::Left => replaced(
                    &self.bank,
                    &self.binds,
                    left,
                    &pos.path,
                    to,
                    &mut renamer,
                    0,
                    work,
                )?,
                Root::Right => instance(&self.bank, &self.binds, left, 1, &mut renamer, 0, work)?,
                _ => return Err(ProofError::TransformUnsupported),
            };
            let right = match pos.root {
                Root::Right => replaced(
                    &self.bank,
                    &self.binds,
                    right,
                    &pos.path,
                    to,
                    &mut renamer,
                    0,
                    work,
                )?,
                Root::Left => instance(&self.bank, &self.binds, right, 1, &mut renamer, 0, work)?,
                _ => return Err(ProofError::TransformUnsupported),
            };
            if vec![Literal {
                positive: target_lit.positive,
                atom: inference::Atom::Equal(left, right),
            }] != expected
            {
                return Err(ProofError::TransformUnsupported);
            }
            let mut sigma = vec![];
            for (parent, side) in [(source, 0u8), (target, 1u8)] {
                for variable in 0..self.clauses[parent as usize].vars {
                    work.tick()?;
                    let key = self
                        .certificate_var(parent, variable)
                        .checked_mul(2)
                        .and_then(|n| n.checked_add(u32::from(side)))
                        .ok_or(ProofError::TransformLimit)?;
                    let term = self.bank.var(variable);
                    let image =
                        instance(&self.bank, &self.binds, term, side, &mut renamer, 0, work)?;
                    sigma.push((key, image));
                }
            }
            sigma.sort_by_key(|(key, _)| *key);
            Ok(sigma)
        })();
        self.binds.clear();
        result
    }

    fn expansion_parent_env(
        &self,
        parent: Id,
        side: u32,
        sigma: &Substitution,
        env: &Env,
        transform: &Transform,
        work: &mut Work,
    ) -> Result<Env, ProofError> {
        let mut output = Env::new();
        for variable in 0..self.clauses[parent as usize].vars {
            work.tick()?;
            let variable = self.certificate_var(parent, variable);
            let key = variable
                .checked_mul(2)
                .and_then(|x| x.checked_add(side))
                .ok_or(ProofError::TransformLimit)?;
            let index = sigma
                .binary_search_by_key(&key, |(key, _)| *key)
                .map_err(|_| ProofError::TransformUnsupported)?;
            output.insert(variable, expand(&sigma[index].1, env, transform, 0, work)?);
        }
        Ok(output)
    }

    fn expand_equation(
        &mut self,
        first: Frame,
        transform: &Transform,
        writer: &mut Writer<'_>,
        work: &mut Work,
    ) -> Result<(), ProofError> {
        let mut pending = vec![first];
        while let Some(frame) = pending.pop() {
            work.tick()?;
            if pending.len() > 4096 {
                return Err(ProofError::TransformLimit);
            }
            let Frame::Apply {
                id,
                env,
                reverse,
                position,
            } = frame
            else {
                let Frame::Check { term, position } = frame else {
                    unreachable!()
                };
                if context_term(&writer.current, &position)? != &term {
                    return Err(ProofError::TransformUnsupported);
                }
                continue;
            };
            let clause = self.bounded_expansion_clause(id, work)?;
            let (a, b) = unit_equation(&clause, true)?;
            let a = expand(a, &env, transform, 0, work)?;
            let b = expand(b, &env, transform, 0, work)?;
            let (from, to) = if reverse { (b, a) } else { (a, b) };
            if context_term(&writer.current, &position)? != &from {
                return Err(ProofError::TransformUnsupported);
            }
            let rule = self.clauses[id as usize].rule.clone();
            if let Rule::Input { index, .. } = rule {
                if index < transform.original_inputs {
                    writer.rewrite(index, &env, reverse, &position, work)?;
                } else {
                    if index >= transform.original_inputs + transform.definitions.len()
                        || from != to
                    {
                        return Err(ProofError::TransformUnsupported);
                    }
                    writer.definitions.insert(index);
                }
                if context_term(&writer.current, &position)? != &to {
                    return Err(ProofError::TransformUnsupported);
                }
                continue;
            }
            let (source, target, source_reverse, pos) = match rule {
                Rule::Para {
                    source,
                    pivot: 0,
                    reverse,
                    target,
                    pos,
                }
                | Rule::Demod {
                    source,
                    pivot: 0,
                    reverse,
                    target,
                    pos,
                } => (source, target, reverse, pos),
                _ => return Err(ProofError::TransformUnsupported),
            };
            if source >= id || target >= id || pos.literal != 0 {
                return Err(ProofError::TransformUnsupported);
            }
            let sigma = self.expansion_sigma(id, work)?;
            let source_env = self.expansion_parent_env(source, 0, &sigma, &env, transform, work)?;
            let target_env = self.expansion_parent_env(target, 1, &sigma, &env, transform, work)?;
            let mut inner = position.clone();
            inner.path.extend(&pos.path);
            if inner.path.len() > 64 {
                return Err(ProofError::TransformLimit);
            }
            let source_backward = match pos.root {
                Root::Left => !source_reverse,
                Root::Right => source_reverse,
                _ => return Err(ProofError::TransformUnsupported),
            };
            let source_frame = Frame::Apply {
                id: source,
                env: source_env,
                reverse: source_backward ^ reverse,
                position: inner,
            };
            let target_frame = Frame::Apply {
                id: target,
                env: target_env,
                reverse,
                position: position.clone(),
            };
            pending.push(Frame::Check { term: to, position });
            // The stack is reversed relative to the equational path.
            if (pos.root == Root::Left) ^ reverse {
                pending.push(target_frame);
                pending.push(source_frame);
            } else {
                pending.push(source_frame);
                pending.push(target_frame);
            }
        }
        Ok(())
    }

    fn final_resolution_equation(
        &mut self,
        empty: Id,
        rule: &Rule,
        transform: &Transform,
        work: &mut Work,
    ) -> Result<(Id, Id, Env), ProofError> {
        let Rule::Resolve {
            left,
            left_lit: 0,
            right,
            right_lit: 0,
        } = *rule
        else {
            return Err(ProofError::TransformUnsupported);
        };
        if left >= empty || right >= empty {
            return Err(ProofError::TransformUnsupported);
        }
        let a = self.bounded_expansion_clause(left, work)?;
        let b = self.bounded_expansion_clause(right, work)?;
        let (positive, negative, side) = if a[0].positive && !b[0].positive {
            (left, right, 0)
        } else if !a[0].positive && b[0].positive {
            (right, left, 1)
        } else {
            return Err(ProofError::TransformUnsupported);
        };
        if !self.bind_rule(rule) {
            self.binds.clear();
            return Err(ProofError::TransformUnsupported);
        }
        let result = (|| {
            let mut env = Env::new();
            let mut renamer = Renamer::new();
            for variable in 0..self.clauses[positive as usize].vars {
                work.tick()?;
                let key = self.certificate_var(positive, variable);
                let term = self.bank.var(variable);
                let image = instance(&self.bank, &self.binds, term, side, &mut renamer, 0, work)?;
                env.insert(key, expand(&image, &Env::new(), transform, 0, work)?);
            }
            Ok((negative, positive, env))
        })();
        self.binds.clear();
        result
    }

    pub(crate) fn expanded_goal_certificate(
        &mut self,
        empty: Id,
        original: &[Clause],
        transform: &Transform,
        max_bytes: usize,
        deadline: Option<Instant>,
    ) -> Result<Certificate, ProofError> {
        if deadline.is_some_and(|end| Instant::now() >= end) {
            return Err(ProofError::TransformLimit);
        }
        let mut work = Work {
            left: 1_000_000,
            deadline,
        };
        if !self.clauses[empty as usize].lits.is_empty() {
            return Err(ProofError::TransformUnsupported);
        }
        let rule = self.clauses[empty as usize].rule.clone();
        let (mut at, final_equation) = match rule {
            Rule::EqRes { parent, pivot: 0 } if parent < empty => (parent, None),
            Rule::Resolve { .. } => {
                let (negative, positive, env) =
                    self.final_resolution_equation(empty, &rule, transform, &mut work)?;
                (negative, Some((positive, env)))
            }
            _ => return Err(ProofError::TransformUnsupported),
        };
        let mut chain = vec![];
        let input = loop {
            work.tick()?;
            let clause = self.bounded_expansion_clause(at, &mut work)?;
            let (a, b) = unit_equation(&clause, false)?;
            // The first implementation translates ground negative proof chains.
            fn ground(t: &Term) -> bool {
                match t {
                    Term::Var(_) => false,
                    Term::Fun(_, xs) => xs.iter().all(ground),
                }
            }
            if !ground(a) || !ground(b) {
                return Err(ProofError::TransformUnsupported);
            }
            match self.clauses[at as usize].rule.clone() {
                Rule::Input { index, .. } if index < original.len() => break index,
                Rule::Para { source, target, .. } | Rule::Demod { source, target, .. }
                    if source < at && target < at =>
                {
                    chain.push(at);
                    at = target;
                }
                _ => return Err(ProofError::TransformUnsupported),
            }
        };
        let mut writer = Writer {
            original,
            functions: &transform.functions[..transform.original_functions],
            text: String::from(HEADER),
            nodes: 0,
            inputs: BTreeMap::new(),
            definitions: BTreeSet::new(),
            current: original[input].clone(),
            current_node: 0,
            rewrites: 0,
            max_bytes,
        };
        writer.current_node = writer.input(input)?;
        for id in chain.into_iter().rev() {
            work.tick()?;
            let (source, reverse, pos) = match self.clauses[id as usize].rule.clone() {
                Rule::Para {
                    source,
                    pivot: 0,
                    reverse,
                    pos,
                    ..
                }
                | Rule::Demod {
                    source,
                    pivot: 0,
                    reverse,
                    pos,
                    ..
                } => (source, reverse, pos),
                _ => return Err(ProofError::TransformUnsupported),
            };
            let sigma = self.expansion_sigma(id, &mut work)?;
            let env =
                self.expansion_parent_env(source, 0, &sigma, &Env::new(), transform, &mut work)?;
            self.expand_equation(
                Frame::Apply {
                    id: source,
                    env,
                    reverse,
                    position: pos,
                },
                transform,
                &mut writer,
                &mut work,
            )?;
            let claimed = self.bounded_expansion_clause(id, &mut work)?;
            let (a, b) = unit_equation(&claimed, false)?;
            let expected = vec![Literal {
                positive: false,
                atom: inference::Atom::Equal(
                    expand(a, &Env::new(), transform, 0, &mut work)?,
                    expand(b, &Env::new(), transform, 0, &mut work)?,
                ),
            }];
            if writer.current != expected {
                return Err(ProofError::TransformUnsupported);
            }
        }
        if let Some((id, env)) = final_equation {
            // Complementary unit resolution is an equation rewrite followed by
            // equality resolution. The original-input replay checks both steps.
            self.expand_equation(
                Frame::Apply {
                    id,
                    env,
                    reverse: false,
                    position: Pos {
                        literal: 0,
                        root: Root::Left,
                        path: vec![],
                    },
                },
                transform,
                &mut writer,
                &mut work,
            )?;
        }
        if deadline.is_some_and(|end| Instant::now() >= end) {
            return Err(ProofError::TransformLimit);
        }
        let certificate = writer.finish()?;
        if deadline.is_some_and(|end| Instant::now() >= end) {
            return Err(ProofError::TransformLimit);
        }
        Ok(certificate)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::options::Options;
    use crate::search::Limits;

    fn derive(search: &mut Search<'_>, rule: Rule) -> Id {
        assert!(search.bind_rule(&rule));
        let (lits, _) = search.conclude(&rule, false);
        search.binds.clear();
        let (weight, depth, vars) = crate::clause::measure(&search.bank, &lits);
        let mut record = search.clauses[0].clone();
        record.lits = lits.into_boxed_slice();
        record.rule = rule;
        record.weight = weight;
        record.depth = depth;
        record.vars = vars;
        let id = search.clauses.len() as Id;
        search.clauses.push(record);
        id
    }
    fn para(source: Id, target: Id, reverse: bool, root: Root, path: Vec<u16>) -> Rule {
        Rule::Para {
            source,
            target,
            pivot: 0,
            reverse,
            pos: Pos {
                literal: 0,
                root,
                path,
            },
        }
    }

    #[test]
    fn original_rewrite_that_exceeds_term_depth_is_a_resource_refusal() {
        let a = Term::Fun(0, vec![]);
        let f = |x| Term::Fun(1, vec![x]);
        let mut deep = a.clone();
        for _ in 0..64 {
            deep = f(deep);
        }
        let original = vec![vec![Literal {
            positive: true,
            atom: inference::Atom::Equal(f(Term::Var(37)), Term::Var(37)),
        }]];
        let mut writer = Writer {
            original: &original,
            functions: &[0, 1],
            text: String::from(HEADER),
            nodes: 0,
            inputs: BTreeMap::new(),
            definitions: BTreeSet::new(),
            current: vec![Literal {
                positive: false,
                atom: inference::Atom::Equal(deep, a.clone()),
            }],
            current_node: 0,
            rewrites: 0,
            max_bytes: MAX_CERTIFICATE_BYTES,
        };
        let result = writer.rewrite(
            0,
            &Env::from([(37, a)]),
            true,
            &Pos {
                literal: 0,
                root: Root::Left,
                path: vec![0; 64],
            },
            &mut Work {
                left: 1_000_000,
                deadline: None,
            },
        );
        assert!(matches!(result, Err(ProofError::TransformLimit)));
        assert_eq!(writer.nodes, 0);
        assert_eq!(writer.text, HEADER);
    }

    #[test]
    fn final_unit_resolution_expands_both_parent_orders_and_definition_terms() {
        for positive_first in [false, true] {
            let a = Term::Fun(0, vec![]);
            let f = |x| Term::Fun(1, vec![x]);
            let eq = |positive, left, right| {
                vec![Literal {
                    positive,
                    atom: inference::Atom::Equal(left, right),
                }]
            };
            let input = vec![
                eq(true, f(Term::Var(37)), Term::Var(37)),
                eq(false, f(a.clone()), a.clone()),
            ];
            let transform = crate::goal_transform::prepare(&input, &[0, 1], None)
                .unwrap()
                .unwrap();
            let options = Options::preset("step1").unwrap();
            let mut search = Search::new(
                &transform.clauses,
                &transform.functions,
                &[],
                &options,
                Limits::default(),
            )
            .unwrap();
            // f(a)=d, then d=a, and d!=a. The final rule resolves the units.
            let equation = derive(&mut search, para(2, 0, false, Root::Left, vec![]));
            let negative = derive(&mut search, para(2, 1, false, Root::Left, vec![]));
            let (left, right) = if positive_first {
                (equation, negative)
            } else {
                (negative, equation)
            };
            let empty = derive(
                &mut search,
                Rule::Resolve {
                    left,
                    left_lit: 0,
                    right,
                    right_lit: 0,
                },
            );
            let certificate = search
                .expanded_goal_certificate(empty, &input, &transform, MAX_CERTIFICATE_BYTES, None)
                .unwrap();
            assert_eq!(certificate.inputs, vec![0, 1]);
            assert_eq!(certificate.unchecked, 0);
            assert!(certificate.goal_definition_inputs > 0);
            assert!(!certificate.text.contains("(f 2"));
            assert!(search.binds.get(0, 0).is_none());
            // A future parent must be refused before any binding or export.
            search.clauses[empty as usize].rule = Rule::Resolve {
                left: empty,
                left_lit: 0,
                right,
                right_lit: 0,
            };
            assert!(matches!(
                search.expanded_goal_certificate(
                    empty,
                    &input,
                    &transform,
                    MAX_CERTIFICATE_BYTES,
                    None
                ),
                Err(ProofError::TransformUnsupported)
            ));
        }
    }

    #[test]
    fn variables_erased_from_a_critical_pair_get_consistent_ground_instances() {
        let a = Term::Fun(0, vec![]);
        let f = |x, y| Term::Fun(1, vec![x, y]);
        let g = |x| Term::Fun(2, vec![x]);
        let eq = |positive, x, y| {
            vec![Literal {
                positive,
                atom: inference::Atom::Equal(x, y),
            }]
        };
        let input = vec![
            eq(true, f(Term::Var(10), Term::Var(20)), Term::Var(10)),
            eq(true, f(Term::Var(5), Term::Var(17)), g(Term::Var(5))),
            eq(false, g(a.clone()), a),
        ];
        let transform = crate::goal_transform::prepare(&input, &[0, 2, 1], None)
            .unwrap()
            .unwrap();
        let options = Options::preset("step1").unwrap();
        let mut search = Search::new(
            &transform.clauses,
            &transform.functions,
            &[],
            &options,
            Limits::default(),
        )
        .unwrap();
        let pair = derive(&mut search, para(0, 1, false, Root::Left, vec![]));
        let negative = derive(&mut search, para(pair, 2, true, Root::Left, vec![]));
        let empty = derive(
            &mut search,
            Rule::EqRes {
                parent: negative,
                pivot: 0,
            },
        );
        let certificate = search
            .expanded_goal_certificate(empty, &input, &transform, MAX_CERTIFICATE_BYTES, None)
            .unwrap();
        assert_eq!(certificate.inputs, vec![0, 1, 2]);
        assert_eq!(certificate.nodes, 6);
        assert_eq!(certificate.unchecked, 0);
        assert!(!certificate.text.contains("(f 3"));
    }

    #[test]
    fn exponential_substitution_expansion_stops_at_the_work_bound() {
        let mut bank = Bank::new();
        let variables: Vec<_> = (0..17).map(|x| bank.var(x)).collect();
        let mut bindings = Bindings::new();
        for i in 0..16 {
            let image = bank.app(0, &[variables[i + 1], variables[i + 1]]);
            assert!(bindings.unify(&bank, variables[i], 0, image, 0));
        }
        let mut work = Work {
            left: 100,
            deadline: None,
        };
        assert!(matches!(
            instance(
                &bank,
                &bindings,
                variables[0],
                0,
                &mut Renamer::new(),
                0,
                &mut work
            ),
            Err(ProofError::TransformLimit)
        ));
        assert_eq!(work.left, 0);
    }

    #[test]
    fn nested_definitions_and_both_parent_sides_expand_to_original_rewrites() {
        for reversed_axiom in [false, true] {
            for right_goal in [false, true] {
                for right_parent in [false, true] {
                    let a = Term::Fun(0, vec![]);
                    let f = |t| Term::Fun(1, vec![t]);
                    let x = Term::Var(37);
                    let (left, right) = if reversed_axiom {
                        (x.clone(), f(x))
                    } else {
                        (f(x.clone()), x)
                    };
                    let goal = f(f(a.clone()));
                    let (goal_left, goal_right) = if right_goal { (a, goal) } else { (goal, a) };
                    let inputs = vec![
                        vec![Literal {
                            positive: true,
                            atom: inference::Atom::Equal(left, right),
                        }],
                        vec![Literal {
                            positive: false,
                            atom: inference::Atom::Equal(goal_left, goal_right),
                        }],
                    ];
                    let transform = crate::goal_transform::prepare(&inputs, &[0, 1], None)
                        .unwrap()
                        .unwrap();
                    let options = Options::preset("step1").unwrap();
                    let mut search = Search::new(
                        &transform.clauses,
                        &transform.functions,
                        &[],
                        &options,
                        Limits::default(),
                    )
                    .unwrap();
                    assert_eq!(search.clauses.len(), 4);
                    let d0 = derive(&mut search, para(0, 2, reversed_axiom, Root::Left, vec![]));
                    let root = if right_goal { Root::Right } else { Root::Left };
                    let final_negative = if right_parent {
                        let r = derive(&mut search, para(d0, 2, true, Root::Right, vec![]));
                        let n0 = derive(&mut search, para(r, 1, false, root, vec![0]));
                        derive(&mut search, para(r, n0, false, root, vec![]))
                    } else {
                        let d1 = derive(&mut search, para(2, 3, false, Root::Left, vec![0]));
                        let d2 =
                            derive(&mut search, para(0, d1, reversed_axiom, Root::Left, vec![]));
                        let n0 = derive(&mut search, para(3, 1, false, root, vec![]));
                        let n1 = derive(&mut search, para(d2, n0, true, root, vec![]));
                        derive(&mut search, para(d0, n1, true, root, vec![]))
                    };
                    let empty = derive(
                        &mut search,
                        Rule::EqRes {
                            parent: final_negative,
                            pivot: 0,
                        },
                    );
                    let certificate = search
                        .expanded_goal_certificate(
                            empty,
                            &inputs,
                            &transform,
                            MAX_CERTIFICATE_BYTES,
                            None,
                        )
                        .unwrap();
                    assert_eq!(certificate.inputs, vec![0, 1]);
                    assert_eq!(certificate.unchecked, 0);
                    assert!(certificate.goal_definition_inputs > 0);
                    assert_eq!(certificate.nodes, 5);
                    assert!(!certificate.text.contains("(f 2"));
                    assert!(!certificate.text.contains("(f 3"));
                    assert!(matches!(
                        search.expanded_goal_certificate(empty, &inputs, &transform, 1, None),
                        Err(ProofError::Bytes { .. })
                    ));
                    assert!(matches!(
                        search.expanded_goal_certificate(
                            empty,
                            &inputs,
                            &transform,
                            MAX_CERTIFICATE_BYTES,
                            Some(Instant::now())
                        ),
                        Err(ProofError::TransformLimit)
                    ));
                }
            }
        }
    }
}
