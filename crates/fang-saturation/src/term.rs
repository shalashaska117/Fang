// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Hash-consed terms: equal terms have equal identifiers. Function symbols keep their numbers; predicate p is
//! stored as symbol `functions + p`, so a predicate atom is an ordinary term of the bank.

use std::collections::HashMap;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

pub type TermId = u32;
const NONE: u32 = u32::MAX;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Head {
    Var(u32),
    Sym(u32),
}

#[derive(Clone, Copy, Debug)]
struct Node {
    head: Head,
    start: u32,
    len: u32,
    /// Node count of the tree, saturating; every symbol and variable weighs 1.
    weight: u32,
    /// Height of the tree; a leaf has height 1.
    depth: u32,
    ground: bool,
    next: u32,
}

#[derive(Default)]
pub struct Bank {
    nodes: Vec<Node>,
    args: Vec<TermId>,
    buckets: HashMap<u64, u32>,
    vars: Vec<TermId>,
}

fn key(head: Head, args: &[TermId]) -> u64 {
    // DefaultHasher::new uses fixed keys, so identifiers do not depend on the run.
    let mut hasher = DefaultHasher::new();
    head.hash(&mut hasher);
    args.hash(&mut hasher);
    hasher.finish()
}

impl Bank {
    pub fn new() -> Self {
        Self::default()
    }

    fn intern(&mut self, head: Head, args: &[TermId]) -> TermId {
        let hash = key(head, args);
        let first = self.buckets.get(&hash).copied().unwrap_or(NONE);
        let mut at = first;
        while at != NONE {
            let node = self.nodes[at as usize];
            if node.head == head
                && self.args[node.start as usize..(node.start + node.len) as usize] == *args
            {
                return at;
            }
            at = node.next;
        }
        let mut weight: u32 = 1;
        let mut depth = 0;
        let mut ground = matches!(head, Head::Sym(_));
        for &argument in args {
            let child = self.nodes[argument as usize];
            weight = weight.saturating_add(child.weight);
            depth = depth.max(child.depth);
            ground &= child.ground;
        }
        let start = self.args.len() as u32;
        self.args.extend_from_slice(args);
        let id = self.nodes.len() as u32;
        self.nodes.push(Node {
            head,
            start,
            len: args.len() as u32,
            weight,
            depth: depth + 1,
            ground,
            next: first,
        });
        self.buckets.insert(hash, id);
        id
    }

    pub fn var(&mut self, variable: u32) -> TermId {
        let index = variable as usize;
        if index < self.vars.len() && self.vars[index] != NONE {
            return self.vars[index];
        }
        if index >= self.vars.len() {
            self.vars.resize(index + 1, NONE);
        }
        let id = self.intern(Head::Var(variable), &[]);
        self.vars[index] = id;
        id
    }

    pub fn app(&mut self, symbol: u32, args: &[TermId]) -> TermId {
        self.intern(Head::Sym(symbol), args)
    }

    pub fn head(&self, term: TermId) -> Head {
        self.nodes[term as usize].head
    }

    pub fn args(&self, term: TermId) -> &[TermId] {
        let node = &self.nodes[term as usize];
        &self.args[node.start as usize..(node.start + node.len) as usize]
    }

    pub fn arg(&self, term: TermId, index: usize) -> TermId {
        self.args(term)[index]
    }

    pub fn weight(&self, term: TermId) -> u32 {
        self.nodes[term as usize].weight
    }

    pub fn depth(&self, term: TermId) -> u32 {
        self.nodes[term as usize].depth
    }

    pub fn ground(&self, term: TermId) -> bool {
        self.nodes[term as usize].ground
    }

    pub fn as_var(&self, term: TermId) -> Option<u32> {
        match self.head(term) {
            Head::Var(variable) => Some(variable),
            Head::Sym(_) => None,
        }
    }

    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Whether `variable` occurs in `term`.
    pub fn contains_var(&self, term: TermId, variable: u32) -> bool {
        if self.ground(term) {
            return false;
        }
        match self.head(term) {
            Head::Var(other) => other == variable,
            Head::Sym(_) => self
                .args(term)
                .iter()
                .any(|&child| self.contains_var(child, variable)),
        }
    }

    /// Variable occurrences of `term`, appended in left-to-right order.
    pub fn collect_vars(&self, term: TermId, found: &mut Vec<u32>) {
        if self.ground(term) {
            return;
        }
        match self.head(term) {
            Head::Var(variable) => found.push(variable),
            Head::Sym(_) => {
                for &child in self.args(term) {
                    self.collect_vars(child, found);
                }
            }
        }
    }

    /// Import a Fang term; `rename` maps each source variable to its internal number.
    pub fn import(
        &mut self,
        term: &fang::syntax::Term,
        rename: &mut dyn FnMut(u32) -> u32,
    ) -> TermId {
        match term {
            fang::syntax::Term::Var(variable) => {
                let internal = rename(*variable);
                self.var(internal)
            }
            fang::syntax::Term::Fun(symbol, arguments) => {
                let mut children = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    children.push(self.import(argument, rename));
                }
                self.app(*symbol, &children)
            }
        }
    }

    /// Export a term; `rename` maps each internal variable to its certificate number.
    pub fn export(&self, term: TermId, rename: &dyn Fn(u32) -> u32) -> fang::syntax::Term {
        match self.head(term) {
            Head::Var(variable) => fang::syntax::Term::Var(rename(variable)),
            Head::Sym(symbol) => fang::syntax::Term::Fun(
                symbol,
                self.args(term)
                    .iter()
                    .map(|&child| self.export(child, rename))
                    .collect(),
            ),
        }
    }
}
