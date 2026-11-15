// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Candidate indexes over the active set. Each list holds active clauses in activation order, and each query
//! returns a superset of the clauses a linear scan would act on, so the search makes the same inferences in the
//! same order with the indexes on or off. Deleted clauses stay in the lists and are skipped when read.

use crate::clause::Id;
use crate::clause::{Atom, Lit};
use std::collections::HashMap;

/// A literal's predicate symbol (u32::MAX for an equation) and sign.
pub type Key = (u32, bool);

#[derive(Default)]
pub struct Index {
    /// Symbol to the clauses with a subterm of that top symbol that superposition may rewrite.
    pub into: HashMap<u32, Vec<Id>>,
    /// Symbol to the clauses with an equation side of that top symbol that superposition may rewrite with.
    pub from: HashMap<u32, Vec<Id>>,
    /// Clauses with an equation side that is a variable and may rewrite.
    pub from_variable: Vec<Id>,
    /// Resolution key to the clauses with a literal of that key that resolution may use.
    pub resolution: HashMap<Key, Vec<Id>>,
    /// For forward subsumption: each clause under one of its keys, the one with the shortest list.
    pub subsume_one: HashMap<Key, Vec<Id>>,
    /// Ground units match only an identical atom, up to equation symmetry.
    /// They are omitted from subsume_one, including its unit-deletion queries.
    pub ground_units: HashMap<Lit, Vec<Id>>,
    /// Non-unit clauses containing this ground literal, for backward subsumption
    /// by a ground unit. Unit occurrences are already in ground_units.
    pub ground_in_nonunits: HashMap<Lit, Vec<Id>>,
    /// For backward subsumption: each clause under every key of its literals.
    pub subsume_all: HashMap<Key, Vec<Id>>,
    /// Top symbol of a unit equation side to the unit and whether that side is the right one.
    pub unit_from: HashMap<u32, Vec<(Id, bool)>>,
    /// Top symbol to the clauses with a subterm of that symbol, for backward demodulation.
    pub symbols: HashMap<u32, Vec<Id>>,
}

pub fn ground_unit_key(mut literal: Lit) -> Lit {
    if let Atom::Eq(left, right) = literal.atom {
        literal.atom = Atom::Eq(left.min(right), left.max(right));
    }
    literal
}

/// The lists named by `keys` in `map`, joined.
pub fn gather<K: std::hash::Hash + Eq>(
    map: &HashMap<K, Vec<Id>>,
    keys: impl IntoIterator<Item = K>,
    out: &mut Vec<Id>,
) {
    for key in keys {
        if let Some(list) = map.get(&key) {
            out.extend_from_slice(list);
        }
    }
}
