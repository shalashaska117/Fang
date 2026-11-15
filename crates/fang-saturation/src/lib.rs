// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
#![forbid(unsafe_code)]

//! The third version's saturation search. It reads the prepared numeric
//! clauses the reviewed producers build and writes version-8 candidate certificates made of the steps the
//! checker accepts. Every result stays a candidate until the independent checker accepts it.

pub mod cited;
pub mod clause;
pub mod critical_score;
mod ground_join;
pub mod index;
pub mod kbo;
mod lpo;
pub mod options;
pub mod producer;
pub mod proof;
pub mod search;
pub mod sine;
pub mod stats;
pub mod subst;
pub mod term;
mod unit_join;
mod variable_balance;
pub mod weights;

#[cfg(test)]
mod tests;
