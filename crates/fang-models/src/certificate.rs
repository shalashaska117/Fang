// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The model certificate the Lean checker reads (`ModelCertificate.lean`): one table per function and predicate
//! symbol of the statements, keyed by the hexadecimal name the Lean decoders store and the arity.

use crate::problem::Problem;
use crate::search::Model;
use std::collections::{BTreeSet, HashMap};
use std::fmt::Write;

/// Dense tables up to this many cells; larger ones are sparse when that is shorter.
const DENSE_CELLS: usize = 1 << 16;

pub fn hex(name: &str) -> String {
    name.bytes().map(|byte| format!("{byte:02x}")).collect()
}

fn arguments(mut cell: usize, size: usize, arity: usize) -> Vec<usize> {
    let mut output = vec![0; arity];
    for position in (0..arity).rev() {
        output[position] = cell % size;
        cell /= size;
    }
    output
}

fn table<T: Copy + Eq + std::hash::Hash + Ord>(
    output: &mut String,
    cells: &[T],
    size: usize,
    arity: usize,
    render: impl Fn(T) -> usize,
    with_value: bool,
) {
    let mut counts: HashMap<T, usize> = HashMap::new();
    for &cell in cells {
        *counts.entry(cell).or_default() += 1;
    }
    let (&common, &count) = counts
        .iter()
        .max_by_key(|(value, count)| (**count, std::cmp::Reverse(**value)))
        .unwrap();
    let exceptions = cells.len() - count;
    let per_exception = arity + usize::from(with_value);
    if cells.len() <= DENSE_CELLS && cells.len() <= 2 + exceptions * per_exception {
        output.push_str(" dense");
        for &cell in cells {
            write!(output, " {}", render(cell)).unwrap();
        }
    } else {
        write!(output, " sparse {} {exceptions}", render(common)).unwrap();
        for (index, &cell) in cells.iter().enumerate() {
            if cell == common {
                continue;
            }
            for argument in arguments(index, size, arity) {
                write!(output, " {argument}").unwrap();
            }
            if with_value {
                write!(output, " {}", render(cell)).unwrap();
            }
        }
    }
    output.push('\n');
}

/// The certificate text for the input symbols that occur in the statements.
pub fn render(
    problem: &Problem,
    model: &Model,
    functions: &BTreeSet<u32>,
    predicates: &BTreeSet<u32>,
) -> String {
    let size = model.size as usize;
    let mut output = format!("fang-model 1\ndomain {size}\n");
    for &symbol in functions {
        let entry = &problem.functions[symbol as usize];
        write!(output, "function {} {}", hex(&entry.name), entry.arity).unwrap();
        table(
            &mut output,
            &model.functions[symbol as usize],
            size,
            entry.arity,
            |value| value as usize,
            true,
        );
    }
    for &symbol in predicates {
        let entry = &problem.predicates[symbol as usize];
        write!(output, "predicate {} {}", hex(&entry.name), entry.arity).unwrap();
        table(
            &mut output,
            &model.predicates[symbol as usize],
            size,
            entry.arity,
            usize::from,
            false,
        );
    }
    output.push_str("end\n");
    output
}
