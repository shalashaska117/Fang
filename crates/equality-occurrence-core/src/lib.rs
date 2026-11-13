// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Original single-occurrence kernel. Reused Fang terms retain LICENSES notices.
#![forbid(unsafe_code)]

use fang::syntax::Term;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    pub max_depth: usize,
    pub max_output_nodes: usize,
    pub max_operations: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            max_depth: 64,
            max_output_nodes: 100_000,
            max_operations: 1_000_000,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    InvalidPath,
    UnknownFunction,
    FunctionArity,
    Depth,
    OutputNodes,
    Operations,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Statistics {
    pub operations: usize,
    pub output_nodes: usize,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Replaced {
    pub term: Term,
    pub statistics: Statistics,
}

fn visit(depth: usize, limits: &Limits, work: &mut Statistics) -> Result<(), Error> {
    // A caller cannot relax the recursion bound beyond the supported stack depth.
    if depth > 64 || depth > limits.max_depth {
        return Err(Error::Depth);
    }
    if work.operations >= limits.max_operations {
        return Err(Error::Operations);
    }
    work.operations += 1;
    Ok(())
}

fn allocate(limits: &Limits, work: &mut Statistics) -> Result<(), Error> {
    if work.output_nodes >= limits.max_output_nodes {
        return Err(Error::OutputNodes);
    }
    work.output_nodes += 1;
    Ok(())
}

fn validate(
    term: &Term,
    arities: &[usize],
    depth: usize,
    limits: &Limits,
    work: &mut Statistics,
) -> Result<(), Error> {
    visit(depth, limits, work)?;
    match term {
        Term::Var(_) => Ok(()),
        Term::Fun(symbol, arguments) => {
            let index = *symbol as usize;
            if index >= arities.len() {
                return Err(Error::UnknownFunction);
            }
            if arities[index] != arguments.len() {
                return Err(Error::FunctionArity);
            }
            let mut index = 0;
            while index < arguments.len() {
                validate(&arguments[index], arities, depth + 1, limits, work)?;
                index += 1;
            }
            Ok(())
        }
    }
}

fn copy(term: &Term, depth: usize, limits: &Limits, work: &mut Statistics) -> Result<Term, Error> {
    visit(depth, limits, work)?;
    allocate(limits, work)?;
    match term {
        Term::Var(variable) => Ok(Term::Var(*variable)),
        Term::Fun(symbol, arguments) => {
            let mut copied = Vec::new();
            let mut index = 0;
            while index < arguments.len() {
                copied.push(copy(&arguments[index], depth + 1, limits, work)?);
                index += 1;
            }
            Ok(Term::Fun(*symbol, copied))
        }
    }
}

fn replace(
    term: &Term,
    path: &[usize],
    at: usize,
    replacement: &Term,
    depth: usize,
    limits: &Limits,
    work: &mut Statistics,
) -> Result<Term, Error> {
    if at == path.len() {
        return copy(replacement, depth, limits, work);
    }
    visit(depth, limits, work)?;
    match term {
        Term::Var(_) => Err(Error::InvalidPath),
        Term::Fun(symbol, arguments) => {
            if path[at] >= arguments.len() {
                return Err(Error::InvalidPath);
            }
            allocate(limits, work)?;
            let mut copied = Vec::new();
            let mut index = 0;
            while index < arguments.len() {
                let result = if index == path[at] {
                    replace(
                        &arguments[index],
                        path,
                        at + 1,
                        replacement,
                        depth + 1,
                        limits,
                        work,
                    )
                } else {
                    copy(&arguments[index], depth + 1, limits, work)
                };
                let result = result?;
                copied.push(result);
                index += 1;
            }
            Ok(Term::Fun(*symbol, copied))
        }
    }
}

/// Replace one occurrence at a zero-based child path; an empty path is the root.
/// Both complete input terms must fit the same function-arity signature.
/// The result keeps the original sibling order and does not replace other equal
/// subterms. Inputs are immutable; an error publishes no partial result.
/// Counters bound visits and output term nodes, not physical allocation or RSS.
pub fn replace_at(
    term: &Term,
    path: &[usize],
    replacement: &Term,
    arities: &[usize],
    limits: &Limits,
) -> Result<Replaced, Error> {
    let mut work = Statistics::default();
    validate(term, arities, 1, limits, &mut work)?;
    validate(replacement, arities, 1, limits, &mut work)?;
    let result = replace(term, path, 0, replacement, 1, limits, &mut work)?;
    Ok(Replaced {
        term: result,
        statistics: work,
    })
}
