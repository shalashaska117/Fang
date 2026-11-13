// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Isolated Skolem candidate.
#![forbid(unsafe_code)]

use fang::syntax::{Literal, SymbolId, Term};
use fang_quantified_fof_core::{Formula, Nnf, Signature};

/// `positive = false` requests the existing checked negation-normalization path.
/// Input roles and their original-byte meaning are outside this AST interface.
#[derive(Debug, PartialEq, Eq)]
pub struct Declaration {
    pub formula: Formula,
    pub positive: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    /// Formula/depth/input limits apply per declaration. Operations and storage
    /// are cumulative across prevalidation, normalization and Skolemization.
    pub core: fang_quantified_fof_core::Limits,
    pub max_declarations: usize,
    pub max_functions: usize,
    pub max_skolem_symbols: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            core: Default::default(),
            max_declarations: 1_000,
            max_functions: 100_000,
            max_skolem_symbols: 10_000,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Resource {
    Declarations,
    Functions,
    SkolemSymbols,
    Operations,
    StoredNodes,
    TermDepth,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Core(fang_quantified_fof_core::Error),
    Resource(Resource),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Introduced {
    pub declaration: usize,
    /// Fresh declaration-local binder ID after the accepted rectifier.
    pub binder: u32,
    pub function: SymbolId,
    /// Every enclosing universal, outermost first, including unused binders.
    pub universals: Vec<u32>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Statistics {
    /// Structural credits, not native instructions or elapsed time.
    pub operations: usize,
    /// Cumulative structural copies and table/metadata positions, not bytes/RSS.
    pub allocated_nodes: usize,
}

#[derive(Debug, PartialEq, Eq)]
pub struct Skolemized {
    /// Existential-free NNF, with universal binders still explicit.
    pub formulas: Vec<Nnf>,
    pub signature: Signature,
    pub introduced: Vec<Introduced>,
    pub statistics: Statistics,
}

fn bounded_add(left: usize, right: usize, cap: usize, kind: Resource) -> Result<usize, Error> {
    if left > cap || right > cap - left {
        Err(Error::Resource(kind))
    } else {
        Ok(left + right)
    }
}

struct Work {
    statistics: Statistics,
}

impl Work {
    fn tick(&mut self, limits: &Limits) -> Result<(), Error> {
        self.statistics.operations = bounded_add(
            self.statistics.operations,
            1,
            limits.core.max_operations,
            Resource::Operations,
        )?;
        Ok(())
    }

    fn allocate(&mut self, count: usize, limits: &Limits) -> Result<(), Error> {
        self.statistics.allocated_nodes = bounded_add(
            self.statistics.allocated_nodes,
            count,
            limits.core.max_stored_nodes,
            Resource::StoredNodes,
        )?;
        Ok(())
    }

    fn remaining(&self, limits: &Limits) -> fang_quantified_fof_core::Limits {
        fang_quantified_fof_core::Limits {
            max_operations: limits.core.max_operations - self.statistics.operations,
            max_stored_nodes: limits.core.max_stored_nodes - self.statistics.allocated_nodes,
            ..limits.core
        }
    }

    fn absorb(
        &mut self,
        statistics: fang_quantified_fof_core::Statistics,
        limits: &Limits,
    ) -> Result<(), Error> {
        self.statistics.operations = bounded_add(
            self.statistics.operations,
            statistics.operations,
            limits.core.max_operations,
            Resource::Operations,
        )?;
        self.allocate(statistics.allocated_nodes, limits)
    }
}

// No Vec::pop: Aeneas models the supported active-prefix representation.
struct Universals {
    entries: Vec<u32>,
    active: usize,
}

impl Universals {
    fn push(&mut self, id: u32, limits: &Limits, work: &mut Work) -> Result<(), Error> {
        work.tick(limits)?;
        if self.active < self.entries.len() {
            self.entries[self.active] = id;
        } else {
            work.allocate(1, limits)?;
            self.entries.push(id);
        }
        self.active += 1;
        Ok(())
    }

    fn pop(&mut self) {
        if self.active > 0 {
            self.active -= 1;
        }
    }
}

fn copy_term(term: &Term, depth: usize, limits: &Limits, work: &mut Work) -> Result<Term, Error> {
    work.tick(limits)?;
    if depth > limits.core.max_term_depth.min(64) {
        return Err(Error::Resource(Resource::TermDepth));
    }
    work.allocate(1, limits)?;
    match term {
        Term::Var(id) => Ok(Term::Var(*id)),
        Term::Fun(id, arguments) => {
            let mut copied = Vec::new();
            let mut index = 0;
            while index < arguments.len() {
                copied.push(copy_term(&arguments[index], depth + 1, limits, work)?);
                index += 1;
            }
            Ok(Term::Fun(*id, copied))
        }
    }
}

/// One simultaneous substitution: replacement terms are copied without further
/// substitution. The public path supplies a fresh application of universal IDs.
fn substitute_term(
    term: &Term,
    binder: u32,
    replacement: &Term,
    depth: usize,
    limits: &Limits,
    work: &mut Work,
) -> Result<Term, Error> {
    work.tick(limits)?;
    if depth > limits.core.max_term_depth.min(64) {
        return Err(Error::Resource(Resource::TermDepth));
    }
    match term {
        Term::Var(id) if *id == binder => copy_term(replacement, depth, limits, work),
        Term::Var(id) => {
            work.allocate(1, limits)?;
            Ok(Term::Var(*id))
        }
        Term::Fun(id, arguments) => {
            work.allocate(1, limits)?;
            let mut copied = Vec::new();
            let mut index = 0;
            while index < arguments.len() {
                copied.push(substitute_term(
                    &arguments[index],
                    binder,
                    replacement,
                    depth + 1,
                    limits,
                    work,
                )?);
                index += 1;
            }
            Ok(Term::Fun(*id, copied))
        }
    }
}

fn copy_literal(literal: &Literal, limits: &Limits, work: &mut Work) -> Result<Literal, Error> {
    let mut arguments = Vec::new();
    let mut index = 0;
    while index < literal.arguments.len() {
        arguments.push(copy_term(&literal.arguments[index], 1, limits, work)?);
        index += 1;
    }
    Ok(Literal {
        positive: literal.positive,
        predicate: literal.predicate,
        arguments,
    })
}

fn substitute_nnf(
    formula: &Nnf,
    binder: u32,
    replacement: &Term,
    active: bool,
    limits: &Limits,
    work: &mut Work,
) -> Result<Nnf, Error> {
    work.tick(limits)?;
    work.allocate(1, limits)?;
    match formula {
        Nnf::Literal(literal) => {
            if !active {
                return Ok(Nnf::Literal(copy_literal(literal, limits, work)?));
            }
            let mut arguments = Vec::new();
            let mut index = 0;
            while index < literal.arguments.len() {
                arguments.push(substitute_term(
                    &literal.arguments[index],
                    binder,
                    replacement,
                    1,
                    limits,
                    work,
                )?);
                index += 1;
            }
            Ok(Nnf::Literal(Literal {
                positive: literal.positive,
                predicate: literal.predicate,
                arguments,
            }))
        }
        Nnf::True => Ok(Nnf::True),
        Nnf::False => Ok(Nnf::False),
        Nnf::And(left, right) => {
            let left = substitute_nnf(left, binder, replacement, active, limits, work)?;
            let right = substitute_nnf(right, binder, replacement, active, limits, work)?;
            Ok(Nnf::And(Box::new(left), Box::new(right)))
        }
        Nnf::Or(left, right) => {
            let left = substitute_nnf(left, binder, replacement, active, limits, work)?;
            let right = substitute_nnf(right, binder, replacement, active, limits, work)?;
            Ok(Nnf::Or(Box::new(left), Box::new(right)))
        }
        Nnf::Forall(id, body) => {
            let body = substitute_nnf(
                body,
                binder,
                replacement,
                active && *id != binder,
                limits,
                work,
            )?;
            Ok(Nnf::Forall(*id, Box::new(body)))
        }
        Nnf::Exists(id, body) => {
            let body = substitute_nnf(
                body,
                binder,
                replacement,
                active && *id != binder,
                limits,
                work,
            )?;
            Ok(Nnf::Exists(*id, Box::new(body)))
        }
    }
}

struct Transformer {
    functions: Vec<usize>,
    introduced: Vec<Introduced>,
    universals: Universals,
    declaration: usize,
    work: Work,
}

fn copy_dependencies(
    universals: &Universals,
    limits: &Limits,
    work: &mut Work,
) -> Result<(Vec<Term>, Vec<u32>), Error> {
    let mut arguments = Vec::new();
    let mut dependencies = Vec::new();
    let mut index = 0;
    while index < universals.active {
        work.tick(limits)?;
        work.allocate(2, limits)?;
        let id = universals.entries[index];
        arguments.push(Term::Var(id));
        dependencies.push(id);
        index += 1;
    }
    Ok((arguments, dependencies))
}

impl Transformer {
    fn introduce(&mut self, binder: u32, limits: &Limits) -> Result<Term, Error> {
        self.work.tick(limits)?;
        if self.functions.len() >= limits.max_functions.min(u32::MAX as usize) {
            return Err(Error::Resource(Resource::Functions));
        }
        if self.introduced.len() >= limits.max_skolem_symbols {
            return Err(Error::Resource(Resource::SkolemSymbols));
        }
        let function = self.functions.len() as u32;
        // One arity slot, one metadata record and one application node.
        self.work.allocate(3, limits)?;
        let (arguments, dependencies) =
            copy_dependencies(&self.universals, limits, &mut self.work)?;
        self.functions.push(self.universals.active);
        self.introduced.push(Introduced {
            declaration: self.declaration,
            binder,
            function,
            universals: dependencies,
        });
        Ok(Term::Fun(function, arguments))
    }

    // Only called on the fully validated, rectified NNF. Each substitution keeps
    // its formula depth and explicitly bounds any increase in term depth.
    fn transform(&mut self, formula: &Nnf, limits: &Limits) -> Result<Nnf, Error> {
        self.work.tick(limits)?;
        match formula {
            Nnf::Literal(literal) => {
                self.work.allocate(1, limits)?;
                Ok(Nnf::Literal(copy_literal(literal, limits, &mut self.work)?))
            }
            Nnf::True => {
                self.work.allocate(1, limits)?;
                Ok(Nnf::True)
            }
            Nnf::False => {
                self.work.allocate(1, limits)?;
                Ok(Nnf::False)
            }
            Nnf::And(left, right) => {
                self.work.allocate(1, limits)?;
                let left = self.transform(left, limits)?;
                let right = self.transform(right, limits)?;
                Ok(Nnf::And(Box::new(left), Box::new(right)))
            }
            Nnf::Or(left, right) => {
                self.work.allocate(1, limits)?;
                let left = self.transform(left, limits)?;
                let right = self.transform(right, limits)?;
                Ok(Nnf::Or(Box::new(left), Box::new(right)))
            }
            Nnf::Forall(id, body) => {
                self.work.allocate(1, limits)?;
                self.universals.push(*id, limits, &mut self.work)?;
                let result = self.transform(body, limits);
                self.universals.pop();
                Ok(Nnf::Forall(*id, Box::new(result?)))
            }
            Nnf::Exists(id, body) => {
                let replacement = self.introduce(*id, limits)?;
                let substituted =
                    substitute_nnf(body, *id, &replacement, true, limits, &mut self.work)?;
                self.transform(&substituted, limits)
            }
        }
    }
}

fn validate_declarations(
    declarations: &[Declaration],
    signature: &Signature,
    limits: &Limits,
    work: &mut Work,
) -> Result<(), Error> {
    let mut index = 0;
    while index < declarations.len() {
        work.tick(limits)?;
        let checked = fang_quantified_fof_core::validate(
            &declarations[index].formula,
            signature,
            &work.remaining(limits),
        )
        .map_err(Error::Core)?;
        work.absorb(checked, limits)?;
        index += 1;
    }
    Ok(())
}

fn copy_arities(arities: &[usize], limits: &Limits, work: &mut Work) -> Result<Vec<usize>, Error> {
    let mut copied = Vec::new();
    let mut index = 0;
    while index < arities.len() {
        work.tick(limits)?;
        work.allocate(1, limits)?;
        copied.push(arities[index]);
        index += 1;
    }
    Ok(copied)
}

fn transform_declarations(
    declarations: &[Declaration],
    signature: &Signature,
    limits: &Limits,
    state: &mut Transformer,
) -> Result<Vec<Nnf>, Error> {
    let mut formulas = Vec::new();
    while state.declaration < declarations.len() {
        state.work.tick(limits)?;
        let declaration = &declarations[state.declaration];
        let normalized = fang_quantified_fof_core::rectify_normalize_closed(
            &declaration.formula,
            declaration.positive,
            signature,
            &state.work.remaining(limits),
        )
        .map_err(Error::Core)?;
        state.work.absorb(normalized.statistics, limits)?;
        let result = state.transform(&normalized.formula, limits)?;
        state.work.allocate(1, limits)?;
        formulas.push(result);
        state.declaration += 1;
    }
    Ok(formulas)
}

/// Reserve the entire original signature, validate every declaration, then
/// rectify/normalize and eliminate existentials with a single global counter.
/// Errors expose no partial formulas, signature or symbol metadata.
pub fn skolemize_problem(
    declarations: &[Declaration],
    signature: &Signature,
    limits: &Limits,
) -> Result<Skolemized, Error> {
    if declarations.len() > limits.max_declarations {
        return Err(Error::Resource(Resource::Declarations));
    }
    if signature.functions.len() > limits.max_functions.min(u32::MAX as usize) {
        return Err(Error::Resource(Resource::Functions));
    }
    let mut state = Transformer {
        functions: Vec::new(),
        introduced: Vec::new(),
        universals: Universals {
            entries: Vec::new(),
            active: 0,
        },
        declaration: 0,
        work: Work {
            statistics: Statistics::default(),
        },
    };
    // No recursive AST copy or fresh allocation precedes whole-input validation.
    validate_declarations(declarations, signature, limits, &mut state.work)?;
    state.functions = copy_arities(&signature.functions, limits, &mut state.work)?;
    let predicates = copy_arities(&signature.predicates, limits, &mut state.work)?;
    let formulas = transform_declarations(declarations, signature, limits, &mut state)?;
    Ok(Skolemized {
        formulas,
        signature: Signature {
            functions: state.functions,
            predicates,
        },
        introduced: state.introduced,
        statistics: state.work.statistics,
    })
}
