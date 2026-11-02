// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Shared Fang components retain LICENSES/Vampire.txt and Vampire.ORIGIN.
#![forbid(unsafe_code)]

//! Expanded frontend preprocessing and search candidates. No original-byte acceptance,
//! FOF certificate envelope, SAT result or installed command is provided here.

use fang::syntax::Symbol;
use fang_equality_inference_core::Clause;
use fang_fof_equality_bridge::Reservation;
use fang_quantified_fof_frontend::{Body, Declaration, Parsed};
use fang_quantified_pipeline_observer as pipeline;
use fang_tptp_full_frontend_candidate::{Encoded, EncodedBody, NameKind};
use std::ops::Range;

/// NUL cannot occur in an accepted source identifier. This name is internal and
/// must be removed before exposing the equality-capable output signature.
const EQUALITY_NAME: &str = "\0fang_equality";

#[derive(Clone, Debug)]
pub struct Limits {
    pub input: fang_tptp_full_frontend_candidate::Limits,
    pub preprocessing: fang_skolem_core::Limits,
    pub max_bookkeeping_operations: usize,
    pub max_generated_name_bytes: usize,
    /// Includes the one reserved binary predicate slot.
    pub max_predicates: usize,
    /// Per source CNF clause and per final decoded clause.
    pub max_bridge_literals: usize,
    /// Table positions, metadata bytes, declarations, output clauses/literals.
    /// These structural credits are not native instructions or allocation bytes.
    pub max_adapter_operations: usize,
    pub search: fang_equality_search::Limits,
}

impl Default for Limits {
    fn default() -> Self {
        let defaults = pipeline::Limits::default();
        Self {
            input: Default::default(),
            preprocessing: defaults.preprocessing,
            max_bookkeeping_operations: defaults.max_bookkeeping_operations,
            max_generated_name_bytes: defaults.max_generated_name_bytes,
            max_predicates: 100_000,
            max_bridge_literals: 256,
            max_adapter_operations: 5_000_000,
            search: Default::default(),
        }
    }
}

#[derive(Debug)]
pub enum Error {
    Input(fang::Error),
    Encoding(fang_fof_equality_bridge::Error),
    Preprocessing(pipeline::Error),
    Conversion(fang_fof_equality_bridge::Error),
    Search(fang_equality_search::PreparedError),
    Resource(&'static str),
    Internal(&'static str),
}

#[derive(Debug, PartialEq, Eq)]
pub struct Source {
    pub name: String,
    pub name_kind: NameKind,
    /// Low-level label, unique by original declaration position.
    pub internal_name: String,
    /// None for FOF, zero or one for normalized source CNF.
    pub cnf_clauses: Option<usize>,
    pub bytes: Range<usize>,
    pub body_bytes: Range<usize>,
    pub variables: Vec<String>,
    pub is_fof: bool,
    /// Exact final mixed-order interval; zero-output declarations are retained.
    pub clauses: Range<usize>,
}

#[derive(Debug)]
pub struct Prepared {
    pub clauses: Vec<Clause>,
    pub functions: Vec<Symbol>,
    /// Complete original predicates only. Equality has its own Atom constructor.
    pub predicates: Vec<Symbol>,
    pub clause_names: Vec<String>,
    pub sources: Vec<Source>,
    pub origins: Vec<pipeline::Origin>,
    pub introduced: Vec<pipeline::Introduced>,
    pub statistics: pipeline::Statistics,
    pub adapter_operations: usize,
}

#[derive(Debug)]
pub struct CandidateRun {
    pub prepared: Prepared,
    /// A candidate or Unknown. Its inherited version-5 text is CNF-only and
    /// cannot be relabelled as a certificate for the original FOF input.
    pub outcome: fang_equality_search::Outcome,
}

struct Work {
    used: usize,
    maximum: usize,
}

impl Work {
    fn add(&mut self, count: usize) -> Result<(), Error> {
        if count > self.maximum - self.used {
            return Err(Error::Resource("equality adapter operation cap"));
        }
        self.used += count;
        Ok(())
    }
}

struct Converted {
    parsed: Parsed,
    reservation: Reservation,
    sources: Vec<Source>,
    original_predicates: Vec<Symbol>,
    active_sources: Vec<usize>,
}

fn convert_parsed(encoded: Encoded, work: &mut Work) -> Result<Converted, Error> {
    work.add(encoded.functions.len())?;
    work.add(encoded.original_predicates.len())?;
    if encoded.reservation.equality_id() as usize != encoded.original_predicates.len()
        || encoded
            .original_predicates
            .iter()
            .any(|s| s.name == EQUALITY_NAME)
    {
        return Err(Error::Internal(
            "reserved equality slot does not follow the original table",
        ));
    }
    let original_predicates = encoded.original_predicates;
    for symbol in &original_predicates {
        work.add(symbol.name.len())?;
    }
    let mut predicates = original_predicates.clone();
    work.add(1)?;
    predicates.push(Symbol {
        name: EQUALITY_NAME.into(),
        arity: 2,
    });
    let mut sources = Vec::new();
    let mut declarations = Vec::new();
    let mut active_sources = Vec::new();
    for (index, declaration) in encoded.declarations.into_iter().enumerate() {
        work.add(1)?;
        work.add(declaration.name.len())?;
        for variable in &declaration.variables {
            work.add(variable.len())?;
        }
        let internal_name = format!("fang_source_{index}");
        work.add(internal_name.len())?;
        let cnf_clauses = match &declaration.body {
            EncodedBody::Cnf(value) => Some(usize::from(value.is_some())),
            EncodedBody::Fof(_) => None,
        };
        sources.push(Source {
            name: declaration.name,
            name_kind: declaration.name_kind,
            internal_name: internal_name.clone(),
            cnf_clauses,
            bytes: declaration.bytes.clone(),
            body_bytes: declaration.body_bytes.clone(),
            variables: declaration.variables.clone(),
            is_fof: matches!(&declaration.body, EncodedBody::Fof(_)),
            clauses: 0..0,
        });
        let body = match declaration.body {
            EncodedBody::Cnf(None) => continue,
            EncodedBody::Cnf(Some(clause)) => Body::Cnf(clause),
            EncodedBody::Fof(formula) => Body::Fof(formula),
        };
        work.add(1)?;
        active_sources.push(index);
        declarations.push(Declaration {
            name: internal_name,
            bytes: declaration.bytes,
            variables: declaration.variables,
            body_bytes: declaration.body_bytes,
            body,
        });
    }
    let stats = encoded.statistics;
    Ok(Converted {
        parsed: Parsed {
            functions: encoded.functions,
            predicates,
            declarations,
            statistics: fang_quantified_fof_frontend::Statistics {
                operations: stats.operations,
                formula_nodes: stats.formula_nodes,
                term_nodes: stats.term_nodes,
                binders: stats.binders,
            },
        },
        reservation: encoded.reservation,
        sources,
        original_predicates,
        active_sources,
    })
}

/// Parse the entire input, reserve equality after every original predicate,
/// invoke the shared preprocessing body, then decode every final clause.
/// Failure exposes no partial Prepared value. Native allocation and destruction
/// are outside the structural budget contract.
pub fn prepare(input: &[u8], limits: &Limits) -> Result<Prepared, Error> {
    let parsed =
        fang_tptp_full_frontend_candidate::parse(input, &limits.input).map_err(Error::Input)?;
    let encoded = parsed
        .encode(limits.max_predicates, limits.max_bridge_literals)
        .map_err(Error::Encoding)?;
    let mut work = Work {
        used: 0,
        maximum: limits.max_adapter_operations,
    };
    // Omitted tautologies still count toward the complete input declaration cap.
    if encoded.declarations.len() > limits.preprocessing.max_declarations {
        return Err(Error::Resource("total source declaration cap"));
    }
    let Converted {
        parsed,
        reservation,
        mut sources,
        original_predicates,
        active_sources,
    } = convert_parsed(encoded, &mut work)?;
    let shared_limits = pipeline::Limits {
        input: fang_quantified_fof_frontend::Limits {
            input: limits.input.input.clone(),
            max_formula_depth: limits.input.max_formula_depth,
            max_formula_nodes: limits.input.max_formula_nodes,
            max_binders: limits.input.max_binders,
        },
        preprocessing: limits.preprocessing,
        max_bookkeeping_operations: limits.max_bookkeeping_operations,
        max_generated_name_bytes: limits.max_generated_name_bytes,
    };
    let mut prepared =
        pipeline::prepare_parsed(parsed, &shared_limits).map_err(Error::Preprocessing)?;
    let mut problem = prepared.problem;
    let reserved = problem
        .predicates
        .pop()
        .ok_or(Error::Internal("missing reserved output slot"))?;
    if reserved.name != EQUALITY_NAME
        || reserved.arity != 2
        || problem.predicates != original_predicates
    {
        return Err(Error::Internal(
            "preprocessing changed the reserved predicate table",
        ));
    }
    if prepared.origins.len() != problem.clauses.len()
        || problem.clause_names.len() != problem.clauses.len()
    {
        return Err(Error::Internal(
            "preprocessing clause metadata length differs",
        ));
    }
    for origin in &mut prepared.origins {
        work.add(1)?;
        origin.declaration = *active_sources
            .get(origin.declaration)
            .ok_or(Error::Internal("active clause origin outside source map"))?;
    }
    for introduced in &mut prepared.introduced {
        work.add(1)?;
        introduced.declaration = *active_sources
            .get(introduced.declaration)
            .ok_or(Error::Internal("active Skolem origin outside source map"))?;
    }
    let mut cursor = 0;
    for (index, source) in sources.iter_mut().enumerate() {
        work.add(1)?;
        let start = cursor;
        while let Some(origin) = prepared.origins.get(cursor) {
            if origin.declaration != index {
                break;
            }
            work.add(1)?;
            if origin.local_clause != cursor - start {
                return Err(Error::Internal("preprocessing local clause order differs"));
            }
            cursor += 1;
        }
        if source
            .cnf_clauses
            .is_some_and(|expected| cursor - start != expected)
        {
            return Err(Error::Internal(
                "source CNF declaration changed clause count",
            ));
        }
        source.clauses = start..cursor;
    }
    if cursor != prepared.origins.len() {
        return Err(Error::Internal(
            "preprocessing origin outside complete source order",
        ));
    }
    let mut clauses = Vec::new();
    for clause in problem.clauses {
        work.add(1)?;
        work.add(clause.len())?;
        clauses.push(
            reservation
                .decode_clause(clause, limits.max_bridge_literals)
                .map_err(Error::Conversion)?,
        );
    }
    Ok(Prepared {
        clauses,
        functions: problem.functions,
        predicates: problem.predicates,
        clause_names: problem.clause_names,
        sources,
        origins: prepared.origins,
        introduced: prepared.introduced,
        statistics: prepared.statistics,
        adapter_operations: work.used,
    })
}

/// Search only the complete converted problem. The search validates all numeric
/// clauses under its own limits. Acceptance against original bytes is separate.
pub fn prove_bytes(input: &[u8], limits: &Limits) -> Result<CandidateRun, Error> {
    let mut prepared = prepare(input, limits)?;
    let mut work = Work {
        used: prepared.adapter_operations,
        maximum: limits.max_adapter_operations,
    };
    work.add(prepared.functions.len())?;
    work.add(prepared.predicates.len())?;
    prepared.adapter_operations = work.used;
    let functions: Vec<_> = prepared
        .functions
        .iter()
        .map(|symbol| symbol.arity)
        .collect();
    let predicates: Vec<_> = prepared
        .predicates
        .iter()
        .map(|symbol| symbol.arity)
        .collect();
    let outcome = fang_equality_search::prove_prepared_ordered(
        &prepared.clauses,
        &functions,
        &predicates,
        &limits.search,
    )
    .map_err(Error::Search)?;
    Ok(CandidateRun { prepared, outcome })
}
