// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Shared Fang components retain LICENSES/Vampire.txt and Vampire.ORIGIN.
#![forbid(unsafe_code)]

//! Signed role tasks through the actual Skolem entry. Each original conjecture gets its own task: every premise with the positive sign and that goal with the negative sign, in source order. Without a conjecture there is one satisfiability task.
//!
//! The stages and per-stage limits follow the Lean `replayTask` in SignedReplay.lean. `produce_task` runs the same prepared ordered search and bounded serializer as the version-8 producer in integration/v8. Its output is a candidate certificate or Unknown, never a checked result or SZS status.

use fang::syntax::{Clause as NumericClause, deduplicate};
use fang_equality_inference_core::Clause;
use fang_tptp_full_frontend_candidate::{EncodedBody, Role};

#[derive(Clone, Debug)]
pub struct Limits {
    pub input: fang_tptp_full_frontend_candidate::Limits,
    /// Includes the one reserved binary predicate slot.
    pub max_predicates: usize,
    /// Per source CNF clause and per final converted clause.
    pub max_bridge_literals: usize,
    /// Applies to the whole FOF list of one task.
    pub skolem: fang_skolem_core::Limits,
    /// Applies to each FOF block separately.
    pub removal: fang_binder_removal_core::Limits,
    /// Applies to each FOF block separately, starting from zero statistics.
    pub clausification: fang_fof_core::Limits,
    pub search: fang_equality_search::Limits,
}

impl Default for Limits {
    /// The final limits record of every native main, `integration/native/final-record/NativeLimits.lean` (tptp-final-limits-record-v2-20261104). The predicate table, the literals per clause and every Skolem, removal and clausification limit take the record's values, as do the parser's input bytes (`byteLimit`) and declarations (`declarationLimit`), and the certificate the serializer writes is bounded by `certificateLimit`.
    ///
    /// The parser counts formula nodes, binders and term nodes per formula, on the lowered tree the Skolem core receives, so it takes the core's per-formula bounds. Its formula height stays 64, the height the decoders of round one read; the record's height applies to the cores. The parser's other counts and the other search limits have no counterpart in the record. `tests/native_limits.rs` compares every record field.
    fn default() -> Self {
        let core = fang_quantified_fof_core::Limits {
            max_formula_depth: 2_984,
            max_formula_nodes: 10_000,
            max_term_depth: 64,
            max_input_term_nodes: 100_000,
            max_clauses: 1_000,
            max_literals_per_clause: 256,
            max_literals: 100_000,
            max_stored_nodes: 7_943_814,
            max_operations: 16_000_000,
            max_binders: 10_000,
        };
        let mut input = fang_tptp_full_frontend_candidate::Limits::default();
        input.input.max_input_bytes = 1024 * 1024;
        input.input.max_clauses = 65_536;
        input.input.max_term_depth = core.max_term_depth;
        input.input.max_term_nodes = core.max_input_term_nodes;
        input.max_formula_nodes = core.max_formula_nodes;
        input.max_binders = core.max_binders;
        let mut search = fang_equality_search::Limits::default();
        search.input.max_proof_bytes = 5_081_233;
        Self {
            input,
            max_predicates: 74_339,
            max_bridge_literals: 256,
            skolem: fang_skolem_core::Limits {
                core,
                max_declarations: 65_536,
                max_functions: 83_412,
                max_skolem_symbols: 30_675,
            },
            removal: fang_binder_removal_core::Limits {
                max_formula_depth: 2_984,
                max_operations: 5_000_000,
                max_output_nodes: 1_000_000,
            },
            clausification: fang_fof_core::Limits {
                max_formula_depth: 2_984,
                max_formula_nodes: 10_000,
                max_term_depth: 64,
                max_input_term_nodes: 100_000,
                max_clauses: 36_045,
                max_literals_per_clause: 256,
                max_literals: 423_500,
                max_stored_nodes: 6_657_931,
                max_operations: 6_657_983,
            },
            search,
        }
    }
}

#[derive(Debug)]
pub enum Error {
    Input(fang::Error),
    Encoding(fang_fof_equality_bridge::Error),
    /// The index is past the last original conjecture.
    NoGoal,
    /// The satisfiability task was requested for input with a conjecture.
    GoalsPresent,
    Skolem(fang_skolem_core::Error),
    Removal(fang_binder_removal_core::Error),
    Clausification(fang_fof_core::Error),
    Conversion(fang_fof_equality_bridge::Error),
    Search(fang_equality_search::PreparedError),
    Serialization(fang_equality_search::Error),
    WrongTraceVersion,
    Internal(&'static str),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Selection {
    /// The original conjecture with this index among all conjectures, in source order.
    Goal(usize),
    /// The satisfiability task; only valid without an original conjecture.
    Inputs,
}

#[derive(Debug)]
pub struct Prepared {
    /// Source index of the selected conjecture.
    pub goal: Option<usize>,
    /// Source index and sign of every declaration sent to the Skolem entry, in order.
    pub signs: Vec<(usize, bool)>,
    /// Converted clauses: CNF items and FOF blocks in source order, each clause deduplicated.
    pub clauses: Vec<Clause>,
    /// Original function arities followed by the Skolem functions.
    pub function_arities: Vec<usize>,
    /// Original predicate arities; equality is native in the clauses.
    pub predicate_arities: Vec<usize>,
    /// One entry per declaration of the task, in the order its clauses appear in `clauses`. CNF items without a clause and FOF blocks that clausify to nothing get an empty range.
    pub origins: Vec<Origin>,
}

/// The declaration behind a run of prepared clauses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Origin {
    /// Index of the declaration in the parsed input (the flat text for bundles), as in `signs`.
    pub source_index: usize,
    /// The declaration's original role: lets a negated_conjecture CNF item count as a goal.
    pub role: fang_tptp_full_frontend_candidate::Role,
    /// The sign the task gives it: false for the selected conjecture, which enters negated.
    pub positive: bool,
    /// The clauses this declaration produced.
    pub clauses: std::ops::Range<usize>,
}

enum Item {
    /// A CNF item that encodes to no clause.
    Empty,
    Cnf(NumericClause),
    Fof,
}

/// Number of original conjectures, so callers can enumerate every goal task.
pub fn goal_count(input: &[u8], limits: &Limits) -> Result<usize, Error> {
    let parsed =
        fang_tptp_full_frontend_candidate::parse(input, &limits.input).map_err(Error::Input)?;
    Ok(parsed
        .declarations
        .iter()
        .filter(|declaration| declaration.role == Role::Conjecture)
        .count())
}

/// Build one task and run the actual Skolem, removal, clausification and equality conversion functions on it. A failure returns no partial task.
pub fn prepare_task(
    input: &[u8],
    selection: Selection,
    limits: &Limits,
) -> Result<Prepared, Error> {
    let parsed =
        fang_tptp_full_frontend_candidate::parse(input, &limits.input).map_err(Error::Input)?;
    let encoded = parsed
        .encode(limits.max_predicates, limits.max_bridge_literals)
        .map_err(Error::Encoding)?;
    let goals: Vec<usize> = encoded
        .declarations
        .iter()
        .enumerate()
        .filter(|(_, declaration)| declaration.role == Role::Conjecture)
        .map(|(index, _)| index)
        .collect();
    let goal = match selection {
        Selection::Goal(index) => Some(*goals.get(index).ok_or(Error::NoGoal)?),
        Selection::Inputs if goals.is_empty() => None,
        Selection::Inputs => return Err(Error::GoalsPresent),
    };
    // The role crate decides which declarations enter the task and with which sign.
    let selected: Vec<(usize, bool)> = {
        let obligation = encoded
            .obligations()
            .map_err(Error::Input)?
            .find(|obligation| obligation.goal_index() == goal)
            .ok_or(Error::Internal("selected obligation is missing"))?;
        obligation
            .declarations()
            .map(|signed| (signed.source_index, signed.positive))
            .collect()
    };
    let signature = encoded.signature();
    let reservation = encoded.reservation;
    let original_predicates: Vec<usize> = encoded
        .original_predicates
        .iter()
        .map(|symbol| symbol.arity)
        .collect();
    let mut sign_of = vec![None; encoded.declarations.len()];
    for &(index, positive) in &selected {
        *sign_of
            .get_mut(index)
            .ok_or(Error::Internal("selected declaration outside the source"))? = Some(positive);
    }
    let mut fof = Vec::new();
    let mut signs = Vec::new();
    // Each layout item with its source index, original role and sign.
    let mut layout = Vec::new();
    for (index, declaration) in encoded.declarations.into_iter().enumerate() {
        let Some(positive) = sign_of[index] else {
            continue;
        };
        let owner = (index, declaration.role, positive);
        match declaration.body {
            EncodedBody::Cnf(None) => layout.push((Item::Empty, owner)),
            EncodedBody::Cnf(Some(clause)) => {
                if !positive {
                    return Err(Error::Internal("negative CNF item"));
                }
                layout.push((Item::Cnf(clause), owner));
            }
            EncodedBody::Fof(formula) => {
                fof.push(fang_skolem_core::Declaration { formula, positive });
                signs.push((index, positive));
                layout.push((Item::Fof, owner));
            }
        }
    }
    let skolem = fang_skolem_core::skolemize_problem(&fof, &signature, &limits.skolem)
        .map_err(Error::Skolem)?;
    if skolem.formulas.len() != fof.len() || skolem.signature.predicates != signature.predicates {
        return Err(Error::Internal(
            "Skolemizer changed declaration count or predicate signature",
        ));
    }
    let function_arities = skolem.signature.functions;
    let mut formulas = skolem.formulas.into_iter();
    let mut ordinary = Vec::new();
    let mut origins = Vec::new();
    for (item, (source_index, role, positive)) in layout {
        let start = ordinary.len();
        match item {
            Item::Empty => {}
            Item::Cnf(clause) => ordinary.push(deduplicate(&clause)),
            Item::Fof => {
                let formula = formulas
                    .next()
                    .ok_or(Error::Internal("missing Skolem output"))?;
                let removed = fang_binder_removal_core::remove_universals(formula, &limits.removal)
                    .map_err(Error::Removal)?;
                let block = fang_fof_core::nnf_entry::clausify_nnf_from(
                    &removed.formula,
                    &limits.clausification,
                    Default::default(),
                )
                .map_err(Error::Clausification)?;
                ordinary.extend(block.clauses.iter().map(deduplicate));
            }
        }
        origins.push(Origin {
            source_index,
            role,
            positive,
            clauses: start..ordinary.len(),
        });
    }
    if formulas.next().is_some() {
        return Err(Error::Internal("extra Skolem output"));
    }
    let mut clauses = Vec::new();
    for clause in ordinary {
        clauses.push(
            reservation
                .decode_clause(clause, limits.max_bridge_literals)
                .map_err(Error::Conversion)?,
        );
    }
    Ok(Prepared {
        goal,
        signs,
        clauses,
        function_arities,
        predicate_arities: original_predicates,
        origins,
    })
}

pub const VERSION: u32 = 8;
pub const CAPABILITY: &str = "expanded-fof-equality-skolem-distributive-v1";
/// The version-8 header from integration/V8.md; the checker selects the task separately.
pub const HEADER: &str =
    "(fang-proof 8\n  (preprocessing expanded-fof-equality-skolem-distributive-v1)\n";
const TRACE_HEADER: &str = "(fang-proof 5\n  (preprocessing identity-cnf-equality-v1)\n";

#[derive(Debug)]
pub enum Outcome {
    CandidateRefutation {
        certificate: fang_equality_search::Certificate,
        text: String,
        statistics: fang_equality_search::Statistics,
    },
    Unknown(fang_equality_search::Statistics),
}

#[derive(Debug)]
pub struct Produced {
    pub prepared: Prepared,
    pub outcome: Outcome,
}

/// Reserve the envelope overhead, call the authoritative bounded ordered serializer, and replace only its version-5 header, exactly as integration/v8 does. Node bytes and the final reference are kept.
pub fn certificate_text(
    certificate: &fang_equality_search::Certificate,
    max_bytes: usize,
) -> Result<String, Error> {
    let extra = HEADER.len() - TRACE_HEADER.len();
    let trace_cap = max_bytes.checked_sub(extra).ok_or(Error::Serialization(
        fang_equality_search::Error::Resource("expanded certificate byte limit"),
    ))?;
    let original = certificate
        .to_text(trace_cap)
        .map_err(Error::Serialization)?;
    let body = original
        .strip_prefix(TRACE_HEADER)
        .ok_or(Error::WrongTraceVersion)?;
    let mut text = String::with_capacity(original.len() + extra);
    text.push_str(HEADER);
    text.push_str(body);
    Ok(text)
}

/// Prepare one task, then run the prepared ordered search on exactly its clauses and signature. A candidate is never a checked result.
pub fn produce_task(
    input: &[u8],
    selection: Selection,
    limits: &Limits,
) -> Result<Produced, Error> {
    let prepared = prepare_task(input, selection, limits)?;
    let outcome = fang_equality_search::prove_prepared_ordered(
        &prepared.clauses,
        &prepared.function_arities,
        &prepared.predicate_arities,
        &limits.search,
    )
    .map_err(Error::Search)?;
    let outcome = match outcome {
        fang_equality_search::Outcome::CandidateRefutation {
            certificate,
            statistics,
        } => {
            let text = certificate_text(&certificate, limits.search.input.max_proof_bytes)?;
            Outcome::CandidateRefutation {
                certificate,
                text,
                statistics,
            }
        }
        fang_equality_search::Outcome::Unknown(statistics) => Outcome::Unknown(statistics),
    };
    Ok(Produced { prepared, outcome })
}

fn term(value: &fang::syntax::Term, output: &mut String) {
    match value {
        fang::syntax::Term::Var(id) => output.push_str(&format!("X{id}")),
        fang::syntax::Term::Fun(symbol, arguments) => {
            output.push_str(&format!("f{symbol}"));
            if !arguments.is_empty() {
                output.push('(');
                for (position, argument) in arguments.iter().enumerate() {
                    if position > 0 {
                        output.push(',');
                    }
                    term(argument, output);
                }
                output.push(')');
            }
        }
    }
}

/// The rejection kind printed by the agreement campaign. The Lean probe maps `SignedError` to the same names.
pub fn error_kind(error: &Error) -> &'static str {
    match error {
        Error::Input(_) => "input",
        Error::Encoding(_) => "reservation",
        Error::NoGoal => "no-goal",
        Error::GoalsPresent => "goals-present",
        Error::Skolem(_) => "skolem",
        Error::Removal(_) => "removal",
        Error::Clausification(_) => "clausification",
        Error::Conversion(_) => "conversion",
        Error::Search(_)
        | Error::Serialization(_)
        | Error::WrongTraceVersion
        | Error::Internal(_) => "internal",
    }
}

/// The text format shared with the Lean probe in the agreement campaign.
pub fn render(prepared: &Prepared) -> String {
    let mut output = format!(
        "functions {:?}\npredicates {:?}\n",
        prepared.function_arities, prepared.predicate_arities
    );
    for clause in &prepared.clauses {
        output.push('[');
        for (position, literal) in clause.iter().enumerate() {
            if position > 0 {
                output.push_str(" | ");
            }
            output.push(if literal.positive { '+' } else { '-' });
            match &literal.atom {
                fang_equality_inference_core::Atom::Predicate(predicate, arguments) => {
                    output.push_str(&format!("p{predicate}"));
                    if !arguments.is_empty() {
                        output.push('(');
                        for (index, argument) in arguments.iter().enumerate() {
                            if index > 0 {
                                output.push(',');
                            }
                            term(argument, &mut output);
                        }
                        output.push(')');
                    }
                }
                fang_equality_inference_core::Atom::Equal(left, right) => {
                    output.push('(');
                    term(left, &mut output);
                    output.push('=');
                    term(right, &mut output);
                    output.push(')');
                }
            }
        }
        output.push_str("]\n");
    }
    output
}

mod named_prepare;
pub use named_prepare::prepare_task_named;
