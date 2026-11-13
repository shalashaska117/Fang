// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! What the three producer binaries share: the leading search flags, the third version's search on a prepared
//! problem, and the stats file. The binaries keep the installed producers' arguments, output and exit codes.

use crate::options::Options;
use crate::proof::ProofError;
use crate::search::{Limits, Search, Stop};
use crate::stats::{Json, quote};
use fang_equality_inference_core::Clause;
use fang_equality_search::InvalidPrepared;
use std::path::PathBuf;
use std::time::{Duration, Instant};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    /// The second release's search through the reviewed producer functions, byte for byte.
    V2,
    V3,
}

pub struct Flags {
    pub mode: Mode,
    pub time_limit: Option<f64>,
    pub memory_mib: Option<u64>,
    pub stats: Option<PathBuf>,
    pub settings: Vec<(String, String)>,
    pub started: Instant,
    /// Where to write the given-clause trace (debugging only; needs `trace_given`).
    pub trace: Option<PathBuf>,
}

/// Symbol names for a trace: functions, then predicates, by number.
#[derive(Default)]
pub struct Names {
    pub functions: Vec<String>,
    pub predicates: Vec<String>,
}

pub const FLAGS_USAGE: &str = "[--search v2|v3] [--time-limit SECONDS] [--memory-mib MIB] [--stats PATH] [--set KEY=VALUE]...";

/// Remove the leading search flags; the rest goes to the installed producer's own argument parser.
pub fn split(mut arguments: Vec<String>, started: Instant) -> Result<(Flags, Vec<String>), String> {
    let mut flags = Flags {
        mode: Mode::V2,
        time_limit: None,
        memory_mib: None,
        stats: None,
        settings: vec![],
        started,
        trace: None,
    };
    loop {
        let Some(flag) = arguments.first().cloned() else {
            break;
        };
        if !matches!(
            flag.as_str(),
            "--search" | "--time-limit" | "--memory-mib" | "--stats" | "--set" | "--trace"
        ) {
            break;
        }
        let value = arguments
            .get(1)
            .cloned()
            .ok_or(format!("{flag} needs a value"))?;
        arguments.drain(..2);
        match flag.as_str() {
            "--search" => {
                flags.mode = match value.as_str() {
                    "v2" => Mode::V2,
                    "v3" => Mode::V3,
                    _ => return Err("--search is v2 or v3".into()),
                }
            }
            "--time-limit" => {
                let seconds: f64 = value.parse().map_err(|_| "--time-limit needs seconds")?;
                if !(seconds.is_finite() && seconds > 0.0) {
                    return Err("--time-limit needs positive seconds".into());
                }
                flags.time_limit = Some(seconds);
            }
            "--memory-mib" => {
                flags.memory_mib = Some(value.parse().map_err(|_| "--memory-mib needs a number")?)
            }
            "--stats" => flags.stats = Some(PathBuf::from(value)),
            "--trace" => flags.trace = Some(PathBuf::from(value)),
            _ => {
                let (key, setting) = value.split_once('=').ok_or("--set needs KEY=VALUE")?;
                flags.settings.push((key.to_owned(), setting.to_owned()));
            }
        }
    }
    if flags.mode == Mode::V2 && !flags.settings.is_empty() {
        return Err("--set needs --search v3".into());
    }
    Ok((flags, arguments))
}

impl Flags {
    pub fn options(&self) -> Result<Options, String> {
        Options::from_settings(&self.settings)
    }

    pub fn elapsed_ms(&self) -> u64 {
        self.started.elapsed().as_millis() as u64
    }

    /// Write the stats record; a failure to write it never changes the producer's result.
    pub fn write_stats(&self, json: &str) {
        if let Some(path) = &self.stats {
            let _ = std::fs::write(path, format!("{json}\n"));
        }
    }

    /// Stats for the second release's search: its own counters and the outcome.
    pub fn v2_stats(
        &self,
        outcome: &str,
        statistics: Option<&fang_equality_search::Statistics>,
        prepared: Option<usize>,
    ) {
        let mut json = Json::new();
        json.string("search", "v2")
            .string("outcome", outcome)
            .number("total_ms", self.elapsed_ms());
        if let Some(count) = prepared {
            json.number("prepared_clauses", count as u64);
        }
        if let Some(statistics) = statistics {
            json.number("processed", statistics.processed_clauses as u64)
                .number("attempts", statistics.attempted_inferences as u64)
                .number("derived", statistics.derived_clauses as u64)
                .number("stored_term_nodes", statistics.stored_term_nodes as u64);
        }
        self.write_stats(&json.finish());
    }
}

#[derive(Debug)]
pub enum Outcome {
    Candidate(String),
    /// Search ended without a refutation the format can state: saturation or a proof that needs a missing rule.
    Unknown {
        processed: u64,
        attempted: u64,
    },
    /// A time, memory or given-clause bound; the message goes into the existing `Resource("...")` shape.
    Stopped(&'static str),
    Invalid(InvalidPrepared),
    CertificateBytes,
    Internal(&'static str),
}

/// Run the third version's search on prepared numeric clauses and write the stats file.
pub fn run(
    flags: &Flags,
    options: &Options,
    clauses: &[Clause],
    functions: &[usize],
    predicates: &[usize],
    groups: Option<&[crate::sine::Group]>,
    names: Option<&Names>,
) -> Outcome {
    let prepare_ms = flags.elapsed_ms();
    let deadline = flags.time_limit.map(|seconds| {
        let reserve = (seconds * 0.1).min(1.0);
        flags.started + Duration::from_secs_f64((seconds - reserve).max(0.0))
    });
    let memory_kib = flags.memory_mib.map(|mib| mib * 1024 * 85 / 100);
    let mut json = Json::new();
    json.string("search", "v3")
        .string("preset", &options.preset)
        .string("options", &options.describe())
        .number("prepared_clauses", clauses.len() as u64)
        .number("functions", functions.len() as u64)
        .number("predicates", predicates.len() as u64)
        .number("prepare_ms", prepare_ms);
    let single = [(1, options.clone())];
    let slices: &[(u32, Options)] = if options.portfolio.is_empty() {
        &single
    } else {
        &options.portfolio
    };
    let mut remaining: u32 = slices.iter().map(|(share, _)| share).sum();
    let mut records = Vec::new();
    let mut counts = Vec::new();
    let mut last = None;
    for (index, (share, slice)) in slices.iter().enumerate() {
        // Each slice gets its share of the time that is left; a fresh search frees the previous one's memory.
        let slice_deadline = deadline.map(|end| {
            let now = Instant::now();
            now + end
                .saturating_duration_since(now)
                .mul_f64(*share as f64 / remaining as f64)
        });
        remaining -= share;
        let (reason, outcome, mut record, slice_counts) = run_one(
            slice,
            clauses,
            functions,
            predicates,
            groups,
            flags.trace.as_deref().zip(names),
            Limits {
                deadline: slice_deadline,
                memory_kib,
            },
        );
        records.push(record.finish());
        counts.push(slice_counts);
        let finished = matches!(
            outcome,
            Outcome::Candidate(_)
                | Outcome::Invalid(_)
                | Outcome::Internal(_)
                | Outcome::CertificateBytes
        );
        last = Some((reason, outcome, records.len() - 1));
        if finished || index + 1 == slices.len() {
            break;
        }
    }
    let (reason, outcome, chosen) = last.expect("at least one slice");
    json.string("stop_reason", reason)
        .number("total_ms", flags.elapsed_ms())
        .raw("slices", &format!("[{}]", records.join(",")))
        .raw("final_slice", &records[chosen])
        // The counts of the slice that decided the outcome, where the harness tools read them.
        .raw("counts", &counts[chosen])
        .raw(
            "time_limit",
            &flags
                .time_limit
                .map_or("null".into(), |value| format!("{value:.3}")),
        )
        .raw(
            "memory_mib",
            &flags
                .memory_mib
                .map_or("null".into(), |value| value.to_string()),
        );
    flags.write_stats(&json.finish());
    outcome
}

/// One search with `options`: its stop reason, outcome and stats record.
fn run_one(
    options: &Options,
    clauses: &[Clause],
    functions: &[usize],
    predicates: &[usize],
    groups: Option<&[crate::sine::Group]>,
    trace: Option<(&std::path::Path, &Names)>,
    limits: Limits,
) -> (&'static str, Outcome, Json, String) {
    let mut json = Json::new();
    json.string("preset", &options.preset);
    // Premise selection needs the goal, which only the signed producer knows.
    let selected = match (options.sine.filter(|_| !options.sine_layer), groups) {
        (Some(tolerance), Some(groups)) => Some(crate::sine::select(
            clauses,
            groups,
            tolerance,
            options.sine_depth,
        )),
        _ => None,
    };
    let goals: Option<Vec<bool>> = groups.map(|groups| {
        let mut flags = vec![false; clauses.len()];
        for group in groups.iter().filter(|group| group.goal) {
            for index in group.clauses.clone() {
                flags[index] = true;
            }
        }
        if options.goal_constants {
            widen_goals(clauses, &mut flags);
        }
        flags
    });
    let levels: Option<Vec<u32>> = match (options.sine_layer, groups) {
        (true, Some(groups)) => Some(crate::sine::levels(
            clauses,
            groups,
            options.sine.unwrap_or(2.0),
        )),
        _ => None,
    };
    let mut search = match Search::with_levels(
        clauses,
        functions,
        predicates,
        options,
        limits,
        selected.as_deref(),
        goals.as_deref(),
        levels.as_deref(),
    ) {
        Ok(search) => search,
        Err(kind) => {
            return (
                "invalid-input",
                Outcome::Invalid(kind),
                json,
                "{}".to_string(),
            );
        }
    };
    let searched = Instant::now();
    let stop = search.run();
    if let Some((path, names)) = trace
        && options.trace_given > 0
    {
        let _ = std::fs::write(path, render_trace(&search, names));
    }
    search.stats.search_ms = searched.elapsed().as_millis() as u64;
    search.finish_stats();
    let (reason, outcome) = match stop {
        Stop::Proof(empty) => {
            let extracting = Instant::now();
            let result = search.certificate(empty, options.max_certificate_bytes);
            search.stats.extract_ms = extracting.elapsed().as_millis() as u64;
            match result {
                Ok(certificate) => {
                    search.stats.proof_nodes = certificate.nodes as u64;
                    search.stats.proof_rules = certificate.by_rule;
                    search.stats.unchecked_nodes = certificate.unchecked;
                    json.number("certificate_bytes", certificate.text.len() as u64);
                    ("proof", Outcome::Candidate(certificate.text))
                }
                Err(ProofError::NeedsEqualityFactoring) => (
                    "needs-equality-factoring",
                    Outcome::Unknown {
                        processed: search.stats.given,
                        attempted: search.stats.attempts,
                    },
                ),
                Err(ProofError::Bytes { needed }) => {
                    json.number("certificate_bytes_needed", needed as u64);
                    ("certificate-bytes", Outcome::CertificateBytes)
                }
                Err(ProofError::Internal(message)) => {
                    json.string("internal", message);
                    ("self-check", Outcome::Internal(message))
                }
            }
        }
        Stop::Saturated => (
            // After pruning, an empty passive set is not a saturation of the clause set.
            if search.stats.pruned > 0 {
                "passive-empty-after-pruning"
            } else {
                "saturated"
            },
            Outcome::Unknown {
                processed: search.stats.given,
                attempted: search.stats.attempts,
            },
        ),
        Stop::Time => ("time", Outcome::Stopped("time limit")),
        Stop::Memory => ("memory", Outcome::Stopped("memory limit")),
        Stop::GivenLimit => ("given-limit", Outcome::Stopped("given clause limit")),
    };
    let counts = search.stats.json();
    json.string("stop_reason", reason).raw("counts", &counts);
    (reason, outcome, json, counts)
}

fn trace_term(search: &Search, names: &Names, term: crate::term::TermId, out: &mut String) {
    use crate::term::Head;
    match search.bank.head(term) {
        Head::Var(variable) => out.push_str(&format!("X{variable}")),
        Head::Sym(symbol) => {
            let symbol = symbol as usize;
            let name = if symbol < search.functions {
                names
                    .functions
                    .get(symbol)
                    .cloned()
                    .unwrap_or(format!("f{symbol}"))
            } else {
                let predicate = symbol - search.functions;
                names
                    .predicates
                    .get(predicate)
                    .cloned()
                    .unwrap_or(format!("p{predicate}"))
            };
            out.push_str(&name);
            let args = search.bank.args(term);
            if !args.is_empty() {
                out.push('(');
                for (index, &child) in args.iter().enumerate() {
                    if index > 0 {
                        out.push(',');
                    }
                    trace_term(search, names, child, out);
                }
                out.push(')');
            }
        }
    }
}

/// The recorded given clauses, one per line, with names (debugging only).
fn render_trace(search: &Search, names: &Names) -> String {
    let mut out = String::new();
    for (order, &id) in search.given_trace.iter().enumerate() {
        let record = &search.clauses[id as usize];
        out.push_str(&format!(
            "{order} #{id} weight={} goal={} {}: ",
            record.weight,
            record.goal,
            record.rule.name()
        ));
        for (index, literal) in record.lits.iter().enumerate() {
            if index > 0 {
                out.push_str(" | ");
            }
            match literal.atom {
                crate::clause::Atom::Pred(term) => {
                    if !literal.positive {
                        out.push('~');
                    }
                    trace_term(search, names, term, &mut out);
                }
                crate::clause::Atom::Eq(left, right) => {
                    trace_term(search, names, left, &mut out);
                    out.push_str(if literal.positive { " = " } else { " != " });
                    trace_term(search, names, right, &mut out);
                }
            }
        }
        out.push('\n');
    }
    out
}

/// The result of one search on a prepared signed task (`refute_prepared`).
#[derive(Debug)]
pub enum Refutation {
    /// An unchecked version-8 candidate certificate and the indices of the prepared clauses it uses, ascending.
    Candidate {
        text: String,
        inputs: Vec<usize>,
    },
    /// The search ended without a refutation the format can state. Counters
    /// describe this search, or the final slice when returned by the portfolio.
    Unknown {
        processed: u64,
        attempted: u64,
    },
    /// A time, memory or given-clause bound.
    Stopped(&'static str),
    Invalid(InvalidPrepared),
    /// A refutation whose certificate would exceed `options.max_certificate_bytes`.
    CertificateBytes {
        needed: usize,
    },
    /// A producer bug found by the self-check; no certificate.
    Internal(&'static str),
}

/// Search a prepared signed task with one option set (portfolio slices are the caller's: call once per slice) until
/// `deadline`, under `memory_mib` of resident memory. Goals and SInE groups come from `prepared.origins`; the
/// returned input indices refer to `prepared.clauses`, so a caller can map them through `origins` to declarations.
pub fn refute_prepared(
    prepared: &fang_tptp_signed_roles::Prepared,
    options: &Options,
    deadline: Option<Instant>,
    memory_mib: Option<u64>,
) -> Refutation {
    let groups: Vec<crate::sine::Group> = prepared
        .origins
        .iter()
        .map(|origin| crate::sine::Group {
            clauses: origin.clauses.clone(),
            goal: !origin.positive
                || origin.role == fang_tptp_full_frontend_candidate::Role::NegatedConjecture,
        })
        .collect();
    let clauses = &prepared.clauses;
    let mut goals = vec![false; clauses.len()];
    for group in groups.iter().filter(|group| group.goal) {
        for index in group.clauses.clone() {
            goals[index] = true;
        }
    }
    if options.goal_constants {
        widen_goals(clauses, &mut goals);
    }
    let selected = options
        .sine
        .filter(|_| !options.sine_layer)
        .map(|tolerance| crate::sine::select(clauses, &groups, tolerance, options.sine_depth));
    let levels = options
        .sine_layer
        .then(|| crate::sine::levels(clauses, &groups, options.sine.unwrap_or(2.0)));
    let limits = Limits {
        deadline,
        memory_kib: memory_mib.map(|mib| mib * 1024 * 85 / 100),
    };
    let mut search = match Search::with_levels(
        clauses,
        &prepared.function_arities,
        &prepared.predicate_arities,
        options,
        limits,
        selected.as_deref(),
        Some(&goals),
        levels.as_deref(),
    ) {
        Ok(search) => search,
        Err(kind) => return Refutation::Invalid(kind),
    };
    let stop = search.run();
    let unknown = Refutation::Unknown {
        processed: search.stats.given,
        attempted: search.stats.attempts,
    };
    match stop {
        Stop::Proof(empty) => match search.certificate(empty, options.max_certificate_bytes) {
            Ok(certificate) => Refutation::Candidate {
                text: certificate.text,
                inputs: certificate.inputs,
            },
            Err(ProofError::NeedsEqualityFactoring) => unknown,
            Err(ProofError::Bytes { needed }) => Refutation::CertificateBytes { needed },
            Err(ProofError::Internal(message)) => Refutation::Internal(message),
        },
        Stop::Saturated => unknown,
        Stop::Time => Refutation::Stopped("time limit"),
        Stop::Memory => Refutation::Stopped("memory limit"),
        Stop::GivenLimit => Refutation::Stopped("given clause limit"),
    }
}

/// Run the portfolio on one prepared task and retain the used input indices.
/// Callers doing premise discovery and replay pass deadlines derived from the
/// same outer budget. This function never starts a fresh per-pass time budget.
pub fn refute_prepared_portfolio(
    prepared: &fang_tptp_signed_roles::Prepared,
    options: &Options,
    deadline: Option<Instant>,
    memory_mib: Option<u64>,
) -> Refutation {
    let single = [(1, options.clone())];
    let slices = if options.portfolio.is_empty() {
        &single[..]
    } else {
        &options.portfolio[..]
    };
    let mut remaining: u64 = slices.iter().map(|(share, _)| u64::from(*share)).sum();
    if remaining == 0 || slices.iter().any(|(share, _)| *share == 0) {
        return Refutation::Internal("portfolio has a zero time share");
    }
    let mut last = Refutation::Internal("portfolio has no slices");
    for (share, slice) in slices {
        let now = Instant::now();
        if deadline.is_some_and(|end| now >= end) {
            return Refutation::Stopped("time limit");
        }
        let slice_deadline = deadline.map(|end| {
            now + end
                .duration_since(now)
                .mul_f64(f64::from(*share) / remaining as f64)
        });
        remaining -= u64::from(*share);
        last = refute_prepared(prepared, slice, slice_deadline, memory_mib);
        if matches!(
            last,
            Refutation::Candidate { .. }
                | Refutation::Invalid(_)
                | Refutation::Internal(_)
                | Refutation::CertificateBytes { .. }
        ) {
            break;
        }
    }
    last
}

/// Add to the goal set every input clause that mentions a constant (a nullary function) of a goal clause.
fn widen_goals(clauses: &[Clause], flags: &mut [bool]) {
    fn constants(term: &fang::syntax::Term, found: &mut std::collections::BTreeSet<u32>) {
        if let fang::syntax::Term::Fun(symbol, arguments) = term {
            if arguments.is_empty() {
                found.insert(*symbol);
            }
            for argument in arguments {
                constants(argument, found);
            }
        }
    }
    let of = |clause: &Clause| {
        let mut found = std::collections::BTreeSet::new();
        for literal in clause {
            match &literal.atom {
                fang_equality_inference_core::Atom::Predicate(_, arguments) => arguments
                    .iter()
                    .for_each(|argument| constants(argument, &mut found)),
                fang_equality_inference_core::Atom::Equal(left, right) => {
                    constants(left, &mut found);
                    constants(right, &mut found);
                }
            }
        }
        found
    };
    let goal_constants: std::collections::BTreeSet<u32> = clauses
        .iter()
        .zip(flags.iter())
        .filter(|(_, goal)| **goal)
        .flat_map(|(clause, _)| of(clause))
        .collect();
    for (clause, flag) in clauses.iter().zip(flags.iter_mut()) {
        if !*flag
            && of(clause)
                .iter()
                .any(|symbol| goal_constants.contains(symbol))
        {
            *flag = true;
        }
    }
}

/// The JSON string form, for binaries that add their own fields.
pub fn json_string(value: &str) -> String {
    quote(value)
}
