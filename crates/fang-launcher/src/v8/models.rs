// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Certified finite models: the model producer's candidates, decided by the compiled Lean model checker.
//!
//! In compiled mode, when the installation has the model binaries, a run takes four steps (their parameters are
//! `STAGE_ORDER`):
//!
//! 1. refutation pass 1: the refutation stages with a short producer time limit, then the checker reserve;
//! 2. model slice A, a share of the wall budget;
//! 3. refutation pass 2: the same stages again from scratch, nothing resumed from pass 1, until a share of the
//!    wall budget;
//! 4. model slice B: what is left less the model reserve, resuming every task at the domain size slice A
//!    reached.
//!
//! A result ends the run at the step that finds it. Steps 2 to 4 run only after GaveUp or ResourceOut, and a
//! time stop at the deadline of a refutation pass counts as ResourceOut. A candidate goes to the model checker at
//! once and needs the model reserve left. Only the checker's acceptance gives Satisfiable, or CounterSatisfiable
//! for a listed conjecture with the listed item; a rejected candidate is an Error and ends the run; a search
//! that finds nothing is never a result. Kernel and none modes run the refutation once with the whole budget and
//! no model step.

use std::collections::HashMap;
use std::ffi::OsString;
use std::sync::OnceLock;
use std::time::{Duration, Instant};

use fang_json::{Object, Value};
use fang_supervisor::{Fault, Snapshot, Status};

use super::run::{
    Run, ascii_text, code_value, failure, first_line, model_limit, python_code, python_strip,
    record_object,
};
use super::signed::{BundleFile, Item};
use super::stages::STAGE_ORDER;
use crate::pattern::{Pattern, group};

pub const MODE: &str = "checked by the compiled Lean model checker";
pub const TSTP_NOTE: &str = "TSTP output prints a refutation; a model result prints no document";
const HEADER: &[u8] = b"fang-model 1\n";
const TRUSTED: &str = " (native checker; compiler/runtime trusted)\n";
const UNSOLVED: [&str; 2] = ["GaveUp", "ResourceOut"];

struct Compiled {
    candidate: Pattern,
    no_model: Pattern,
    goal: Pattern,
    resource: Pattern,
}

fn compiled() -> &'static Compiled {
    static COMPILED: OnceLock<Compiled> = OnceLock::new();
    COMPILED.get_or_init(|| Compiled {
        candidate: Pattern::of(r"candidate-model: unchecked domain ([0-9]+)\n"),
        no_model: Pattern::of(r"no-model: (?:no model up to domain ([0-9]+)|stopped at domain ([0-9]+) \([ -~]*\))\n"),
        goal: Pattern::of(r"accepted-countermodel-goal ([0-9]+) item ([0-9]+) ([0-9]+) \(native checker; compiler/runtime trusted\)\n"),
        resource: Pattern::of(r"resource\.(model|bytes|bundle)\.(?:.|\n)*"),
    })
}

fn number(bytes: Option<&[u8]>) -> Option<u64> {
    std::str::from_utf8(bytes?).ok()?.parse().ok()
}

/// The producer's outcome: a candidate or no model up to a domain size, or a refusal; any other exit is an
/// error, given as its message.
pub fn producer_outcome(
    code: i64,
    stdout: &[u8],
    stderr: &[u8],
) -> Result<(&'static str, Option<u64>), String> {
    let patterns = compiled();
    if code == 0
        && stdout.starts_with(HEADER)
        && let Some(captures) = patterns.candidate.fullmatch(stderr)
    {
        return Ok(("candidate", number(group(stderr, &captures, 1))));
    }
    if !stdout.is_empty() {
        return Err("A model producer that found no candidate wrote output".to_string());
    }
    if code == 2
        && let Some(captures) = patterns.no_model.fullmatch(stderr)
    {
        let domain =
            number(group(stderr, &captures, 1)).or_else(|| number(group(stderr, &captures, 2)));
        return Ok(("none", domain));
    }
    if code == 3 && stderr.starts_with(b"refused: ") {
        return Ok(("refused", None));
    }
    Err("Unrecognized model producer contract".to_string())
}

/// The status the model checker's verdict gives, or a Failure for every other outcome.
pub fn checker_outcome(
    code: Option<i32>,
    stdout: &[u8],
    stderr: &[u8],
    task: &str,
    item: Option<(u64, u64, u64)>,
) -> Result<&'static str, Fault> {
    if code == Some(0) && stderr.is_empty() {
        let accepted = match task {
            "single" | "bundle" | "inputs" => Some(format!("accepted-model-{task}{TRUSTED}")),
            _ => None,
        };
        if accepted.as_deref().map(str::as_bytes) == Some(stdout) {
            return Ok("Satisfiable");
        }
        if task == "goal"
            && let Some(captures) = compiled().goal.fullmatch(stdout)
        {
            let printed = (
                number(group(stdout, &captures, 1)),
                number(group(stdout, &captures, 2)),
                number(group(stdout, &captures, 3)),
            );
            let expected =
                item.map(|(goal, file, statement)| (Some(goal), Some(file), Some(statement)));
            if Some(printed) != expected {
                return Err(failure(
                    Status::Error,
                    "The model checker accepted a countermodel for another listed item",
                    "model-check",
                ));
            }
            return Ok("CounterSatisfiable");
        }
        return Err(failure(
            Status::Error,
            "Unrecognized model checker acceptance",
            "model-check",
        ));
    }
    let first = first_line(stderr);
    if code == Some(1) && stderr.starts_with(b"model-rejection: ") {
        return Err(failure(
            Status::Error,
            format!("The model checker rejected a candidate model: {first}"),
            "model-check",
        ));
    }
    if code == Some(4) && compiled().resource.is_full(stderr) {
        return Err(failure(
            Status::ResourceOut,
            format!("The model checker stopped at a resource limit: {first}"),
            "model-check",
        ));
    }
    Err(failure(
        Status::Error,
        format!(
            "The model checker failed (exit {}): {first}",
            python_code(code)
        ),
        "model-check",
    ))
}

/// One producer task: its label, its selection arguments, its checker task and, for a goal, its listed item.
type Task = (String, Vec<OsString>, &'static str, Option<(u64, u64, u64)>);

/// The model steps of one run: producer and checker on the sealed input files of the route.
pub struct ModelStages {
    snapshots: Vec<Snapshot>,
    triples: Vec<OsString>,
    domains: HashMap<String, Option<u64>>,
}

impl ModelStages {
    /// The model steps of compiled mode, when the installation has the model binaries; None otherwise.
    pub fn new(run: &mut Run, files: &[BundleFile]) -> Result<Option<ModelStages>, Fault> {
        if run.args.check != "compiled" || run.capability.section("model").is_none() {
            return Ok(None);
        }
        let mut snapshots = Vec::new();
        let mut triples = Vec::new();
        for (index, file) in files.iter().enumerate() {
            let snapshot =
                Snapshot::create(&run.root.join(format!("model-input-{index}.p")), &file.data)?;
            triples.push(OsString::from(&file.root));
            triples.push(OsString::from(&file.path));
            triples.push(snapshot.argument().as_os_str().to_os_string());
            snapshots.push(snapshot);
        }
        if run.manifest.get("model").is_none() {
            run.manifest.set("model", Value::Array(Vec::new()));
        }
        Ok(Some(ModelStages {
            snapshots,
            triples,
            domains: HashMap::new(),
        }))
    }

    fn tasks(route: &str, listed: Option<&[Item]>) -> Vec<Task> {
        match route {
            "single" => vec![(
                "single".to_string(),
                vec!["--single".into()],
                "single",
                None,
            )],
            "bundle" => vec![(
                "bundle".to_string(),
                vec!["--bundle".into()],
                "bundle",
                None,
            )],
            _ => match listed {
                Some(items) if !items.is_empty() => items
                    .iter()
                    .enumerate()
                    .map(|(index, (file, statement))| {
                        (
                            format!("goal-{index}"),
                            vec!["--goal".into(), index.to_string().into()],
                            "goal",
                            Some((index as u64, *file, *statement)),
                        )
                    })
                    .collect(),
                _ => vec![(
                    "inputs".to_string(),
                    vec!["--inputs".into()],
                    "inputs",
                    None,
                )],
            },
        }
    }

    fn push_record(run: &mut Run, record: Object) {
        if let Some(Value::Array(records)) = run.manifest.get_mut("model") {
            records.push(Value::Object(record));
        }
    }

    fn update_record(run: &mut Run, key: &str, value: Value) {
        if let Some(Value::Array(records)) = run.manifest.get_mut("model")
            && let Some(Value::Object(last)) = records.last_mut()
        {
            last.set(key, value);
        }
    }

    /// One producer run; a candidate goes to the checker. Returns a status or None.
    fn run_task(
        &mut self,
        run: &mut Run,
        task: &Task,
        seconds: f64,
        phase: &str,
    ) -> Result<Option<(String, String)>, Fault> {
        let (label, selection, kind, item) = task;
        let stage_name = format!("{label}-{phase}");
        if seconds < 1.0 {
            return Ok(None);
        }
        let whole = seconds.floor() as i64;
        let producer = run.binary("model", "producer");
        let mut command: Vec<OsString> = vec![producer.into_os_string()];
        command.extend(selection.iter().cloned());
        command.push("--seconds".into());
        command.push(whole.to_string().into());
        command.push("--memory-mib".into());
        command.push(
            run.args
                .memory_mib
                .saturating_sub(STAGE_ORDER.memory_margin_mib)
                .max(16)
                .to_string()
                .into(),
        );
        if let Some(Some(domain)) = self.domains.get(label) {
            command.push("--from-domain".into());
            command.push(domain.to_string().into());
        }
        command.extend(self.triples.iter().cloned());
        let find = format!("model-find-{stage_name}");
        let limit = model_limit(run);
        let output = run.stage(&find, &command, &run.root.join(&find), None, Some(limit))?;
        let code = output.record.exit_code.map(i64::from).unwrap_or(-1);
        let (outcome, domain) = producer_outcome(code, &output.stdout, &output.stderr)
            .map_err(|message| failure(Status::Error, message, &find))?;
        let mut record = Object::new();
        record.set("task", label.as_str());
        record.set("slice", phase);
        record.set("producer", outcome);
        record.set("domain", domain.map(Value::from).unwrap_or(Value::Null));
        record.set("seconds", Value::from(whole));
        Self::push_record(run, record);
        if outcome == "none" {
            self.domains.insert(label.clone(), domain);
            return Ok(None);
        }
        if outcome == "refused" {
            self.domains.insert(label.clone(), None);
            return Ok(None);
        }
        if remaining(run) < STAGE_ORDER.model_reserve_seconds {
            return Err(failure(
                Status::ResourceOut,
                "A candidate model arrived without time left for the model checker",
                "model-check",
            ));
        }
        let certificate = Snapshot::create(
            &run.root.join(format!("model-{stage_name}.fang")),
            &output.stdout,
        )?;
        Self::update_record(
            run,
            "certificate_sha256",
            Value::from(certificate.sha256.as_str()),
        );
        Self::update_record(
            run,
            "certificate_bytes",
            Value::from(output.stdout.len() as u64),
        );
        let arguments: Vec<OsString> = if *kind == "single" {
            vec![
                "--single".into(),
                certificate.argument().as_os_str().to_os_string(),
                self.snapshots[0].argument().as_os_str().to_os_string(),
            ]
        } else {
            let mut arguments = selection.clone();
            arguments.push(certificate.argument().as_os_str().to_os_string());
            arguments.extend(self.triples.iter().cloned());
            arguments
        };
        let check = format!("model-check-{stage_name}");
        let mut command = vec![run.binary("model", "checker").into_os_string()];
        command.extend(arguments.iter().cloned());
        let output = run.stage(&check, &command, &run.root.join(&check), None, None)?;
        let code = output.record.exit_code;
        Self::update_record(run, "checker_exit", code_value(code));
        let status = checker_outcome(code, &output.stdout, &output.stderr, kind, *item)?;
        let mut sealed: Vec<&Snapshot> = self.snapshots.iter().collect();
        sealed.push(&certificate);
        run.confirm(&sealed, "model-checked")?;
        let printed = ascii_text(&output.stdout);
        Self::update_record(run, "checker", Value::from(python_strip(&printed)));
        let mut accepted = Object::new();
        accepted.set("accepted", true);
        accepted.set("task", label.as_str());
        accepted.set("status", status);
        accepted.set("trust", "Lean compiler, runtime and operating system");
        run.manifest.set("model_check", Value::Object(accepted));
        if run.args.output == "tstp" {
            match run.capability.section_record("model", "exporter") {
                None => run.manifest.set("export_note", TSTP_NOTE),
                Some(exporter) => {
                    let mut command = vec![exporter.path.into_os_string()];
                    command.extend(arguments.iter().cloned());
                    // The status is the checker's; the exporter's exit only decides whether a document is printed.
                    run.export_document(&command, "export-model", "solution-model.p")?;
                }
            }
        }
        let reason = if status == "Satisfiable" {
            "The compiled Lean model checker accepted a finite model of the input"
        } else {
            "The compiled Lean model checker accepted a finite countermodel of a listed conjecture"
        };
        Ok(Some((status.to_string(), reason.to_string())))
    }

    fn slice(
        &mut self,
        run: &mut Run,
        route: &str,
        mut seconds: f64,
        listed: Option<&[Item]>,
        resume: bool,
    ) -> Result<Option<(String, String)>, Fault> {
        let phase = if resume { "b" } else { "a" };
        let tasks: Vec<Task> = Self::tasks(route, listed)
            .into_iter()
            .filter(|task| !resume || !matches!(self.domains.get(&task.0), Some(None)))
            .collect();
        let count = tasks.len();
        for (position, task) in tasks.iter().enumerate() {
            let share = (seconds / (count - position).max(1) as f64)
                .min(remaining(run) - STAGE_ORDER.model_reserve_seconds);
            let started = Instant::now();
            let found = self.run_task(run, task, share, phase)?;
            seconds -= started.elapsed().as_secs_f64();
            if found.is_some() {
                return Ok(found);
            }
        }
        Ok(None)
    }

    fn slice_a(
        &mut self,
        run: &mut Run,
        route: &str,
        listed: Option<&[Item]>,
    ) -> Result<Option<(String, String)>, Fault> {
        let seconds = (STAGE_ORDER.slice_a_share * run.args.wall_seconds)
            .min(remaining(run) - STAGE_ORDER.model_reserve_seconds);
        self.slice(run, route, seconds, listed, false)
    }

    fn slice_b(
        &mut self,
        run: &mut Run,
        route: &str,
        listed: Option<&[Item]>,
    ) -> Result<Option<(String, String)>, Fault> {
        let seconds = remaining(run) - STAGE_ORDER.model_reserve_seconds;
        self.slice(run, route, seconds, listed, true)
    }
}

/// Seconds left before the command deadline; negative once it has passed.
fn remaining(run: &Run) -> f64 {
    let deadline = run.supervisor.deadline();
    let now = Instant::now();
    if deadline >= now {
        (deadline - now).as_secs_f64()
    } else {
        -(now - deadline).as_secs_f64()
    }
}

fn discard_export(run: &mut Run) {
    run.manifest.remove("export");
    run.manifest.remove("export_note");
}

fn passed(run: &mut Run, number: u32, started: Instant, status: &str) {
    let mut record = Object::new();
    record.set("pass", Value::from(u64::from(number)));
    record.set("status", status);
    record.set(
        "seconds",
        Value::from((started.elapsed().as_secs_f64() * 1000.0).round() / 1000.0),
    );
    if run.manifest.get("refutation_passes").is_none() {
        run.manifest
            .set("refutation_passes", Value::Array(Vec::new()));
    }
    if let Some(Value::Array(passes)) = run.manifest.get_mut("refutation_passes") {
        passes.push(Value::Object(record));
    }
}

/// The refutation stages of one pass, given the pass number.
pub type Refute<'a> = dyn FnMut(&mut Run, u32) -> Result<(String, String), Fault> + 'a;

/// Refutation pass 1: the producer gets the pass-one time limit and the checker of its candidate the reserve
/// after it. A time or resource stop goes on to slice A as ResourceOut unless the command's own deadline is near.
fn first_pass(run: &mut Run, refute: &mut Refute) -> Result<(String, String), Fault> {
    let saved = run.supervisor.deadline();
    let started = Instant::now();
    let window = Duration::from_secs_f64(
        STAGE_ORDER.pass_one_seconds + STAGE_ORDER.search_check_reserve_seconds,
    );
    run.supervisor.set_deadline(saved.min(started + window));
    let result = refute(run, 1);
    run.supervisor.set_deadline(saved);
    let time_left =
        Instant::now() + Duration::from_secs_f64(STAGE_ORDER.model_reserve_seconds) < saved;
    match result {
        Ok((status, reason)) => {
            passed(run, 1, started, &status);
            Ok((status, reason))
        }
        Err(Fault::Failure(error))
            if matches!(error.status, Status::Timeout | Status::ResourceOut) && time_left =>
        {
            passed(run, 1, started, "ResourceOut");
            discard_export(run);
            let reason = if error.status == Status::Timeout {
                "Refutation pass 1 reached its time limit".to_string()
            } else {
                error.reason
            };
            Ok(("ResourceOut".to_string(), reason))
        }
        Err(fault) => {
            passed(run, 1, started, fault.status().name());
            Err(fault)
        }
    }
}

/// Refutation pass 2, from scratch, until the refutation share of the wall budget; a stop at that share is
/// ResourceOut.
fn capped(run: &mut Run, refute: &mut Refute) -> Result<(String, String), Fault> {
    let saved = run.supervisor.deadline();
    let started = Instant::now();
    let cap = run.supervisor.started
        + Duration::from_secs_f64(STAGE_ORDER.refutation_share * run.args.wall_seconds);
    run.supervisor.set_deadline(saved.min(cap));
    let result = refute(run, 2);
    run.supervisor.set_deadline(saved);
    match result {
        Ok((status, reason)) => {
            passed(run, 2, started, &status);
            Ok((status, reason))
        }
        Err(Fault::Failure(error))
            if error.status == Status::Timeout
                && Instant::now() + Duration::from_secs_f64(STAGE_ORDER.model_reserve_seconds)
                    < saved =>
        {
            passed(run, 2, started, "ResourceOut");
            discard_export(run);
            Ok((
                "ResourceOut".to_string(),
                "The refutation stages used their share of the time budget".to_string(),
            ))
        }
        Err(fault) => {
            passed(run, 2, started, fault.status().name());
            Err(fault)
        }
    }
}

/// Refutation pass 1, slice A, refutation pass 2, then slice B when pass 2 stopped early. Without model stages
/// the refutation runs once, as pass 1, with the whole budget.
pub fn around(
    run: &mut Run,
    stages: Option<&mut ModelStages>,
    route: &str,
    listed: Option<&[Item]>,
    refute: &mut Refute,
) -> Result<(String, String), Fault> {
    let Some(stages) = stages else {
        return refute(run, 1);
    };
    let (status, reason) = first_pass(run, refute)?;
    if !UNSOLVED.contains(&status.as_str()) {
        return Ok((status, reason));
    }
    if let Some(found) = stages.slice_a(run, route, listed)? {
        return Ok(found);
    }
    let (status, reason) = match capped(run, refute) {
        Ok(result) => result,
        Err(fault) if fault.status() == Status::ResourceOut => {
            discard_export(run);
            if let Some(found) = stages.slice_b(run, route, listed)? {
                return Ok(found);
            }
            return Err(fault);
        }
        Err(fault) => return Err(fault),
    };
    if UNSOLVED.contains(&status.as_str())
        && let Some(found) = stages.slice_b(run, route, listed)?
    {
        return Ok(found);
    }
    Ok((status, reason))
}

/// The record of a finished stage as an object, for callers that classify it.
pub fn stage_record(output: &fang_supervisor::StageOutput) -> Object {
    record_object(output)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn producer_and_checker_contracts() {
        assert_eq!(
            producer_outcome(
                0,
                b"fang-model 1\n(model)\n",
                b"candidate-model: unchecked domain 2\n"
            )
            .unwrap(),
            ("candidate", Some(2))
        );
        assert_eq!(
            producer_outcome(2, b"", b"no-model: no model up to domain 3\n").unwrap(),
            ("none", Some(3))
        );
        assert_eq!(
            producer_outcome(2, b"", b"no-model: stopped at domain 4 (time)\n").unwrap(),
            ("none", Some(4))
        );
        assert_eq!(
            producer_outcome(3, b"", b"refused: unsupported input\n").unwrap(),
            ("refused", None)
        );
        assert!(producer_outcome(2, b"x", b"no-model: no model up to domain 3\n").is_err());
        let trusted = TRUSTED;
        let single = format!("accepted-model-single{trusted}");
        assert_eq!(
            checker_outcome(Some(0), single.as_bytes(), b"", "single", None).unwrap(),
            "Satisfiable"
        );
        let goal = format!("accepted-countermodel-goal 0 item 0 1{trusted}");
        assert_eq!(
            checker_outcome(Some(0), goal.as_bytes(), b"", "goal", Some((0, 0, 1))).unwrap(),
            "CounterSatisfiable"
        );
        assert!(checker_outcome(Some(0), goal.as_bytes(), b"", "goal", Some((0, 7, 0))).is_err());
        let rejected = checker_outcome(
            Some(1),
            b"",
            b"model-rejection: the formula a is false\n",
            "single",
            None,
        )
        .unwrap_err();
        assert_eq!(rejected.status(), Status::Error);
        let resource =
            checker_outcome(Some(4), b"", b"resource.model.cells\n", "single", None).unwrap_err();
        assert_eq!(resource.status(), Status::ResourceOut);
        let killed = checker_outcome(None, b"", b"", "single", None).unwrap_err();
        assert_eq!(
            killed.reason(),
            "The model checker failed (exit None): no diagnostic"
        );
    }
}
