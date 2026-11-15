// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
#![forbid(unsafe_code)]
use fang_json::{Object, Value};
use fang_launcher::v8::signed::{self, Checked, Listing};
use fang_launcher::v8::{bundle, protocol};
use fang_supervisor::{Fault, Limits, Snapshot, Stage, StageOutput, Supervisor};
use std::ffi::OsString;
use std::fs;
use std::path::{Path, PathBuf};

const VARIANTS: [(&str, &str); 8] = [
    ("baseline", "kbo_weights=uniform"),
    ("constant-heavy", "kbo_weights=constant-heavy"),
    ("inverse-frequency", "kbo_weights=invfreq"),
    ("lpo", "ordering=lpo"),
    ("ground-negative", "selection=ground-negative"),
    ("negative-equality", "selection=negative-equality"),
    ("lightest", "selection=lightest-negative"),
    ("lookahead", "selection=lookahead"),
];

fn save(path: &Path, value: Value) -> Result<(), String> {
    let text = fang_json::dumps(&value, &Default::default()).map_err(|e| format!("{e:?}"))?;
    fs::write(path, format!("{text}\n")).map_err(|e| e.to_string())
}

fn supervisor(seconds: f64) -> Result<Supervisor, String> {
    Supervisor::new(
        Limits {
            wall_seconds: seconds,
            memory_mib: 2048,
            artifact_bytes: 64 << 20,
            ..Limits::default()
        },
        None,
    )
    .map_err(|e| format!("{e:?}"))
}

fn stage(
    sup: &mut Supervisor,
    directory: &Path,
    name: &str,
    command: &[OsString],
) -> Result<StageOutput, String> {
    stage_input(sup, directory, name, command, None)
}

fn stage_input(
    sup: &mut Supervisor,
    directory: &Path,
    name: &str,
    command: &[OsString],
    stdin: Option<&Path>,
) -> Result<StageOutput, String> {
    sup.run(&Stage {
        name,
        command,
        directory: &directory.join(name),
        run_root: directory,
        environment: None,
        stdin,
        stdout_limit: Some(8 << 20),
        cwd: None,
    })
    .map_err(|e| e.reason())
}

struct Input {
    snapshots: Vec<Snapshot>,
    triples: Vec<OsString>,
    goal: Option<signed::Item>,
    route: &'static str,
    tptp: PathBuf,
    keys: Vec<(String, String)>,
}

fn prepare(top: &Path, tptp: &Path, directory: &Path, installed: &Path) -> Result<Input, String> {
    fs::create_dir_all(directory).map_err(|e| e.to_string())?;
    let mut sup = supervisor(15.0)?;
    let result = (|| {
        let mut total = 0usize;
        let mut read = |path: &Path| -> Result<Vec<u8>, Fault> {
            let data =
                fang_supervisor::read_regular(path, 1 << 20, &mut || sup.check("capture", 0.0))?;
            total = total
                .checked_add(data.len())
                .ok_or_else(|| Fault::Value("bundle size overflow".into()))?;
            if total > 4 << 20 {
                return Err(Fault::Value("bundle byte limit".into()));
            }
            Ok(data)
        };
        let bytes = read(top).map_err(|e| e.reason())?;
        let name = top
            .file_name()
            .and_then(|s| s.to_str())
            .ok_or("Invalid input name")?;
        let files = signed::discover(
            name,
            bytes,
            top.parent().ok_or("Missing input parent")?,
            Some(tptp),
            &mut read,
        )
        .map_err(|e| e.reason())?;
        let route = match signed::route(&files, bundle::needs_bundle(&files[0].data)) {
            "signed" if files.len() == 1 && !bundle::needs_bundle(&files[0].data) => {
                "signed-single"
            }
            "signed" => "signed-bundle",
            route => route,
        };
        let mut snapshots = Vec::new();
        let mut triples = Vec::new();
        let mut inventory = Vec::new();
        let mut keys = Vec::new();
        for file in files {
            if !matches!(file.root.as_str(), "base" | "tptp")
                || Path::new(&file.path)
                    .components()
                    .any(|c| !matches!(c, std::path::Component::Normal(_)))
            {
                return Err("unsafe discovered path".into());
            }
            let path = directory.join("sealed").join(&file.root).join(&file.path);
            fs::create_dir_all(path.parent().ok_or("missing sealed parent")?)
                .map_err(|e| e.to_string())?;
            let snapshot = Snapshot::create(&path, &file.data).map_err(|e| e.reason())?;
            keys.push((file.root.clone(), file.path.clone()));
            triples.extend([
                OsString::from(&file.root),
                OsString::from(&file.path),
                snapshot.argument().as_os_str().to_owned(),
            ]);
            let mut row = Object::new();
            row.set("root", file.root);
            row.set("path", file.path);
            row.set("bytes", file.data.len());
            row.set("sha256", fang_hash::sha256_hex(&file.data));
            inventory.push(Value::Object(row));
            snapshots.push(snapshot);
        }
        save(&directory.join("inputs.json"), Value::Array(inventory))?;
        let mut command = vec![
            installed.join("bin/fang-signed-check").into_os_string(),
            "--goals".into(),
        ];
        command.extend(triples.iter().cloned());
        let output = stage(&mut sup, directory, "goals", &command)?;
        let record = output.record.to_json();
        let items = match signed::listing(
            record.as_object().ok_or("Missing record")?,
            &output.stdout,
            &output.stderr,
        )
        .map_err(|e| format!("{e:?}"))?
        {
            Listing::Listed(items) => items,
            Listing::Rejected(reason) => return Err(format!("listing rejected: {reason}")),
        };
        // A pilot row describes a task, not a whole problem with several goals.
        let mut selection = Object::new();
        selection.set("listed_goals", items.len());
        selection.set("task", if items.is_empty() { "inputs" } else { "goal-0" });
        selection.set("whole_problem_result", false);
        selection.set("producer_route", route);
        save(&directory.join("task.json"), Value::Object(selection))?;
        sup.confirm_clean("listing-finish", &snapshots.iter().collect::<Vec<_>>())
            .map_err(|e| e.reason())?;
        Ok(Input {
            snapshots,
            triples,
            goal: items.first().copied(),
            route,
            tptp: directory.join("sealed/tptp"),
            keys,
        })
    })();
    save(
        &directory.join("records.json"),
        Value::Array(sup.records.iter().map(|r| r.to_json()).collect()),
    )?;
    result
}

fn task_arguments(input: &Input) -> Vec<OsString> {
    if input.goal.is_some() {
        vec!["--goal".into(), "0".into()]
    } else {
        vec!["--inputs".into()]
    }
}

fn is_expected(result: Option<Checked>, goal: Option<signed::Item>) -> bool {
    match (result, goal) {
        (Some(Checked::Inputs), None) => true,
        (Some(Checked::Goal(item)), Some(expected)) => item == expected,
        _ => false,
    }
}

fn checker_command(installed: &Path, input: &Input, certificate: &Snapshot) -> Vec<OsString> {
    let binary = match input.route {
        "single" => "fang-v8-check",
        "bundle" => "fang-bundle-check",
        _ => "fang-signed-check",
    };
    let mut command = vec![installed.join("bin").join(binary).into_os_string()];
    if input.route == "single" {
        command.push(input.snapshots[0].argument().as_os_str().to_owned());
    } else if input.route.starts_with("signed-") {
        command.extend(task_arguments(input));
    }
    command.push(certificate.argument().as_os_str().to_owned());
    if input.route != "single" {
        command.extend(input.triples.iter().cloned());
    }
    command
}

fn checker_accepted(input: &Input, output: &StageOutput) -> Result<bool, String> {
    let record = output.record.to_json();
    let record = record.as_object().ok_or("Missing checker record")?;
    match input.route {
        "single" => protocol::checker_outcome(record, &output.stdout, &output.stderr)
            .map(|outcome| outcome == "accepted")
            .map_err(|e| format!("{e:?}")),
        "bundle" => bundle::checker_outcome(record, &output.stdout, &output.stderr)
            .map(|outcome| outcome == "accepted")
            .map_err(|e| format!("{e:?}")),
        _ => signed::accepted(
            record,
            &output.stdout,
            &output.stderr,
            input.goal.map(|_| 0),
        )
        .map(|accepted| is_expected(accepted, input.goal))
        .map_err(|e| format!("{e:?}")),
    }
}

fn attempt(
    installed: &Path,
    input: &Input,
    directory: &Path,
    variant: usize,
) -> Result<bool, String> {
    fs::create_dir(directory).map_err(|e| e.to_string())?;
    let mut sup = supervisor(10.0)?;
    let mut result = Object::new();
    result.set("variant", VARIANTS[variant].0);
    result.set("producer_seconds", 2.0);
    result.set("task_seconds", 10.0);
    result.set("memory_mib", 2048u64);
    result.set("producer_route", input.route);
    result.set("whole_problem_result", false);
    let checked: Result<bool, String> = (|| {
        let stats = directory.join("search.json");
        let binary = match input.route {
            "single" => "fang-v8-engine",
            "bundle" => "fang-bundle-producer",
            "signed-single" => "fang-signed-single-producer",
            _ => "fang-signed-producer",
        };
        let mut command = vec![installed.join("bin").join(binary).into_os_string()];
        command.extend(
            [
                "--search",
                "v3",
                "--time-limit",
                "2",
                "--memory-mib",
                "1792",
                "--stats",
            ]
            .into_iter()
            .map(OsString::from),
        );
        command.push(stats.into_os_string());
        for setting in [
            "preset=step5",
            "index=on",
            "filter=on",
            "simplify_new=on",
            VARIANTS[variant].1,
        ] {
            command.extend(["--set".into(), setting.into()]);
        }
        let stdin = match input.route {
            "single" => Some(input.snapshots[0].argument()),
            "signed-single" => {
                command.extend(task_arguments(input));
                Some(input.snapshots[0].argument())
            }
            "bundle" => {
                command.push(input.snapshots[0].argument().as_os_str().to_owned());
                command.extend(["--tptp-root".into(), input.tptp.clone().into_os_string()]);
                None
            }
            _ => {
                command.extend(task_arguments(input));
                command.extend(input.triples.iter().cloned());
                None
            }
        };
        let produced = stage_input(&mut sup, directory, "producer", &command, stdin)?;
        result.set("producer_wall_seconds", produced.record.elapsed_seconds);
        let producer_record = produced.record.to_json();
        let record = producer_record
            .as_object()
            .ok_or("Missing producer record")?;
        let outcome = match input.route {
            "single" => {
                protocol::engine_outcome(
                    record,
                    &produced.stdout,
                    &produced.stderr,
                    &input.snapshots[0].data,
                )
                .map_err(|e| format!("{e:?}"))?
                .0
            }
            "bundle" => match bundle::producer_outcome(record, &produced.stdout, &produced.stderr)
                .map_err(|e| format!("{e:?}"))?
            {
                bundle::Outcome::Status(status, _) => status,
                bundle::Outcome::Candidate(info) => {
                    let files: Vec<_> = input
                        .keys
                        .iter()
                        .zip(&input.snapshots)
                        .map(|((root, path), snapshot)| {
                            (root.as_str(), path.as_str(), snapshot.data.as_slice())
                        })
                        .collect();
                    if info.files != input.keys || info.bundle_sha256 != bundle::digest(&files) {
                        return Err("bundle candidate differs from captured inputs".into());
                    }
                    "candidate".into()
                }
            },
            _ => signed::producer_outcome_for(
                record,
                &produced.stdout,
                &produced.stderr,
                if input.route == "signed-single" {
                    signed::Producer::NamedSingle
                } else {
                    signed::Producer::CitedBundle
                },
            )
            .map_err(|e| format!("{e:?}"))?
            .into(),
        };
        result.set("producer_outcome", outcome.as_str());
        if outcome != "candidate" {
            return Ok(false);
        }
        let certificate = Snapshot::create(&directory.join("candidate.fang"), &produced.stdout)
            .map_err(|e| e.reason())?;
        let command = checker_command(installed, input, &certificate);
        let checked = stage(&mut sup, directory, "checker", &command)?;
        result.set("checker_wall_seconds", checked.record.elapsed_seconds);
        if !checker_accepted(input, &checked)? {
            return Err("candidate rejected or goal identity differs".into());
        }
        let mut snapshots: Vec<_> = input.snapshots.iter().collect();
        snapshots.push(&certificate);
        sup.confirm_clean("accepted-finish", &snapshots)
            .map_err(|e| e.reason())?;
        Ok(true)
    })();
    result.set("checked_task", matches!(checked, Ok(true)));
    if let Err(message) = &checked {
        result.set("error", message.as_str());
    }
    result.set(
        "stages",
        Value::Array(sup.records.iter().map(|r| r.to_json()).collect()),
    );
    save(&directory.join("result.json"), Value::Object(result))?;
    // Per-cell failures stay visible; no candidate becomes a checked task.
    Ok(matches!(checked, Ok(true)))
}

fn corruption_control(installed: &Path, input: &Input, directory: &Path) -> Result<(), String> {
    fs::create_dir(directory).map_err(|e| e.to_string())?;
    let certificate =
        Snapshot::create(&directory.join("invalid.fang"), b"not a Fang certificate\n")
            .map_err(|e| e.reason())?;
    let command = checker_command(installed, input, &certificate);
    let mut sup = supervisor(10.0)?;
    let output = stage(&mut sup, directory, "checker", &command)?;
    let record = output.record.to_json();
    if checker_accepted(input, &output)? || output.record.exit_code == Some(0) {
        return Err("corrupt certificate accepted".into());
    }
    save(&directory.join("record.json"), record)?;
    Ok(())
}

fn self_test(installed: &Path, out: &Path) -> Result<(), String> {
    fs::create_dir(out).map_err(|e| e.to_string())?;
    fs::create_dir(out.join("Axioms")).map_err(|e| e.to_string())?;
    fs::write(out.join("Axioms/control.ax"), "fof(a,axiom,p(a)).\n").map_err(|e| e.to_string())?;
    for (name, text, expected_route) in [
        (
            "inputs",
            "cnf(a,axiom,p(a)).\ncnf(b,axiom,~p(a)).\n",
            "single",
        ),
        (
            "goal",
            "fof(a,axiom,p(a)).\nfof(g,conjecture,p(a)).\n",
            "signed-single",
        ),
        (
            "bundle",
            "include('Axioms/control.ax').\nfof(b,axiom,~p(a)).\n",
            "bundle",
        ),
        (
            "signed-bundle",
            "include('Axioms/control.ax').\nfof(g,conjecture,p(a)).\n",
            "signed-bundle",
        ),
        ("objects", "fof(a,axiom,\"one\" = \"two\").\n", "bundle"),
    ] {
        let top = out.join(format!("{name}.p"));
        fs::write(&top, text).map_err(|e| e.to_string())?;
        let input = prepare(&top, out, &out.join(format!("{name}-capture")), installed)?;
        if input.route != expected_route {
            return Err(format!("wrong route: {name}: {}", input.route));
        }
        for (index, variant) in VARIANTS.iter().enumerate() {
            if !attempt(
                installed,
                &input,
                &out.join(format!("{name}-{}", variant.0)),
                index,
            )? {
                return Err(format!("positive control failed: {name}/{}", variant.0));
            }
        }
        corruption_control(installed, &input, &out.join(format!("{name}-corruption")))?;
    }
    println!(
        "PASS: 40 checked task controls across four routes and five corrupted-certificate rejections"
    );
    Ok(())
}

fn pilot(installed: &Path, library: &Path, membership: &Path, out: &Path) -> Result<(), String> {
    let bytes = fs::read(membership).map_err(|e| e.to_string())?;
    if fang_hash::sha256_hex(&bytes)
        != "f508f7354ca152b12568545faff956a1cd0351014ce99a7c9038f53fb80f0078"
    {
        return Err(
            "expected the frozen training list; validation and held-out lists are refused".into(),
        );
    }
    let text = std::str::from_utf8(&bytes).map_err(|e| e.to_string())?;
    fs::create_dir(out).map_err(|e| e.to_string())?;
    let mut rows = Vec::new();
    for (index, line) in text.lines().skip(1).enumerate() {
        let fields: Vec<_> = line.split('\t').collect();
        if fields.len() != 4 {
            return Err("invalid frozen row".into());
        }
        let filename = fields[1];
        let top = library.join("Problems").join(&filename[..3]).join(filename);
        let directory = out.join(filename);
        fs::create_dir(&directory).map_err(|e| e.to_string())?;
        let input = prepare(&top, library, &directory.join("capture"), installed);
        for offset in 0..VARIANTS.len() {
            let variant = (index + offset) % VARIANTS.len();
            let mut row = Object::new();
            row.set("filename", filename);
            row.set("variant", VARIANTS[variant].0);
            match &input {
                Ok(input) => {
                    row.set(
                        "checked_task",
                        attempt(
                            installed,
                            input,
                            &directory.join(VARIANTS[variant].0),
                            variant,
                        )?,
                    );
                }
                Err(reason) => {
                    row.set("checked_task", false);
                    row.set("capture_error", reason.as_str());
                }
            }
            rows.push(Value::Object(row));
            save(&out.join("results.json"), Value::Array(rows.clone()))?;
        }
        println!("completed {}/256: {filename}", index + 1);
    }
    if rows.len() != 2048 {
        return Err("wrong pilot row count".into());
    }
    Ok(())
}

fn run() -> Result<(), String> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    match args.as_slice() {
        [mode, installed, out] if mode == "self-test" => {
            self_test(Path::new(installed), &PathBuf::from(out))
        }
        [mode, installed, library, membership, out] if mode == "pilot" => pilot(
            Path::new(installed),
            Path::new(library),
            Path::new(membership),
            Path::new(out),
        ),
        _ => Err("expected self-test INSTALL OUT or pilot INSTALL LIBRARY TRAIN_TSV OUT".into()),
    }
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn a_checked_task_must_match_the_selected_goal_identity() {
        assert!(is_expected(Some(Checked::Inputs), None));
        assert!(is_expected(Some(Checked::Goal((2, 4))), Some((2, 4))));
        assert!(!is_expected(Some(Checked::Inputs), Some((2, 4))));
        assert!(!is_expected(Some(Checked::Goal((2, 5))), Some((2, 4))));
        assert!(!is_expected(Some(Checked::Rejected("no".into())), None));
        assert!(!is_expected(None, None));
    }
}
