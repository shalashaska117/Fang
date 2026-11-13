// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Fetch the pinned Aeneas backend for a clean lean-v8 build. Uses the network. The specification is
//! tools/fetch-v8-backend.py.
//!
//! Clones Aeneas and every Lake package at the exact revisions in lean-v8/lake-manifest.json, downloads the
//! mathlib prebuilt cache, obtains the Aeneas build (release archive or local build of Aeneas only), and checks
//! every package against tools/v8_szs/backend-pins.json. A missing or different mathlib cache is an install
//! error: mathlib is never built from source as a fallback. Pass the resulting package directory to
//! fang-build-v8-lean --packages, which checks the pins again before and after the lean-v8 build. Both use the
//! fetch digest of each pin, which leaves out only Lake build records (.hash, .trace, .setup.json, .rsp); a
//! differing file of any other kind is an error that names the package and the file kinds.
//!
//! Like the script, the fetch runs without a supervisor. `--root` names the source tree, which the script took
//! from its own location.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::time::Duration;

use fang_json::{Object, Value};

use crate::adapt;
use crate::common::{
    Error, Result, compact, copyfile, mkdir, mkdir_plain, object, read_json, resolve, run_captured,
    strings, tail_text, text_of, utc_now, write_manifest,
};

pub struct Options {
    pub root: PathBuf,
    pub work: PathBuf,
    pub lean_toolchain: PathBuf,
}

fn cache_error(rev: &str) -> String {
    format!(
        "The mathlib prebuilt cache for revision {rev} could not be downloaded. Installation stopped; \
             mathlib is not built from source."
    )
}

/// `differences(result, problems)`.
fn differences(result: &Value, problems: &[String]) -> String {
    problems.iter().map(|name| {
        let kinds: Vec<&str> = result.get(name).and_then(|row| row.get("differing_kinds")).and_then(Value::as_array)
            .map(|kinds| kinds.iter().filter_map(Value::as_str).collect()).unwrap_or_default();
        let kinds = if kinds.is_empty() { "(file count)".to_string() } else { kinds.join(", ") };
        format!("Installation stopped: {name} differs from the pinned inventory in file kinds: {kinds}.")
    }).collect::<Vec<_>>().join(" ")
}

struct Runner {
    environment: BTreeMap<String, String>,
    commands: Vec<Value>,
}

impl Runner {
    /// `run(command, cwd, environment, record, timeout)`: records the command and returns whether it exited 0.
    fn run(&mut self, command: Vec<String>, cwd: &Path, timeout: u64) -> Result<bool> {
        let done = run_captured(
            &command,
            Some(cwd),
            Some(&self.environment),
            Duration::from_secs(timeout),
        )?;
        self.commands.push(object(vec![
            ("command", strings(&command)),
            ("exit_code", i64::from(done.returncode).into()),
            ("stdout_tail", tail_text(&done.stdout, 2000).into()),
            ("stderr_tail", tail_text(&done.stderr, 2000).into()),
        ]));
        Ok(done.returncode == 0)
    }
}

fn key<'a>(value: &'a Value, name: &str) -> Result<&'a Value> {
    value
        .get(name)
        .ok_or_else(|| Error::Key(format!("'{name}'")))
}

fn text(value: &Value, name: &str) -> Result<String> {
    Ok(key(value, name)?.as_str().unwrap_or_default().to_string())
}

pub fn main(options: &Options) -> Result<i32> {
    require_linux()?;
    let root = resolve(&options.root)?;
    let work = resolve(&options.work)?;
    mkdir(&work, 0o777, true, false)?;
    let toolchain = resolve(&options.lean_toolchain)?;
    let lake = text_of(&toolchain.join("bin/lake"));
    let environment: BTreeMap<String, String> = [
        (
            "PATH".to_string(),
            format!("{}:/usr/bin:/bin", text_of(&toolchain.join("bin"))),
        ),
        ("HOME".to_string(), text_of(&work.join("home"))),
        ("LANG".to_string(), "C.UTF-8".to_string()),
        ("LC_ALL".to_string(), "C.UTF-8".to_string()),
        ("LEAN_NUM_THREADS".to_string(), "1".to_string()),
    ]
    .into_iter()
    .collect();
    mkdir_plain(&work.join("home"))?;
    let mut report: Object = [
        ("schema", Value::from("fang-v8-backend-fetch-v1")),
        ("status", "running".into()),
        ("started_utc", utc_now().into()),
    ]
    .into_iter()
    .collect();
    let mut runner = Runner {
        environment,
        commands: Vec::new(),
    };
    let result = fetch(&root, &work, &lake, &mut runner, &mut report);
    report.set(
        "commands",
        Value::Array(std::mem::take(&mut runner.commands)),
    );
    if let Err(error) = result {
        report.set("status", "failed");
        report.set("error", error.message());
    }
    report.set("finished_utc", utc_now());
    let report = Value::Object(report);
    write_manifest(&work.join("fetch-manifest.json"), &report)?;
    let printed = object(vec![
        (
            "status",
            report.get("status").cloned().unwrap_or(Value::Null),
        ),
        (
            "packages_directory",
            report
                .get("packages_directory")
                .cloned()
                .unwrap_or(Value::Null),
        ),
        ("error", report.get("error").cloned().unwrap_or(Value::Null)),
    ]);
    println!("{}", compact(&printed));
    Ok(i32::from(
        report.get("status").and_then(Value::as_str) != Some("fetched-and-checked"),
    ))
}

fn require_linux() -> Result<()> {
    if cfg!(target_os = "linux") {
        Ok(())
    } else {
        Err(Error::Value("Run on Linux or WSL".to_string()))
    }
}

fn fetch(
    root: &Path,
    work: &Path,
    lake: &str,
    runner: &mut Runner,
    report: &mut Object,
) -> Result<()> {
    let manifest = read_json(&root.join("lean-v8/lake-manifest.json"))?;
    let pins = adapt::load_pins(root)?;
    let project = work.join("project");
    mkdir_plain(&project)?;
    for name in ["lakefile.toml", "lean-toolchain", "lake-manifest.json"] {
        copyfile(&root.join("lean-v8").join(name), &project.join(name))?;
    }
    let packages = project.join(".lake/packages");
    mkdir(&packages, 0o777, true, false)?;
    let mut revisions: BTreeMap<String, Value> = BTreeMap::new();
    for entry in key(&manifest, "packages")?
        .as_array()
        .cloned()
        .unwrap_or_default()
    {
        revisions.insert(text(&entry, "name")?, entry);
    }
    let pinned = key(&pins, "packages")?
        .as_object()
        .cloned()
        .unwrap_or_default();
    if revisions.keys().map(String::as_str).collect::<Vec<_>>() != {
        let mut names: Vec<&str> = pinned.keys().collect();
        names.sort();
        names.dedup();
        names
    } {
        return Err(Error::Value(
            "lake-manifest.json and backend-pins.json name different packages".to_string(),
        ));
    }
    for (name, entry) in &revisions {
        let rev = text(entry, "rev")?;
        if Some(rev.as_str())
            != pinned
                .get(name)
                .and_then(|pin| pin.get("rev"))
                .and_then(Value::as_str)
        {
            return Err(Error::Value(format!(
                "Revision of {name} differs between the manifest and the pins"
            )));
        }
        let target = text_of(&packages.join(name));
        let fetched = runner.run(
            vec![
                "git".into(),
                "clone".into(),
                "-q".into(),
                "--no-checkout".into(),
                text(entry, "url")?,
                target.clone(),
            ],
            work,
            3600,
        )? && runner.run(
            vec![
                "git".into(),
                "-C".into(),
                target.clone(),
                "-c".into(),
                "advice.detachedHead=false".into(),
                "checkout".into(),
                "-q".into(),
                rev.clone(),
            ],
            work,
            600,
        )?;
        if !fetched {
            return Err(Error::Value(format!("Could not fetch {name} at {rev}")));
        }
        let head = run_captured(
            &[
                "git".into(),
                "-C".into(),
                target,
                "rev-parse".into(),
                "HEAD".into(),
            ],
            None,
            Some(&runner.environment),
            Duration::MAX,
        )?;
        if String::from_utf8_lossy(&head.stdout).trim_matches(crate::scan::py_space) != rev {
            return Err(Error::Value(format!(
                "{name} is not at its pinned revision"
            )));
        }
    }
    if !runner.run(
        vec![
            lake.to_string(),
            "-d".into(),
            text_of(&project),
            "exe".into(),
            "cache".into(),
            "get".into(),
        ],
        &project,
        7200,
    )? {
        let rev = revisions
            .get("mathlib")
            .map(|entry| text(entry, "rev"))
            .transpose()?
            .unwrap_or_default();
        return Err(Error::Value(cache_error(&rev)));
    }
    let mathlib_pin = pinned
        .get("mathlib")
        .cloned()
        .ok_or_else(|| Error::Key("'mathlib'".to_string()))?;
    let only_mathlib = object(vec![("packages", object(vec![("mathlib", mathlib_pin)]))]);
    let (result, _, problems) =
        adapt::check_packages(&packages, &only_mathlib, None, false, None, true)?;
    report.set(
        "mathlib",
        result.get("mathlib").cloned().unwrap_or(Value::Null),
    );
    if !problems.is_empty() {
        return Err(Error::Value(
            differences(&result, &problems)
                + " The mathlib cache is never replaced by a source build.",
        ));
    }
    if !runner.run(
        vec![
            lake.to_string(),
            "-d".into(),
            text_of(&project),
            "build".into(),
            "Aeneas".into(),
            "AeneasMeta".into(),
        ],
        &project,
        14400,
    )? {
        return Err(Error::Value(
            "Aeneas could not be fetched or built at the pinned revision".to_string(),
        ));
    }
    let (result, _, problems) = adapt::check_packages(&packages, &pins, None, false, None, true)?;
    report.set("packages", result.clone());
    if !problems.is_empty() {
        return Err(Error::Value(differences(&result, &problems)));
    }
    report.set("status", "fetched-and-checked");
    report.set("packages_directory", text_of(&packages));
    Ok(())
}
