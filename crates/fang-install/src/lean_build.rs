// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Build lean-v8 with Lake (the checkers and exporters the source map names), then rerun the fixed axiom
//! audits. The specification is tools/build-v8-lean.py; this module follows it step by step, with the same
//! manifest fields, stage names, commands and refusals.
//!
//! The recipe checks every lean-v8 file against tools/v8_szs/lean-sources.json, requires the exact import
//! closures of every executable and of the library, checks the backend packages against
//! tools/v8_szs/backend-pins.json before and after the build, builds offline with Lake (no cache download,
//! no network Git), and audits the fixed theorems of every gate named in lean-v8/audits.json, gate by gate:
//! each must use only propext, Classical.choice and Quot.sound, exactly as that gate recorded.
//!
//! Backend sources: `--backend` copies a pinned local backend (it is never written to); `--packages` uses a
//! package directory produced by fang-fetch-v8-backend. `--root` names the source tree, which the script
//! took from its own location.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

use fang_json::{Object, Value};
use fang_supervisor::Supervisor;
use fang_supervisor::guard::Worker;

use crate::adapt::{self, StageCall};
use crate::common::{
    At, Error, Result, copy2, copyfile, mkdir, mkdir_plain, object, require, resolve, run_captured,
    strings, tail_text, text_of, utc_now, write_bytes, write_manifest,
};
use crate::report::{self, Report};
use crate::scan::{import_like, import_names, py_space, splitlines};

/// Imports from outside lean-v8: the pinned Aeneas backend and these modules of the pinned toolchain's library.
pub const ALLOWED_EXTERNAL: [&str; 9] = [
    "Aeneas",
    "Aeneas.Data.Discriminant",
    "Init.Data.Char.Lemmas",
    "Init.Data.List.Find",
    "Std",
    "Init.Data.Nat.ToString",
    "Init.Data.String.Lemmas.Intercalate",
    "Std.Data.HashSet",
    "Std.Data.String.ToNat",
];
pub const CHECKER: &str = "fang-v8-check";
pub const LIBRARY: &str = "FangV8";
const SCOPE: &str = "Lake build of lean-v8 (the lexer-gate and document-gate modules, Fang.BoundedInput and the \
checker and exporter mains) and the fixed axiom audits of every gate. Compiled execution of fang-v8-check and \
fang-v8-tstp trusts the Lean compiler, runtime and OS; per-input acceptance and export are separate runtime matters.";

/// `imports(path)`: the modules a lean-v8 file imports, refusing any other import syntax.
pub fn imports(path: &Path) -> Result<Vec<String>> {
    let text = fs::read_to_string(path).at(path)?;
    let mut result = Vec::new();
    for line in splitlines(&text) {
        if let Some(names) = import_names(line) {
            result.extend(names);
        } else if import_like(line) {
            let name = path
                .file_name()
                .map(|name| name.to_string_lossy().into_owned())
                .unwrap_or_default();
            return Err(Error::Value(format!("Unreviewed import syntax in {name}")));
        }
    }
    Ok(result)
}

/// `closure(project, modules, roots)`: the modules in dependency order and the external imports.
pub fn closure(
    project: &Path,
    modules: &BTreeMap<String, String>,
    roots: &[String],
) -> Result<(Vec<String>, BTreeSet<String>)> {
    struct Walk<'a> {
        project: &'a Path,
        modules: &'a BTreeMap<String, String>,
        order: Vec<String>,
        visiting: BTreeSet<String>,
        external: BTreeSet<String>,
    }
    fn visit(walk: &mut Walk<'_>, name: &str) -> Result<()> {
        if walk.order.iter().any(|done| done == name) {
            return Ok(());
        }
        if !walk.modules.contains_key(name) {
            walk.external.insert(name.to_string());
            return Ok(());
        }
        require(
            !walk.visiting.contains(name),
            format!("Import cycle at {name}"),
        )?;
        walk.visiting.insert(name.to_string());
        let file = walk
            .project
            .join(format!("{}.lean", name.replace('.', "/")));
        for dependency in imports(&file)? {
            visit(walk, &dependency)?;
        }
        walk.visiting.remove(name);
        walk.order.push(name.to_string());
        Ok(())
    }
    let mut walk = Walk {
        project,
        modules,
        order: Vec::new(),
        visiting: BTreeSet::new(),
        external: BTreeSet::new(),
    };
    for root in roots {
        visit(&mut walk, root)?;
    }
    Ok((walk.order, walk.external))
}

fn str_list(value: Option<&Value>) -> Vec<String> {
    value
        .and_then(Value::as_array)
        .map(|items| {
            items
                .iter()
                .filter_map(|item| item.as_str().map(str::to_string))
                .collect()
        })
        .unwrap_or_default()
}

fn field<'a>(value: &'a Value, key: &str) -> Result<&'a Value> {
    value
        .get(key)
        .ok_or_else(|| Error::Key(crate::common::py_repr(key)))
}

fn entries(value: &Value) -> Result<&Object> {
    value
        .as_object()
        .ok_or_else(|| Error::Value("Expected a JSON object".to_string()))
}

/// `check_closures(project, lean_map)`: every executable closure equals its pin, the library is exactly the
/// modules no executable roots, and every outside import is allowed. Returns the closure sizes.
pub fn check_closures(project: &Path, lean_map: &Value) -> Result<Value> {
    let mut modules = BTreeMap::new();
    for (relative, _) in entries(field(lean_map, "files")?)?.iter() {
        if let Some(stem) = relative.strip_suffix(".lean") {
            modules.insert(stem.replace('/', "."), relative.to_string());
        }
    }
    let mut mains = BTreeSet::new();
    let mut external = BTreeSet::new();
    let mut sizes = Object::new();
    let mut executables: Vec<(&str, &Value)> =
        entries(field(lean_map, "executables")?)?.iter().collect();
    executables.sort_by(|a, b| a.0.cmp(b.0));
    for (name, entry) in executables {
        let root = field(entry, "root")?
            .as_str()
            .unwrap_or_default()
            .to_string();
        let (order, outside) = closure(project, &modules, std::slice::from_ref(&root))?;
        let mut sorted_order = order.clone();
        sorted_order.sort();
        let mut pinned = str_list(entry.get("closure"));
        pinned.sort();
        require(
            sorted_order == pinned,
            format!("{name} import closure differs from the pinned closure"),
        )?;
        mains.insert(root);
        external.extend(outside);
        sizes.set(name, order.len() as u64);
    }
    let (library_order, library_external) =
        closure(project, &modules, &str_list(lean_map.get("library_roots")))?;
    let library: BTreeSet<&String> = library_order.iter().collect();
    let expected: BTreeSet<&String> = modules
        .keys()
        .filter(|module| !mains.contains(*module))
        .collect();
    require(
        library == expected,
        "Library closure is not exactly the pinned module set",
    )?;
    external.extend(library_external);
    let unpinned: Vec<&String> = external
        .iter()
        .filter(|name| !ALLOWED_EXTERNAL.contains(&name.as_str()))
        .collect();
    require(
        unpinned.is_empty(),
        format!(
            "Unpinned external import: {}",
            unpinned
                .iter()
                .map(|name| name.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        ),
    )?;
    sizes.set("library", library_order.len() as u64);
    sizes.set(
        "external",
        strings(&external.into_iter().collect::<Vec<_>>()),
    );
    Ok(Value::Object(sizes))
}

/// `audit_text(roots, names)`. The comment names the Python script so that the file stays byte-equal on the
/// comparison tree.
pub fn audit_text(roots: &[String], names: &[String]) -> String {
    let mut lines = vec![
        "-- Fixed axiom audit generated by tools/build-v8-lean.py from lean-v8/audits.json."
            .to_string(),
    ];
    lines.extend(roots.iter().map(|root| format!("import {root}")));
    lines.push(String::new());
    lines.extend(names.iter().map(|name| format!("#print axioms {name}")));
    lines.join("\n") + "\n"
}

/// The parsed command line.
pub struct Options {
    pub root: PathBuf,
    pub out: PathBuf,
    pub lean_toolchain: PathBuf,
    pub backend: Option<PathBuf>,
    pub packages: Option<PathBuf>,
    pub aeneas_checkout: Option<PathBuf>,
    pub receipts: bool,
    pub memory_mib: u64,
    pub wall_seconds: u64,
}

const PLAIN_TIMEOUT: Duration = Duration::from_secs(1800);

/// Run the build. Returns the exit status: 0 when the manifest's status is `built-and-audited`.
pub fn main(options: &Options, worker: Option<&Worker>) -> Result<i32> {
    require(
        cfg!(target_os = "linux"),
        "Lean builds require Linux or WSL",
    )?;
    require(
        options.backend.is_none() || options.aeneas_checkout.is_some(),
        "--backend needs --aeneas-checkout",
    )?;
    let root = resolve(&options.root)?;
    let out = resolve(&options.out)?;
    mkdir(&out, 0o700, false, false)?;
    let toolchain = resolve(&options.lean_toolchain)?;
    let lake = toolchain.join("bin/lake");
    let report = Report::new(vec![
        ("schema", "fang-v8-lean-build-v1".into()),
        ("status", "running".into()),
        ("started_utc", utc_now().into()),
        ("scope", SCOPE.into()),
    ]);
    let mut supervisor = adapt::supervisor(
        options.wall_seconds as f64,
        options.memory_mib,
        64 << 20,
        64 << 30,
    )?;
    report.set(
        "limits",
        object(vec![
            ("wall_seconds", options.wall_seconds.into()),
            ("sampled_tree_rss_mib", options.memory_mib.into()),
        ]),
    );
    report::on_cancel(worker, &report, out.join("manifest.json"), |_| {});
    report.set(
        "inherited_descriptors",
        supervisor.inherited_descriptors_json(),
    );
    let result = build(
        options,
        &root,
        &out,
        &toolchain,
        &lake,
        &report,
        &mut supervisor,
    );
    if let Err(error) = result {
        report.set("status", "failed");
        report.set("error", error.typed());
    }
    report.set("stages", adapt::records(&supervisor));
    report.set("sampled_peak_rss_kib", supervisor.peak_kib);
    report.set("finished_utc", utc_now());
    let manifest = out.join("manifest.json");
    let mut written = Ok(());
    report::finish(worker, || {
        written = write_manifest(&manifest, &report.value())
    });
    written?;
    let printed = object(vec![
        ("status", report.get("status").unwrap_or(Value::Null)),
        (
            "executable_sha256",
            report.get("executable_sha256").unwrap_or(Value::Null),
        ),
        ("error", report.get("error").unwrap_or(Value::Null)),
    ]);
    println!("{}", crate::common::compact(&printed));
    Ok(i32::from(
        report
            .get("status")
            .and_then(|status| status.as_str().map(str::to_string))
            .as_deref()
            != Some("built-and-audited"),
    ))
}

/// The commands outside the supervisor (`plain`), recorded in `setup_commands`.
struct Plain<'a> {
    out: &'a Path,
    commands: Vec<Value>,
}

impl Plain<'_> {
    fn run(
        &mut self,
        supervisor: &Supervisor,
        command: &[String],
        cwd: Option<&Path>,
    ) -> Result<String> {
        adapt::check_stage(supervisor, "adapter")?;
        let environment: BTreeMap<String, String> = [
            ("PATH", "/usr/bin:/bin"),
            ("LANG", "C.UTF-8"),
            ("LC_ALL", "C.UTF-8"),
            ("GIT_ALLOW_PROTOCOL", "file"),
        ]
        .into_iter()
        .map(|(key, value)| (key.to_string(), value.to_string()))
        .chain(std::iter::once(("HOME".to_string(), text_of(self.out))))
        .collect();
        let done = run_captured(command, cwd, Some(&environment), PLAIN_TIMEOUT)?;
        self.commands.push(object(vec![
            ("command", strings(command)),
            ("exit_code", i64::from(done.returncode).into()),
            ("stderr", tail_text(&done.stderr, 2000).into()),
        ]));
        require(
            done.returncode == 0,
            format!("Setup command failed: {}", command.join(" ")),
        )?;
        Ok(String::from_utf8_lossy(&done.stdout).into_owned())
    }
}

fn path_arg(path: &Path) -> String {
    text_of(path)
}

#[allow(clippy::too_many_arguments)]
fn build(
    options: &Options,
    root: &Path,
    out: &Path,
    toolchain: &Path,
    lake: &Path,
    report: &Report,
    supervisor: &mut Supervisor,
) -> Result<()> {
    let lean_map = adapt::load_map(root, adapt::LEAN_MAP, adapt::LEAN_SCHEMA, supervisor)?;
    let listed = adapt::lean_files(root, supervisor)?;
    report.set(
        "source_map_sha256",
        adapt::digest(&root.join(adapt::LEAN_MAP))?,
    );
    report.set("sources_checked", listed.len() as u64);
    if options.receipts {
        report.set(
            "receipt_entries_checked",
            adapt::check_lean_receipts(root, supervisor)?,
        );
    }
    let project_source = root.join(field(&lean_map, "project")?.as_str().unwrap_or_default());
    let executables = entries(field(&lean_map, "executables")?)?.clone();
    let checker_name = primary_checker_name(&executables)?;
    report.set("closures", check_closures(&project_source, &lean_map)?);
    let pins = adapt::load_pins(root)?;
    report.set(
        "backend_pins_sha256",
        adapt::digest(&root.join(adapt::PINS))?,
    );
    let project = out.join("project");
    let files = entries(field(&lean_map, "files")?)?.clone();
    for (relative, entry) in files.iter() {
        let target = project.join(relative);
        if let Some(parent) = target.parent() {
            mkdir(parent, 0o777, true, true)?;
        }
        copyfile(&project_source.join(relative), &target)?;
        require(
            Some(adapt::digest(&target)?.as_str()) == entry.get("sha256").and_then(Value::as_str),
            format!("Copied project file differs: {relative}"),
        )?;
    }
    let packages = project.join(".lake/packages");
    mkdir(&packages, 0o777, true, false)?;
    let mut plain = Plain {
        out,
        commands: Vec::new(),
    };
    let pinned = entries(field(&pins, "packages")?)?.clone();
    let mut pinned_names: Vec<&str> = pinned.keys().collect();
    pinned_names.sort();
    if let Some(backend) = &options.backend {
        let backend = resolve(backend)?;
        let checkout = options.aeneas_checkout.as_ref().expect("checked above");
        report.set(
            "backend",
            object(vec![
                ("mode", "local-copy".into()),
                ("path", text_of(&backend).into()),
                ("aeneas_checkout", text_of(checkout).into()),
            ]),
        );
        let aeneas = packages.join("aeneas");
        let aeneas_rev = field(&pinned_value(&pinned, "aeneas")?, "rev")?
            .as_str()
            .unwrap_or_default()
            .to_string();
        let url = field(field(&lean_map, "aeneas")?, "url")?
            .as_str()
            .unwrap_or_default()
            .to_string();
        let aeneas_text = path_arg(&aeneas);
        plain.run(
            supervisor,
            &[
                "git".into(),
                "clone".into(),
                "-q".into(),
                "--no-checkout".into(),
                path_arg(&resolve(checkout)?),
                aeneas_text.clone(),
            ],
            None,
        )?;
        plain.run(
            supervisor,
            &[
                "git".into(),
                "-C".into(),
                aeneas_text.clone(),
                "-c".into(),
                "advice.detachedHead=false".into(),
                "checkout".into(),
                "-q".into(),
                aeneas_rev,
            ],
            None,
        )?;
        plain.run(
            supervisor,
            &[
                "git".into(),
                "-C".into(),
                aeneas_text,
                "remote".into(),
                "set-url".into(),
                "origin".into(),
                url,
            ],
            None,
        )?;
        let lake_dir = aeneas.join(adapt::AENEAS_SUBDIR).join(".lake");
        mkdir(&lake_dir, 0o777, true, false)?;
        plain.run(
            supervisor,
            &[
                "cp".into(),
                "-a".into(),
                path_arg(&backend.join(".lake/build")),
                path_arg(&lake_dir.join("build")),
            ],
            None,
        )?;
        for name in &pinned_names {
            if *name != "aeneas" {
                plain.run(
                    supervisor,
                    &[
                        "cp".into(),
                        "-a".into(),
                        path_arg(&backend.join(".lake/packages").join(name)),
                        path_arg(&packages.join(name)),
                    ],
                    None,
                )?;
            }
        }
    } else {
        let fetched = resolve(
            options
                .packages
                .as_ref()
                .expect("one backend source is required"),
        )?;
        report.set(
            "backend",
            object(vec![
                ("mode", "fetched".into()),
                ("path", text_of(&fetched).into()),
            ]),
        );
        for name in &pinned_names {
            plain.run(
                supervisor,
                &[
                    "cp".into(),
                    "-a".into(),
                    path_arg(&fetched.join(name)),
                    path_arg(&packages.join(name)),
                ],
                None,
            )?;
        }
    }
    for name in &pinned_names {
        let rev = plain.run(
            supervisor,
            &[
                "git".into(),
                "-C".into(),
                path_arg(&packages.join(name)),
                "rev-parse".into(),
                "HEAD".into(),
            ],
            None,
        )?;
        let expected = pinned
            .get(name)
            .and_then(|pin| pin.get("rev"))
            .and_then(Value::as_str)
            .unwrap_or_default();
        require(
            rev.trim_matches(py_space) == expected,
            format!("Package {name} is not at its pinned revision"),
        )?;
    }
    report.set("setup_commands", Value::Array(plain.commands));
    let fetch = options.packages.is_some();
    report.set("pin_check", if fetch { "fetch" } else { "exact" });
    let (before_result, before_rows, problems) =
        adapt::check_packages(&packages, &pins, Some(supervisor), false, None, fetch)?;
    report.set("packages_before", before_result);
    require(
        problems.is_empty(),
        format!(
            "Backend packages differ from their pins: {}",
            problems.join(", ")
        ),
    )?;
    let gitbin = out.join("gitbin");
    mkdir_plain(&gitbin)?;
    std::os::unix::fs::symlink("/usr/bin/git", gitbin.join("git")).at(&gitbin.join("git"))?;
    mkdir_plain(&out.join("home"))?;
    mkdir_plain(&out.join("tmp"))?;
    let environment: BTreeMap<String, String> = [
        (
            "PATH".to_string(),
            format!("{}:{}", text_of(&toolchain.join("bin")), text_of(&gitbin)),
        ),
        ("HOME".to_string(), text_of(&out.join("home"))),
        ("TMPDIR".to_string(), text_of(&out.join("tmp"))),
        ("LEAN_NUM_THREADS".to_string(), "1".to_string()),
        ("LANG".to_string(), "C.UTF-8".to_string()),
        ("LC_ALL".to_string(), "C.UTF-8".to_string()),
    ]
    .into_iter()
    .collect();
    report.set(
        "environment",
        Value::Object(
            environment
                .iter()
                .map(|(key, value)| (key.clone(), Value::from(value.as_str())))
                .collect(),
        ),
    );
    let lean_sha256 = adapt::digest(&toolchain.join("bin/lean"))?;
    let lake_sha256 = adapt::digest(lake)?;
    report.set(
        "toolchain",
        object(vec![
            ("path", text_of(toolchain).into()),
            ("lean_sha256", lean_sha256.clone().into()),
            ("lake_sha256", lake_sha256.clone().into()),
        ]),
    );
    let stages = out.join("stages");
    mkdir_plain(&stages)?;
    let stage_environment = adapt::environment(&environment)?;
    let run = |supervisor: &mut Supervisor,
               label: &str,
               command: Vec<String>|
     -> Result<(String, String)> {
        let mut wrapped = vec![
            "/usr/bin/env".to_string(),
            "GIT_ALLOW_PROTOCOL=file".to_string(),
        ];
        wrapped.extend(command);
        let result = adapt::run(
            supervisor,
            StageCall {
                name: label,
                command: wrapped,
                directory: stages.join(label),
                run_root: &stages,
                environment: Some(&stage_environment),
                stdout_limit: None,
                cwd: None,
            },
        );
        report.set("stages", adapt::records(supervisor));
        let output = result?;
        require(adapt::completed(&output), format!("Stage failed: {label}"))?;
        Ok((
            String::from_utf8_lossy(&output.stdout).into_owned(),
            String::from_utf8_lossy(&output.stderr).into_owned(),
        ))
    };
    let mut names: Vec<String> = executables.keys().map(str::to_string).collect();
    names.sort();
    let mut lake_build = vec![
        path_arg(lake),
        "-d".into(),
        path_arg(&project),
        "--no-cache".into(),
        "build".into(),
        LIBRARY.into(),
    ];
    lake_build.extend(names.iter().cloned());
    run(supervisor, "lake-build", lake_build)?;
    for (relative, entry) in files.iter() {
        require(
            Some(adapt::digest(&project.join(relative))?.as_str())
                == entry.get("sha256").and_then(Value::as_str),
            format!("Project source changed during the build: {relative}"),
        )?;
    }
    let (after_result, _, problems) = adapt::check_packages(
        &packages,
        &pins,
        Some(supervisor),
        true,
        Some(&before_rows),
        false,
    )?;
    report.set("packages_after", after_result);
    require(
        problems.is_empty(),
        format!(
            "Build changed pinned backend content: {}",
            problems.join(", ")
        ),
    )?;
    let audits = crate::common::read_json(&project.join("audits.json"))?;
    require(
        audits.get("schema").and_then(Value::as_str) == Some("fang-v8-audits-v2"),
        "Unexpected audit list",
    )?;
    let audit_names = entries(field(&audits, "names")?)?.clone();
    let recorded: BTreeMap<String, Vec<String>> = audit_names
        .iter()
        .map(|(name, row)| (name.to_string(), str_list(row.get("axioms"))))
        .collect();
    let audit_dir = out.join("audit");
    mkdir_plain(&audit_dir)?;
    let mut reports: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut gates: Vec<(String, Vec<String>)> = entries(field(&audits, "roots")?)?
        .iter()
        .map(|(gate, roots)| (gate.to_string(), str_list(Some(roots))))
        .collect();
    gates.sort_by(|a, b| a.0.cmp(&b.0));
    for (index, (gate, roots)) in gates.iter().enumerate() {
        let mut gate_names: Vec<String> = audit_names
            .iter()
            .filter(|(_, row)| row.get("gate").and_then(Value::as_str) == Some(gate.as_str()))
            .map(|(name, _)| name.to_string())
            .collect();
        gate_names.sort();
        let audit_file = audit_dir.join(format!("Audit{index}.lean"));
        write_bytes(&audit_file, audit_text(roots, &gate_names).as_bytes())?;
        let (stdout, stderr) = run(
            supervisor,
            &format!("axiom-audit-{index}"),
            vec![
                path_arg(lake),
                "-d".into(),
                path_arg(&project),
                "env".into(),
                "lean".into(),
                path_arg(&audit_file),
            ],
        )?;
        require(stderr.is_empty(), "Axiom audit wrote diagnostics")?;
        reports.extend(adapt::parse_build_audit(&stdout, &gate_names, &recorded)?);
    }
    let mut all_names: Vec<&str> = audit_names.keys().collect();
    all_names.sort();
    require(
        reports.keys().map(String::as_str).collect::<Vec<_>>() == all_names,
        "Audit reports differ from the fixed audit list",
    )?;
    let axioms: BTreeSet<&String> = reports.values().flatten().collect();
    report.set(
        "axiom_audits",
        object(vec![
            ("count", (reports.len() as u64).into()),
            (
                "gates",
                strings(
                    &gates
                        .iter()
                        .map(|(gate, _)| gate.clone())
                        .collect::<Vec<_>>(),
                ),
            ),
            ("compared_with_gate_record", true.into()),
            (
                "gate_record_checked_against_receipts",
                options.receipts.into(),
            ),
            (
                "axioms",
                strings(&axioms.into_iter().cloned().collect::<Vec<_>>()),
            ),
        ]),
    );
    let bin_dir = out.join("bin");
    mkdir_plain(&bin_dir)?;
    let mut built = Object::new();
    let usage_environment = adapt::environment(
        &[
            ("PATH", "/usr/bin:/bin"),
            ("LANG", "C.UTF-8"),
            ("LC_ALL", "C.UTF-8"),
        ]
        .into_iter()
        .map(|(key, value)| (key.to_string(), value.to_string()))
        .collect(),
    )?;
    for name in &names {
        let binary = project.join(".lake/build/bin").join(name);
        let installed = bin_dir.join(name);
        copy2(&binary, &installed)?;
        require(
            adapt::digest(&installed)? == adapt::digest(&binary)?,
            format!("Copied executable differs: {name}"),
        )?;
        let label = format!("usage-{name}");
        let usage = adapt::run(
            supervisor,
            StageCall {
                name: &label,
                command: vec![path_arg(&installed)],
                directory: stages.join(&label),
                run_root: &stages,
                environment: Some(&usage_environment),
                stdout_limit: None,
                cwd: None,
            },
        );
        report.set("stages", adapt::records(supervisor));
        let usage = usage?;
        let expected = format!(
            "{}\n",
            executables
                .get(name)
                .and_then(|entry| entry.get("usage"))
                .and_then(Value::as_str)
                .unwrap_or_default()
        );
        require(
            adapt::exit_code(&usage) == Some(64)
                && usage.stdout.is_empty()
                && usage.stderr == expected.as_bytes(),
            format!("Usage contract differs: {name}"),
        )?;
        let bytes = fs::metadata(&installed).at(&installed)?.len();
        built.set(
            name.as_str(),
            object(vec![
                ("path", text_of(&installed).into()),
                ("sha256", adapt::digest(&installed)?.into()),
                ("bytes", bytes.into()),
            ]),
        );
    }
    require(
        adapt::digest(&toolchain.join("bin/lean"))? == lean_sha256
            && adapt::digest(lake)? == lake_sha256,
        "Lean toolchain changed during the build",
    )?;
    let checker = checker_from_build(&built, checker_name)?;
    report.set("status", "built-and-audited");
    report.set("executables", Value::Object(built));
    report.set(
        "executable",
        checker.get("path").cloned().unwrap_or(Value::Null),
    );
    report.set(
        "executable_sha256",
        checker.get("sha256").cloned().unwrap_or(Value::Null),
    );
    report.set(
        "executable_bytes",
        checker.get("bytes").cloned().unwrap_or(Value::Null),
    );
    Ok(())
}

fn primary_checker_name(executables: &Object) -> Result<&str> {
    let mut primary = None;
    for (name, entry) in executables.iter() {
        let installed_as = entries(entry)?
            .get("installed_as")
            .and_then(Value::as_str)
            .ok_or_else(|| {
                Error::Value(format!("Invalid installed_as for Lean executable: {name}"))
            })?;
        if installed_as == CHECKER {
            require(
                primary.is_none(),
                "Multiple Lean executables install as fang-v8-check",
            )?;
            primary = Some(name);
        }
    }
    primary.ok_or_else(|| Error::Value("No Lean executable installs as fang-v8-check".to_string()))
}

fn checker_from_build(built: &Object, name: &str) -> Result<Value> {
    built
        .get(name)
        .cloned()
        .ok_or_else(|| Error::Key(format!("'{name}'")))
}

fn pinned_value(pinned: &Object, name: &str) -> Result<Value> {
    pinned
        .get(name)
        .cloned()
        .ok_or_else(|| Error::Key(format!("'{name}'")))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn splitlines_follows_python() {
        assert_eq!(
            splitlines("a\nb\r\nc\rd\x0be\u{2028}f"),
            vec!["a", "b", "c", "d", "e", "f"]
        );
        assert_eq!(splitlines("a\n"), vec!["a"]);
        assert_eq!(splitlines("a\n\nb"), vec!["a", "", "b"]);
        assert!(splitlines("").is_empty());
    }

    #[test]
    fn import_lines_follow_the_two_patterns() {
        assert_eq!(
            import_names("import A.B C"),
            Some(vec!["A.B".to_string(), "C".to_string()])
        );
        assert_eq!(import_names("public import A"), Some(vec!["A".to_string()]));
        assert_eq!(import_names("import  A"), Some(vec!["A".to_string()]));
        assert_eq!(import_names("import A -- note"), None);
        assert_eq!(import_names("public  import A"), None);
        assert!(import_like("  import A -- note"));
        assert!(import_like("public\timport A"));
        assert!(import_like("import"));
        assert!(!import_like("imports"));
        assert!(!import_like("-- import A"));
        assert!(!import_like("publicimport A"));
    }

    #[test]
    fn audit_text_matches_the_script() {
        let text = audit_text(
            &["A".to_string(), "B".to_string()],
            &["x".to_string(), "y".to_string()],
        );
        assert_eq!(
            text,
            "-- Fixed axiom audit generated by tools/build-v8-lean.py from lean-v8/audits.json.\nimport A\nimport B\n\n\
#print axioms x\n#print axioms y\n"
        );
    }

    #[test]
    fn closure_orders_dependencies_and_collects_outside_imports() {
        let directory =
            std::env::temp_dir().join(format!("fang-install-closure-{}", std::process::id()));
        fs::create_dir_all(directory.join("P")).unwrap();
        fs::write(directory.join("P/A.lean"), "import P.B\nimport Std\n").unwrap();
        fs::write(
            directory.join("P/B.lean"),
            "public import Init.Data.List.Find\n",
        )
        .unwrap();
        let modules: BTreeMap<String, String> = [("P.A", "P/A.lean"), ("P.B", "P/B.lean")]
            .into_iter()
            .map(|(a, b)| (a.to_string(), b.to_string()))
            .collect();
        let (order, external) = closure(&directory, &modules, &["P.A".to_string()]).unwrap();
        assert_eq!(order, vec!["P.B".to_string(), "P.A".to_string()]);
        assert_eq!(
            external.into_iter().collect::<Vec<_>>(),
            vec!["Init.Data.List.Find".to_string(), "Std".to_string()]
        );
        fs::write(directory.join("P/B.lean"), "import P.A\n").unwrap();
        let error = closure(&directory, &modules, &["P.A".to_string()]).unwrap_err();
        assert_eq!(error.typed(), "ValueError: Import cycle at P.A");
        fs::remove_dir_all(&directory).unwrap();
    }

    #[test]
    fn complete_closures_allow_pinned_string_parser_and_reject_other_external_imports() {
        let directory = std::env::temp_dir().join(format!(
            "fang-install-closure-stdlib-{}",
            std::process::id()
        ));
        fs::create_dir(&directory).unwrap();
        fs::write(directory.join("Library.lean"), "-- Synthetic library.\n").unwrap();
        let main = directory.join("ModelExportComplete.lean");
        fs::write(&main, "import Library\nimport Std.Data.String.ToNat\n").unwrap();
        let lean_map = object(vec![
            (
                "files",
                object(vec![
                    ("Library.lean", Value::Null),
                    ("ModelExportComplete.lean", Value::Null),
                ]),
            ),
            (
                "executables",
                object(vec![(
                    "model-export",
                    object(vec![
                        ("root", "ModelExportComplete".into()),
                        (
                            "closure",
                            strings(&["Library".to_string(), "ModelExportComplete".to_string()]),
                        ),
                    ]),
                )]),
            ),
            ("library_roots", strings(&["Library".to_string()])),
        ]);
        let accepted = check_closures(&directory, &lean_map).unwrap();
        assert_eq!(
            accepted.get("model-export").and_then(Value::as_u64),
            Some(2)
        );
        assert_eq!(accepted.get("library").and_then(Value::as_u64), Some(1));
        assert_eq!(
            accepted.get("external"),
            Some(&strings(&["Std.Data.String.ToNat".to_string()]))
        );
        fs::write(&main, "import Library\nimport Unreviewed.External\n").unwrap();
        let error = check_closures(&directory, &lean_map).unwrap_err();
        assert_eq!(
            error.typed(),
            "ValueError: Unpinned external import: Unreviewed.External"
        );
        fs::remove_dir_all(&directory).unwrap();
    }

    #[test]
    fn primary_checker_uses_unique_installed_alias_and_requires_its_build() {
        let mut executables = Object::new();
        let mut built = Object::new();
        executables.set(CHECKER, object(vec![("installed_as", CHECKER.into())]));
        built.set(CHECKER, "legacy-checker-record");
        assert_eq!(primary_checker_name(&executables).unwrap(), CHECKER);
        assert_eq!(
            checker_from_build(&built, primary_checker_name(&executables).unwrap()).unwrap(),
            Value::from("legacy-checker-record")
        );

        executables = Object::new();
        executables.set(
            "fang-expanded-native-named",
            object(vec![("installed_as", CHECKER.into())]),
        );
        executables.set(
            "unrelated",
            object(vec![("installed_as", "other-binary".into())]),
        );
        built.set("fang-expanded-native-named", "final-checker-record");
        let name = primary_checker_name(&executables).unwrap();
        assert_eq!(name, "fang-expanded-native-named");
        assert_eq!(
            checker_from_build(&built, name).unwrap(),
            Value::from("final-checker-record")
        );
        assert!(checker_from_build(&Object::new(), name).is_err());
        assert!(primary_checker_name(&Object::new()).is_err());

        executables.set(CHECKER, object(vec![("installed_as", CHECKER.into())]));
        assert!(primary_checker_name(&executables).is_err());
        let mut missing_alias = Object::new();
        missing_alias.set(CHECKER, object(vec![]));
        assert!(primary_checker_name(&missing_alias).is_err());
        for alias in [Value::Null, true.into(), 7u64.into()] {
            let mut malformed = Object::new();
            malformed.set(CHECKER, object(vec![("installed_as", alias)]));
            assert!(primary_checker_name(&malformed).is_err());
        }
        let mut unrelated = Object::new();
        unrelated.set(
            "other",
            object(vec![("installed_as", "other-binary".into())]),
        );
        assert!(primary_checker_name(&unrelated).is_err());
    }
}
