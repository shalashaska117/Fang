// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Inventory and generation children. They emit data only; the parent owns every verdict.
use std::ffi::OsString;
use std::fs;
use std::path::Path;
use std::process::ExitCode;

use fang_json::{Object, ParseLimits, Value};
use fang_supervisor::{Fault, Stage, Supervisor};

use crate::{generator, trees, util};

pub const INVENTORY: &str = "--internal-inventory";
pub const GENERATE: &str = "--internal-generate";

pub fn is_internal(flag: &std::ffi::OsStr) -> bool {
    flag == INVENTORY || flag == GENERATE
}

fn read(path: &Path, cap: u64) -> Result<Vec<u8>, String> {
    fang_supervisor::read_regular(path, cap, &mut || Ok(())).map_err(|e| e.python_str())
}

fn inventory(path: &Path, expected: &str) -> Result<Value, String> {
    let data = read(path, 256 << 20)?;
    let record = fang_json::parse(
        &data,
        &ParseLimits {
            max_bytes: 64 << 20,
            max_depth: 64,
        },
    )
    .map_err(|e| e.python_message(&data))?;
    let canonical = util::manifest_bytes(&record)?;
    if fang_hash::sha256_hex(&canonical) != expected {
        return Err("Tree record differs from the installation record".into());
    }
    let record = record.as_object().ok_or("Tree record is not an object")?;
    let (unchanged, totals, differences) = trees::verify(record)?;
    let mut result = Object::new();
    result.set("unchanged", unchanged);
    result.set("totals", totals);
    result.set("differences", differences);
    Ok(Value::Object(result))
}

fn generate(paths: &[OsString]) -> Result<Value, String> {
    let input = read(Path::new(&paths[0]), 4096)?;
    let certificate = read(Path::new(&paths[1]), 65536)?;
    let witness = read(Path::new(&paths[2]), 16 << 20)?;
    let source = Path::new(&paths[3]);
    let mut result = Object::new();
    if let Some(recipe) = generator::selected_recipe(&witness) {
        result.set("selected_generator", recipe);
    }
    match generator::generate(&input, &certificate, &witness) {
        Err(refusal) => {
            result.set("status", "refused");
            result.set("class", refusal.class());
            result.set("message", refusal.message());
        }
        Ok(generated) => {
            let mut modules = Vec::new();
            for (name, data) in generated.modules {
                if !module_name(&name) {
                    return Err("Invalid generated module name".into());
                }
                let path = source.join(format!("{name}.lean"));
                use std::io::Write;
                fs::OpenOptions::new()
                    .create_new(true)
                    .write(true)
                    .open(&path)
                    .and_then(|mut file| file.write_all(&data))
                    .map_err(|e| e.to_string())?;
                let mut module = Object::new();
                module.set("name", name);
                module.set("sha256", fang_hash::sha256_hex(&data));
                modules.push(Value::Object(module));
            }
            result.set("status", "generated");
            result.set("recipe", generated.recipe);
            result.set("modules", Value::Array(modules));
            result.set(
                "phases",
                Value::Array(
                    generated
                        .phases
                        .into_iter()
                        .map(|phase| Value::Array(phase.into_iter().map(Value::from).collect()))
                        .collect(),
                ),
            );
        }
    }
    Ok(Value::Object(result))
}

pub fn module_name(name: &str) -> bool {
    !name.is_empty() && name.bytes().all(|c| c.is_ascii_alphanumeric() || c == b'_')
}

/// An internal child has no guard, installation mutation, or positive-result output.
pub fn run(args: &[OsString]) -> ExitCode {
    let result = match args {
        [_, flag, record, expected] if flag == INVENTORY => expected
            .to_str()
            .ok_or_else(|| "Invalid tree record digest".to_owned())
            .and_then(|expected| inventory(Path::new(record), expected)),
        [_, flag, paths @ ..] if flag == GENERATE && paths.len() == 4 => generate(paths),
        _ => Err("Invalid internal kernel stage arguments".into()),
    };
    match result.and_then(|value| util::sorted_line(&value)) {
        Ok(text) => {
            println!("{text}");
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("{error}");
            ExitCode::from(6)
        }
    }
}

/// Run an internal stage under the parent's remaining wall, RSS and artifact limits.
pub fn supervised(
    supervisor: &mut Supervisor,
    command: &[OsString],
    name: &str,
    directory: &Path,
    root: &Path,
) -> Result<Value, Fault> {
    let output = supervisor.run(&Stage {
        name,
        command,
        directory,
        run_root: root,
        environment: None,
        stdin: None,
        stdout_limit: None,
        cwd: None,
    })?;
    if output.record.classification != "completed"
        || output.record.exit_code != Some(0)
        || !output.stderr.is_empty()
    {
        return Err(Fault::Value(format!(
            "Internal kernel stage failed: {name}: {}",
            String::from_utf8_lossy(&output.stderr).trim()
        )));
    }
    fang_supervisor::strict_json(&output.stdout)
}
