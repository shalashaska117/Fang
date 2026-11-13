// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Kernel mode: the witness tool suggests values, the kernel entry checks every one in Lean. Only exit 0 with
//! status KernelChecked gives a result; ResourceOut, Timeout and MemoryOut keep their names, and every other
//! outcome, ReviewPending included, is an Error and never a result.

use std::ffi::OsString;
use std::path::PathBuf;

use fang_json::{Object, Value};
use fang_supervisor::{Fault, Snapshot, Status};

use super::run::{Run, code_value, failure, python_code, write_new};

/// The kernel entry's exit codes and the status each names.
fn exit_name(code: i64) -> Option<&'static str> {
    Some(match code {
        0 => "KernelChecked",
        2 => "Usage",
        3 => "Rejected",
        4 => "ReviewPending",
        5 => "ResourceOut",
        6 => "Error",
        7 => "Timeout",
        8 => "MemoryOut",
        9 => "Forced",
        _ => return None,
    })
}

fn stop_status(name: &str) -> Option<Status> {
    match name {
        "ResourceOut" => Some(Status::ResourceOut),
        "Timeout" => Some(Status::Timeout),
        "MemoryOut" => Some(Status::MemoryOut),
        _ => None,
    }
}

/// Python's `strict_json(data.decode("ascii"))`, or None where it raises.
fn ascii_json(data: &[u8]) -> Option<Value> {
    if !data.is_ascii() {
        return None;
    }
    fang_supervisor::strict_json(data).ok()
}

/// Replay the captured pair in the kernel; Unsatisfiable only on KernelChecked.
pub fn kernel_check(
    run: &mut Run,
    source: &Snapshot,
    certificate: &Snapshot,
) -> Result<(String, String), Fault> {
    let witness = run.binary("kernel", "witness");
    let entry = run.binary("kernel", "entry");
    let installation = run.binary("kernel", "installation");
    let command: Vec<OsString> = vec![
        witness.into_os_string(),
        source.argument().as_os_str().to_os_string(),
        certificate.argument().as_os_str().to_os_string(),
    ];
    let output = run.stage(
        "witness",
        &command,
        &run.root.join("witness"),
        None,
        Some(16 << 20),
    )?;
    let source_bytes = std::fs::read(source.argument()).map_err(Fault::Os)?;
    let certificate_bytes = std::fs::read(certificate.argument()).map_err(Fault::Os)?;
    let parsed = ascii_json(&output.stdout);
    let valid = output.record.exit_code == Some(0)
        && output.stderr.is_empty()
        && parsed.as_ref().is_some_and(|value| {
            value.get("schema").and_then(Value::as_str) == Some("fang-equality-kernel-witness-1")
                && value.get("source_hex").and_then(Value::as_str)
                    == Some(fang_hash::hex(&source_bytes).as_str())
                && value.get("certificate_hex").and_then(Value::as_str)
                    == Some(fang_hash::hex(&certificate_bytes).as_str())
        });
    if !valid {
        return Err(failure(
            Status::Error,
            "The kernel witness tool failed or described other files",
            "witness",
        ));
    }
    let witness_path = run.root.join("witness.json");
    write_new(&witness_path, &output.stdout)?;
    let mut check = || run.supervisor.check_default();
    source.verify(&mut check)?;
    certificate.verify(&mut check)?;
    let output_root = run
        .capability
        .section("kernel")
        .and_then(|kernel| kernel.get("output_root"))
        .and_then(Value::as_str)
        .map(PathBuf::from)
        .unwrap_or_default();
    // The entry refuses an existing directory; run directories of different runs may share a name.
    let token = fang_supervisor::fresh_token()?.replace('-', "");
    let run_name = run
        .root
        .file_name()
        .map(|name| name.to_string_lossy().into_owned())
        .unwrap_or_default();
    let out = output_root.join(format!("{run_name}-{token}"));
    // The entry reads its installation record when it starts: both are hashed together.
    run.verify(&[entry.as_path(), installation.as_path()])?;
    let command: Vec<OsString> = vec![
        entry.into_os_string(),
        "--input".into(),
        run.root.join("input.p").into_os_string(),
        "--certificate".into(),
        run.root.join("proof.fang").into_os_string(),
        "--witness".into(),
        witness_path.into_os_string(),
        "--out".into(),
        out.clone().into_os_string(),
    ];
    let output = run.stage("kernel", &command, &run.root.join("kernel"), None, None)?;
    let code = output.record.exit_code;
    let named = code.and_then(|code| exit_name(i64::from(code)));
    let line = ascii_json(&output.stdout)
        .and_then(|value| value.as_object().cloned())
        .unwrap_or_default();
    let mut record = Object::new();
    record.set("exit_code", code_value(code));
    record.set("status", line.get("status").cloned().unwrap_or(Value::Null));
    record.set("error", line.get("error").cloned().unwrap_or(Value::Null));
    record.set("out", out.display().to_string());
    record.set("expected", named.map(Value::from).unwrap_or(Value::Null));
    let kernel_manifest = out.join("manifest.json");
    if kernel_manifest.is_file()
        && let Ok(bytes) = std::fs::read(&kernel_manifest)
    {
        record.set("manifest_sha256", fang_hash::sha256_hex(&bytes));
    }
    let status = line
        .get("status")
        .and_then(Value::as_str)
        .map(str::to_string);
    let manifest = line
        .get("manifest")
        .and_then(Value::as_str)
        .map(str::to_string);
    if code == Some(0)
        && status.as_deref() == Some("KernelChecked")
        && manifest.as_deref() == Some(&kernel_manifest.display().to_string())
    {
        record.set("accepted", true);
        run.manifest.set("kernel_check", Value::Object(record));
        return Ok((
            super::protocol::task_status(0, 1).to_string(),
            "Lean kernel replay checked the exact captured pair (KernelChecked)".to_string(),
        ));
    }
    run.manifest.set("kernel_check", Value::Object(record));
    if let Some(name) = named
        && let Some(stop) = stop_status(name)
        && status.as_deref() == Some(name)
    {
        return Err(failure(
            stop,
            format!("Kernel replay stopped: {name}"),
            "kernel",
        ));
    }
    let described = named
        .map(str::to_string)
        .unwrap_or_else(|| format!("exit {}", python_code(code)));
    Err(failure(
        Status::Error,
        format!("Kernel replay gave no result ({described})"),
        "kernel",
    ))
}
