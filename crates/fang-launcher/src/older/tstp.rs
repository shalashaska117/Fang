// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Capture a pinned compiled export before any positive SZS output: a port of tools/fang_szs/tstp.py and
//! tools/fof_szs/fof_tstp.py, which differ only in the row prefixes they admit and in two texts.

use std::ffi::OsString;
use std::path::Path;

use fang_json::{Object, Value};
use fang_supervisor::{Failure, Fault, Snapshot, Status, Supervisor};

use crate::older::{error, failure, run_stage};

/// Which profile's exporter protocol applies.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Profile {
    Cnf,
    GroundFof,
}

/// The transport guard of the exporter's rows; returns the row count.
pub fn validate_output(
    data: &[u8],
    profile: Profile,
    check: &mut dyn FnMut() -> Result<(), Failure>,
) -> Result<usize, Fault> {
    if data.is_empty() || !data.ends_with(b"\n") || !data.is_ascii() {
        return Err(error(
            "Exporter returned empty, truncated or non-ASCII text",
            "exporter",
        ));
    }
    // bytes.splitlines also splits at \r; a row holding \r is refused either way.
    if data.contains(&b'\r') {
        return Err(error(
            "Exporter violated its row-only output protocol",
            "exporter",
        ));
    }
    let rows: Vec<&[u8]> = data[..data.len() - 1]
        .split(|&byte| byte == b'\n')
        .collect();
    for row in &rows {
        check()?;
        let prefix = row.starts_with(b"cnf('")
            || (profile == Profile::GroundFof && row.starts_with(b"fof('"));
        if !prefix || !row.ends_with(b").") || row.contains(&b'%') {
            return Err(error(
                "Exporter violated its row-only output protocol",
                "exporter",
            ));
        }
    }
    let last = rows[rows.len() - 1];
    let empty_clause = last.windows(10).any(|window| window == b",($false),");
    if (profile == Profile::GroundFof && !last.starts_with(b"cnf('")) || !empty_clause {
        return Err(error(
            "Exporter did not end with an empty clause",
            "exporter",
        ));
    }
    Ok(rows.len())
}

/// Run the pinned exporter on the captured pair and capture its rows as `solution.tstp`.
pub fn export_solution(
    supervisor: &mut Supervisor,
    exporter: &Path,
    root: &Path,
    source: &Snapshot,
    certificate: &Snapshot,
    byte_limit: u64,
    profile: Profile,
) -> Result<Value, Fault> {
    if source.data.len() > 1 << 20 || certificate.data.len() > 1 << 20 {
        return Err(failure(
            Status::ResourceOut,
            "TSTP export accepts at most 1 MiB each of input and certificate",
            "exporter",
        ));
    }
    let command: Vec<OsString> = vec![
        exporter.into(),
        source.argument().into(),
        certificate.argument().into(),
        "input.p".into(),
    ];
    let output = run_stage(
        supervisor,
        "exporter",
        &command,
        &root.join("exporter"),
        root,
        None,
        Some(byte_limit),
        None,
    )?;
    let (code, class) = crate::older::exit_and_class(&output);
    if code == Some(2)
        && output.stdout.is_empty()
        && (output.stderr
            == b"resource-exhaustion: export supports at most 1000 certificate nodes\n"
            || output.stderr == b"resource-exhaustion: TSTP output exceeds 16 MiB\n")
    {
        let text = String::from_utf8_lossy(&output.stderr).trim().to_string();
        return Err(failure(Status::ResourceOut, text, "exporter"));
    }
    if code != Some(0) || class != "completed" || !output.stderr.is_empty() {
        return Err(error(
            match profile {
                Profile::Cnf => "Pinned TSTP exporter did not return a clean success",
                Profile::GroundFof => "Pinned FOF TSTP exporter did not return a clean success",
            },
            "exporter",
        ));
    }
    let supervisor: &Supervisor = supervisor;
    let mut check = || crate::older::check(supervisor);
    let rows = validate_output(&output.stdout, profile, &mut check)?;
    source.verify(&mut check)?;
    certificate.verify(&mut check)?;
    let snapshot = Snapshot::create(&root.join("solution.tstp"), &output.stdout)?;
    snapshot.verify(&mut check)?;
    let mut record = Object::new();
    record.set("path", "solution.tstp");
    record.set("bytes", Value::from(output.stdout.len() as i64));
    record.set("sha256", snapshot.sha256.clone());
    record.set("rows", Value::from(rows as i64));
    record.set("source_label", "input.p");
    record.set("execution", "compiled-exporter");
    record.set("per_instance_kernel_check_of_printed_bytes", false);
    record.set(
        "scope",
        match profile {
            Profile::Cnf => "General exporter correspondence proofs plus trusted compilation/runtime; kernel profile checks the original input and internal certificate",
            Profile::GroundFof => "Checked ground-FOF exporter correspondence plus trusted compilation/runtime; the kernel profile proves the original input/certificate pair",
        },
    );
    Ok(Value::Object(record))
}

/// Read the captured solution back and require the recorded length and hash.
pub fn read_solution(
    root: &Path,
    record: &Object,
    check: &mut dyn FnMut() -> Result<(), Failure>,
) -> Result<Vec<u8>, Fault> {
    let bytes = match record.get("bytes") {
        Some(Value::Number(fang_json::Number::Integer(integer))) => integer.as_u64().unwrap_or(0),
        _ => 0,
    };
    let sha256 = match record.get("sha256") {
        Some(Value::String(text)) => text.clone(),
        _ => String::new(),
    };
    let data = fang_supervisor::read_regular(&root.join("solution.tstp"), bytes, check)?;
    if data.len() as u64 != bytes || fang_hash::sha256_hex(&data) != sha256 {
        return Err(error("Captured solution changed before output", "exporter"));
    }
    Ok(data)
}

/// The solution lines after the status line.
pub fn solution_output(data: &[u8], problem_id: &str) -> Vec<u8> {
    let mut output = b"% Fang TSTP execution: compiled exporter; printed bytes are not a per-instance kernel theorem\n".to_vec();
    output.extend_from_slice(
        format!("% SZS output start CNFRefutation for {problem_id}\n").as_bytes(),
    );
    output.extend_from_slice(data);
    output
        .extend_from_slice(format!("% SZS output end CNFRefutation for {problem_id}\n").as_bytes());
    output
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rows_follow_each_profile_protocol() {
        let mut check = || Ok(());
        let cnf = b"cnf('c1',axiom,(p),file('input.p',a)).\ncnf('c2',plain,($false),inference(r,[],[c1])).\n";
        assert_eq!(validate_output(cnf, Profile::Cnf, &mut check).unwrap(), 2);
        let fof = b"fof('f1',axiom,(p),file('input.p',a)).\ncnf('c2',plain,($false),inference(r,[],[f1])).\n";
        assert!(validate_output(fof, Profile::Cnf, &mut check).is_err());
        assert_eq!(
            validate_output(fof, Profile::GroundFof, &mut check).unwrap(),
            2
        );
        assert!(validate_output(b"cnf('c',axiom,(p)).\r\n", Profile::Cnf, &mut check).is_err());
        assert!(validate_output(b"", Profile::Cnf, &mut check).is_err());
    }

    /// tools/tests/test_tstp_adapter.py `test_solution_capture_hash_detects_equal_length_change`.
    #[test]
    fn solution_capture_hash_detects_equal_length_change() {
        let solution: &[u8] = b"cnf('a',axiom,(p),file('input.p','a')).\ncnf('s',plain,($false),inference(r,[],[a])).\n";
        let root =
            fang_supervisor::make_temp_dir(Path::new("/var/tmp"), "fang-tstp-control-").unwrap();
        let path = root.join("solution.tstp");
        std::fs::write(&path, solution).unwrap();
        let mut record = Object::new();
        record.set("bytes", Value::from(solution.len() as i64));
        record.set("sha256", fang_hash::sha256_hex(solution));
        let mut check = || Ok(());
        let read = read_solution(&root, &record, &mut check);
        std::fs::write(
            &path,
            String::from_utf8_lossy(solution).replacen("(p)", "(q)", 1),
        )
        .unwrap();
        let changed = read_solution(&root, &record, &mut check);
        std::fs::remove_dir_all(&root).unwrap();
        assert_eq!(read.unwrap(), solution);
        assert_eq!(
            changed.unwrap_err().python_str(),
            "Captured solution changed before output"
        );
    }
}
