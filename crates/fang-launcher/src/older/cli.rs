// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The argument set both older profiles share: a port of tools/fang_szs/cli.py `arguments` on the crate's
//! argparse-compatible parser. The installed command is the public one, so the program name is `fang`, the
//! configuration option and `--artifacts` are optional, and a missing `--artifacts` gives a fresh UUID
//! directory under `.local/runs` in the current directory.

use std::path::PathBuf;

use crate::cli::{Default, Kind, Outcome, Parsed, Parser};

/// The parsed and range-checked arguments.
#[derive(Clone, Debug)]
pub struct Arguments {
    pub input: PathBuf,
    /// `--installation` (cnf) or `--capability` (ground-FOF).
    pub configuration: PathBuf,
    pub artifacts: PathBuf,
    pub auto_artifacts: bool,
    pub check: String,
    pub output: String,
    pub max_solution_bytes: i64,
    /// The wall limit as parsed: the integer default 60, or the float given.
    pub wall_seconds: Parsed,
    pub memory_mib: i64,
    pub max_steps: i64,
    pub max_clauses: i64,
    pub max_operations: i64,
    pub max_input_bytes: i64,
    pub max_certificate_bytes: i64,
    pub max_log_bytes: i64,
    pub max_artifact_bytes: i64,
}

impl Arguments {
    pub fn wall(&self) -> f64 {
        match self.wall_seconds {
            Parsed::Int(value) => value as f64,
            Parsed::Float(value) => value,
            _ => 60.0,
        }
    }
}

/// What parsing gives.
pub enum Parse {
    Run(Arguments),
    /// `--help`: the text for standard output, then exit 0.
    Help(String),
    /// The run-record reason "Invalid adapter arguments: ...".
    Error(String),
}

/// The numeric limits after the common options: name, default and description.
fn numeric(fof_cap: Option<i64>) -> [(&'static str, i64, &'static str); 7] {
    [
        ("steps", 100_000, "maximum search steps"),
        ("clauses", 1_000, "maximum clauses retained by search"),
        (
            "operations",
            5_000_000,
            "maximum structural search operations",
        ),
        (
            "input-bytes",
            fof_cap.unwrap_or(1 << 20),
            "maximum captured input bytes",
        ),
        (
            "certificate-bytes",
            fof_cap.unwrap_or(64 << 20),
            "maximum captured certificate bytes",
        ),
        (
            "log-bytes",
            4 << 20,
            "maximum bytes per child output stream",
        ),
        (
            "artifact-bytes",
            256 << 20,
            "maximum retained run artifact bytes",
        ),
    ]
}

/// The parser of cli.py `arguments` with `public=True`; `fof_cap` is the ground-FOF capability byte cap.
pub fn parser(fof_cap: Option<i64>) -> Parser {
    let fof = fof_cap.is_some();
    let scope = if fof {
        "equality-free CNF and ground FOF axioms"
    } else {
        "strict equality-free CNF"
    };
    let configuration = if fof { "capability" } else { "installation" };
    let mut parser = Parser::new("fang")
        .description(&format!(
            "Fang theorem prover for {scope} on Linux/WSL. Kernel replay is the default. Unsupported syntax is rejected; no SAT result is reported."
        ))
        .epilog("Compiled checking trusts compiler/runtime execution. Kernel checking also requires a fresh exact-input Lean proof.")
        .positional("input", Kind::Path, "TPTP problem file to read and capture")
        .option(
            &format!("--{configuration}"),
            Kind::Path,
            Default::none(),
            &format!("override the pinned {configuration} JSON file supplied by the installed launcher"),
        )
        .required(false)
        .option(
            "--artifacts",
            Kind::Path,
            Default::none(),
            "new directory for input, certificate, logs and manifest; must not exist (default: a fresh UUID directory under .local/runs in the current directory)",
        )
        .required(false)
        .option(
            "--check",
            Kind::Text,
            Default::text("kernel"),
            "verification profile: fresh Lean kernel replay or compiled checker execution (default: %(default)s)",
        )
        .choices(&["kernel", "compiled"])
        .option(
            "--output",
            Kind::Text,
            Default::text("status"),
            "SZS status only, or status plus a checked TSTP refutation when supported (default: %(default)s)",
        )
        .choices(&["status", "tstp"])
        .option(
            "--max-solution-bytes",
            Kind::Int,
            Default::int(16 << 20),
            "maximum TSTP solution bytes, from 0 to 16777216 (default: %(default)s)",
        )
        .option(
            "--wall-seconds",
            Kind::Float,
            Default::int_for_float(60),
            "total command deadline in seconds, from 0.25 to 86400 (default: %(default)s)",
        )
        .option(
            "--memory-mib",
            Kind::Int,
            Default::int(2048),
            "sampled memory limit for adapter and owned processes, in MiB, from 16 to 1048576 (default: %(default)s)",
        );
    for (name, value, description) in numeric(fof_cap) {
        let cap = match fof_cap {
            Some(cap) if name == "input-bytes" || name == "certificate-bytes" => {
                format!("; checker hard cap: {cap} bytes")
            }
            _ => String::new(),
        };
        parser = parser.option(
            &format!("--max-{name}"),
            Kind::Int,
            Default::int(value),
            &format!("{description}{cap} (default: %(default)s)"),
        );
    }
    parser
}

fn invalid(message: &str) -> Parse {
    Parse::Error(format!("Invalid adapter arguments: {message}"))
}

/// Parse and range-check `arguments` as cli.py `arguments(argv, public=True, capability_bytes=...)`.
pub fn arguments(
    arguments: &[String],
    fof_cap: Option<i64>,
) -> Result<Parse, fang_supervisor::Fault> {
    let fof = fof_cap.is_some();
    let supplied: Vec<String> = if arguments == ["help"] {
        vec!["--help".to_string()]
    } else {
        arguments.to_vec()
    };
    let values = match parser(fof_cap).parse(&supplied) {
        Outcome::Values(values) => values,
        Outcome::Help(text) => return Ok(Parse::Help(text)),
        Outcome::Error(message) => return Ok(invalid(&message)),
    };
    let configuration = if fof { "capability" } else { "installation" };
    let Some(configured) = values.text(configuration) else {
        return Ok(invalid(&format!(
            "--{configuration} must be supplied by the installed launcher or explicitly"
        )));
    };
    let wall_seconds = values.get("wall_seconds").clone();
    let wall = match wall_seconds {
        Parsed::Int(value) => value as f64,
        Parsed::Float(value) => value,
        _ => f64::NAN,
    };
    if !wall.is_finite() || !(0.25..=86400.0).contains(&wall) {
        return Ok(invalid(
            "wall-seconds must be finite and between 0.25 and 86400",
        ));
    }
    let memory_mib = values.int("memory_mib").unwrap_or(-1);
    if !(16..=1 << 20).contains(&memory_mib) {
        return Ok(invalid(if fof {
            "memory-mib outside supported range"
        } else {
            "memory-mib must be between 16 and 1048576"
        }));
    }
    let mut limits = Vec::new();
    for (name, _, _) in numeric(fof_cap) {
        let attribute = format!("max_{}", name.replace('-', "_"));
        let value = values.int(&attribute).unwrap_or(-1);
        if value < 0 {
            return Ok(invalid(&if fof {
                format!("Invalid nonnegative limit: {}", name.replace('-', "_"))
            } else {
                format!("{attribute} is outside the supported nonnegative range")
            }));
        }
        limits.push(value);
    }
    if let Some(cap) = fof_cap
        && (limits[3] > cap || limits[4] > cap)
    {
        return Ok(invalid(
            "The actual FOF checker accepts at most 1 MiB each of source and certificate",
        ));
    }
    let max_solution_bytes = values.int("max_solution_bytes").unwrap_or(-1);
    if !(0..=16 << 20).contains(&max_solution_bytes) {
        return Ok(invalid(if fof {
            "max-solution-bytes must be between zero and 16 MiB"
        } else {
            "max-solution-bytes must be between 0 and 16777216"
        }));
    }
    let (artifacts, auto_artifacts) = match values.text("artifacts") {
        Some(path) => (PathBuf::from(path), false),
        None => {
            let directory = std::env::current_dir().map_err(|error| {
                crate::older::error(
                    format!("Adapter input, installation or I/O failure: {error}"),
                    "adapter",
                )
            })?;
            (
                directory
                    .join(".local")
                    .join("runs")
                    .join(crate::older::fresh_hex()?),
                true,
            )
        }
    };
    Ok(Parse::Run(Arguments {
        input: PathBuf::from(values.text("input").unwrap_or_default()),
        configuration: PathBuf::from(configured),
        artifacts,
        auto_artifacts,
        check: values.text("check").unwrap_or("kernel").to_string(),
        output: values.text("output").unwrap_or("status").to_string(),
        max_solution_bytes,
        wall_seconds,
        memory_mib,
        max_steps: limits[0],
        max_clauses: limits[1],
        max_operations: limits[2],
        max_input_bytes: limits[3],
        max_certificate_bytes: limits[4],
        max_log_bytes: limits[5],
        max_artifact_bytes: limits[6],
    }))
}
