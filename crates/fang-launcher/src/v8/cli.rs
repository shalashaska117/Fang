// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The version-8 command line: the options, their help, and the range checks that follow parsing.

use crate::capability::{DEFAULT_CHECK, KERNEL_MINIMUMS, MAX_BYTES, MAX_CERTIFICATE_BYTES};
use crate::cli::{Default, Kind, Outcome, Parser, Values};
use crate::dispatch::PROFILES;

/// The text after "Invalid command arguments: " for each refusal of the command line.
pub type Refusal = String;

/// The `--check kernel` minimums as the help and the messages name them.
pub fn kernel_flags() -> String {
    KERNEL_MINIMUMS
        .iter()
        .map(|(option, minimum)| format!("{option} {minimum}"))
        .collect::<Vec<_>>()
        .join(" ")
}

/// The parser. `public` is the installed command, where the capability and the artifacts directory are
/// optional; a non-public run must name both.
pub fn parser(public: bool) -> Parser {
    let kernel = kernel_flags();
    Parser::new(if public { "fang" } else { "main.py" })
        .description(
            "Fang theorem prover for TPTP CNF and FOF with equality on Linux/WSL. Rust searches for refutations \
             and finite models. By default, an independent Lean checker must accept a candidate before a result \
             is reported. Unsupported input is rejected.",
        )
        .epilog(&format!(
            "Profiles: v8 (default) handles every input. --profile cnf and --profile ground-fof run the older \
             restricted CNF and ground-FOF commands of an earlier installation, with their own options (see fang \
             --profile cnf --help); they are available only when that installation was linked. There is no retry \
             or fallback between profiles, and the older profiles keep their own defaults. For v8 input the \
             default check is compiled: only the compiled Lean checker can accept a result, and the Lean compiler \
             and runtime are trusted. --check kernel is opt-in and needs at least {kernel}; when the installation \
             has kernel mode, single-file axiom input is replayed in the Lean kernel. --check none reports the \
             producer's result without any checker; it is never the default. Every run names its checking mode in \
             a comment line before the status. --output tstp requests a CNFRefutation or FiniteModel document \
             after acceptance. Export support depends on the input route and the installed exporters; a positive \
             status alone does not certify that a document was printed. Inputs with annotations, include \
             directives or distinct objects use the bundle checker; includes resolve relative to the including \
             file, then the TPTP root. Inputs with conjectures or other non-axiom roles use the signed checker: \
             Theorem needs an accepted certificate for every selected conjecture. The limits cover the whole \
             command."
        ))
        .positional("input", Kind::Path, "TPTP problem file to read and capture")
        .option(
            "--profile",
            Kind::Text,
            Default::text("v8"),
            "pipeline: v8, or an older profile chosen explicitly (default: %(default)s)",
        )
        .choices(&PROFILES)
        .option(
            "--capability",
            Kind::Path,
            Default::none(),
            "override the pinned capability JSON file supplied by the installed launcher",
        )
        .required(!public)
        .option(
            "--artifacts",
            Kind::Path,
            Default::none(),
            "new directory for input, certificate, logs and manifest; must not exist (default: a fresh UUID \
             directory under .local/runs in the current directory)",
        )
        .required(!public)
        .option(
            "--tptp-root",
            Kind::Path,
            Default::none(),
            "directory for include files not found next to the input (default: the TPTP environment variable)",
        )
        .option(
            "--check",
            Kind::Text,
            Default::none(),
            &format!(
                "verification mode: the compiled checker, per-input kernel replay, or none (default: \
                 {DEFAULT_CHECK}, which trusts the Lean compiler and runtime; kernel needs at least {kernel}; none \
                 reports the producer's result unchecked, is never the default and says so on every run)"
            ),
        )
        .choices(&["compiled", "kernel", "none"])
        .option(
            "--output",
            Kind::Text,
            Default::text("status"),
            "SZS status only, or status plus a refutation or finite model document when supported (default: %(default)s)",
        )
        .choices(&["status", "tstp"])
        .option(
            "--max-solution-bytes",
            Kind::Int,
            Default::int(16 << 20),
            "maximum TSTP document bytes, from 0 to 16777216 (default: %(default)s)",
        )
        .option(
            "--self-check",
            Kind::Flag,
            Default::flag(),
            "verify the installed launcher and pinned files, then exit; no input is read",
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
            "sampled memory limit for the adapter and its processes, in MiB, from 16 to 1048576 (default: \
             %(default)s)",
        )
        .option(
            "--max-input-bytes",
            Kind::Int,
            Default::int(MAX_BYTES as i64),
            "maximum captured input bytes; checker hard cap 1048576 (default: %(default)s)",
        )
        .option(
            "--max-certificate-bytes",
            Kind::Int,
            Default::int(MAX_CERTIFICATE_BYTES as i64),
            "maximum captured certificate bytes; checker hard cap 5081233, model certificates 1048576 (default: \
             %(default)s)",
        )
        .option(
            "--max-log-bytes",
            Kind::Int,
            Default::int(4 << 20),
            "maximum bytes per child output stream (default: %(default)s)",
        )
        .option(
            "--max-artifact-bytes",
            Kind::Int,
            Default::int(256 << 20),
            "maximum retained run artifact bytes (default: %(default)s)",
        )
}

/// What parsing the version-8 command line gives.
pub enum Parsed {
    Values(Values),
    Help(String),
    Refused(Refusal),
}

/// Parse and range-check the command line, as the Python `arguments` did. `help` alone means `--help`.
pub fn arguments(argv: &[String], public: bool) -> Parsed {
    let argv: Vec<String> = if public && argv == ["help"] {
        vec!["--help".to_string()]
    } else {
        argv.to_vec()
    };
    let values = match parser(public).parse(&argv) {
        Outcome::Values(values) => values,
        Outcome::Help(text) => return Parsed::Help(text),
        Outcome::Error(message) => return Parsed::Refused(message),
    };
    if values.text("profile") != Some("v8") {
        return Parsed::Refused(format!(
            "--profile {} is dispatched by the fang launcher, not by the v8 adapter",
            values.text("profile").unwrap_or_default()
        ));
    }
    let wall = values.float("wall_seconds").unwrap_or(f64::NAN);
    if !wall.is_finite() || !(0.25..=86400.0).contains(&wall) {
        return Parsed::Refused(
            "wall-seconds must be finite and between 0.25 and 86400".to_string(),
        );
    }
    let memory = values.int("memory_mib").unwrap_or(-1);
    if !(16..=1 << 20).contains(&memory) {
        return Parsed::Refused("memory-mib must be between 16 and 1048576".to_string());
    }
    let solution = values.int("max_solution_bytes").unwrap_or(-1);
    if !(0..=16 << 20).contains(&solution) {
        return Parsed::Refused("max-solution-bytes must be between 0 and 16777216".to_string());
    }
    for (name, maximum) in [
        ("input_bytes", MAX_BYTES as i64),
        ("certificate_bytes", MAX_CERTIFICATE_BYTES as i64),
        ("log_bytes", i64::MAX),
        ("artifact_bytes", i64::MAX),
    ] {
        let value = values.int(&format!("max_{name}")).unwrap_or(-1);
        if !(0..=maximum).contains(&value) {
            return Parsed::Refused(format!(
                "max-{} is outside the supported range",
                name.replace('_', "-")
            ));
        }
    }
    Parsed::Values(values)
}

#[cfg(test)]
mod tests {
    use super::*;

    const HELP: &str = include_str!("../../tests/data/v8-help-final-public.txt");

    fn strings(items: &[&str]) -> Vec<String> {
        items.iter().map(|item| item.to_string()).collect()
    }

    fn refusal(items: &[&str]) -> String {
        match arguments(&strings(items), true) {
            Parsed::Refused(message) => message,
            _ => panic!("expected a refusal for {items:?}"),
        }
    }

    #[test]
    fn help_matches_final_public_fixture() {
        // Final public help; the frozen Python parity fixture remains in v8-help-public.txt.
        if std::env::var_os("COLUMNS").is_some() {
            return;
        }
        assert_eq!(parser(true).help(), HELP);
    }

    #[test]
    fn refusals_are_python_texts() {
        assert_eq!(refusal(&[]), "the following arguments are required: input");
        assert_eq!(
            refusal(&["p.p", "--check", "x"]),
            "argument --check: invalid choice: 'x' (choose from compiled, kernel, none)"
        );
        assert_eq!(
            refusal(&["p.p", "--max"]),
            "ambiguous option: --max could match --max-solution-bytes, --max-input-bytes, \
             --max-certificate-bytes, --max-log-bytes, --max-artifact-bytes"
        );
        assert_eq!(
            refusal(&["p.p", "--check=kernel", "--wall"]),
            "argument --wall-seconds: expected one argument"
        );
        assert_eq!(
            refusal(&["p.p", "--output", "html"]),
            "argument --output: invalid choice: 'html' (choose from status, tstp)"
        );
        assert_eq!(
            refusal(&["p.p", "--profile", "cnf", "--capability", "c.json"]),
            "--profile cnf is dispatched by the fang launcher, not by the v8 adapter"
        );
        assert_eq!(
            refusal(&["p.p", "--wall-seconds", "0.1", "--capability", "c.json"]),
            "wall-seconds must be finite and between 0.25 and 86400"
        );
        assert_eq!(
            refusal(&[
                "p.p",
                "--max-input-bytes",
                "2000000",
                "--capability",
                "c.json"
            ]),
            "max-input-bytes is outside the supported range"
        );
    }
}
