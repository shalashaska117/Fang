// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The output and exit codes of the single-file signed producer with naming.

use std::io::Write;
use std::process::{Command, Output, Stdio};

const HEADER: &str =
    "(fang-proof 8\n  (preprocessing expanded-fof-equality-skolem-distributive-v1)\n";

fn run(arguments: &[&str], input: &str) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_fang-v3-signed-named"))
        .args(arguments)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    // A usage error exits before reading its input, so a failed write is expected there.
    let _ = child.stdin.take().unwrap().write_all(input.as_bytes());
    child.wait_with_output().unwrap()
}

#[test]
fn goal_and_inputs_candidates_are_written() {
    let goal = run(
        &["--search", "v3", "--time-limit", "20", "--goal", "0"],
        "fof(a,axiom,p).fof(b,axiom,p=>q).fof(g,conjecture,q).",
    );
    assert_eq!(goal.status.code(), Some(0));
    assert!(String::from_utf8(goal.stdout).unwrap().starts_with(HEADER));
    assert_eq!(
        goal.stderr,
        b"candidate-certificate: unchecked signed task\n"
    );
    let inputs = run(
        &["--search", "v3", "--time-limit", "20", "--inputs"],
        "fof(a,axiom,((p&q&r)|(s&t&u))).fof(b,axiom,~p).fof(c,axiom,~s).",
    );
    assert_eq!(inputs.status.code(), Some(0));
    assert!(
        String::from_utf8(inputs.stdout)
            .unwrap()
            .starts_with(HEADER)
    );
}

#[test]
fn a_formula_above_height_64_is_read() {
    let deep = format!(
        "fof(a,axiom,{}).fof(g,conjecture,p).",
        vec!["p"; 100].join("&")
    );
    let output = run(
        &["--search", "v3", "--time-limit", "20", "--goal", "0"],
        &deep,
    );
    assert_eq!(output.status.code(), Some(0));
}

#[test]
fn gave_up_errors_and_usage_keep_their_codes() {
    let unknown = run(
        &["--search", "v3", "--time-limit", "20", "--inputs"],
        "fof(a,axiom,p).",
    );
    assert_eq!(unknown.status.code(), Some(2));
    assert!(unknown.stdout.is_empty());
    assert!(
        String::from_utf8(unknown.stderr)
            .unwrap()
            .starts_with("unknown: processed=")
    );
    let no_goal = run(
        &["--search", "v3", "--goal", "1"],
        "fof(a,axiom,p).fof(g,conjecture,p).",
    );
    assert_eq!(no_goal.status.code(), Some(1));
    assert!(
        String::from_utf8(no_goal.stderr)
            .unwrap()
            .starts_with("error: no-goal ")
    );
    assert_eq!(
        run(&["--goal", "0"], "fof(g,conjecture,p).").status.code(),
        Some(64)
    );
    assert_eq!(
        run(&["--search", "v3"], "fof(g,conjecture,p).")
            .status
            .code(),
        Some(64)
    );
}

#[test]
fn render_prints_the_named_task() {
    let output = run(
        &["--search", "v3", "--render", "--goal", "0"],
        "fof(a,axiom,p).fof(g,conjecture,p).",
    );
    assert_eq!(output.status.code(), Some(0));
    assert!(
        String::from_utf8(output.stdout)
            .unwrap()
            .starts_with("functions ")
    );
}
