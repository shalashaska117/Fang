// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use std::{fs, path::PathBuf, process::Command};

struct Fixture(PathBuf);

impl Fixture {
    fn new(name: &str, input: &str) -> Self {
        let directory = std::env::temp_dir().join(format!(
            "fang-fof-driver-test-{}-{name}",
            std::process::id()
        ));
        fs::create_dir(&directory).expect("fresh fixture directory");
        fs::write(directory.join("input.p"), input).unwrap();
        Self(directory)
    }

    fn run(&self, flags: &[&str]) -> std::process::Output {
        Command::new(env!("CARGO_BIN_EXE_fang-ground-fof-driver"))
            .arg(self.0.join("input.p"))
            .arg("--proof")
            .arg(self.0.join("proof.fang"))
            .args(flags)
            .output()
            .unwrap()
    }
}

impl Drop for Fixture {
    fn drop(&mut self) {
        fs::remove_dir_all(&self.0).expect("remove this fixture's fresh directory");
    }
}

#[test]
fn all_three_input_paths_produce_only_versioned_candidates() {
    for (name, input) in [
        ("fof", "fof(a,axiom,p(a)). fof(b,axiom,~p(a))."),
        ("cnf", "cnf(a,axiom,(p(X))). cnf(b,axiom,(~p(a)))."),
        ("mixed", "fof(a,axiom,p(a)). cnf(b,axiom,(~p(X)))."),
    ] {
        let fixture = Fixture::new(name, input);
        let output = fixture.run(&[]);
        assert_eq!(output.status.code(), Some(0), "{name}: {output:?}");
        assert_eq!(output.stdout, b"candidate-refutation\n");
        assert!(String::from_utf8(output.stderr).unwrap().ends_with(
            " recorded search nodes; serialized proof keeps only refutation dependencies; independent checking required\n"
        ));
        let proof = fs::read_to_string(fixture.0.join("proof.fang")).unwrap();
        assert!(proof.starts_with("(fang-proof 2\n  (preprocessing ground-fof-distributive-v1)\n"));
    }
}

#[test]
fn unsupported_invalid_and_resource_outcomes_stay_separate() {
    let cases: [(&str, &str, &[&str], i32, &str); 6] = [
        (
            "quantifier",
            "fof(a,axiom,?[X]:p(X)).",
            &[],
            4,
            "Unsupported",
        ),
        ("equality", "fof(a,axiom,a=b).", &[], 4, "Unsupported"),
        (
            "free-variable",
            "fof(a,axiom,p(X)).",
            &[],
            3,
            "InvalidInput",
        ),
        ("delimiter", "fof(a,axiom,p(a).", &[], 3, "InvalidInput"),
        (
            "expansion-limit",
            "fof(a,axiom,(p & q)).",
            &["--max-clauses", "1"],
            5,
            "ResourceLimit: preprocessing Clauses",
        ),
        (
            "work-limit",
            "fof(a,axiom,p).",
            &["--max-operations", "0"],
            5,
            "ResourceLimit",
        ),
    ];
    for (name, input, flags, code, prefix) in cases {
        let fixture = Fixture::new(name, input);
        let output = fixture.run(flags);
        assert_eq!(output.status.code(), Some(code), "{name}: {output:?}");
        assert!(output.stdout.is_empty(), "{name}");
        assert!(
            String::from_utf8(output.stderr)
                .unwrap()
                .starts_with(prefix),
            "{name}"
        );
        assert!(!fixture.0.join("proof.fang").exists(), "{name}");
    }
}

#[test]
fn exhausted_search_is_unknown_and_writes_no_certificate() {
    let fixture = Fixture::new("unknown", "fof(a,axiom,$true).");
    let output = fixture.run(&[]);
    assert_eq!(output.status.code(), Some(2), "{output:?}");
    assert_eq!(output.stdout, b"unknown\n");
    assert!(
        String::from_utf8(output.stderr)
            .unwrap()
            .starts_with("queue exhausted after ")
    );
    assert!(!fixture.0.join("proof.fang").exists());
}
