// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Flat rendering and the producer entry over real directory trees.

use fang_tptp_bundle_v8::{flat_limits, object_names, produce_bundle, render};
use fang_tptp_coverage_candidate::{Bundle, Limits as CoverageLimits, capture, expand};
use fang_tptp_expanded_integration::Limits;
use fang_tptp_expanded_v8::{HEADER, Outcome, native_limits};
use std::path::PathBuf;
use std::sync::atomic::{AtomicUsize, Ordering};

static COUNTER: AtomicUsize = AtomicUsize::new(0);

struct Tree(PathBuf);

impl Tree {
    fn new(files: &[(&str, &str)]) -> Self {
        let root = std::env::temp_dir().join(format!(
            "fang-bundle-v8-{}-{}",
            std::process::id(),
            COUNTER.fetch_add(1, Ordering::Relaxed)
        ));
        for (path, text) in files {
            let target = root.join(path);
            std::fs::create_dir_all(target.parent().unwrap()).unwrap();
            std::fs::write(target, text).unwrap();
        }
        std::fs::create_dir_all(root.join("tptp")).unwrap();
        Tree(root)
    }
    fn top(&self) -> PathBuf {
        self.0.join("base/top.p")
    }
    fn tptp(&self) -> PathBuf {
        self.0.join("tptp")
    }
}

impl Drop for Tree {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn flat(text: &str) -> String {
    let expanded = expand(
        &Bundle::single(text.as_bytes().to_vec()),
        &CoverageLimits::default(),
    )
    .unwrap();
    render(&expanded).unwrap()
}

#[test]
fn plain_records_keep_their_formula_bytes() {
    assert_eq!(
        flat("fof(a,axiom,p(a) <= /* c */ q /* d */). cnf(1,axiom,(~p(X) | $false),file(x,1))."),
        "fof(fang_bundle_0,axiom,p(a) <= /* c */ q).\ncnf(fang_bundle_1,axiom,(~p(X) | $false)).\n"
    );
}

#[test]
fn objects_are_renamed_and_pairs_follow() {
    assert_eq!(
        flat(
            "fof(a,axiom,p(\"x\") & /* \"w\" */ '\"x\"' = \"y\" % \"z\"\n). cnf(b,axiom,q(\"x\"))."
        ),
        "fof(fang_bundle_0,axiom,p(fang_object_0) & /* \"w\" */ '\"x\"' = fang_object_1).\n\
         cnf(fang_bundle_1,axiom,q(fang_object_0)).\n\
         cnf(fang_distinct_0_1,axiom,fang_object_0 != fang_object_1).\n"
    );
}

#[test]
fn fresh_names_avoid_ordinary_constants() {
    let expanded = expand(
        &Bundle::single(b"fof(a,axiom,p(fang_object_0) & p(\"o\")).".to_vec()),
        &CoverageLimits::default(),
    )
    .unwrap();
    assert_eq!(object_names(&expanded), ["xfang_object_0"]);
}

#[test]
fn includes_selections_and_objects_reach_the_accepted_producer() {
    let tree = Tree::new(&[
        ("base/top.p", "include('ax.ax',[x,y]). fof(goal,axiom,p)."),
        (
            "base/ax.ax",
            "fof(x,axiom,f(\"a\") = \"b\"). fof(y,axiom,f(\"a\") = \"a\"). fof(z,axiom,$false).",
        ),
    ]);
    let run = match produce_bundle(&tree.top(), Some(&tree.tptp()), &Limits::default()) {
        Ok(run) => run,
        Err(error) => panic!("{error:?}"),
    };
    assert_eq!(run.expanded.bundle.files.len(), 2);
    assert_eq!(run.expanded.distinct_objects.len(), 2);
    assert!(
        run.flat
            .ends_with("cnf(fang_distinct_0_1,axiom,fang_object_0 != fang_object_1).\n")
    );
    let Outcome::CandidateRefutation { text, .. } = run.produced.outcome else {
        panic!("expected a candidate refutation");
    };
    assert!(text.starts_with(HEADER));
}

#[test]
fn capture_errors_are_typed() {
    let tree = Tree::new(&[("base/top.p", "include('missing.ax').")]);
    assert!(produce_bundle(&tree.top(), None, &Limits::default()).is_err());
    let tree = Tree::new(&[("base/top.p", "fof(a,axiom,p(1)).")]);
    assert!(produce_bundle(&tree.top(), None, &Limits::default()).is_err());
    let tree = Tree::new(&[("base/top.p", "fof(a,axiom,p(\"o\")).")]);
    let expanded = capture(&tree.top(), None, &CoverageLimits::default()).unwrap();
    assert_eq!(
        render(&expanded).unwrap(),
        "fof(fang_bundle_0,axiom,p(fang_object_0)).\n"
    );
}

/// 70 files and more than 1 MiB in all: over the coverage candidate's earlier defaults of 64
/// files and 1 MiB. The producer, on the checker's limits record, returns a candidate refutation.
/// The expansion stays under 1,000 clauses, the bound of the search's prepared problem.
#[test]
fn bundle_over_the_earlier_file_and_byte_counts_is_produced() {
    let mut top: String = (1..70)
        .map(|index| format!("include('f{index}.ax').\n"))
        .collect();
    for index in 0..200 {
        top += &format!("fof(a{index},axiom,p{index}(c)).\n");
    }
    top += "fof(z,axiom,~p0(c)).\n";
    let padding = format!("% {}\n", "x".repeat(16_000));
    let leaves: Vec<(String, String)> = (1..70)
        .map(|index| {
            let mut text = padding.clone();
            for item in 0..10 {
                text += &format!("fof(b{item},axiom,q{index}_{item}(c)).\n");
            }
            (format!("base/f{index}.ax"), text)
        })
        .collect();
    let mut files = vec![("base/top.p", top.as_str())];
    files.extend(
        leaves
            .iter()
            .map(|(path, text)| (path.as_str(), text.as_str())),
    );
    let tree = Tree::new(&files);
    let run = match produce_bundle(&tree.top(), Some(&tree.tptp()), &native_limits()) {
        Ok(run) => run,
        Err(error) => panic!("{error:?}"),
    };
    assert_eq!(run.expanded.bundle.files.len(), 70);
    assert_eq!(run.expanded.parsed.declarations.len(), 201 + 69 * 10);
    let bytes: usize = run
        .expanded
        .bundle
        .files
        .iter()
        .map(|file| file.bytes.len())
        .sum();
    assert!(bytes > 1 << 20, "{bytes}");
    let Outcome::CandidateRefutation { text, .. } = run.produced.outcome else {
        panic!("expected a candidate refutation");
    };
    assert!(text.starts_with(HEADER));
    let widened = flat_limits(&native_limits(), &run.expanded, &run.flat);
    assert_eq!(widened.input.input.max_clauses, 65_536 * 70);
    assert_eq!(widened.input.input.max_input_bytes, 1 << 20);
}
