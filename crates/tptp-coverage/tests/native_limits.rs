// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The default limits follow the checker's limits record `NativeLimits.lean` and the bundle
//! checker main field by field, and a bundle over the earlier default counts is now captured.

use fang::ErrorKind;
use fang_tptp_coverage_candidate::{Bundle, BundleFile, Key, Limits, Root, capture, expand};

const RECORD: &str = include_str!("../../../lean-v8/NativeLimits.lean");
const MAIN: &str = include_str!("../../../lean-v8/BundleLimitNativeMain.lean");
const NUMERIC: &str = include_str!("../../../lean-v8/BundleNumeric.lean");

/// The literal after `field := ` at its first occurrence in `text`.
fn literal(text: &str, field: &str) -> usize {
    let pattern = format!("{field} := ");
    let start = text
        .find(&pattern)
        .unwrap_or_else(|| panic!("{field} missing"))
        + pattern.len();
    let digits: String = text[start..]
        .chars()
        .take_while(char::is_ascii_digit)
        .collect();
    digits
        .parse()
        .unwrap_or_else(|_| panic!("{field} is not a literal"))
}

/// The text of the brace block that opens with `opening`, up to its first closing brace.
fn block(opening: &str) -> &'static str {
    let start = RECORD
        .find(opening)
        .unwrap_or_else(|| panic!("{opening} missing from NativeLimits.lean"));
    let rest = &RECORD[start + opening.len()..];
    let end = rest
        .find('}')
        .unwrap_or_else(|| panic!("{opening} is not closed"));
    &rest[..end]
}

#[test]
fn default_limits_match_the_checker() {
    let limits = Limits::default();
    let input = &limits.input;
    assert!(RECORD.contains("def byteLimit : Nat := 1024 * 1024"));
    assert_eq!(input.max_input_bytes, 1024 * 1024);
    assert_eq!(
        input.max_clauses,
        literal(RECORD, "def declarationLimit : Nat")
    );
    assert_eq!(
        input.max_literals,
        literal(RECORD, "def maximumLiterals : Usize")
    );
    // The per-formula limits of the Skolem core, which the checker applies to each formula.
    let core = block("core := {");
    assert_eq!(limits.max_formula_depth, literal(core, "max_formula_depth"));
    assert_eq!(limits.max_formula_nodes, literal(core, "max_formula_nodes"));
    assert_eq!(limits.max_binders, literal(core, "max_binders"));
    assert_eq!(input.max_term_depth, literal(core, "max_term_depth"));
    assert_eq!(input.max_term_nodes, literal(core, "max_input_term_nodes"));
    assert_eq!(input.max_literals, literal(core, "max_literals_per_clause"));
    // The bundle checker reads each file under the record's byte limit and all files under four
    // times that limit, and has no file cap, so the byte bound stands for the file count.
    assert!(MAIN.contains("def byteLimit : Nat := Fang.NativeLimits.byteLimit"));
    assert!(MAIN.contains("def bundleLimit : Nat := 4 * byteLimit"));
    assert_eq!(limits.max_bundle_bytes, 4 * input.max_input_bytes);
    assert_eq!(limits.max_files, limits.max_bundle_bytes);
    // Expansion fuel 17 admits include depth 16.
    assert_eq!(
        limits.max_include_depth + 1,
        literal(NUMERIC, "def bundleFuel : Nat")
    );
    // No counterpart in the checker: these counts keep their earlier values, except the parser
    // operations, raised so that 4 MiB of FOF records fit (`four_mib_of_fof_records_is_expanded`).
    assert_eq!(limits.max_include_directives, 1_024);
    assert_eq!(limits.max_selection_names, 4_096);
    assert_eq!(limits.max_annotation_nodes, 100_000);
    assert_eq!(limits.max_distinct_objects, 64);
    assert_eq!(input.max_operations, 10_000_000);
}

/// One formula with 6 binders, 9 formula nodes and 67 term nodes.
fn formula(name: &str) -> String {
    let deep = |index: usize| format!("{}X{index}{}", "f(".repeat(10), ")".repeat(10));
    let arguments: Vec<String> = (1..=6).map(deep).collect();
    format!(
        "fof({name},axiom,![X1,X2,X3,X4,X5,X6]:(p(X1)=>r({}))).\n",
        arguments.join(",")
    )
}

/// 70 files, 1,100 formulas in the top-level file, 1,790 expanded declarations, and more than
/// 10,000 formula nodes, 100,000 term nodes, 10,000 binders and 1 MiB in all: over each earlier
/// default (64 files, 1,000 formulas per file and expanded, those node and binder totals, 1 MiB).
#[test]
fn bundle_over_the_earlier_counts_is_captured() {
    let root = std::env::temp_dir().join(format!(
        "fang-coverage-native-limits-{}",
        std::process::id()
    ));
    let base = root.join("base");
    std::fs::create_dir_all(&base).unwrap();
    let mut top: String = (1..70)
        .map(|index| format!("include('f{index}.ax').\n"))
        .collect();
    for index in 0..1_100 {
        top += &formula(&format!("a{index}"));
    }
    std::fs::write(base.join("top.p"), top).unwrap();
    let padding = format!("% {}\n", "x".repeat(12_000));
    for index in 1..70 {
        let mut text = padding.clone();
        for item in 0..10 {
            text += &formula(&format!("b{index}_{item}"));
        }
        std::fs::write(base.join(format!("f{index}.ax")), text).unwrap();
    }
    let top = base.join("top.p");
    let expanded = capture(&top, None, &Limits::default()).unwrap();
    assert_eq!(expanded.bundle.files.len(), 70);
    assert_eq!(expanded.parsed.declarations.len(), 1_100 + 69 * 10);
    let statistics = expanded.parsed.statistics;
    assert!(
        statistics.formula_nodes > 10_000
            && statistics.term_nodes > 100_000
            && statistics.binders > 10_000,
        "{statistics:?}"
    );
    let bytes: usize = expanded
        .bundle
        .files
        .iter()
        .map(|file| file.bytes.len())
        .sum();
    assert!(bytes > 1 << 20, "{bytes}");
    // Each earlier structural default alone refuses the bundle as a resource.
    let mut formulas = Limits::default();
    formulas.input.max_clauses = 1_000;
    let earlier = [
        Limits {
            max_files: 64,
            ..Limits::default()
        },
        Limits {
            max_bundle_bytes: 1 << 20,
            ..Limits::default()
        },
        formulas,
    ];
    for limits in earlier {
        let error = capture(&top, None, &limits).unwrap_err();
        assert_eq!(error.kind, ErrorKind::ResourceLimit, "{error:?}");
    }
    std::fs::remove_dir_all(&root).unwrap();
}

/// Up to 1 MiB of the records of `formula`, named with `prefix`.
fn records(prefix: &str, head: &str) -> String {
    let mut text = String::from(head);
    for index in 0.. {
        let next = formula(&format!("{prefix}{index}"));
        if text.len() + next.len() > 1 << 20 {
            break;
        }
        text += &next;
    }
    text
}

/// Four files of nearly 1 MiB of FOF records, under the 4 MiB bound: the parser needs more than
/// the earlier 5,000,000 operations and fewer than 10,000,000.
#[test]
fn four_mib_of_fof_records_is_expanded() {
    let key = |path: &str| Key {
        root: Root::Base,
        path: vec![path.to_owned()],
    };
    let mut files = vec![BundleFile {
        key: key("top.p"),
        bytes: records(
            "t",
            "include('h1.ax').\ninclude('h2.ax').\ninclude('h3.ax').\n",
        )
        .into_bytes(),
    }];
    for index in 1..4 {
        files.push(BundleFile {
            key: key(&format!("h{index}.ax")),
            bytes: records(&format!("h{index}_"), "").into_bytes(),
        });
    }
    let bundle = Bundle { files };
    let bytes: usize = bundle.files.iter().map(|file| file.bytes.len()).sum();
    assert!(bytes > 4 * 1_000_000 && bytes <= 4 << 20, "{bytes}");
    let expanded = expand(&bundle, &Limits::default()).unwrap();
    let operations = expanded.parsed.statistics.operations;
    assert!(
        operations > 5_000_000 && operations < 10_000_000,
        "{operations}"
    );
    let mut earlier = Limits::default();
    earlier.input.max_operations = 5_000_000;
    let error = expand(&bundle, &earlier).unwrap_err();
    assert_eq!(error.kind, ErrorKind::ResourceLimit, "{error:?}");
}
