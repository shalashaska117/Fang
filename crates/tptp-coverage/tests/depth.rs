// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The formula depth bound: exact at 64 and at the record's 2,984, capped at `FORMULA_DEPTH_CEILING`
//! when a caller asks for more, and the deepest admitted shapes parse, encode and drop on half of the
//! 8 MiB main-thread stack the producers parse on. The boundaries are those of the Lean decoder
//! `CnfBoolean.declarationD` (`CnfBooleanDeclarationDepthControls.lean`).
use fang::ErrorKind;
use fang_tptp_coverage_candidate::{FORMULA_DEPTH_CEILING, Limits, parse};

/// An atom under `count` negations: height `count + 1`.
fn negations(count: usize) -> String {
    format!("fof(a,axiom,{}p).", "~".repeat(count))
}

/// A flat conjunction of `count` atoms: height `count`.
fn conjunction(count: usize) -> String {
    format!("fof(a,axiom,{}).", vec!["p"; count].join("&"))
}

/// `count` nested universal quantifiers of one variable each over one atom: height `count + 1`.
fn quantifiers(count: usize) -> String {
    let prefix: String = (0..count).map(|index| format!("![X{index}]:")).collect();
    format!("fof(a,axiom,{prefix}p(X0)).")
}

/// One universal quantifier over `count` variables: height `count + 1`.
fn binders(count: usize) -> String {
    let names: Vec<String> = (0..count).map(|index| format!("X{index}")).collect();
    format!("fof(a,axiom,![{}]:p(X0)).", names.join(","))
}

/// A CNF clause under `count` pairs of parentheses.
fn parentheses(count: usize) -> String {
    format!("cnf(a,axiom,{}p{}).", "(".repeat(count), ")".repeat(count))
}

/// An atom under `count` negations, each with parentheses: decoder depth `2 * count + 1`.
fn grouped(count: usize) -> String {
    format!("fof(a,axiom,{}p{}).", "~(".repeat(count), ")".repeat(count))
}

/// Runs `check` on a thread with half of the 8 MiB main-thread stack in a release build, the build the
/// producers ship. The deepest admitted shape, nested quantifiers, needs about 2.6 MiB there (2,587 KiB
/// here and 2,395 KiB in the CNF candidate, measured on 2026-11-08), more than the 2 MiB of a test
/// thread. A debug build needs about 24 MiB (24,392 KiB and 20,836 KiB), so it gets 48 MiB.
fn on_stack(check: impl FnOnce() + Send + 'static) {
    let stack = if cfg!(debug_assertions) {
        48 << 20
    } else {
        4 << 20
    };
    std::thread::Builder::new()
        .stack_size(stack)
        .spawn(check)
        .unwrap()
        .join()
        .unwrap();
}

/// Each shape with the largest size that a bound admits.
fn deepest(bound: usize) -> [(&'static str, String); 5] {
    [
        ("negations", negations(bound - 1)),
        ("conjunction", conjunction(bound)),
        ("quantifiers", quantifiers(bound - 1)),
        ("binders", binders(bound - 1)),
        ("parentheses", parentheses(bound - 1)),
    ]
}

/// Each shape one level deeper than a bound admits.
fn too_deep(bound: usize) -> [(&'static str, String); 5] {
    [
        ("negations", negations(bound)),
        ("conjunction", conjunction(bound + 1)),
        ("quantifiers", quantifiers(bound)),
        ("binders", binders(bound)),
        ("parentheses", parentheses(bound)),
    ]
}

fn limits(bound: usize) -> Limits {
    Limits {
        max_formula_depth: bound,
        ..Limits::default()
    }
}

fn check_bound(bound: usize, configured: usize) {
    for (shape, text) in deepest(bound) {
        assert!(
            parse(text.as_bytes(), &limits(configured)).is_ok(),
            "{shape} at {bound}"
        );
    }
    for (shape, text) in too_deep(bound) {
        assert_eq!(
            parse(text.as_bytes(), &limits(configured))
                .unwrap_err()
                .kind,
            ErrorKind::ResourceLimit,
            "{shape} over {bound}"
        );
    }
}

#[test]
fn bound_is_exact_at_64() {
    assert_eq!(Limits::default().max_formula_depth, 64);
    check_bound(64, 64);
}

#[test]
fn bound_is_exact_at_the_record_height() {
    assert_eq!(FORMULA_DEPTH_CEILING, 2_984);
    on_stack(|| check_bound(2_984, 2_984));
}

#[test]
fn bounds_above_the_ceiling_are_capped() {
    on_stack(|| {
        check_bound(FORMULA_DEPTH_CEILING, FORMULA_DEPTH_CEILING + 1);
        check_bound(FORMULA_DEPTH_CEILING, usize::MAX);
    });
}

#[test]
fn deepest_shapes_parse_encode_and_drop_on_half_the_main_stack() {
    on_stack(|| {
        let mut shapes = deepest(FORMULA_DEPTH_CEILING).to_vec();
        shapes.push(("grouped", grouped((FORMULA_DEPTH_CEILING - 1) / 2)));
        for (shape, text) in shapes {
            let parsed = parse(text.as_bytes(), &limits(FORMULA_DEPTH_CEILING))
                .unwrap_or_else(|error| panic!("{shape}: {error:?}"));
            let encoded = parsed
                .encode(74_339, 256)
                .unwrap_or_else(|error| panic!("{shape}: {error:?}"));
            drop(encoded);
        }
    });
}
