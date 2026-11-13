// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Parse-time limits after the census of the TPTP FOF and CNF problems: the
//! formula node, binder and term node bounds count per formula, as the Skolem core does; the
//! operation budget grows with the input and with each declaration; and a nest of equivalences, the
//! shape of TPTP SYN007+1.014 (Pelletier 71), stops at the formula node bound. Run under a memory
//! guard: the copies of an unbounded nest of equivalences grow exponentially.
use fang::ErrorKind;
use fang_tptp_full_frontend_candidate::{Limits, OPERATIONS_PER_BYTE, parse};

/// `count` atoms joined by `&`, in groups of 50 so that the formula stays shallow.
fn grouped_conjunction(count: usize) -> String {
    let groups: Vec<String> = (0..count)
        .collect::<Vec<_>>()
        .chunks(50)
        .map(|chunk| format!("({})", vec!["p"; chunk.len()].join("&")))
        .collect();
    groups.join("&")
}

/// `groups` universal quantifiers over `width` variables each, joined by `&`.
fn grouped_binders(groups: usize, width: usize) -> String {
    let group = |index: usize| {
        let names: Vec<String> = (0..width).map(|v| format!("X{index}_{v}")).collect();
        format!("(![{}]:p(X{index}_0))", names.join(","))
    };
    (0..groups).map(group).collect::<Vec<_>>().join("&")
}

/// One atom whose argument list has `count` constants.
fn wide_atom(count: usize) -> String {
    format!("q({})", vec!["a"; count].join(","))
}

/// The right-nested chain `p1 <=> (p2 <=> ... <=> pn)`.
fn equivalences(count: usize) -> String {
    let mut text = format!("p{count}");
    for index in (1..count).rev() {
        text = format!("(p{index} <=> {text})");
    }
    text
}

fn shallow() -> Limits {
    Limits {
        max_formula_depth: 200,
        ..Limits::default()
    }
}

fn two(body: &str) -> String {
    format!("fof(a,axiom,{body}).\nfof(b,axiom,{body}).\n")
}

#[test]
fn formula_nodes_count_per_formula() {
    // About 6,000 nodes each: over the default bound of 10,000 together, under it apart.
    let text = two(&grouped_conjunction(3_000));
    let parsed = parse(text.as_bytes(), &shallow()).unwrap();
    assert!(parsed.statistics.formula_nodes > 10_000);
    let one = format!("fof(a,axiom,{}).", grouped_conjunction(6_000));
    assert_eq!(
        parse(one.as_bytes(), &shallow()).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
}

#[test]
fn binders_count_per_formula() {
    let text = two(&grouped_binders(60, 100));
    let parsed = parse(text.as_bytes(), &shallow()).unwrap();
    assert!(parsed.statistics.binders > 10_000);
    let one = format!("fof(a,axiom,{}).", grouped_binders(120, 100));
    assert_eq!(
        parse(one.as_bytes(), &shallow()).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
}

#[test]
fn term_nodes_count_per_formula() {
    let text = two(&wide_atom(60_000));
    let parsed = parse(text.as_bytes(), &Limits::default()).unwrap();
    assert!(parsed.statistics.term_nodes > 100_000);
    let one = format!("fof(a,axiom,{}).", wide_atom(120_000));
    assert_eq!(
        parse(one.as_bytes(), &Limits::default()).unwrap_err().kind,
        ErrorKind::ResourceLimit
    );
}

#[test]
fn the_operation_budget_admits_copies_within_the_node_bound() {
    // Each chain of 11 equivalences lowers to several thousand nodes from a few dozen bytes, more
    // operations than the per-byte budget alone allows; the per-declaration allowance admits them.
    let text: String = (0..20)
        .map(|index| format!("fof(e{index},axiom,{}).\n", equivalences(11)))
        .collect();
    let parsed = parse(text.as_bytes(), &shallow()).unwrap();
    assert!(parsed.statistics.operations > OPERATIONS_PER_BYTE * text.len());
    assert!(parsed.statistics.operations <= parsed.statistics.budget);
}

#[test]
fn nested_equivalences_stop_at_the_formula_node_bound() {
    // SYN007+1.014 is this chain over 28 atoms; its lowering would take about 2^28 nodes.
    let text = format!("fof(a,axiom,{}).", equivalences(28));
    let error = parse(text.as_bytes(), &shallow()).unwrap_err();
    assert_eq!(error.kind, ErrorKind::ResourceLimit);
    assert_eq!(error.message, "input formula node limit exceeded");
}
