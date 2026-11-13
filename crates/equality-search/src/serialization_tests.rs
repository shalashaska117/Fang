// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Graph projection controls only; these synthetic nodes assert no inference.
use super::*;

fn node(rule: Rule) -> Node {
    Node {
        clause: Vec::new(),
        rule,
    }
}

fn resolve(left: usize, right: usize) -> Rule {
    Rule::Resolve {
        left,
        left_position: 0,
        right,
        right_position: 0,
        substitution: Vec::new(),
    }
}

#[test]
fn shared_ancestors_and_repeated_parents_keep_exact_earlier_ids() {
    let certificate = Certificate {
        ordered: true,
        nodes: vec![
            node(Rule::Input(0)),
            node(Rule::Input(1)),
            node(Rule::Factor {
                parent: 0,
                first: 0,
                second: 1,
                substitution: Vec::new(),
            }),
            node(resolve(2, 2)),
            node(resolve(3, 2)),
        ],
        final_node: 4,
    };
    let (order, ids) = certificate.serialization_order(true).unwrap();
    assert_eq!(order, [0, 2, 3, 4]);
    assert_eq!(ids, [0, usize::MAX, 1, 2, 3]);
    let text = certificate.to_text(4096).unwrap();
    assert!(text.contains("(factor 1 0 0 1"));
    assert!(text.contains("(resolve 2 1 0 1 0"));
    assert!(text.contains("(resolve 3 2 0 1 0"));
    assert!(text.contains("(final 3)"));
    assert!(!text.contains("(input 1 1)"));
}

#[test]
fn missing_parent_is_a_typed_serialization_failure() {
    let certificate = Certificate {
        ordered: true,
        nodes: vec![node(Rule::Input(0)), node(resolve(0, 9))],
        final_node: 1,
    };
    assert!(matches!(
        certificate.to_text(4096),
        Err(Error::Certificate("parent does not precede child"))
    ));
}

#[test]
fn forward_and_self_parents_are_rejected() {
    for parent in [1, 2] {
        let certificate = Certificate {
            ordered: true,
            nodes: vec![
                node(Rule::Input(0)),
                node(resolve(0, parent)),
                node(Rule::Input(1)),
            ],
            final_node: 1,
        };
        assert!(matches!(
            certificate.to_text(4096),
            Err(Error::Certificate("parent does not precede child"))
        ));
    }
}

#[test]
fn missing_final_node_is_rejected() {
    let certificate = Certificate {
        ordered: true,
        nodes: vec![node(Rule::Input(0))],
        final_node: 1,
    };
    assert!(matches!(
        certificate.to_text(4096),
        Err(Error::Certificate("final node is out of range"))
    ));
}
