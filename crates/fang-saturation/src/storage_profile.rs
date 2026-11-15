// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use super::*;

#[test]
#[ignore = "synthetic storage measurement; run explicitly"]
fn passive_record_allocation_inventory() {
    println!(
        "width\tclauses\trecord_size\trecord_capacity_bytes\tliteral_payload_bytes\tadmission_ns"
    );
    for width in [1, 4, 16] {
        let mut options = Options::preset("step1").unwrap();
        options.duplicates = false;
        let mut search = Search::new(&[], &[], &[0], &options, Limits::default()).unwrap();
        let literal = Lit {
            positive: true,
            atom: Atom::Pred(search.bank.app(0, &[])),
        };
        let start = Instant::now();
        for index in 0..100_000 {
            // Spare capacity models a generated conclusion assembled in a growing buffer.
            let mut lits = Vec::with_capacity(width * 2);
            lits.resize(width, literal);
            let id = search
                .try_push(
                    lits,
                    Rule::Input {
                        index,
                        original: vec![],
                    },
                )
                .unwrap();
            assert!(!search.admit(id));
        }
        let elapsed = start.elapsed().as_nanos();
        let record_bytes = search.clauses.capacity() * std::mem::size_of::<ClauseRec>();
        let literal_bytes: usize = search
            .clauses
            .iter()
            .map(|record| record.lits.len() * std::mem::size_of::<Lit>())
            .sum();
        println!(
            "{width}\t{}\t{}\t{record_bytes}\t{literal_bytes}\t{elapsed}",
            search.clauses.len(),
            std::mem::size_of::<ClauseRec>()
        );
        assert_eq!(search.passive, 100_000);
    }
}
