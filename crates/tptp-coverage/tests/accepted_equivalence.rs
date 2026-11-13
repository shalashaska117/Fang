// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Single files without new constructs parse exactly as the accepted v5 crate.

use fang_tptp_coverage_candidate::{Bundle, Limits, Source, expand};

struct Random(u64);

impl Random {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, bound: usize) -> usize {
        (self.next() % bound as u64) as usize
    }
    fn pick<'a>(&mut self, values: &[&'a str]) -> &'a str {
        values[self.below(values.len())]
    }
}

fn term(random: &mut Random, depth: usize, variables: &[&str]) -> String {
    let choice = random.below(if depth == 0 { 3 } else { 6 });
    match choice {
        0 if !variables.is_empty() => random.pick(variables).to_owned(),
        0 | 1 => random.pick(&["a", "b", "'c'", "'a'"]).to_owned(),
        2 => random.pick(&["'q d'", "e"]).to_owned(),
        _ => {
            let head = random.pick(&["f", "g", "p", "'f'"]);
            let arity = 1 + random.below(2);
            let arguments: Vec<String> = (0..arity)
                .map(|_| term(random, depth - 1, variables))
                .collect();
            format!("{head}({})", arguments.join(","))
        }
    }
}

fn atom(random: &mut Random, variables: &[&str]) -> String {
    match random.below(4) {
        0 => format!(
            "{} = {}",
            term(random, 2, variables),
            term(random, 2, variables)
        ),
        1 => format!(
            "{} != {}",
            term(random, 2, variables),
            term(random, 2, variables)
        ),
        2 => random.pick(&["p", "q", "$true", "$false"]).to_owned(),
        _ => format!(
            "{}({})",
            random.pick(&["p", "q", "f"]),
            term(random, 2, variables)
        ),
    }
}

fn formula(random: &mut Random, depth: usize, variables: &mut Vec<&'static str>) -> String {
    if depth == 0 {
        return atom(random, variables);
    }
    match random.below(6) {
        0 => atom(random, variables),
        1 => format!("~ {}", formula(random, depth - 1, variables)),
        2 => {
            let name = random.pick(&["X", "Y", "Z"]);
            let quantifier = random.pick(&["!", "?"]);
            variables.push(name);
            let body = formula(random, depth - 1, variables);
            variables.pop();
            format!("{quantifier}[{name}] : {body}")
        }
        _ => {
            let operator = random.pick(&["&", "|", "=>", "<=", "<=>", "<~>", "~&", "~|"]);
            format!(
                "({} {operator} {})",
                formula(random, depth - 1, variables),
                formula(random, depth - 1, variables)
            )
        }
    }
}

fn clause(random: &mut Random) -> String {
    let count = 1 + random.below(3);
    let literals: Vec<String> = (0..count)
        .map(|_| {
            let sign = random.pick(&["", "~ "]);
            match random.below(3) {
                0 => format!("{sign}{}", random.pick(&["$true", "$false", "p"])),
                1 => format!("X = {}", term(random, 1, &["X", "Y"])),
                _ => format!("{sign}q({})", term(random, 1, &["X", "Y"])),
            }
        })
        .collect();
    let body = literals.join(" | ");
    if random.below(2) == 0 {
        format!("({body})")
    } else {
        body
    }
}

fn document(random: &mut Random) -> String {
    let count = random.below(4);
    let mut text = String::new();
    for index in 0..count {
        let name = random.pick(&["a", "'b c'", "1", "+2", "d"]);
        let name = format!("{name}{index}");
        let name = if name.starts_with('\'') {
            format!("'n{index}'")
        } else if name.starts_with(['1', '+']) {
            format!("{}", 10 + index)
        } else {
            name
        };
        if random.below(2) == 0 {
            text += &format!("cnf({name},axiom,{}).", clause(random));
        } else {
            let mut variables = Vec::new();
            text += &format!("fof({name},axiom,{}).", formula(random, 3, &mut variables));
        }
        text += random.pick(&["\n", " % c\n", "/* b */", ""]);
    }
    text
}

fn uses_new_constructs(bytes: &[u8]) -> bool {
    match expand(&Bundle::single(bytes.to_vec()), &Limits::default()) {
        Ok(value) => {
            !value.distinct_objects.is_empty()
                || value.sources.iter().any(|source| {
                    matches!(
                        source,
                        Source::File {
                            annotation: Some(_),
                            ..
                        }
                    )
                })
        }
        Err(_) => false,
    }
}

fn compare(bytes: &[u8], counts: &mut [usize; 4]) {
    let old = accepted::parse(bytes, &accepted::Limits::default());
    let new = fang_tptp_coverage_candidate::parse(bytes, &Limits::default());
    match (old, new) {
        (Ok(old), Ok(new)) => {
            counts[0] += 1;
            assert_eq!(old.functions, new.functions, "{bytes:?}");
            assert_eq!(old.predicates, new.predicates);
            assert_eq!(
                format!("{:?}", old.declarations),
                format!("{:?}", new.declarations)
            );
            let (a, b) = (old.statistics, new.statistics);
            assert_eq!(
                (a.operations, a.formula_nodes, a.term_nodes, a.binders),
                (b.operations, b.formula_nodes, b.term_nodes, b.binders),
                "{}",
                String::from_utf8_lossy(bytes)
            );
        }
        (Ok(_), Err(error)) => panic!(
            "regression on {:?}: {error:?}",
            String::from_utf8_lossy(bytes)
        ),
        (Err(_), Ok(_)) => {
            counts[1] += 1;
            assert!(
                uses_new_constructs(bytes),
                "{:?}",
                String::from_utf8_lossy(bytes)
            );
        }
        (Err(_), Err(_)) => counts[2] += 1,
    }
    counts[3] += 1;
}

#[test]
fn generated_documents_and_mutations_match_the_accepted_parser() {
    let mut random = Random(0x9e37_79b9_7f4a_7c15);
    let mut counts = [0; 4];
    for _ in 0..1_500 {
        let text = document(&mut random);
        compare(text.as_bytes(), &mut counts);
        let bytes = text.as_bytes();
        if bytes.is_empty() {
            continue;
        }
        for _ in 0..8 {
            let mut changed = bytes.to_vec();
            let position = random.below(changed.len());
            changed[position] = *[
                b'"', b',', b'$', b'*', b'.', b'/', b'e', b'1', b'(', b')', b'`', b'-', b'[', b']',
            ]
            .get(random.below(14))
            .expect("index");
            compare(&changed, &mut counts);
        }
    }
    assert_eq!(counts[3], counts[0] + counts[1] + counts[2]);
    assert!(counts[0] > 1_000, "{counts:?}");
    assert!(counts[1] > 0 && counts[2] > 1_000, "{counts:?}");
}

#[test]
fn operation_caps_agree_at_the_exact_boundary() {
    for text in [
        "fof(a,axiom,![X]:(p(X) <=> q(f(X)))). cnf(b,axiom,(~p(a) | $false)).",
        "% c\ncnf(1,axiom,X = f(Y) | ~q(Y)).",
    ] {
        let used = accepted::parse(text.as_bytes(), &accepted::Limits::default())
            .unwrap()
            .statistics
            .operations;
        for cap in [used - 1, used] {
            let mut old = accepted::Limits::default();
            old.input.max_operations = cap;
            let mut new = Limits::default();
            new.input.max_operations = cap;
            assert_eq!(
                accepted::parse(text.as_bytes(), &old).is_ok(),
                fang_tptp_coverage_candidate::parse(text.as_bytes(), &new).is_ok()
            );
        }
    }
}
