// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Random include graphs against an independent reference expansion, byte
//! mutations of a mixed seed, and SHA-256 vectors.

use fang_tptp_coverage_candidate::{
    Bundle, BundleFile, Key, Limits, Reason, Root, Source, expand, sha256,
};
use std::collections::BTreeMap;

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
}

#[derive(Clone, Debug)]
enum Statement {
    Formula(String),
    Include(usize, Option<Vec<String>>),
}

type Files = Vec<Vec<Statement>>;

/// The problem library rule written directly as a recursion.
fn reference(
    files: &Files,
    present: &[bool],
    file: usize,
    stack: &mut Vec<usize>,
    reached: &mut Vec<usize>,
) -> Result<Vec<(usize, usize)>, Reason> {
    let mut output: Vec<(usize, usize)> = Vec::new();
    for (index, statement) in files[file].iter().enumerate() {
        match statement {
            Statement::Formula(_) => {
                if !output.contains(&(file, index)) {
                    output.push((file, index));
                }
            }
            Statement::Include(target, selection) => {
                if !present[*target] {
                    return Err(Reason::Missing);
                }
                if !reached.contains(target) {
                    reached.push(*target);
                }
                if stack.contains(target) {
                    return Err(Reason::Cycle);
                }
                stack.push(*target);
                let items = reference(files, present, *target, stack, reached);
                stack.pop();
                let mut items = items?;
                if let Some(names) = selection {
                    let name = |item: &(usize, usize)| match &files[item.0][item.1] {
                        Statement::Formula(name) => name.clone(),
                        Statement::Include(..) => unreachable!(),
                    };
                    for wanted in names {
                        match items.iter().filter(|item| &name(item) == wanted).count() {
                            0 => return Err(Reason::SelectionMissing),
                            1 => {}
                            _ => return Err(Reason::SelectionAmbiguous),
                        }
                    }
                    items.retain(|item| names.contains(&name(item)));
                }
                for item in items {
                    if !output.contains(&item) {
                        output.push(item);
                    }
                }
            }
        }
    }
    Ok(output)
}

fn render(statements: &[Statement]) -> String {
    statements
        .iter()
        .map(|statement| match statement {
            Statement::Formula(name) => format!("fof({name},axiom,p({name})).\n"),
            Statement::Include(target, None) => format!("include('f{target}.ax').\n"),
            Statement::Include(target, Some(names)) => {
                format!("include('f{target}.ax',[{}]).\n", names.join(","))
            }
        })
        .collect()
}

#[test]
fn random_include_graphs_match_the_reference_expansion() {
    let mut random = Random(0x2545_f491_4f6c_dd1d);
    let mut outcomes: BTreeMap<String, usize> = BTreeMap::new();
    for _ in 0..24_000 {
        let count = 1 + random.below(5);
        let names = ["a", "b", "c"];
        let mut files: Files = Vec::new();
        for _ in 0..count {
            let mut statements = Vec::new();
            let mut used = Vec::new();
            for _ in 0..random.below(5) {
                if random.below(3) == 0 {
                    let target = if random.below(8) == 0 {
                        count
                    } else {
                        random.below(count)
                    };
                    let selection = match random.below(3) {
                        0 => None,
                        _ => Some(
                            (0..1 + random.below(2))
                                .map(|_| names[random.below(3)].to_owned())
                                .collect::<Vec<_>>(),
                        ),
                    };
                    statements.push(Statement::Include(target, selection));
                } else {
                    let name = names[random.below(3)];
                    if !used.contains(&name) {
                        used.push(name);
                        statements.push(Statement::Formula(name.to_owned()));
                    }
                }
            }
            files.push(statements);
        }
        // File `count` is never present, so including it is missing.
        files.push(Vec::new());
        let present: Vec<bool> = (0..=count).map(|index| index < count).collect();
        let mut reached = vec![0];
        let expected = reference(&files, &present, 0, &mut vec![0], &mut reached);
        // Seal reached files first, in reach order, then the rest.
        let mut order = reached.clone();
        order.extend((0..count).filter(|index| !reached.contains(index)));
        let bundle = Bundle {
            files: order
                .iter()
                .map(|&index| BundleFile {
                    key: Key {
                        root: Root::Base,
                        path: vec![if index == 0 {
                            "input".to_owned()
                        } else {
                            format!("f{index}.ax")
                        }],
                    },
                    bytes: render(&files[index]).into_bytes(),
                })
                .collect(),
        };
        // Include of file 0 by name targets f0.ax, which is absent; rewrite.
        let bundle = Bundle {
            files: bundle
                .files
                .into_iter()
                .map(|file| BundleFile {
                    bytes: String::from_utf8(file.bytes)
                        .unwrap()
                        .replace("'f0.ax'", "'input'")
                        .into_bytes(),
                    key: file.key,
                })
                .collect(),
        };
        let actual = expand(&bundle, &Limits::default());
        let label = match (&expected, &actual) {
            (Ok(items), Ok(value)) => {
                if reached.len() == count {
                    let got: Vec<(usize, usize)> = value
                        .sources
                        .iter()
                        .map(|source| match source {
                            Source::File {
                                file, statement, ..
                            } => (order[*file], *statement),
                            Source::DistinctPair { .. } => unreachable!(),
                        })
                        .collect();
                    assert_eq!(&got, items);
                    "ok".to_owned()
                } else {
                    panic!("unreached files must make the bundle invalid");
                }
            }
            (Ok(_), Err(error)) => {
                assert!(reached.len() < count, "{error:?}");
                assert_eq!(error.reason, Reason::BundleShape);
                "shape".to_owned()
            }
            (Err(reason), Err(error)) => {
                assert_eq!(*reason, error.reason, "{files:?}");
                format!("{reason:?}")
            }
            (Err(reason), Ok(_)) => panic!("expected {reason:?} for {files:?}"),
        };
        *outcomes.entry(label).or_default() += 1;
    }
    for label in [
        "ok",
        "shape",
        "Cycle",
        "Missing",
        "SelectionMissing",
        "SelectionAmbiguous",
    ] {
        assert!(
            outcomes.get(label).copied().unwrap_or(0) > 20,
            "{outcomes:?}"
        );
    }
}

#[test]
fn byte_mutations_never_panic_and_are_deterministic() {
    let seed = b"% s\ninclude('input',[zz]).fof(a,axiom,![X]:(p(X,\"o\") <=> X = 'q'),file(f,a),[1.5,\"d\",$fof(p)]).\ncnf(b,axiom,~p(Y,\"o2\") | $true,inference(r,[],[a])).";
    let mut random = Random(77);
    for round in 0..20_000 {
        let mut bytes = seed.to_vec();
        for _ in 0..1 + round % 3 {
            let position = random.below(bytes.len());
            bytes[position] = random.below(256) as u8;
        }
        let bundle = Bundle::single(bytes.clone());
        let first = expand(&bundle, &Limits::default());
        let second = expand(&bundle, &Limits::default());
        assert_eq!(format!("{first:?}"), format!("{second:?}"));
        if let Ok(value) = first {
            for declaration in &value.parsed.declarations {
                assert!(declaration.bytes.end <= bytes.len());
                assert!(declaration.body_bytes.end <= declaration.bytes.end);
            }
        }
    }
}

fn hex(bytes: [u8; 32]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

#[test]
fn sha256_matches_fips_vectors() {
    assert_eq!(
        hex(sha256(b"")),
        "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
    );
    assert_eq!(
        hex(sha256(b"abc")),
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    );
    assert_eq!(
        hex(sha256(
            b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
        )),
        "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
    );
    assert_eq!(
        hex(sha256(&[b'a'; 1_000_000])),
        "cdc76e5c9914fb9281a1c7e284d73e67f1809a48a497200e046d39ccc7112cd0"
    );
}
