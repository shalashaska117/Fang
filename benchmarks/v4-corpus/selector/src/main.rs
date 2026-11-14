// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
#![forbid(unsafe_code)]
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::Path;

const SEED: &str = "fang-v4-corpus-20261114-v1";

fn problem(name: &str) -> Option<(&str, &'static str)> {
    let bytes = name.as_bytes();
    if bytes.len() < 8 || !bytes[..3].iter().all(u8::is_ascii_uppercase) || !name.ends_with(".p") {
        return None;
    }
    let end = 3 + bytes[3..].iter().take_while(|c| c.is_ascii_digit()).count();
    if end < 6 {
        return None;
    }
    let kind = match bytes.get(end)? {
        b'+' => "fof",
        b'-' => "cnf",
        _ => return None,
    };
    if !bytes[end + 1..bytes.len() - 2]
        .iter()
        .all(|c| c.is_ascii_digit() || *c == b'.')
    {
        return None;
    }
    Some((&name[..end], kind))
}

fn digest(tag: &str, text: &str) -> String {
    fang_hash::sha256_hex(format!("{SEED}\0{tag}\0{text}").as_bytes())
}

fn exclusions(text: &str) -> Result<BTreeSet<String>, String> {
    let mut families = BTreeSet::new();
    let mut occurrences = 0;
    let mut tptp_occurrences = 0;
    let mut ids = BTreeSet::new();
    for line in text.lines() {
        let fields: Vec<_> = line.split('\t').collect();
        if fields.len() != 12 || fields[0].parse::<usize>().is_err() {
            continue;
        }
        occurrences += 1;
        if fields[5] != "-" {
            let (family, _) = problem(fields[5]).ok_or("Invalid historical filename")?;
            tptp_occurrences += 1;
            families.insert(family.to_owned());
            ids.insert(fields[5]);
        }
    }
    if (occurrences, tptp_occurrences, ids.len()) != (1536, 1361, 1346) {
        return Err(format!(
            "Historical membership mismatch: {occurrences}/{tptp_occurrences}/{}",
            ids.len()
        ));
    }
    // Explicit unresolved V4 search targets from the existing plan.
    for name in ["CSR114", "CSR116", "HWV116", "COM146", "COM123", "CSR239"] {
        families.insert(name.to_owned());
    }
    Ok(families)
}

fn select(
    members: &str,
    excluded: &BTreeSet<String>,
) -> Result<[Vec<(String, String)>; 3], String> {
    let mut families = BTreeMap::<String, (String, String)>::new();
    let mut unique = BTreeSet::new();
    for member in members.lines() {
        if !member.starts_with("TPTP-v9.3.1/Problems/") || !unique.insert(member) {
            continue;
        }
        let parts: Vec<_> = member.split('/').collect();
        if parts.len() != 4 {
            continue;
        }
        let Some((family, _)) = problem(parts[3]) else {
            continue;
        };
        if parts[2] != &family[..3] || excluded.contains(family) {
            continue;
        }
        let rank = digest("representative", member);
        let entry = families
            .entry(family.to_owned())
            .or_insert_with(|| (rank.clone(), member.to_owned()));
        if (&rank, member) < (&entry.0, entry.1.as_str()) {
            *entry = (rank, member.to_owned());
        }
    }
    let mut pools: [Vec<(String, String, String)>; 3] = Default::default();
    for (family, (_, member)) in families {
        let hash = digest("partition", &family);
        let bucket = u8::from_str_radix(&hash[..2], 16).map_err(|e| e.to_string())? % 8;
        let partition = match bucket {
            0..=3 => 0,
            4 => 1,
            _ => 2,
        };
        pools[partition].push((digest("rank", &family), family, member));
    }
    let mut selected: [Vec<(String, String)>; 3] = Default::default();
    for (index, count) in [256, 64, 256].into_iter().enumerate() {
        pools[index].sort();
        if pools[index].len() < count {
            return Err(format!(
                "Insufficient families in partition {index}: {}",
                pools[index].len()
            ));
        }
        selected[index] = pools[index]
            .iter()
            .take(count)
            .map(|(_, family, member)| (family.clone(), member.clone()))
            .collect();
    }
    Ok(selected)
}

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.len() != 3 {
        return Err("expected archive-members historical-list output-directory".into());
    }
    let members = fs::read_to_string(&args[0])?;
    let historical = fs::read_to_string(&args[1])?;
    let excluded = exclusions(&historical)?;
    let selected = select(&members, &excluded)?;
    let out = Path::new(&args[2]);
    fs::create_dir(out)?;
    let mut used = BTreeSet::new();
    let mut extract = String::new();
    let mut totals = String::from("partition\tcases\tcnf\tfof\n");
    for (name, entries) in ["train", "validation", "heldout"]
        .into_iter()
        .zip(&selected)
    {
        let mut manifest = String::from("family\tfilename\tkind\tarchive_member\n");
        let mut plain = String::new();
        let mut cnf = 0;
        for (family, member) in entries {
            if excluded.contains(family) || !used.insert(family) {
                return Err("Partition overlap".into());
            }
            let filename = member.rsplit('/').next().ok_or("Missing filename")?;
            let (_, kind) = problem(filename).ok_or("Invalid selection")?;
            cnf += usize::from(kind == "cnf");
            manifest.push_str(&format!("{family}\t{filename}\t{kind}\t{member}\n"));
            plain.push_str(&format!("{filename}\n"));
            extract.push_str(&format!("{member}\n"));
        }
        fs::write(out.join(format!("{name}.tsv")), manifest)?;
        fs::write(out.join(format!("{name}.txt")), plain)?;
        totals.push_str(&format!(
            "{name}\t{}\t{cnf}\t{}\n",
            entries.len(),
            entries.len() - cnf
        ));
    }
    // Include all axiom files in the extraction request. Each problem's actual
    // transitive include closure will be recorded before training or evaluation.
    let axioms: BTreeSet<_> = members
        .lines()
        .filter(|m| {
            m.starts_with("TPTP-v9.3.1/Axioms/")
                && m.ends_with(".ax")
                && !m.contains("..")
                && !m.contains('\t')
        })
        .collect();
    for member in axioms {
        extract.push_str(&format!("{member}\n"));
    }
    fs::write(out.join("extract-members.txt"), extract)?;
    fs::write(
        out.join("excluded-families.txt"),
        excluded
            .into_iter()
            .map(|f| format!("{f}\n"))
            .collect::<String>(),
    )?;
    fs::write(out.join("totals.tsv"), &totals)?;
    println!("{totals}");
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn variants_share_a_family_and_typed_names_are_excluded() {
        assert_eq!(problem("CSR114+13.p"), Some(("CSR114", "fof")));
        assert_eq!(problem("CSR114-2.004.p"), Some(("CSR114", "cnf")));
        assert_eq!(problem("SYN1234-1.p"), Some(("SYN1234", "cnf")));
        for name in [
            "ITP211^3.p",
            "ITP234_4.p",
            "../../CSR114-1.p",
            "CSR11-1.p",
            "CSR114-1.ax",
        ] {
            assert_eq!(problem(name), None);
        }
    }

    #[test]
    fn membership_is_independent_of_tar_order_and_excludes_known_families() {
        let members: Vec<_> = (0..4000)
            .flat_map(|n| {
                [
                    format!("TPTP-v9.3.1/Problems/SYN/SYN{n:04}-1.p"),
                    format!("TPTP-v9.3.1/Problems/SYN/SYN{n:04}+2.p"),
                ]
            })
            .collect();
        let excluded: BTreeSet<_> = (0..1000).map(|n| format!("SYN{n:04}")).collect();
        let first = select(&members.join("\n"), &excluded).unwrap();
        let second = select(
            &members.into_iter().rev().collect::<Vec<_>>().join("\n"),
            &excluded,
        )
        .unwrap();
        assert_eq!(first, second);
        let mut families = BTreeSet::new();
        for pool in first {
            for (family, _) in pool {
                assert!(!excluded.contains(&family));
                assert!(families.insert(family));
            }
        }
        assert_eq!(families.len(), 576);
        assert!(select("", &excluded).is_err());
    }
}
