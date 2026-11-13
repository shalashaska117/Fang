// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Diagnostic candidate transport. Exit 0 never means an independently checked result.
#![forbid(unsafe_code)]

//! Candidate producer for signed role tasks over a sealed bundle. Bundle files come as ROOT PATH FILE triples, top-level file first, as the bundle checker reads them. `--goals` lists the selected conjectures with their bundle items; `--goal N` and `--inputs` select a task as the checker does. With `--render` the prepared task is printed instead of searched; `--skolem-symbols` sets the Skolem symbol budget for agreement controls. With `--cite F:S,...` the task keeps only the cited bundle items and the selected goal, and a candidate is printed after its premise line `(premises (item F S) ...)`; an empty list after `--cite` cites nothing. Exit 0 means a list, a render or a candidate certificate, 2 Unknown, 1 a typed error; none of these is a checked result.

use fang_tptp_coverage_candidate::Root;
use fang_tptp_signed_bundle::{
    error_kind, flatten, premise_line, prepare_bundle_task, prepare_cited_task,
    produce_bundle_task, produce_cited_task, sealed,
};
use fang_tptp_signed_roles::{Limits, Outcome, Selection, render};
use std::io::{Read, Write};
use std::process::ExitCode;

const USAGE: &str = "usage: signed-bundle-produce [--render] [--skolem-symbols N] [--cite F:S,...] (--goal N | --inputs | --goals) ROOT PATH FILE [ROOT PATH FILE]...";
const FILE_BYTES: u64 = 1024 * 1024;

enum Mode {
    Goals,
    Task(Selection),
}

fn usage() -> ExitCode {
    eprintln!("{USAGE}");
    ExitCode::from(64)
}

fn read_files(arguments: &[String]) -> Result<Vec<(Root, String, Vec<u8>)>, ExitCode> {
    if arguments.is_empty() || !arguments.len().is_multiple_of(3) {
        return Err(usage());
    }
    let mut files = Vec::new();
    for triple in arguments.chunks(3) {
        let root = match triple[0].as_str() {
            "base" => Root::Base,
            "tptp" => Root::Tptp,
            _ => return Err(usage()),
        };
        let mut bytes = Vec::new();
        let read = std::fs::File::open(&triple[2])
            .and_then(|file| file.take(FILE_BYTES + 1).read_to_end(&mut bytes));
        if read.is_err() {
            eprintln!("io: bundle file read failed");
            return Err(ExitCode::from(74));
        }
        if bytes.len() as u64 > FILE_BYTES {
            eprintln!("error: resource bundle file");
            return Err(ExitCode::from(1));
        }
        files.push((root, triple[1].clone(), bytes));
    }
    Ok(files)
}

/// Bundle items written `F:S`, separated by commas; the empty string is the empty list.
fn parse_items(text: &str) -> Option<Vec<(usize, usize)>> {
    if text.is_empty() {
        return Some(Vec::new());
    }
    text.split(',')
        .map(|item| {
            let (file, statement) = item.split_once(':')?;
            Some((file.parse().ok()?, statement.parse().ok()?))
        })
        .collect()
}

fn main() -> ExitCode {
    let mut arguments: Vec<String> = std::env::args().skip(1).collect();
    let render_only = arguments.first().is_some_and(|flag| flag == "--render");
    if render_only {
        arguments.remove(0);
    }
    let mut limits = Limits::default();
    if arguments
        .first()
        .is_some_and(|flag| flag == "--skolem-symbols")
    {
        match arguments.get(1).map(|value| value.parse()) {
            Some(Ok(count)) => limits.skolem.max_skolem_symbols = count,
            _ => return usage(),
        }
        arguments.drain(..2);
    }
    let mut cited = None;
    if arguments.first().is_some_and(|flag| flag == "--cite") {
        match arguments.get(1).map(|value| parse_items(value)) {
            Some(Some(items)) => cited = Some(items),
            _ => return usage(),
        }
        arguments.drain(..2);
    }
    let (mode, rest) = match arguments.as_slice() {
        [flag, rest @ ..] if flag == "--goals" => (Mode::Goals, rest),
        [flag, rest @ ..] if flag == "--inputs" => (Mode::Task(Selection::Inputs), rest),
        [flag, value, rest @ ..] if flag == "--goal" => match value.parse() {
            Ok(index) => (Mode::Task(Selection::Goal(index)), rest),
            Err(_) => return usage(),
        },
        _ => return usage(),
    };
    let files = match read_files(rest) {
        Ok(files) => files,
        Err(code) => return code,
    };
    let bundle = sealed(files);
    let mut stdout = std::io::stdout().lock();
    let written = match mode {
        Mode::Goals if cited.is_some() => return usage(),
        Mode::Goals => match flatten(&bundle, &limits) {
            Ok(flat) => {
                let mut text = format!("goals {}\n", flat.goals.len());
                for (index, (file, statement)) in flat.goals.iter().enumerate() {
                    text.push_str(&format!("goal {index} item {file} {statement}\n"));
                }
                stdout.write_all(text.as_bytes())
            }
            Err(error) => {
                eprintln!("error: {} {error:?}", error_kind(&error));
                return ExitCode::from(1);
            }
        },
        Mode::Task(selection) if render_only => {
            let prepared = match &cited {
                Some(items) => prepare_cited_task(&bundle, selection, items, &limits)
                    .map(|(_, _, prepared)| prepared),
                None => {
                    prepare_bundle_task(&bundle, selection, &limits).map(|(_, prepared)| prepared)
                }
            };
            match prepared {
                Ok(prepared) => stdout.write_all(render(&prepared).as_bytes()),
                Err(error) => {
                    eprintln!("error: {} {error:?}", error_kind(&error));
                    return ExitCode::from(1);
                }
            }
        }
        Mode::Task(selection) => {
            let produced = match &cited {
                Some(items) => produce_cited_task(&bundle, selection, items, &limits)
                    .map(|(citations, _, produced)| (Some(premise_line(&citations)), produced)),
                None => produce_bundle_task(&bundle, selection, &limits)
                    .map(|(_, produced)| (None, produced)),
            };
            match produced {
                Ok((line, produced)) => match produced.outcome {
                    Outcome::CandidateRefutation { text, .. } => {
                        eprintln!("candidate-certificate: unchecked signed bundle task");
                        match line {
                            Some(line) => stdout
                                .write_all(line.as_bytes())
                                .and_then(|()| stdout.write_all(b"\n"))
                                .and_then(|()| stdout.write_all(text.as_bytes())),
                            None => stdout.write_all(text.as_bytes()),
                        }
                    }
                    Outcome::Unknown(statistics) => {
                        eprintln!(
                            "unknown: processed={} attempted={}",
                            statistics.processed_clauses, statistics.attempted_inferences
                        );
                        return ExitCode::from(2);
                    }
                },
                Err(error) => {
                    eprintln!("error: {} {error:?}", error_kind(&error));
                    return ExitCode::from(1);
                }
            }
        }
    };
    if written.is_err() {
        eprintln!("io: output failed");
        return ExitCode::from(74);
    }
    ExitCode::SUCCESS
}
