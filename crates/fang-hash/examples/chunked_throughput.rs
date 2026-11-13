// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Throughput of hash_file and of the chunked digest over a set of files, to fix CHUNK_BYTES and
//! THREAD_CAP. A measurement tool; it does not ship.
//!
//! Usage: chunked_throughput LIST REPETITIONS [CHUNK_MIB,...] [THREADS,...]
//! LIST holds one absolute path per line. One plain pass runs first and is reported as the first
//! read. Every configuration then hashes the whole set REPETITIONS times; the median and the best
//! wall time give MiB/s. The digests of one chunk size must agree across thread counts.

use std::path::PathBuf;
use std::time::Instant;

use fang_hash::{hash_file, hash_file_chunked_sized};

fn numbers(text: Option<&String>, default: &[u64]) -> Vec<u64> {
    text.map_or_else(
        || default.to_vec(),
        |text| {
            text.split(',')
                .map(|item| item.parse().expect("number"))
                .collect()
        },
    )
}

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let list = std::fs::read_to_string(&arguments[0]).expect("list");
    let files: Vec<PathBuf> = list
        .lines()
        .filter(|line| !line.is_empty())
        .map(PathBuf::from)
        .collect();
    let repetitions: usize = arguments[1].parse().expect("repetitions");
    let chunks = numbers(arguments.get(2), &[1, 2, 4, 8, 16]);
    let threads = numbers(arguments.get(3), &[1, 2, 4, 6, 8, 12, 16]);
    let total: u64 = files
        .iter()
        .map(|path| std::fs::metadata(path).expect("file").len())
        .sum();
    let mib = total as f64 / f64::from(1 << 20);
    let load = std::fs::read_to_string("/proc/loadavg").unwrap_or_default();
    println!(
        "files\t{}\tbytes\t{total}\tMiB\t{mib:.1}\tloadavg\t{}",
        files.len(),
        load.trim()
    );
    let mut no_check = || Ok::<(), ()>(());
    let plain = |no_check: &mut dyn FnMut() -> Result<(), ()>| {
        for path in &files {
            hash_file(path, u64::MAX, no_check).expect("hash");
        }
    };
    let started = Instant::now();
    plain(&mut no_check);
    let first = started.elapsed().as_secs_f64();
    println!(
        "first-read\tplain\t1\t{first:.3}s\t{:.0} MiB/s",
        mib / first
    );
    let report = |name: &str, chunk: u64, thread_count: u64, times: &mut Vec<f64>| {
        times.sort_by(f64::total_cmp);
        let median = times[times.len() / 2];
        let best = times[0];
        println!(
            "{name}\t{chunk}\t{thread_count}\tmedian {median:.3}s\t{:.0} MiB/s\tbest {best:.3}s\t{:.0} MiB/s",
            mib / median,
            mib / best
        );
    };
    let mut times = Vec::new();
    for _ in 0..repetitions {
        let started = Instant::now();
        plain(&mut no_check);
        times.push(started.elapsed().as_secs_f64());
    }
    report("plain", 0, 1, &mut times);
    for chunk in &chunks {
        let mut digests: Option<Vec<String>> = None;
        for thread_count in &threads {
            let mut times = Vec::new();
            for _ in 0..repetitions {
                let started = Instant::now();
                let found: Vec<String> = files
                    .iter()
                    .map(|path| {
                        hash_file_chunked_sized(
                            path,
                            u64::MAX,
                            usize::try_from(*thread_count).expect("threads"),
                            chunk << 20,
                            &mut no_check,
                        )
                        .expect("chunked hash")
                        .0
                    })
                    .collect();
                times.push(started.elapsed().as_secs_f64());
                match &digests {
                    None => digests = Some(found),
                    Some(earlier) => assert_eq!(earlier, &found, "digests differ across runs"),
                }
            }
            report("chunked", *chunk, *thread_count, &mut times);
        }
    }
}
