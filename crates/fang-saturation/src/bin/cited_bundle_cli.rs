// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Test driver only. These fixture limits are not the final product record.
#[path = "../experimental/cited_bundle_cli.rs"]
mod cli;

fn main() -> std::process::ExitCode {
    let started = std::time::Instant::now();
    let mut replay = fang_tptp_signed_roles::Limits::default();
    if let Ok(value) = std::env::var("FANG_TEST_REPLAY_PREDICATES") {
        replay.max_predicates = value.parse().expect("test predicate cap");
    }
    let cap = std::env::var("FANG_TEST_CERTIFICATE_BYTES")
        .ok()
        .map(|value| value.parse().expect("test certificate cap"))
        .unwrap_or(1 << 20);
    let config = cli::ReplayConfig {
        discovery_limits: fang_tptp_signed_roles::Limits::default(),
        replay_limits: replay,
        naming_threshold: 8,
        certificate_bytes: cap,
    };
    cli::run_with_limits(std::env::args().skip(1).collect(), started, &config)
}
