// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Experimental final-record driver. The existing producer proof cap still applies.
#[path = "../experimental/cited_bundle_cli.rs"]
mod cli;
#[path = "../experimental/final_limits.rs"]
mod final_limits;

fn main() -> std::process::ExitCode {
    let started = std::time::Instant::now();
    let limits = final_limits::replay_limits();
    let config = cli::ReplayConfig {
        discovery_limits: limits.clone(),
        replay_limits: limits,
        naming_threshold: final_limits::NAMING_THRESHOLD,
        certificate_bytes: final_limits::CERTIFICATE_BYTES,
    };
    cli::run_with_limits(std::env::args().skip(1).collect(), started, &config)
}
