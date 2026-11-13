// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The `fang` command. `dispatch` chooses one profile from the command line only, with no retry and no
//! fallback. The version-8 profile is `v8`; the older CNF and ground-FOF profiles are `profile_cnf` and
//! `profile_ground_fof`. The shared pieces are the argument parser (`cli`), the capability (`capability`),
//! configuration loading (`config`), the run record (`manifest`) and status delivery (`output`).
#![forbid(unsafe_code)]

pub mod capability;
pub mod cli;
pub mod config;
pub mod dispatch;
pub mod manifest;
pub mod older;
pub mod output;
pub mod pattern;
pub mod profile_cnf;
pub mod profile_ground_fof;
pub mod v8;
