// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Kernel mode, entry revision 8.
//!
//! - `entry` and `check`: the kernel entry (`fang-v8-kernel`), revision 7's main.py and check.py;
//! - `generator`: the exact-instance Lean modules for one sealed input, certificate and witness,
//!   revision 7's generator version 4 with its two equality recipes and the mixed emitters, with
//!   the bytes and refusal classes of the Python generator;
//! - `install`, `helpers` and `provision`: `fang-v8-kernel-install`, `fang-v8-kernel-helpers` and
//!   `fang-v8-kernel-provision`;
//! - `trees`: the tree inventory; `launch`: the direct compiler launch; `util`: small shared parts.
#![forbid(unsafe_code)]

pub mod check;
pub mod entry;
pub mod generator;
pub mod helpers;
pub mod install;
pub mod internal;
pub mod launch;
pub mod provision;
pub mod trees;
pub mod util;
