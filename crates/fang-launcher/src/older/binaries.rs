// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The binaries an older-profile run may execute, verified as the version-8 path verifies its own (INTEGRATION.md,
//! per-run hashing): each by the chunked SHA-256 of its pin, hashed in background threads from the moment the run
//! knows its route, each waited for before its first execution, and every one hashed checked for its identity
//! before a positive status. A binary the run does not execute is not hashed.
//!
//! The launcher is checked under the path it runs from against the launcher's pin. Failures carry the profile's
//! own texts (installation.py's or capability.py's), chosen by the binary's name.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use fang_supervisor::Fault;

use crate::capability::Pin;
use crate::v8::verify::{Messages, Verifier};

/// The Verifier reports the path; `Binaries` turns it into the profile's text.
const PATHS: Messages = Messages {
    changed: |path| path.display().to_string(),
    unpinned: |path| path.display().to_string(),
    executed_changed: |path| path.to_string(),
};

/// The pinned binaries of one run.
pub struct Binaries {
    verifier: Verifier,
    paths: BTreeMap<&'static str, PathBuf>,
    refusal: fn(&str) -> Fault,
}

impl Binaries {
    /// `pins` names every binary the configuration pins; `launcher` is checked under the running path.
    /// `refusal` gives the profile's failure for a binary's name.
    pub fn new(
        pins: Vec<(&'static str, Pin)>,
        refusal: fn(&str) -> Fault,
    ) -> Result<Binaries, Fault> {
        let running = std::env::current_exe().map_err(Fault::Os)?;
        let mut paths = BTreeMap::new();
        let mut verified = Vec::new();
        for (name, mut pin) in pins {
            if name == "launcher" {
                pin.path = running.clone();
            }
            paths.insert(name, pin.path.clone());
            verified.push(pin);
        }
        Ok(Binaries {
            verifier: Verifier::new(verified, PATHS),
            paths,
            refusal,
        })
    }

    fn paths(&self, names: &[&str]) -> Vec<PathBuf> {
        names
            .iter()
            .filter_map(|name| self.paths.get(name).cloned())
            .collect()
    }

    fn translate(&self, fault: Fault) -> Fault {
        match &fault {
            Fault::Value(text) => match self
                .paths
                .iter()
                .find(|(_, path)| path.display().to_string() == *text)
            {
                Some((name, _)) => (self.refusal)(name),
                None => fault,
            },
            _ => fault,
        }
    }

    /// Start hashing the named binaries in background threads.
    pub fn start(&mut self, names: &[&str]) {
        let paths = self.paths(names);
        let paths: Vec<&Path> = paths.iter().map(PathBuf::as_path).collect();
        self.verifier.start(&paths);
    }

    /// Before the first execution of the named binaries: wait for their hashes, which must match their pins.
    pub fn verify(&mut self, names: &[&str]) -> Result<(), Fault> {
        self.verify_checked(names, &mut || Ok(()))
    }

    /// The per-run variant also checks the command's deadline and cancellation while waiting.
    pub fn verify_checked(
        &mut self,
        names: &[&str],
        check: &mut dyn FnMut() -> Result<(), Fault>,
    ) -> Result<(), Fault> {
        let paths = self.paths(names);
        let paths: Vec<&Path> = paths.iter().map(PathBuf::as_path).collect();
        self.verifier
            .verify_checked(&paths, check)
            .map_err(|fault| self.translate(fault))
    }

    /// Before a positive status: every binary verified in this run is still the same file, unmodified.
    pub fn check_identities(&self) -> Result<(), Fault> {
        self.verifier
            .check_identities()
            .map_err(|fault| self.translate(fault))
    }

    /// The paths verified so far, sorted, for the run record's `verified_before_run`.
    pub fn listed(&self) -> Vec<String> {
        self.verifier.listed()
    }

    /// The path a binary is executed from.
    pub fn path(&self, name: &str) -> PathBuf {
        self.paths.get(name).cloned().unwrap_or_default()
    }
}
