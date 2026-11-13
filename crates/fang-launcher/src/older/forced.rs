// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The Forced path of the older profiles. Python's adapters caught SIGINT and SIGTERM and recorded Forced on
//! their main path; the launcher runs as the guard's worker, whose watcher thread runs a hook once the caller's
//! process is gone. The main path publishes its latest record here, and the hook writes the Forced record and
//! the status line from it, at most once and never after the main path has finalized.

use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex, MutexGuard};
use std::time::{Duration, Instant};

use fang_json::{Object, Value};
use fang_supervisor::Supervisor;
use fang_supervisor::guard::Worker;

use crate::output::Delivery;

/// What the main path last published.
pub struct Shared {
    pub manifest: Object,
    /// The run directory, once this invocation created it.
    pub root: Option<PathBuf>,
    /// The supervisor's stage records, as the run record lists them.
    pub processes: Value,
    pub peak_kib: Option<u64>,
}

/// The handle both paths share.
#[derive(Clone)]
pub struct Published(Arc<Mutex<Shared>>);

fn lock(shared: &Mutex<Shared>) -> MutexGuard<'_, Shared> {
    shared
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

/// The supervisor's records as the run record's `processes` list.
pub fn processes(supervisor: &Supervisor) -> Value {
    Value::Array(
        supervisor
            .records
            .iter()
            .map(|record| record.to_json())
            .collect(),
    )
}

impl Published {
    pub fn new(manifest: &Object) -> Published {
        Published(Arc::new(Mutex::new(Shared {
            manifest: manifest.clone(),
            root: None,
            processes: Value::Array(Vec::new()),
            peak_kib: None,
        })))
    }

    /// Publish the current record and, when there is one, the supervisor's records.
    pub fn publish(&self, manifest: &Object, supervisor: Option<&Supervisor>) {
        let mut state = lock(&self.0);
        state.manifest = manifest.clone();
        if let Some(supervisor) = supervisor {
            state.processes = processes(supervisor);
            state.peak_kib = Some(supervisor.peak_kib);
        }
    }

    /// Record that this invocation owns `root`, so the Forced record may be written there.
    pub fn own(&self, root: &Path) {
        lock(&self.0).root = Some(root.to_path_buf());
    }

    /// Install the Forced path. `forced` turns the published state into the Forced record and its status
    /// output; `delivered` records the outcome of writing that output (true when every byte was written).
    pub fn on_parent_death(
        &self,
        worker: &Worker,
        forced: impl Fn(&Shared) -> (Object, Vec<u8>) + Send + 'static,
        delivered: impl Fn(&mut Object, &[u8], bool) + Send + 'static,
    ) {
        let shared = Arc::clone(&self.0);
        worker.on_parent_death(move || {
            let state = lock(&shared);
            let (mut manifest, output) = forced(&state);
            let path = state.root.as_ref().map(|root| root.join("manifest.json"));
            if let Some(path) = &path {
                let _ = fang_supervisor::write_json(path, &Value::Object(manifest.clone()));
            }
            let written = matches!(
                crate::output::emit_status(
                    output.clone(),
                    Instant::now() + Duration::from_millis(150),
                    None
                ),
                Ok(Delivery::Written)
            );
            delivered(&mut manifest, &output, written);
            if let Some(path) = &path {
                let _ = fang_supervisor::write_json(path, &Value::Object(manifest));
            }
        });
    }
}
