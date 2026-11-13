// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! A manifest under construction, shared with the guard's cancellation path.
//!
//! The Python scripts caught SIGTERM and SIGINT in the supervisor, so the next check raised Forced and the
//! script's `except` and `finally` wrote the manifest. Here the guard's watcher thread runs the cancellation
//! hook and then ends the process group, so the hook writes the manifest itself, from the report as it stood
//! after the last completed step, with the same status and error text.

use std::path::PathBuf;
use std::sync::{Arc, Mutex};

use fang_json::{Object, Value};
use fang_supervisor::guard::Worker;

use crate::common::{utc_now, write_manifest};

/// Python's error text for a cancelled run: `Failure: External cancellation`.
pub const CANCELLED: &str = "Failure: External cancellation";

#[derive(Clone, Default)]
pub struct Report {
    inner: Arc<Mutex<Object>>,
}

impl Report {
    pub fn new(pairs: Vec<(&str, Value)>) -> Report {
        Report {
            inner: Arc::new(Mutex::new(pairs.into_iter().collect())),
        }
    }

    fn lock(&self) -> std::sync::MutexGuard<'_, Object> {
        self.inner
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    pub fn set(&self, key: &str, value: impl Into<Value>) {
        self.lock().set(key, value);
    }

    pub fn get(&self, key: &str) -> Option<Value> {
        self.lock().get(key).cloned()
    }

    pub fn value(&self) -> Value {
        Value::Object(self.lock().clone())
    }

    /// Run `edit` on the report under its lock.
    pub fn edit<R>(&self, edit: impl FnOnce(&mut Object) -> R) -> R {
        edit(&mut self.lock())
    }
}

/// Register the cancellation hook: on the parent's death, `status` failed, `error` the cancellation text,
/// `finished_utc` now, and the report written to `path` through `write_json`. `extra` adds any further fields
/// the script's `finally` sets.
pub fn on_cancel(worker: Option<&Worker>, report: &Report, path: PathBuf, extra: fn(&mut Object)) {
    if let Some(worker) = worker {
        let report = report.clone();
        worker.on_parent_death(move || {
            let value = report.edit(|object| {
                object.set("status", "failed");
                object.set("error", CANCELLED);
                extra(object);
                object.set("finished_utc", utc_now());
                Value::Object(object.clone())
            });
            let _ = write_manifest(&path, &value);
        });
    }
}

/// Write the final manifest unless the cancellation path already did.
pub fn finish(worker: Option<&Worker>, write: impl FnOnce()) {
    match worker {
        Some(worker) => {
            worker.finalize(write);
        }
        None => write(),
    }
}
