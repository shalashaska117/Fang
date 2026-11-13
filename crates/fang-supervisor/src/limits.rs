// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
use fang_json::{Object, Value};

/// The Limits dataclass of supervisor.py, with its defaults.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Limits {
    pub wall_seconds: f64,
    pub memory_mib: u64,
    pub input_bytes: u64,
    pub certificate_bytes: u64,
    pub log_bytes: u64,
    pub artifact_bytes: u64,
    pub poll_seconds: f64,
}

impl Default for Limits {
    fn default() -> Limits {
        Limits {
            wall_seconds: 60.0,
            memory_mib: 2048,
            input_bytes: 1 << 20,
            certificate_bytes: 64 << 20,
            log_bytes: 4 << 20,
            artifact_bytes: 256 << 20,
            poll_seconds: 0.02,
        }
    }
}

impl Limits {
    /// `dataclasses.asdict(limits)`: the two seconds fields as floats, the rest as integers.
    pub fn to_json(&self) -> Value {
        let mut object = Object::new();
        object.set("wall_seconds", self.wall_seconds);
        object.set("memory_mib", self.memory_mib);
        object.set("input_bytes", self.input_bytes);
        object.set("certificate_bytes", self.certificate_bytes);
        object.set("log_bytes", self.log_bytes);
        object.set("artifact_bytes", self.artifact_bytes);
        object.set("poll_seconds", self.poll_seconds);
        Value::Object(object)
    }
}
