// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.

/// The statuses of supervisor.EXIT with their exit codes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Status {
    Unsatisfiable,
    GaveUp,
    Unknown,
    InputError,
    Inappropriate,
    ResourceOut,
    Error,
    Timeout,
    MemoryOut,
    Forced,
}

impl Status {
    pub const ALL: [Status; 10] = [
        Status::Unsatisfiable,
        Status::GaveUp,
        Status::Unknown,
        Status::InputError,
        Status::Inappropriate,
        Status::ResourceOut,
        Status::Error,
        Status::Timeout,
        Status::MemoryOut,
        Status::Forced,
    ];

    pub fn exit_code(self) -> i32 {
        match self {
            Status::Unsatisfiable => 0,
            Status::GaveUp | Status::Unknown => 2,
            Status::InputError => 3,
            Status::Inappropriate => 4,
            Status::ResourceOut => 5,
            Status::Error => 6,
            Status::Timeout => 7,
            Status::MemoryOut => 8,
            Status::Forced => 9,
        }
    }

    pub fn name(self) -> &'static str {
        match self {
            Status::Unsatisfiable => "Unsatisfiable",
            Status::GaveUp => "GaveUp",
            Status::Unknown => "Unknown",
            Status::InputError => "InputError",
            Status::Inappropriate => "Inappropriate",
            Status::ResourceOut => "ResourceOut",
            Status::Error => "Error",
            Status::Timeout => "Timeout",
            Status::MemoryOut => "MemoryOut",
            Status::Forced => "Forced",
        }
    }

    pub fn from_name(name: &str) -> Option<Status> {
        Status::ALL.into_iter().find(|status| status.name() == name)
    }
}

/// supervisor.Failure: a status, a reason and the stage it happened in.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Failure {
    pub status: Status,
    pub reason: String,
    pub stage: String,
}

impl Failure {
    pub fn new(status: Status, reason: impl Into<String>, stage: impl Into<String>) -> Failure {
        Failure {
            status,
            reason: reason.into(),
            stage: stage.into(),
        }
    }

    /// `Failure(status, reason)` with Python's default stage "adapter".
    pub fn adapter(status: Status, reason: impl Into<String>) -> Failure {
        Failure::new(status, reason, "adapter")
    }
}

impl std::fmt::Display for Failure {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(&self.reason)
    }
}

impl std::error::Error for Failure {}
