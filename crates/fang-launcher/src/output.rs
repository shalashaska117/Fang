// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Delivery to the caller that never waits past a deadline.
//!
//! A writer thread writes the bytes to standard output or standard error while the calling thread waits with a
//! timeout. If the deadline passes first, the caller is told so and the run records an incomplete delivery; the
//! blocked writer ends with the process.

use std::io::Write;
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

use fang_supervisor::{Failure, Status};

/// How often cancellation is looked at while the write is pending.
const POLL: Duration = Duration::from_millis(50);

/// Where the bytes go.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Stream {
    Stdout,
    Stderr,
}

/// The outcome of one delivery.
#[derive(Debug)]
pub enum Delivery {
    /// Every byte was written and flushed.
    Written,
    /// The deadline passed before the caller accepted every byte.
    DeadlinePassed,
    /// The write failed, for example on a closed pipe.
    Failed(std::io::Error),
}

/// Write `data` to `stream` before `deadline`. `cancelled`, when given, is looked at every 50 ms; a cancellation
/// gives Forced "External cancellation" at stage status-output.
pub fn emit(
    stream: Stream,
    data: Vec<u8>,
    deadline: Instant,
    cancelled: Option<&dyn Fn() -> bool>,
) -> Result<Delivery, Failure> {
    let write = move || match stream {
        Stream::Stdout => {
            let mut out = std::io::stdout().lock();
            out.write_all(&data).and_then(|()| out.flush())
        }
        Stream::Stderr => {
            let mut out = std::io::stderr().lock();
            out.write_all(&data).and_then(|()| out.flush())
        }
    };
    deliver(write, deadline, cancelled)
}

/// Run `write` on a writer thread and wait for it until `deadline`, looking at `cancelled` meanwhile.
fn deliver(
    write: impl FnOnce() -> std::io::Result<()> + Send + 'static,
    deadline: Instant,
    cancelled: Option<&dyn Fn() -> bool>,
) -> Result<Delivery, Failure> {
    let (sender, receiver) = mpsc::channel();
    thread::spawn(move || {
        let _ = sender.send(write());
    });
    loop {
        if let Some(cancelled) = cancelled
            && cancelled()
        {
            return Err(Failure {
                status: Status::Forced,
                reason: "External cancellation".to_string(),
                stage: "status-output".to_string(),
            });
        }
        let now = Instant::now();
        if now >= deadline {
            return Ok(Delivery::DeadlinePassed);
        }
        match receiver.recv_timeout(POLL.min(deadline - now)) {
            Ok(Ok(())) => return Ok(Delivery::Written),
            Ok(Err(error)) => return Ok(Delivery::Failed(error)),
            Err(mpsc::RecvTimeoutError::Timeout) => continue,
            Err(mpsc::RecvTimeoutError::Disconnected) => {
                return Ok(Delivery::Failed(std::io::Error::other(
                    "status writer stopped",
                )));
            }
        }
    }
}

/// The status block on standard output: `emit(Stream::Stdout, ...)`.
pub fn emit_status(
    data: Vec<u8>,
    deadline: Instant,
    cancelled: Option<&dyn Fn() -> bool>,
) -> Result<Delivery, Failure> {
    emit(Stream::Stdout, data, deadline, cancelled)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A pipe whose buffer a thread has filled and that nobody reads.
    fn full_pipe() -> (std::io::PipeReader, std::io::PipeWriter) {
        let (reader, writer) = std::io::pipe().unwrap();
        let mut filler = writer.try_clone().unwrap();
        thread::spawn(move || while filler.write_all(&[b'x'; 4096]).is_ok() {});
        thread::sleep(Duration::from_millis(200));
        (reader, writer)
    }

    /// test_fang_szs ProtocolTests.test_blocked_status_output_is_bounded.
    #[test]
    fn blocked_status_output_is_bounded() {
        let (_reader, mut writer) = full_pipe();
        let started = Instant::now();
        let data = b"% SZS status Error for fang_control\n".to_vec();
        let outcome = deliver(
            move || writer.write_all(&data).and_then(|()| writer.flush()),
            Instant::now() + Duration::from_millis(30),
            None,
        );
        assert!(matches!(outcome, Ok(Delivery::DeadlinePassed)));
        assert!(started.elapsed() < Duration::from_secs(2));
    }

    #[test]
    fn a_closed_reader_is_a_failed_delivery_and_cancellation_is_forced() {
        let (reader, mut writer) = std::io::pipe().unwrap();
        drop(reader);
        let outcome = deliver(
            move || writer.write_all(b"x\n"),
            Instant::now() + Duration::from_secs(5),
            None,
        );
        assert!(matches!(outcome, Ok(Delivery::Failed(_))));
        let (_reader, mut writer) = full_pipe();
        let cancelled = || true;
        let outcome = deliver(
            move || writer.write_all(b"x\n"),
            Instant::now() + Duration::from_secs(5),
            Some(&cancelled),
        );
        let failure = outcome.unwrap_err();
        assert_eq!(
            (failure.status, failure.stage.as_str()),
            (Status::Forced, "status-output")
        );
    }
}
