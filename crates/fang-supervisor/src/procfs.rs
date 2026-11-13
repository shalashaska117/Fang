// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! /proc readers, the system constants from the auxiliary vector, and kills through /bin/kill.

use std::collections::{HashMap, HashSet};
use std::process::{Command, Stdio};
use std::sync::OnceLock;

use crate::status::{Failure, Status};

const AT_PAGESZ: u64 = 6;
const AT_CLKTCK: u64 = 17;

struct Constants {
    page_kib: u64,
    ticks_per_second: u64,
}

fn getconf(name: &str) -> Option<u64> {
    let output = Command::new("getconf")
        .arg(name)
        .stdin(Stdio::null())
        .stderr(Stdio::null())
        .output()
        .ok()?;
    String::from_utf8(output.stdout).ok()?.trim().parse().ok()
}

/// AT_PAGESZ and AT_CLKTCK from /proc/self/auxv, read once; `getconf` if auxv has no entry.
fn constants() -> &'static Constants {
    static CONSTANTS: OnceLock<Constants> = OnceLock::new();
    CONSTANTS.get_or_init(|| {
        let mut page = None;
        let mut ticks = None;
        if let Ok(bytes) = std::fs::read("/proc/self/auxv") {
            for pair in bytes.chunks_exact(16) {
                let key = u64::from_ne_bytes(pair[..8].try_into().expect("eight bytes"));
                let value = u64::from_ne_bytes(pair[8..].try_into().expect("eight bytes"));
                match key {
                    AT_PAGESZ => page = Some(value),
                    AT_CLKTCK => ticks = Some(value),
                    _ => {}
                }
            }
        }
        let page = page.or_else(|| getconf("PAGESIZE")).unwrap_or(4096);
        let ticks = ticks.or_else(|| getconf("CLK_TCK")).unwrap_or(100);
        Constants {
            page_kib: page / 1024,
            ticks_per_second: ticks.max(1),
        }
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Entry {
    pub state: char,
    pub ppid: i32,
    pub group: i32,
    pub start: u64,
    pub rss_kib: u64,
}

impl Entry {
    /// A zombie or dead task holds no memory and runs no code; it waits only to be reaped.
    pub fn alive(&self) -> bool {
        !matches!(self.state, 'Z' | 'X' | 'x')
    }
}

fn fields(text: &str) -> Option<Vec<&str>> {
    let close = text.rfind(')')?;
    Some(text.get(close + 2..)?.split_whitespace().collect())
}

pub(crate) fn entry(pid: i32) -> Option<Entry> {
    let text = std::fs::read_to_string(format!("/proc/{pid}/stat")).ok()?;
    let fields = fields(&text)?;
    Some(Entry {
        state: fields.first()?.chars().next()?,
        ppid: fields.get(1)?.parse().ok()?,
        group: fields.get(2)?.parse().ok()?,
        start: fields.get(19)?.parse().ok()?,
        rss_kib: fields.get(21)?.parse::<u64>().ok()? * constants().page_kib,
    })
}

/// supervisor.process_table: every task in /proc that has not been reaped.
pub(crate) fn process_table() -> HashMap<i32, Entry> {
    let mut table = HashMap::new();
    let Ok(directory) = std::fs::read_dir("/proc") else {
        return table;
    };
    for item in directory.flatten() {
        let name = item.file_name();
        let Some(pid) = name
            .to_str()
            .filter(|name| name.bytes().all(|byte| byte.is_ascii_digit()))
            .and_then(|name| name.parse().ok())
        else {
            continue;
        };
        if let Some(entry) = entry(pid) {
            table.insert(pid, entry);
        }
    }
    table
}

/// Living processes owned through the stage groups: the members of `groups` other than `pid`,
/// and their parent-PID descendants. Processes this process starts outside a stage (helpers it
/// waits for, or another thread's work in a test binary) are not owned.
pub(crate) fn owned(table: &HashMap<i32, Entry>, pid: i32, groups: &[i32]) -> HashSet<i32> {
    let mut owned = owned_unreaped(table, pid, groups);
    owned.retain(|other| table.get(other).is_some_and(Entry::alive));
    owned
}

/// The same view with the zombies not yet reaped, as Python's process_table listed them: the PIDs
/// cleanup records as terminated.
pub(crate) fn owned_unreaped(
    table: &HashMap<i32, Entry>,
    pid: i32,
    groups: &[i32],
) -> HashSet<i32> {
    let mut owned: HashSet<i32> = table
        .iter()
        .filter(|(other, entry)| **other != pid && groups.contains(&entry.group))
        .map(|(other, _)| *other)
        .collect();
    let mut frontier: HashSet<i32> = owned.clone();
    while !frontier.is_empty() {
        let next: HashSet<i32> = table
            .iter()
            .filter(|(other, entry)| {
                frontier.contains(&entry.ppid) && **other != pid && !owned.contains(other)
            })
            .map(|(other, _)| *other)
            .collect();
        owned.extend(next.iter().copied());
        frontier = next;
    }
    owned
}

/// SIGKILL through /bin/kill to the given PIDs, each still the process it was (same start time).
pub(crate) fn kill_verified(targets: &[(i32, u64)]) {
    let pids: Vec<String> = targets
        .iter()
        .filter(|(pid, start)| entry(*pid).is_some_and(|current| current.start == *start))
        .map(|(pid, _)| pid.to_string())
        .collect();
    if pids.is_empty() {
        return;
    }
    let _ = Command::new("/bin/kill")
        .args(["-s", "KILL", "--"])
        .args(&pids)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status();
}

/// SIGKILL through /bin/kill to a whole process group.
pub(crate) fn kill_group(group: i32) -> bool {
    Command::new("/bin/kill")
        .args(["-s", "KILL", "--", &format!("-{group}")])
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|status| status.success())
}

/// The CPU times of this process and of its waited-for children, in seconds.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct Times {
    pub user: f64,
    pub system: f64,
    pub children_user: f64,
    pub children_system: f64,
}

/// utime, stime, cutime and cstime of /proc/self/stat over CLK_TCK, in place of getrusage.
pub fn process_times() -> Result<Times, Failure> {
    let failure = || Failure::adapter(Status::Error, "Cannot read /proc/self/stat");
    let text = std::fs::read_to_string("/proc/self/stat").map_err(|_| failure())?;
    let fields = fields(&text).ok_or_else(failure)?;
    let tick = |index: usize| -> Result<f64, Failure> {
        let value: u64 = fields
            .get(index)
            .and_then(|field| field.parse().ok())
            .ok_or_else(failure)?;
        Ok(value as f64 / constants().ticks_per_second as f64)
    };
    Ok(Times {
        user: tick(11)?,
        system: tick(12)?,
        children_user: tick(13)?,
        children_system: tick(14)?,
    })
}

// O_CLOEXEC as /proc/PID/fdinfo prints it (octal flags); the same value on both architectures.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
const O_CLOEXEC: u32 = 0o2000000;
#[cfg(not(any(target_arch = "x86_64", target_arch = "aarch64")))]
compile_error!("O_CLOEXEC is written down for x86_64 and aarch64 only");

/// A descriptor above 2 that this process holds without close-on-exec, so every child inherits
/// it, with the target /proc/self/fd shows for it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InheritedDescriptor {
    pub fd: i32,
    pub target: String,
}

impl InheritedDescriptor {
    pub fn to_json(&self) -> fang_json::Value {
        let mut object = fang_json::Object::new();
        object.set("fd", self.fd);
        object.set("target", self.target.as_str());
        fang_json::Value::Object(object)
    }
}

/// The descriptors above 2 without close-on-exec, from /proc/self/fd and /proc/self/fdinfo, in
/// number order. std's Command closes none of them before exec, where Python's subprocess
/// (close_fds) closed every one; the run records list them instead (DESIGN.md). Descriptors
/// std opens itself, such as this listing's, carry close-on-exec and are not listed.
pub fn inherited_descriptors() -> Vec<InheritedDescriptor> {
    let Ok(listing) = std::fs::read_dir("/proc/self/fd") else {
        return Vec::new();
    };
    let mut found = Vec::new();
    for item in listing.flatten() {
        let Some(fd) = item
            .file_name()
            .to_str()
            .and_then(|name| name.parse::<i32>().ok())
        else {
            continue;
        };
        if fd <= 2 {
            continue;
        }
        let Ok(info) = std::fs::read_to_string(format!("/proc/self/fdinfo/{fd}")) else {
            continue;
        };
        let Some(flags) = info
            .lines()
            .find_map(|line| line.strip_prefix("flags:"))
            .and_then(|value| u32::from_str_radix(value.trim(), 8).ok())
        else {
            continue;
        };
        if flags & O_CLOEXEC != 0 {
            continue;
        }
        let target = std::fs::read_link(format!("/proc/self/fd/{fd}"))
            .map(|path| path.to_string_lossy().into_owned())
            .unwrap_or_default();
        found.push(InheritedDescriptor { fd, target });
    }
    found.sort_by_key(|descriptor| descriptor.fd);
    found
}
