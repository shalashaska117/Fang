// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Small pieces revision 7 took from Python's standard library: UTC timestamps in
//! `datetime.isoformat()` form, `Path.resolve()` without strictness, and the JSON writer of its
//! records.

use std::path::{Component, Path, PathBuf};
use std::time::{SystemTime, UNIX_EPOCH};

use fang_json::Value;

/// `datetime.now(timezone.utc).isoformat()`: microseconds unless zero, then `+00:00`.
pub fn utc_now() -> String {
    let elapsed = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default();
    let seconds = elapsed.as_secs();
    let micros = elapsed.subsec_micros();
    let days = (seconds / 86_400) as i64;
    let rest = seconds % 86_400;
    let (year, month, day) = civil(days);
    let time = format!(
        "{:02}:{:02}:{:02}",
        rest / 3600,
        rest % 3600 / 60,
        rest % 60
    );
    let fraction = if micros == 0 {
        String::new()
    } else {
        format!(".{micros:06}")
    };
    format!("{year:04}-{month:02}-{day:02}T{time}{fraction}+00:00")
}

/// Days since 1970-01-01 to a proleptic Gregorian date (Howard Hinnant's civil_from_days).
fn civil(days: i64) -> (i64, u32, u32) {
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = (doy - (153 * mp + 2) / 5 + 1) as u32;
    let month = if mp < 10 { mp + 3 } else { mp - 9 } as u32;
    let year = yoe + era * 400 + i64::from(month <= 2);
    (year, month, day)
}

/// `Path(path).resolve()`: symbolic links of existing components resolved, the rest kept,
/// `.` and `..` folded, relative paths taken from the working directory.
pub fn resolve(path: &Path) -> PathBuf {
    let start = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir()
            .unwrap_or_else(|_| PathBuf::from("/"))
            .join(path)
    };
    let mut budget = 40;
    resolve_from(&PathBuf::from("/"), &start, &mut budget)
}

fn resolve_from(base: &Path, path: &Path, budget: &mut u32) -> PathBuf {
    let mut current = base.to_path_buf();
    for component in path.components() {
        match component {
            Component::RootDir => current = PathBuf::from("/"),
            Component::Prefix(_) | Component::CurDir => {}
            Component::ParentDir => {
                current.pop();
            }
            Component::Normal(name) => {
                let candidate = current.join(name);
                match std::fs::symlink_metadata(&candidate) {
                    Ok(info) if info.file_type().is_symlink() && *budget > 0 => {
                        *budget -= 1;
                        match std::fs::read_link(&candidate) {
                            Ok(target) => current = resolve_from(&current, &target, budget),
                            Err(_) => current = candidate,
                        }
                    }
                    _ => current = candidate,
                }
            }
        }
    }
    current
}

/// `path.is_relative_to(other)`, lexically.
pub fn inside(path: &Path, other: &Path) -> bool {
    path.starts_with(other)
}

/// `json.dumps(value, indent=2, sort_keys=True) + "\n"` as bytes.
pub fn manifest_bytes(value: &Value) -> Result<Vec<u8>, String> {
    let text = fang_json::dumps_manifest(value).map_err(|error| error.0)?;
    Ok((text + "\n").into_bytes())
}

/// `json.dumps(value, sort_keys=True)`.
pub fn sorted_line(value: &Value) -> Result<String, String> {
    fang_json::dumps(
        value,
        &fang_json::DumpOptions {
            indent: None,
            sort_keys: true,
        },
    )
    .map_err(|error| error.0)
}

/// SHA-256 of a whole file, in hex.
pub fn file_sha256(path: &Path) -> Result<String, String> {
    let data = std::fs::read(path).map_err(|error| format!("{}: {error}", path.display()))?;
    Ok(fang_hash::sha256_hex(&data))
}

#[cfg(test)]
mod tests {
    use super::civil;

    #[test]
    fn civil_dates() {
        assert_eq!(civil(0), (1970, 1, 1));
        assert_eq!(civil(20_402), (2025, 11, 10));
        assert_eq!(civil(11_016), (2000, 2, 29));
    }
}
