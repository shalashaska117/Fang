// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Route one invocation to exactly one profile.
//!
//! Every input goes to the version-8 profile unless `--profile` selects the CNF or ground-FOF profile. The
//! choice depends only on the command line, never on the input or on an earlier failure, so there is no
//! retry and no fallback between profiles.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use fang_supervisor::guard::Worker;

use crate::capability::{self, Capability};
use crate::{profile_cnf, profile_ground_fof, v8};

/// The profiles, in the order the error messages name them.
pub const PROFILES: [&str; 3] = ["v8", "cnf", "ground-fof"];

/// Exit code of a refusal before any profile runs.
const REFUSED: u8 = 6;

/// The selected profile and the arguments without the `--profile` option.
///
/// `--profile` may be given once, as `--profile NAME` or `--profile=NAME`; everything from `--` on is left
/// as it is. The messages are those of the earlier router.
pub fn selected_profile(arguments: &[String]) -> Result<(String, Vec<String>), String> {
    let mut profile: Option<String> = None;
    let mut rest = Vec::new();
    let mut index = 0;
    while index < arguments.len() {
        let item = &arguments[index];
        if item == "--" {
            rest.extend(arguments[index..].iter().cloned());
            break;
        }
        if item == "--profile" || item.starts_with("--profile=") {
            if profile.is_some() {
                return Err("--profile may be given once".to_string());
            }
            let value = if item == "--profile" {
                if index + 1 >= arguments.len() {
                    return Err(format!("--profile needs a value: {}", PROFILES.join(", ")));
                }
                index += 2;
                arguments[index - 1].clone()
            } else {
                index += 1;
                item["--profile=".len()..].to_string()
            };
            if !PROFILES.contains(&value.as_str()) {
                return Err(format!(
                    "unknown profile {}; choose one of: {}",
                    python_repr(&value),
                    PROFILES.join(", ")
                ));
            }
            profile = Some(value);
            continue;
        }
        rest.push(item.clone());
        index += 1;
    }
    Ok((profile.unwrap_or_else(|| "v8".to_string()), rest))
}

/// Python's repr of a str, for the one message that quotes a profile name.
fn python_repr(text: &str) -> String {
    let quote = if text.contains('\'') && !text.contains('"') {
        '"'
    } else {
        '\''
    };
    let mut result = String::new();
    result.push(quote);
    for character in text.chars() {
        match character {
            '\\' => result.push_str("\\\\"),
            '\n' => result.push_str("\\n"),
            '\r' => result.push_str("\\r"),
            '\t' => result.push_str("\\t"),
            c if c == quote => {
                result.push('\\');
                result.push(c);
            }
            c if (c as u32) < 0x20 || c as u32 == 0x7f => {
                result.push_str(&format!("\\x{:02x}", c as u32))
            }
            c => result.push(c),
        }
    }
    result.push(quote);
    result
}

/// The capability next to the installed binary: `<directory of the binary>/../v8-capability.json`.
pub fn installed_capability_path() -> Result<PathBuf, String> {
    let executable = std::env::current_exe()
        .map_err(|error| format!("cannot locate the installed command: {error}"))?;
    let directory = executable
        .parent()
        .ok_or("cannot locate the installed command's directory")?;
    Ok(directory.join("..").join("v8-capability.json"))
}

/// Run the profile the command line selects, and return its exit code.
pub fn run(worker: Worker, arguments: Vec<String>) -> ExitCode {
    let arguments = if arguments == ["help"] {
        vec!["--help".to_string()]
    } else {
        arguments
    };
    let (profile, rest) = match selected_profile(&arguments) {
        Ok(selection) => selection,
        Err(message) => return refuse(&message),
    };
    if profile == "v8" {
        // An explicit --capability names the version-8 capability, as on a non-public run; otherwise it is
        // the one installed next to this binary.
        let path = match explicit_option(&rest, "--capability") {
            Some(path) => path,
            None => match installed_capability_path() {
                Ok(path) => path,
                Err(message) => return refuse(&message),
            },
        };
        return v8::run(worker, rest, &path);
    }
    // An older profile given its own configuration file explicitly (--installation for cnf, --capability for
    // ground-fof, as on a non-public run) reads that file unpinned; otherwise the capability's pin decides.
    let own_option = if profile == "cnf" {
        "--installation"
    } else {
        "--capability"
    };
    let record = if explicit_option(&rest, own_option).is_some() {
        None
    } else {
        let path = match installed_capability_path() {
            Ok(path) => path,
            Err(message) => return refuse(&message),
        };
        let capability = match Capability::load(&path) {
            Ok(capability) => capability,
            Err(fault) => return refuse(&fault.reason()),
        };
        if let Err(message) = capability::check_launcher(&capability) {
            return refuse(&message);
        }
        let pinned = if profile == "cnf" {
            capability.cnf()
        } else {
            capability.ground_fof()
        };
        match pinned {
            Some(record) => Some(record.clone()),
            None => {
                return refuse(&format!(
                    "profile {profile} is not installed here; no other profile was run"
                ));
            }
        }
    };
    if profile == "cnf" {
        profile_cnf::run(worker, rest, record.as_ref())
    } else {
        profile_ground_fof::run(worker, rest, record.as_ref())
    }
}

/// The value of `OPTION PATH` or `OPTION=PATH` before any `--`, if given.
fn explicit_option(arguments: &[String], option: &str) -> Option<PathBuf> {
    let mut iter = arguments.iter();
    while let Some(item) = iter.next() {
        if item == "--" {
            return None;
        }
        if item == option {
            return iter.next().map(|value| Path::new(value).to_path_buf());
        }
        if let Some(value) = item
            .strip_prefix(option)
            .and_then(|rest| rest.strip_prefix('='))
        {
            return Some(PathBuf::from(value));
        }
    }
    None
}

fn refuse(message: &str) -> ExitCode {
    eprintln!("fang: {message}");
    ExitCode::from(REFUSED)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strings(items: &[&str]) -> Vec<String> {
        items.iter().map(|item| item.to_string()).collect()
    }

    #[test]
    fn profile_selection_matches_the_router() {
        assert_eq!(
            selected_profile(&strings(&["p.p"])).unwrap(),
            ("v8".to_string(), strings(&["p.p"]))
        );
        assert_eq!(
            selected_profile(&strings(&["--profile", "cnf", "p.p"]))
                .unwrap()
                .0,
            "cnf"
        );
        assert_eq!(
            selected_profile(&strings(&["--profile=ground-fof", "p.p"]))
                .unwrap()
                .0,
            "ground-fof"
        );
        assert_eq!(
            selected_profile(&strings(&["--", "--profile", "cnf"])).unwrap(),
            ("v8".to_string(), strings(&["--", "--profile", "cnf"]))
        );
        assert_eq!(
            selected_profile(&strings(&["--profile"])).unwrap_err(),
            "--profile needs a value: v8, cnf, ground-fof"
        );
        assert_eq!(
            selected_profile(&strings(&["--profile", "v7"])).unwrap_err(),
            "unknown profile 'v7'; choose one of: v8, cnf, ground-fof"
        );
        assert_eq!(
            selected_profile(&strings(&["--profile", "v8", "--profile", "v8"])).unwrap_err(),
            "--profile may be given once"
        );
    }
}
