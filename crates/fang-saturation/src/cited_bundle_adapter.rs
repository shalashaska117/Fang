// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! Experimental signed-bundle adapter, built against the isolated research
//! bundle APIs. Its output is an unchecked candidate for the role-v6 checker.

use fang_saturation::{cited, options::Options, producer::Refutation};
use fang_tptp_coverage_candidate::Bundle;
use fang_tptp_signed_bundle::{
    Error as BundleError, InputOriginError, cited_inputs, premise_line, prepare_bundle_task_named,
    prepare_cited_task_named,
};
use fang_tptp_signed_roles::{Limits, Selection};
use std::time::Instant;

pub struct Config<'a> {
    /// Discovery can use wider producer limits than the checked kept task.
    pub discovery_limits: &'a Limits,
    /// Must match the record used by the role-v6 checker.
    pub replay_limits: &'a Limits,
    pub naming_threshold: usize,
    pub options: &'a Options,
    /// Absolute deadlines include loading and preparation; callers set them
    /// before reading input. Discovery is clamped to the overall deadline.
    pub discovery_deadline: Option<Instant>,
    pub deadline: Option<Instant>,
    pub memory_mib: Option<u64>,
    /// Includes the premise line, newline, and proof, as read by the checker.
    pub certificate_bytes: usize,
}

#[derive(Debug)]
pub enum AdapterError {
    Preparation(BundleError),
    Mapping(InputOriginError),
    CitationOrder,
}

#[derive(Debug)]
pub enum Error {
    Preparation(BundleError),
    Refutation(cited::Error<AdapterError>),
    CertificateBytes,
    Deadline,
}

/// Prepare the full task, discover premise items, then prepare and refute the
/// kept task with its own numbering. Only the second proof is serialized.
pub fn produce(
    bundle: &Bundle,
    selection: Selection,
    config: &Config<'_>,
) -> Result<String, Error> {
    let expired = || config.deadline.is_some_and(|end| Instant::now() >= end);
    if expired() {
        return Err(Error::Deadline);
    }
    let (flat, prepared) = prepare_bundle_task_named(
        bundle,
        selection,
        config.discovery_limits,
        config.naming_threshold,
    )
    .map_err(Error::Preparation)?;
    let candidate = cited::refute(
        prepared,
        config.options,
        config.discovery_deadline,
        config.deadline,
        config.memory_mib,
        |prepared, inputs| cited_inputs(&flat, prepared, inputs).map_err(AdapterError::Mapping),
        |items| {
            let (canonical, _, prepared) = prepare_cited_task_named(
                bundle,
                selection,
                items,
                config.replay_limits,
                config.naming_threshold,
            )
            .map_err(AdapterError::Preparation)?;
            // The map promises expansion order. Reject a disagreement rather
            // than writing a premise list for a different kept task.
            if canonical != items {
                return Err(AdapterError::CitationOrder);
            }
            Ok(prepared)
        },
    )
    .map_err(Error::Refutation)?;
    let mut output = premise_line(&candidate.premises);
    let size = output
        .len()
        .checked_add(1)
        .and_then(|n| n.checked_add(candidate.text.len()));
    if size.is_none_or(|n| n > config.certificate_bytes) {
        return Err(Error::CertificateBytes);
    }
    output.push('\n');
    output.push_str(&candidate.text);
    if expired() {
        return Err(Error::Deadline);
    }
    Ok(output)
}

/// The CLI may translate these outcomes to its established resource/unknown
/// protocol. This adapter never reports a proved SZS status.
pub fn search_outcome(error: &Error) -> Option<&Refutation> {
    match error {
        Error::Refutation(cited::Error::Discovery(outcome) | cited::Error::Replay(outcome)) => {
            Some(outcome)
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fang_tptp_coverage_candidate::Root;
    use fang_tptp_signed_bundle::sealed;
    use std::time::Duration;

    #[test]
    fn complete_envelope_counts_the_premise_line_in_the_byte_limit() {
        let bundle = sealed(vec![(
            Root::Base,
            "main.p".into(),
            b"fof(a,axiom,p). fof(b,axiom,~p).".to_vec(),
        )]);
        let limits = Limits::default();
        let options = Options::preset("step5").unwrap();
        let mut config = Config {
            discovery_limits: &limits,
            replay_limits: &limits,
            naming_threshold: 8,
            options: &options,
            discovery_deadline: None,
            deadline: None,
            memory_mib: None,
            certificate_bytes: 1 << 20,
        };
        let output = produce(&bundle, Selection::Inputs, &config).unwrap();
        assert!(output.starts_with("(premises (item 0 0) (item 0 1))\n"));
        config.certificate_bytes = output.len();
        assert_eq!(
            produce(&bundle, Selection::Inputs, &config).unwrap(),
            output
        );
        config.certificate_bytes -= 1;
        assert!(matches!(
            produce(&bundle, Selection::Inputs, &config),
            Err(Error::CertificateBytes)
        ));
    }

    #[test]
    fn goal_without_premises_has_an_explicit_empty_premise_line() {
        let bundle = sealed(vec![(
            Root::Base,
            "main.p".into(),
            b"fof(g,conjecture,$true).".to_vec(),
        )]);
        let limits = Limits::default();
        let options = Options::preset("step5").unwrap();
        let config = Config {
            discovery_limits: &limits,
            replay_limits: &limits,
            naming_threshold: 8,
            options: &options,
            discovery_deadline: None,
            deadline: None,
            memory_mib: None,
            certificate_bytes: 1 << 20,
        };
        assert!(
            produce(&bundle, Selection::Goal(0), &config)
                .unwrap()
                .starts_with("(premises)\n")
        );
    }

    #[test]
    fn expired_budget_stops_before_preparation() {
        // Deliberately malformed input distinguishes an early deadline from
        // input preparation and prevents accidental work after expiration.
        let bundle = sealed(vec![(Root::Base, "bad.p".into(), b"malformed".to_vec())]);
        let limits = Limits::default();
        let options = Options::preset("step5").unwrap();
        let config = Config {
            discovery_limits: &limits,
            replay_limits: &limits,
            naming_threshold: 8,
            options: &options,
            discovery_deadline: None,
            deadline: Some(Instant::now() - Duration::from_secs(1)),
            memory_mib: None,
            certificate_bytes: 1 << 20,
        };
        assert!(matches!(
            produce(&bundle, Selection::Inputs, &config),
            Err(Error::Deadline)
        ));
    }

    #[test]
    fn replay_uses_its_own_limits_after_successful_discovery() {
        let bundle = sealed(vec![(
            Root::Base,
            "main.p".into(),
            b"fof(a,axiom,p). fof(b,axiom,~p).".to_vec(),
        )]);
        let discovery = Limits::default();
        let mut replay = discovery.clone();
        replay.max_predicates = 0;
        let options = Options::preset("step5").unwrap();
        let config = Config {
            discovery_limits: &discovery,
            replay_limits: &replay,
            naming_threshold: 8,
            options: &options,
            discovery_deadline: None,
            deadline: None,
            memory_mib: None,
            certificate_bytes: 1 << 20,
        };
        assert!(matches!(
            produce(&bundle, Selection::Inputs, &config),
            Err(Error::Refutation(cited::Error::Preparation(
                AdapterError::Preparation(_)
            )))
        ));
    }
}
