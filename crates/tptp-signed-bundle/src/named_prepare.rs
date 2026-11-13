// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
// Staged as a module of the research signed-bundle crate.
use super::*;

/// Prepare the complete bundle with naming at the caller's threshold.
pub fn prepare_bundle_task_named(
    bundle: &Bundle,
    selection: Selection,
    limits: &Limits,
    threshold: usize,
) -> Result<(Flat, Prepared), Error> {
    let flat = flatten(bundle, limits)?;
    let limits = flat_limits(
        limits,
        bundle.files.len(),
        flat.text.len(),
        flat.distinct_clauses,
    );
    let prepared = fang_tptp_signed_roles::prepare_task_named(
        flat.text.as_bytes(),
        selection,
        &limits,
        threshold,
    )
    .map_err(Error::Signed)?;
    Ok((flat, prepared))
}

/// Prepare only the cited premises and selected goal with naming.
/// The first tuple field is the canonical citation list in expansion order.
pub fn prepare_cited_task_named(
    bundle: &Bundle,
    selection: Selection,
    cited: &[(usize, usize)],
    limits: &Limits,
    threshold: usize,
) -> Result<CitedPrepared, Error> {
    let (citations, kept, selection) = kept_task(bundle, selection, cited, limits)?;
    let limits = flat_limits(
        limits,
        bundle.files.len(),
        kept.text.len(),
        kept.distinct_clauses,
    );
    let prepared = fang_tptp_signed_roles::prepare_task_named(
        kept.text.as_bytes(),
        selection,
        &limits,
        threshold,
    )
    .map_err(Error::Signed)?;
    Ok((citations, kept, prepared))
}
