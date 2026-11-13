// Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
//! The parameters of the step order, kept in one place so that a new measurement changes one value.
//!
//! The order is: refutation pass 1 with a short producer time limit, model slice A, refutation pass 2 from
//! scratch until a share of the wall budget, then model slice B for what is left. The values come from a
//! replay of recorded stage times at the 60 s default, which solved the same problems as the earlier order on
//! every release sample in less than half the time. The shares are not measured at other wall budgets.

/// The step order's parameters.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct StageOrder {
    /// The producer's time limit in refutation pass 1, in seconds.
    pub pass_one_seconds: f64,
    /// Model slice A's share of the wall budget.
    pub slice_a_share: f64,
    /// Refutation pass 2 runs until this share of the wall budget.
    pub refutation_share: f64,
    /// Time a candidate model needs left for the model checker, and the reserve slice B leaves.
    pub model_reserve_seconds: f64,
    /// The producer's time limit is the stage deadline less this reserve, which its checker keeps.
    pub search_check_reserve_seconds: f64,
    /// Memory the producers leave below the command's limit, in MiB.
    pub memory_margin_mib: u64,
    /// The exporters stop this long before the command deadline, so their time-out cannot cancel a result.
    pub export_reserve_seconds: f64,
}

/// Round one's values, which the Python adapter uses and the equivalence campaign runs with.
pub const ROUND_ONE: StageOrder = StageOrder {
    pass_one_seconds: 1.0,
    slice_a_share: 2.0 / 60.0,
    refutation_share: 0.75,
    model_reserve_seconds: 10.0,
    search_check_reserve_seconds: 5.0,
    memory_margin_mib: 256,
    export_reserve_seconds: 1.0,
};

/// Round two's values: slice A takes 3/60 of the wall budget and refutation pass 2 runs until 80 percent of it;
/// the rest is unchanged. Measured at 60 s on the release samples, they lose no solve, take less total time on
/// solved problems and are faster on models. This is a listed change: it takes force after the equivalence
/// campaign, and the round-two differential measures it.
pub const ROUND_TWO: StageOrder = StageOrder {
    slice_a_share: 3.0 / 60.0,
    refutation_share: 0.80,
    ..ROUND_ONE
};

/// The order in force.
pub const STAGE_ORDER: StageOrder = ROUND_TWO;
