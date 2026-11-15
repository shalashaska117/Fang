# V4 search profiles

Development measurements from 2026-11-15. The baseline source is commit `40f995aceb86e99fe756008f009bbfbb2c80e8ce`. The new ground-unit index changes producer retrieval; the checker and certificate language are unchanged.

## Why this index

On the retained CSR inputs, the predicate-level index returned millions of ground facts that could not match the queried literal. A ground unit can subsume a clause only when that clause contains the same literal, allowing equality sides to be reversed. The new index uses that exact key for forward subsumption and unit deletion. A second set of postings finds matching occurrences in non-unit clauses for backward subsumption. Query results keep activation order and omit deleted clauses.

The implementation is in `crates/fang-saturation/src/index.rs` and `search.rs`. `ground_unit_index_tests.rs` compares both query directions against linear search on 210 clause shapes, with reversed activation order and deleted postings. Another 4,900 pairs compare the exact unit-deletion result and chosen proof rule.

## Fixed-work comparison

Both versions ran `step5`, `index=on`, `simplify_new=on`, and either heaviest-negative or lookahead selection. The bound was 4,000 given clauses, with a 60-second producer cap and 1,792 MiB. The cited route still reserved half its remaining time for the second search. Each case ran with diagnostic timers disabled and enabled.

The counts below are calls to the full subsumption test during discovery. All listed runs reached the same given-clause bound and preserved search counters, including generated clauses and inference counts.

| Input | Selection | Before | After |
| --- | --- | ---: | ---: |
| CSR114+13 | heaviest-negative | 26,047,266 | 263,099 |
| CSR114+13 | lookahead | 12,852,373 | 4,299 |
| CSR116+2 | heaviest-negative | 26,047,266 | 263,099 |
| CSR116+2 | lookahead | 12,852,373 | 4,299 |
| HWV116+1 | heaviest-negative | 1,050,087 | 653,488 |
| HWV116+1 | lookahead | 1,536,861 | 1,486,266 |
| CSR239+1 | heaviest-negative | 9,853,902 | 65,864 |
| CSR239+1 | lookahead | 10,317,969 | 87,389 |

Twenty before/after pairs preserved their work and certificate bytes, including the early proofs of COM146+1. Four COM123+1 pairs reached a time bound and are excluded from work-equivalence claims. The native controls also passed: 122 compiled-Lean replays and 34 explicit resource refusals. Removing the diagnostic instrumentation preserved those outcomes and certificate bytes.

For CSR114+13 with heaviest-negative selection and timers disabled, one observed construction/search interval changed from 1.987 s to 0.064 s; producer peak RSS was 38,460 and 38,696 KiB. These intervals exclude parsing, clausification, proof extraction and independent checking. Training and other development jobs ran concurrently. They are diagnostic observations, not controlled speed estimates or final benchmark results. Instrumented phase times overlap and must not be added.

## Remaining development targets

On the qualified installation preceding this index, the six named TPTP targets ran through the default launcher with compiled checking, complete TSTP output, 60 seconds and 2,048 MiB. COM146+1 produced a checked theorem and a complete document. CSR114+13, CSR116+2, HWV116+1, COM123+1 and CSR239+1 ended with ResourceOut.

The failed cited searches reached their discovery deadline before using the reserved second-search budget. Giving discovery three quarters of the same 40-second producer budget recovered none of the five failures, so the default split remains unchanged. The new index also recovered none under the same nine-slice portfolio. Running the first lookahead strategy continuously did not recover them either. These follow-ups do not count as additional solves.

The local `block-21000` fixture was found in four historical experiment directories with identical bytes: SHA-256 `f15716eddd5e0e614371df09dd38f3786d511405df4259e1e5a6d2caf2ce275d`, 846 bytes. The preceding qualified installation already returned Satisfiable with a checked one-element model and a complete finite-model document. Its observed time before status was 0.294 s under concurrent development load. This result does not depend on the new index.

## Evidence scope

The local receipts are retained under `experiments/v4-index-profile-v1`, `experiments/v4-ground-unit-index-v1`, `experiments/v4-ground-unit-index-v2`, `experiments/v4-cited-budget-v1`, `experiments/v4-slow-targets-v1` and `experiments/v4-block-21000-v1`. They include frozen commands, source and binary hashes, per-stage output, certificates and documents. These ignored experiment directories are local evidence; they are not release assets.

The longer strategy matrix uses the frozen training set. Validation and held-out outcomes remain unused. The final V4 versus Vampire comparison is still pending.
