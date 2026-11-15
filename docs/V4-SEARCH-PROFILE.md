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

## Ground-congruence shortcut

The optional `ground_joinability=on` setting closes congruence over available ground unit equations before saturation. A matching negative ground unit equation yields an explanation expanded to the existing paramodulation and equality-resolution certificate rules. The scan admits at most 65,536 records, 16,384 terms and one million work ticks; explanations have at most 4,096 rewrites and position depth 64. Refused heuristic work leaves ordinary saturation available. Deadline and stored-record limits still stop the search.

This component covers existing ground equations. General ground-joinability redundancy concerns every grounding substitution of equations with variables, while connectedness concerns an inference in its parent context. The separate UEQ implementation is described below; see also [Duarte and Korovin, IJCAR 2022](https://link.springer.com/chapter/10.1007/978-3-031-10769-6_11).

Tests compare 15,488 term pairs against a separate equivalence-relation implementation and replay every successful explanation. The qualified installation passes 1,000 Rust tests (three ignored), 45 compiled-Lean proofs with exported documents, 15 negative controls and two corrupted-certificate refusals. Default-mode regression preserves 122 certificate byte sequences and 34 explicit limit refusals.

The training comparison uses all 256 frozen training inputs, actual producer routes, two producer seconds and a ten-second limit per cell, with 2,048 MiB sampled total RSS. Each input contributes its inputs task or first listed goal, so these are task results, not whole-problem solves. All 512 cells are retained: 144 checked tasks, 322 producer resource refusals, 24 GaveUp outcomes, 18 capture errors and four whole-cell deadlines. Both variants check the same 72 tasks. One successful certificate changes, on ALG172+1; the other 71 are identical. This trial adds no coverage, and its concurrent development timings do not establish a speed improvement. The default remains off. Validation and held-out outcomes were not used.

Local evidence: `experiments/v4-ground-join-qualification-v1/receipt.json`, `experiments/v4-ground-joinability-v1/native-v4/`, and `experiments/v4-ground-join-training/receipt.json`. The last receipt has SHA-256 `f3c4bdd6997defa99c000574ed3c182118d637561b801ef77207ec27d7ee27a5`.

## Longer strategy slices

The six-variant training matrix is complete: baseline, lookahead and LPO at five and 15 producer seconds, over the same 256 inputs. Each cell has eight additional seconds for capture and checking, with 2,048 MiB sampled total RSS. The producers come from the compact-storage installation at `40f995aceb86e99fe756008f009bbfbb2c80e8ce`, before the ground-unit index and ground-congruence shortcut.

| Strategy | Checked tasks at 5 s | Checked tasks at 15 s |
| --- | ---: | ---: |
| Baseline | 74 | 77 |
| Lookahead | 74 | 77 |
| LPO | 68 | 73 |

The union across all six variants is 80 tasks. All 1,536 cells remain in the audited matrix, including refusals. These results concern inputs or the first listed goal, not whole-problem solves. Concurrent development work prevents controlled speed comparisons. The receipt is `experiments/v4-strategy-longer/receipt.json`, SHA-256 `1a56d3fa1059a808755636d258ac299c98dcd561e7b8d0e6ee0a2379b2c00bac`.

## Critical-pair queue scores

An isolated producer prototype compares three queue scores for positive unit equations. The standard score preserves current behavior. Max-side uses four times the larger term weight plus the smaller weight. Shared-max-side uses that formula after counting repeated subterms as one symbol, with bounded traversal and fallback to cached tree weights. Other clauses keep the standard score. The age queue remains available; these scores do not filter inferences.

All 256 training inputs ran through all three variants at two producer seconds and ten seconds per cell. The 768 audited cells contain 72 checked tasks for standard, 71 for max-side and 71 for shared-max-side, with union 74. Both alternatives gain SET646+3 and SWW407-1, and lose GRP777-10, GRP442-1 and SET680+3 at this budget. A second matrix covers all five changed tasks at both two and 15 seconds:

| Score | Checked changed tasks at 2 s | Checked changed tasks at 15 s |
| --- | ---: | ---: |
| Standard | 3/5 | 4/5 |
| Max-side | 2/5 | 3/5 |
| Shared-max-side | 2/5 | 3/5 |

Both alternative scores check SWW407-1 at two seconds; standard still fails at 15 seconds. Their GRP442-1 regression disappears at 15 seconds, while GRP777-10 and SET680+3 remain unresolved. Thus neither alternative dominates standard. All 17 positive follow-up outcomes also export complete refutation documents. The four successful SWW407-1 cells each produce a 3,759-byte certificate and an 8,249-byte document. These are candidate portfolio options, with no default change or final benchmark claim.

Local receipts: `experiments/v4-critical-score-training/receipt.json`, `experiments/v4-critical-score-followup/receipt.json` and `experiments/v4-critical-score-followup/export-receipt.json`. Their SHA-256 hashes are respectively `4aefa9253b1564dbc5b0019887231b43c79120b95d53d8f2df2e76cd8fa90e32`, `30ee126badf9a0cc64a23e110d4f01a4baf6eaa56a9ceca535890afe1a7cd785` and `30f36835590d3134ad0110034f2ce7cbf1492df139a2b518e713646158db67ff`. The export controller pins certificates before and after export, but did not separately pin its previously qualified exporter binary at both points.

## Unit-equation redundancy prototype

A separate isolated prototype tests whether a positive unit critical-pair conclusion joins under every total preorder of its variables. Equal-variable cases are included. Its comparison extends uniform KBO conservatively: an unknown orientation keeps the equation. The test admits at most four variables, 64 active equations, 200,000 work ticks and 128 rewrites per normalization. Inputs remain available. Mixed-clause problems, LPO and nonuniform KBO weights bypass this heuristic.

The prototype passes 77 Rust tests, including compatible ground-substitution comparisons and small-model checks, plus 18 compiled-Lean proofs with documents and six satisfiable controls that emit no proof. The positive associative-commutative controls exercise actual redundancy deletions. These tests do not constitute a formal completeness proof for the redundancy criterion.

Its 512-cell comparison on the full training split checks 72 tasks with the heuristic disabled and 71 enabled. The enabled set loses GRP777-10 and adds none. There are 143 checked cells, 325 ResourceOut outcomes, 24 GaveUp outcomes, 18 capture errors and two whole-cell deadlines. The option is now integrated and qualified, with the default still disabled. Local receipts: `experiments/v4-unit-ground-join-v1/receipt.json` and `experiments/v4-unit-join-training/receipt.json`; the training receipt has SHA-256 `7f80fb7db08db5371b9f68894f8f7f89eea16aa16f1048de0c3ca3419518c67b`.

The combined installation includes this option and all three queue scores. It passes 1,009 Rust tests (three ignored), formatting and Clippy, 54 compiled proofs with complete documents and 18 satisfiable controls across their combinations. Default-mode regression preserves 122 certificate byte streams and 34 explicit limit refusals. The existing ground-congruence controls also pass: 45 proofs/documents, 15 negative controls and two corrupted-certificate rejections. The installation receipt is `experiments/v4-ueq-qualification-v1/receipt.json`, SHA-256 `c75bb57d4fc885bbeddb40c5439a2a6f48fc8ba004164610b9623013dc0c1431`.

Validation and held-out outcomes remain unused throughout these experiments. None of these matrices is the final V4 versus Vampire benchmark.
