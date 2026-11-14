# V4 implementation checklist

Working checklist for [V4-PLAN.md](V4-PLAN.md). Updated 2026-11-14.

A checked box means the stated task passed at the stated scope. An isolated prototype is not an installed or released capability. Unchecked tasks still need work or evidence; they do not necessarily mean there is no earlier code. V4 is incomplete, and no SOTA result has been established.

## Current work

The current integrated installation passed qualification: 985 Rust tests (two ignored), formatting and Clippy, with the unchanged Lean build and its 1,634 fixed audits. Its launcher passed self-check, 12 positive cases with complete documents, two include-selection rejections and the malformed-UTF-8 rejection control. The integrated KBO variable-count optimization passed 366 installed compiled-Lean replays, with identical certificates and search counters apart from timing. Those replays cover optional KBO weights and literal-selection policies across KBO and LPO. The preceding passive-queue integration passed 62 replays, eight queue-exhaustion regressions, two passive-limit controls and an orphan-deletion control.

1. Characterize SWC279-1's sensitivity to timed search slices. The export-deadline correction is integrated and qualified: CSR051-10, CSR072-10, SEV606+1 and SWC279-1 produced complete checked documents on the new installation within the original 60-second budget. These four follow-ups do not replace the earlier 222/226 campaign. SWC279-1 also passed with the unchanged launcher, so its earlier search timeout remains unexplained.
2. Obtain independent review and integrate equality factoring. The coherent native build, all 1,634 fixed audits, original-input compiled replay, named document and corruption controls passed, as did the full kernel route.
3. Finish qualification of the retained-clause array exporter. Its isolated 53-module rebuild, seven compiled result/error controls and 14 byte-identical document comparisons passed. Integration and installed performance measurements remain pending.
4. Collect strategy outcomes on the [frozen training corpus](../benchmarks/v4-corpus/README.md), then select schedule participation for the qualified KBO weights and literal-selection policies. The 256 training, 64 validation and 256 held-out problems have disjoint filename families. Defaults remain unchanged; no strategy runs have started on these sets.

The detailed local evidence and running commands are recorded in `experiments/V4-STATE.json`. The current product search still disables equality factoring.

## Installation and integration

- [x] Run the combined Rust component checks: 937 tests passed, three ignored, Clippy passed.
- [x] Validate Rust and Lean source maps and import closures; 16 source-check tests passed.
- [x] Compile the integrated Lean project from a fresh build directory: 4,449 jobs passed.
- [x] Pass all 1,634 fixed axiom audits in that fresh build.
- [x] Validate the corrected usage metadata against all ten compiled executables.
- [x] Pass the production installer's Rust checks: 953 tests, two ignored, formatting and Clippy.
- [x] Complete the production installer's audits, Rust checks and installation manifest.
- [x] Run `fang --self-check` from the new installation.
- [x] Verify installed cited-goal output.
- [x] Verify installed signed distinct-object output.
- [x] Verify installed distinct-object axioms output.
- [x] Verify installed commented-include goal and inputs-refutation output.
- [x] Verify installed UTF-8 commented include output.
- [x] Verify installed three-witness and dependent-witness finite models.
- [x] Verify malformed UTF-8 is refused without a positive status.
- [x] Verify installed nested include selections for goal and inputs refutations, preserving original source citations.
- [x] Verify two conjectures produce two complete installed refutation documents.
- [x] Verify repeated inclusion of the same statement is accepted and canonically cited.
- [x] Verify missing selected names and ambiguous names from distinct declarations produce InputError without a positive result or document.
- [x] Record the combined qualification receipt with current source hashes and actual installation manifests.
- [x] Qualify the export-deadline and passive-queue integration with 965 installer tests, current source maps, installed regressions and a new qualification receipt.
- [x] Qualify optional LPO ordering with 970 installer tests, current source maps, installed launcher controls and 40 installed proof replays.
- [x] Qualify optional KBO weights and additional literal-selection policies with 981 installer tests, current source maps, installed launcher controls and 360 installed proof replays.
- [x] Qualify bounded DAG variable counting with 985 installer tests, current source maps, installed launcher controls and 366 byte-identical proof replays.

## 8. Equality factoring

- [x] Implement bounded Rust reconstruction in an isolated workspace; 20 reconstruction tests passed.
- [x] Check semantic entailment in 49,152 two-element interpretations, with wrong-polarity and missing-equation controls.
- [x] Add the Lean certificate rule and acceptance/rejection controls in an isolated overlay.
- [x] Prove that disabling the extension preserves the legacy parser's complete result.
- [x] Generate an eight-node certificate containing equality factoring from an actual TPTP input.
- [x] Check the earlier numeric fixture from exact certificate bytes in the Lean kernel.
- [x] Reject a corrupted claimed clause in the earlier numeric kernel fixture.
- [x] Prove TSTP row correspondence and validity from the rule's actual parent.
- [x] Pass seven output controls covering terms, substitution, parent labels, signatures and quoting.
- [x] Extend the isolated kernel generator while preserving legacy parsing; eight Rust tests and Clippy passed.
- [x] Finish the coherent 147-module native rebuild, reusing 107 completed modules with pinned sources and artifacts after the interpreter-memory retry.
- [x] Compare all 1,634 fixed declaration audits with their expected axiom sets.
- [x] Replay the original TPTP proof through the compiled checker and named exporter.
- [x] Reject wrong claims and future parents through both compiled paths; verify the V3 checker refuses the extended certificate.
- [x] Finish the 16-module kernel proof of acceptance and unsatisfiability from the original TPTP bytes.
- [x] Audit 33 instance theorems and preserve the exact 83 expected axiom sets across the 42 rebuilt helpers.
- [x] Reject a corrupted certificate through the complete original-input kernel route after exact-byte decoding, with a claimed-clause error and no accepted proof artifact.
- [ ] Obtain independent review of the new acceptance changes.
- [ ] Integrate the checked rule, serializer and kernel generator into product sources.
- [ ] Update source receipts and helper pins for the integrated rule.
- [ ] Qualify the installed rule and select its use in search strategies.

## 14. Checker data structures

- [x] Replace list-indexed lookup with an array store in both checker entry points.
- [x] Prove equality of complete results, including errors.
- [x] Pass 1,596 original declaration audits, 36 AST checks and 24 compiled replay comparisons.
- [x] Obtain independent review of the array checker integration.
- [x] Prove the isolated retained-clause array implementation returns the same result as the list implementation.
- [x] Compile its 53 affected modules and compare seven exact results/errors and 14 documents against the previous exporter.
- [ ] Integrate and check the retained-clause optimization in the compiled exporter.
- [ ] Profile substitution lookup and implement a change if the measurements justify it.
- [ ] Measure installed checking and export costs on retained certificates.

## 24. Complete proof output

- [x] Classify the 226 missing documents in the V3 1000-case sample.
- [x] Implement cited source rows with original paths, statement names and roles.
- [x] Prove cited-goal and inputs-refutation document semantics.
- [x] Route the launcher by certificate producer, including commented includes.
- [x] Pass the cited exporter's 38 theorem audits, 12 Lean controls and 12 native IO controls.
- [x] Obtain independent component reviews and integrate the source maps.
- [x] Pass the installed output checks listed above.
- [x] Run focused nested-include and selection-list fixtures through the installed path.
- [x] Rerun all 226 retained historical missing-document cases through the installed path, including the nested-include and selection-list cases.
- [x] Reassess the 11 historical exporter rejections and three export timeouts: all 11 rejections produced complete documents in the earlier 222/226 campaign; the three timeouts recovered in the separate export-deadline follow-up. Retained document hashes were rechecked.
- [x] In an isolated launcher, give accepted-result export the remaining command budget and test that the original deadline still holds; 202 tests passed, two ignored, with Clippy.
- [x] Recover CSR051-10, CSR072-10 and SEV606+1 with that isolated correction, preserving the 60-second, 2-GiB limits and original checkers.
- [x] Repeat SWC279-1 separately: three checked complete documents, including one from the unchanged installed launcher. This does not establish the cause of its earlier search timeout.
- [x] Run nine controlled SWC279-1 producer repetitions at 38, 39 and 40 seconds. All passed compiled checking with the unchanged producer; the one-second budget difference alone does not reproduce the historical timeout.
- [x] Integrate the export-deadline correction and qualify a new installation; all four historical follow-up cases produced complete checked documents.
- [ ] Resolve or characterize SWC279-1's sensitivity to timed search slices before final evaluation.
- [x] Validate recovered output: 222 of 226 cases produced complete checked documents; three remained checked without a document and SWC279-1 returned ResourceOut. This was a regression run during development, not a performance comparison.

## 20. Frontend gaps

- [x] Validate canonical UTF-8 in comments with a structural validator whose theorems use no axioms.
- [x] Pass the 202-module native rebuild and 48 compiled comparisons, preserving all 1,596 original axiom sets.
- [x] Integrate UTF-8 comment handling into the frontend and its source maps.
- [x] Qualify UTF-8 comments through the installed launcher.
- [ ] Extend and qualify kernel replay for UTF-8 comments.
- [ ] Define the checking and export contract for the `assumption` role.
- [ ] Implement and verify that role across parsing, checking and output.
- [ ] Define the supported subset of typed declarations inside otherwise FOF/CNF inputs.
- [ ] Implement that subset with rejection tests for unsupported typed reasoning.

## 22. Finite-model search

- [x] Implement compact at-most-one constraints for large function cells.
- [x] Account for auxiliary variables in the memory budget.
- [x] Check three domain-16 models with Lean and reject a corrupted model.
- [x] Include zero-arity Skolem symbols in the function-free domain bound.
- [x] Distinguish complete bound exhaustion from ordinary bounded exhaustion and interruption.
- [x] Retire only the exhausted model task; do not turn exhaustion into an UNSAT result.
- [x] Obtain component reviews and integrate the source maps.
- [x] Pass the installed model regressions listed above.
- [ ] Measure remaining instance-size limits on retained failures.
- [ ] Implement incremental solving across domain sizes.
- [ ] Infer useful sorts and preserve checking against the original unsorted problem.

## 12-13. Scheduling and fixed runtime cost

- [x] Test an isolated adaptive-polling supervisor with existing guard tests and Clippy.
- [ ] Review and integrate adaptive polling without changing resource limits.
- [ ] Measure installed process startup and short-certificate replay.
- [ ] Profile unsuccessful schedule slices and their share of total wall time.
- [ ] Adjust slice termination using those measurements.
- [ ] Profile goal listing and large-input preprocessing separately.
- [ ] Reduce measured fixed costs and rerun the affected regressions.

Adaptive polling also passed 222 combined supervisor/launcher tests, but installation correctly rejected its changed supervisor hash against the independently reviewed kernel-entry policy. The product supervisor and source map were restored. This change needs a new independent policy review before integration.

## 1. Strategy schedule

- [x] Freeze disjoint training, validation and held-out filename families, with the original benchmark families excluded; publish the lists, archive hash and tested Rust selector in [benchmarks/v4-corpus](../benchmarks/v4-corpus/README.md).
- [ ] Record problem features and strategy outcomes on the training set.
- [ ] Select a schedule, including unequal slice lengths, using training results only.
- [ ] Freeze the selected schedule before final evaluation.

## 2. AVATAR splitting

- [ ] Implement a producer-only splitting experiment.
- [ ] Measure certificate expansion and replay cost.
- [ ] Decide whether an additional checked split rule is necessary.
- [ ] If needed, define fresh predicates and prove the checked split rule.
- [ ] Add malformed-certificate controls and obtain independent acceptance review.
- [ ] Integrate and qualify the selected implementation.

## 3. Learned clause selection

- [ ] Define and record clause features and training data.
- [ ] Train a deterministic selector without evaluation-set leakage.
- [ ] Integrate reproducible inference in safe Rust.
- [ ] Compare selection and proof-search outcomes on held-out inputs.

## 4. Passive-set control

- [x] Implement optional lazy orphan deletion in an isolated workspace, preserving generating parents through proof simplifications.
- [x] Verify all selection queues, preserve replayable certificates and report orphan exhaustion as unknown.
- [x] Reproduce the V3 single-queue exhaustion loop and test its correction with orphan deletion disabled.
- [x] Integrate and qualify the queue fix and optional orphan heuristic; orphan exhaustion remains unknown.
- [x] Implement an isolated limit on queued passive clauses; pass 30 Rust tests and 62 compiled-Lean replays, including limit-zero controls.
- [x] Integrate and qualify the passive-clause limit; it does not bound total stored proof records or total memory.
- [ ] Assess additional count limits for stored clauses and generated work.
- [ ] Profile passive-clause memory and implement a compact representation where justified.
- [x] Check installed search behavior and resource accounting with 62 compiled certificate replays, eight queue controls, two passive-limit controls and a real orphan-deletion case.

## 5. Unit-equality search

- [ ] Implement and test ground joinability.
- [ ] Implement and test connectedness guidance.
- [ ] Compare critical-pair scoring variants on training inputs.
- [ ] Implement and check goal transformation.
- [ ] Qualify the chosen strategy variants and their certificates.

## 6. Selection and ordering

- [x] Implement and test isolated ground-negative and negative-equality selection policies; 46 Rust tests and 240 combined compiled-Lean replays passed.
- [x] Add and test isolated constant-heavy and inverse-frequency KBO weights; 41 Rust tests and 120 compiled-Lean replays passed.
- [x] Integrate and qualify the KBO weights and additional selection policies; 360 installed compiled-Lean replays passed.
- [x] Add and qualify optional bounded LPO ordering in low-level producers; 40 installed compiled-Lean replays passed. Default search still uses KBO.
- [x] Profile variable counting on shared terms and test an isolated bounded DAG implementation against expanded occurrence lists.
- [x] Replay 366 certificates from the isolated DAG optimization, with identical bytes and search counters apart from timing.
- [x] Qualify and integrate the DAG variable-count optimization; 366 installed replays preserve certificate bytes and search counters apart from timing.
- [ ] Select schedule participation using training results.

## 7. Indexes

- [ ] Profile retrieval, subsumption and rewriting on retained slow inputs.
- [ ] Choose an index change supported by those measurements.
- [ ] Compare its query results with a reference implementation.
- [ ] Measure whole-search effects before integration.

## 9. Ground instantiation

- [ ] Define the effectively propositional input path and grounding limits.
- [ ] Implement ground instantiation and SAT search.
- [ ] Connect UNSAT and model results to checked original-input results.
- [ ] Add refusal and corrupted-certificate controls.
- [ ] Review and qualify the installed path.

## 10. Parallel portfolio

- [ ] Define the shared wall-time, memory and process budgets.
- [ ] Implement concurrent strategies with cancellation and cleanup.
- [ ] Retain reproducible strategy and resource records.
- [ ] Test accounting, cancellation and conflicting candidate outcomes.
- [ ] Compare against the sequential schedule under equal total resources.

## 11. Remaining search targets

- [ ] Profile CSR114+13, CSR116+2, HWV116+1, COM146+1, COM123+1 and CSR239+1 with retained commands.
- [ ] Profile the local block-21000 fixture.
- [ ] Implement fixes for the measured failure causes.
- [ ] Verify each recovered result and record unresolved cases.

## 15-16. Certificate and clausifier costs

- [ ] Measure certificate size and replay time for repeated simplification steps.
- [ ] Evaluate position-only nodes and chain nodes.
- [ ] Prove semantics and add rejection tests for each adopted representation.
- [ ] Profile the extracted clausifier.
- [ ] Implement measured clausifier improvements while preserving its checked preprocessing connection.

## 17-19. Larger inputs and remaining refusals

- [ ] Repeat the clausification-refusal census at the final V3 limits.
- [ ] Measure decoding and premise-selection costs for larger theories.
- [ ] Address the measured byte-limit failures and qualify any new limits.
- [ ] Address formula-height and term-depth failures.
- [ ] Address literal-count and signed-goal memory failures.
- [ ] Preserve explicit refusal behavior for unsupported or exhausted paths.

## 21. Infinite-model satisfiability

- [ ] Define a certifiable infinite-model construction or saturated-set argument.
- [ ] Implement the candidate construction.
- [ ] Prove that accepted certificates imply satisfiability of the original input.
- [ ] Add valid and corrupted certificate tests.
- [ ] Obtain independent review and qualify the installed path.

## 23. Model evaluation

- [ ] Profile retained cases that exceed the model-evaluation budget.
- [ ] Implement the measured evaluation improvements.
- [ ] Add path-specific export corollaries where the proof and measurements justify them.
- [ ] Verify models and complete documents through the installed launcher.

## 25-26. Kernel coverage and certificate limits

- [ ] Inventory current kernel depth, time and input-coverage refusals.
- [ ] Extend the bundled independent kernels.
- [ ] Add structural preprocessing counterparts required by the supported paths.
- [ ] Evaluate passing certificates as Lean values and qualify the chosen route.
- [ ] Reassess the certificate-size cap using installed checker measurements.
- [ ] Check boundary refusals before adopting a larger cap.

## Final evaluation and release

- [ ] Finish independent reviews of all changed acceptance boundaries.
- [ ] Freeze source, dependency, binary and corpus hashes.
- [ ] Freeze supported inputs, output settings and equal resource budgets for each comparison.
- [ ] Run Fang without Lean checking (`--check none`).
- [ ] Run Fang with its default compiled Lean checking.
- [ ] Run Fang with kernel checking (`--check kernel`).
- [ ] Rerun the pinned Vampire under the corresponding comparison conditions.
- [ ] Separate unchecked candidates, checked results and complete requested documents.
- [ ] Report solved counts and paired wall times; never count refusals as speed wins.
- [ ] Produce the complete TXT problem list, retaining repeated occurrences.
- [ ] Produce per-occurrence TXT and CSV timings.
- [ ] Produce the searchable HTML with checking-mode views and green/red qualified timing comparisons.
- [ ] Write the benchmark report with configuration differences and exclusions.
- [ ] Update CAPABILITIES, CODEMAP and release notes to match the final implementation.
- [ ] Run final installation and release checks on the frozen candidate.
- [ ] Push the qualified changes and publish the release assets.

Beating Vampire on a sample would establish that measured result. A broader SOTA claim requires an evaluation that supports its scope; it is not a checkbox implied by implementing this plan.
