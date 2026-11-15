# V4 implementation checklist

Working checklist for [V4-PLAN.md](V4-PLAN.md). Updated 2026-11-15.

A checked box means the stated task passed at the stated scope. An isolated prototype is not an installed or released capability. Unchecked tasks still need work or evidence; they do not necessarily mean there is no earlier code. V4 is incomplete, and no SOTA result has been established.

## Current work

The current integrated installation passed qualification: 1,022 Rust tests (three ignored, including an explicit storage profile), formatting and Clippy, with the unchanged Lean build and its 1,634 fixed audits. Its launcher passed self-check, 12 positive cases with complete documents, two include-selection rejections and the malformed-UTF-8 rejection control. The latest goal-transformation follow-up passes 164 installed proof/document replays, 61 satisfiable controls, two corrupted-certificate refusals and two depth refusals. Default regression preserves 122 certificate byte streams and 34 limit refusals. The earlier KBO variable-count qualification passed 366 byte-identical installed replays across KBO and LPO; the passive-queue qualification passed 62 replays and its exhaustion, limit and orphan-deletion controls.

1. Characterize SWC279-1's sensitivity to timed search slices. The export-deadline correction is integrated and qualified: CSR051-10, CSR072-10, SEV606+1 and SWC279-1 produced complete checked documents on the new installation within the original 60-second budget. These four follow-ups do not replace the earlier 222/226 campaign. SWC279-1 also passed with the unchanged launcher, so its earlier search timeout remains unexplained.
2. Obtain independent review and integrate equality factoring. The coherent native build, all 1,634 fixed audits, original-input compiled replay, named document and corruption controls passed, as did the full kernel route.
3. Finish qualification of the retained-clause array exporter. Its isolated 53-module rebuild, seven compiled result/error controls and 14 byte-identical document comparisons passed. Integration and installed performance measurements remain pending.
4. Measure longer slices before selecting schedule participation for the qualified KBO weights and literal-selection policies. The [first full training matrix](../benchmarks/v4-training/README.md) contains 2,048 audited cells across all 256 frozen training inputs and eight strategies, using the launcher producer routes. The baseline checked 72 tasks and the union checked 74. These are single-task outcomes with two-second producer budgets, not whole-problem solves or controlled performance measurements. Defaults remain unchanged; validation and held-out outcomes are unused.

The ground-unit index is integrated and qualified. The longer training matrix is complete and audited: 1,536 cells, with 80 tasks checked by at least one variant. Baseline and lookahead each check 77 tasks at 15 producer seconds; LPO checks 73. This matrix uses the frozen pre-index installation at `40f995a`, so it does not measure the later ground-unit index. The final schedule remains unselected.

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
- [x] Qualify optional stored-record and generated-conclusion limits with 992 installer tests, 122 installed compiled-Lean replays, 34 explicit boundary refusals and the installed launcher controls.
- [x] Qualify compact literal storage with 992 installer tests (three ignored), the same 122 proof replays and 34 boundary refusals, and the installed launcher controls.

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
- [x] Validate an isolated training harness with 16 positive task controls and two corrupted-certificate rejections; complete and audit 128 pilot cells on the first 16 training inputs. These are task outcomes, not whole-problem benchmark results.
- [x] Record input kind, captured byte/file counts, goal counts and eight strategy outcomes across all 256 training inputs, retaining capture failures. Audit all 2,048 cells and publish the data and tested Rust harness in [v4-training](../benchmarks/v4-training/README.md).
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
- [x] Assess and qualify additional count limits: `max_stored` includes all proof records, and `max_generated` includes conclusions later discarded. Neither is a total-memory or unification-work limit; both default to unset.
- [x] Profile passive-clause memory and qualify compact literal arrays. The record shrinks from 112 to 104 bytes on the tested target; 12 paired fixed-work comparisons on two training inputs preserve search counters. At 1,600 given clauses, median process RSS fell about 9% and 11%; the smaller SYO694 case had a roughly 2% increase. These measurements do not establish a general memory or speed improvement.
- [x] Check installed search behavior and resource accounting with 62 compiled certificate replays, eight queue controls, two passive-limit controls and a real orphan-deletion case.

## 5. Unit-equality search

- [x] Add an optional bounded ground-congruence shortcut with explanations expanded to existing checked rules. Qualify 45 installed compiled-Lean proofs and documents, 15 negative controls and two corrupted-certificate refusals. The default remains off.
- [x] Compare the shortcut enabled and disabled on all 256 frozen training inputs at two producer seconds. Both check the same 72 tasks; this experiment adds no coverage. See [V4-SEARCH-PROFILE.md](V4-SEARCH-PROFILE.md).
- [x] Implement and qualify bounded ground-joinability redundancy for equations with variables. It checks every total preorder of at most four variables and is restricted to positive unit critical pairs in pure UEQ problems with uniform KBO. Unknown or refused work retains the candidate; no formal completeness proof is claimed.
- [x] Compare the unit-equation redundancy option on all 256 frozen training inputs. Its 512-cell trial checks 71 tasks with the heuristic and 72 without it. The integrated option remains off by default.
- [x] Implement and test inference-local connectedness, including 5,120 bounded graph comparisons, ground-substitution checks, 108 compiled proofs/documents and 36 satisfiable controls.
- [x] Compare connectedness on all 256 training inputs. The 512-cell matrix checks 72 tasks disabled and 71 enabled; it loses GRP777-10 and adds none. The default remains off.
- [x] Compare standard, max-side and shared-max-side scores on all 256 training inputs: 768 audited cells, with 72, 71 and 71 checked tasks respectively, and union 74. A 30-cell follow-up covers all five changed tasks at two and 15 seconds; all 17 positive outcomes also export complete documents. These isolated results do not change the default score.
- [x] Integrate and qualify the optional scores together with unit-equation redundancy: 1,009 installer tests, 54 new installed compiled proofs/documents, 18 satisfiable controls, 122 default certificate replays and 34 explicit limit refusals. Defaults remain unchanged.
- [x] Implement ground-goal transformation with direct proof reconstruction over original inputs. The isolated candidate passes 85 Rust tests, 30 compiled proofs/documents, 15 satisfiable controls and two corrupted-certificate refusals. Ten plain proofs exercise actual definition erasure.
- [x] Combine connectedness and goal transformation with the existing scores and unit redundancy. The isolated combined candidate passes 90 Rust tests, 246 compiled proofs/documents and 87 satisfiable controls, plus 122 default replays and 34 limit refusals.
- [x] Complete and audit the 512-cell goal-transformation training matrix. Disabled checks 72 tasks and enabled 67, with no added task. The five losses are GRP777-10, GRP442-1, GRP529-1, GRP448-1 and GRP519-1; the option remains off by default.
- [x] Qualify connectedness and goal transformation through the production installer: 1,020 Rust tests, 246 installed proofs/documents, 87 satisfiable controls, two corrupted-certificate refusals, 122 default replays and 34 limit refusals. Both defaults remain off.
- [x] Qualify final complementary unit resolution and bound replacement depth before expansion: 1,022 installer tests, 164 installed proofs/documents, 61 satisfiable controls, two corrupted-certificate refusals and two depth refusals. The signed producer's existing typed resource outcome is preserved. GRP529-1, GRP448-1 and GRP519-1 recover at two and 15 seconds; GRP442-1 still reaches the depth bound.
- [x] Repeat the full 512-cell goal-transformation training matrix after the correction: 70 tasks disabled, 69 enabled, union 71. All three corrected tasks recover. Baseline outcomes also vary under concurrent load; retain both matrices and keep the default off.
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

The [search profile](V4-SEARCH-PROFILE.md) records the measurements and remaining failures.

- [x] Profile retrieval, subsumption and rewriting on the six retained development inputs at 400 and 4,000 given clauses.
- [x] Add exact ground-unit keys for forward/backward subsumption and unit deletion. On CSR114+13 and CSR116+2, the heaviest-negative prefix drops from 26,047,266 to 263,099 subsumption calls with identical inference counters.
- [x] Compare both query directions on 210 clause shapes and 4,900 exact unit-deletion pairs against linear search, including deleted entries and activation order.
- [x] Compare 20 fixed-work before/after pairs with identical search counters and certificate bytes; exclude four timed pairs. The six-target full producer follow-up adds no solves. Qualify the installed index with 995 Rust tests, 122 compiled-Lean replays, 34 explicit refusals and the installed launcher controls. Timing observations remain development diagnostics.

## 9. Ground instantiation

- [ ] Define the effectively propositional input path and grounding limits.
- [x] Test an isolated bounded grounder for equality-free, function-free clauses with original constants: three Rust controls, 256 two-element semantic comparisons, sparse variable IDs and exact count boundaries. Equality and constant-free signatures remain unsupported in this prototype; it has no SAT or acceptance path yet.
- [x] Test isolated reconstruction of propositional learned clauses by reverse unit propagation. Six Rust tests include all 256 subsets of the eight non-tautological clauses on two variables, malformed claims and exact resource boundaries.
- [x] Connect the isolated grounder to CDCL with bounded learned-clause recording and RUP reconstruction. Eleven Rust tests include 4,096 three-variable formulas checked against truth tables, learned clauses on pigeonhole problems and trace-budget exhaustion.
- [x] Reconstruct original-input proofs with explicit resolution and factoring. The first transport passes 13 Rust tests, seven compiled-Lean checks and seven complete documents, including first-order variables, FOF preprocessing and pigeonhole refutations.
- [x] Transport satisfying assignments to existing finite-model certificates and evaluate original formulas before emission. Four models, including an existential and quoted names, pass the unchanged Lean checker and exporter; the combined prototype passes 14 Rust tests.
- [x] Extend the isolated path to constant-free signatures. Refutations use an arbitrary variable and existing inference rules; models use a one-element domain. The combined controls pass 11 original-input proofs, six models, all 17 documents, two unsupported-input refusals and four invalid-candidate refusals. The receipt is `experiments/v4-epr-constant-free-v1/receipt.json`, SHA-256 `66612351398d3d641918d5449704c22c548b98d736ab8d2c18b31c6ceeb84fc0`.
- [x] Add isolated equality refinement and quotient models. Exhaustive controls classify all 4,096 assignments over three constants and a unary predicate; each of the 4,074 conflict lemmas is tested against 216 interpretations. Another 4,096 ground formulas are compared with finite interpretations. The 17-test prototype passes 12 proof and ten model checks with complete documents. Its receipt is `experiments/v4-epr-equality-v1/receipt.json`, SHA-256 `2e7d3dda83a28c952ed40881084cdae2a7d7b8125ef3cfe6544a4af202b36681`.
- [x] Reconstruct equality-theory proofs and their TSTP documents in an isolated successor. Canonical chain witnesses supply valid theory clauses; Lean proves their validity, original-input acceptance and document correspondence. All 15 audited theorem dependencies contain only `propext`, `Classical.choice` and `Quot.sound`. Eighteen Rust tests, 24 original-input proof checks, ten model checks and all 34 documents pass. Corrupted certificates and changed inputs are rejected. Native checks trust the compiler/runtime; kernel-mode instance qualification and independent acceptance review remain open. The receipt is `experiments/v4-epr-theory-proof-v1/receipt.json`, SHA-256 `ace1d03d9f5f9a57c19a6c33a1e974b28bf383e5919017bf05a75e03547ca47f`.
- [ ] Integrate ground instantiation and SAT search in the product.
- [ ] Connect both result kinds to the installed original-input checking routes.
- [ ] Integrate and qualify equality handling, signed/include routes and strategy selection; the controls above cover standalone prototypes.
- [ ] Add refusal and corrupted-certificate controls.
- [ ] Review and qualify the installed path.

## 10. Parallel portfolio

- [ ] Define the shared wall-time, memory and process budgets.
- [ ] Implement concurrent strategies with cancellation and cleanup.
- [ ] Retain reproducible strategy and resource records.
- [ ] Test accounting, cancellation and conflicting candidate outcomes.
- [ ] Compare against the sequential schedule under equal total resources.

## 11. Remaining search targets

- [x] Profile the six named inputs with retained launcher commands and search instrumentation. COM146+1 produces a checked complete document; the other five remain unresolved under the recorded budgets.
- [x] Recover the original block-21000 bytes from four matching historical copies. The preceding qualified installation returns Satisfiable with a checked one-element model and a complete document.
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
