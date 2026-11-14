# Version 4 work plan

Version 4 starts from [v0.3.0-alpha.1](https://github.com/shalashaska117/Fang/releases/tag/v0.3.0-alpha.1), commit `8947c0aad087bbe9f50d5988c1ed4be06cf1272a`. This plan carries forward the 26 work items agreed before that release. It describes planned work, not capabilities of the released version.

The target is competitive checked first-order reasoning on FOF and CNF: FNE, FEQ, unit equality and effectively propositional problems. ICU is an evaluation target. Results must include checking and the requested output. Typed logic, higher-order logic and arithmetic belong to the later versions in the [roadmap](ROADMAP.md).

## Starting measurements

The release's [benchmark report](https://github.com/shalashaska117/Fang/releases/download/v0.3.0-alpha.1/benchmark.md) is the v3 baseline. Earlier development measurements used different source revisions or conditions and must not replace it.

| Sample | Fang v3 counted results | Vampire counted results |
| --- | ---: | ---: |
| Mixed d286 | 180 / 286 | 235 / 286 |
| Satisfiable sample | 175 / 250 | 140 / 250 |
| TPTP 1000 | 267 / 1000 | 820 / 1000 |

A counted result needs a positive status, successful exit, no safety termination, a complete requested document and command wall time within 60 seconds. Fang also needs its compiled checker acceptance. The d286 Vampire total includes the incorrect nested-selection result discussed in the report. Sample memberships overlap; totals must not be added as if they were disjoint. See the report for paired timings and measurement limitations, and the [problem list](https://github.com/shalashaska117/Fang/releases/download/v0.3.0-alpha.1/fang-v3-vs-vampire-problems.txt) for every occurrence.

On the 1000-case sample, Fang returned 493 checked positive statuses. Of these, 226 lacked a complete document: 184 signed include bundles, 28 single-file distinct-object cases, 11 exporter rejections and three export timeouts. Fixing output is a separate task from finding more proofs. The include restriction is checked before other export restrictions, so removing it does not by itself establish that all 184 cases will produce documents.

## First integration milestones

Work proceeds on a branch based on the published v3 source. The released source, installation and benchmark evidence remain the reference.

- Item 14: both trace checker entry points now use an array clause store. Equivalence proofs preserve the complete result and every error. The source integration passed axiom audits for 1,596 declarations, 36 AST checks and 24 compiled-certificate replays against v3, with identical exits and output. Installation and end-to-end performance measurements remain separate work.
- Item 24: the 226 missing documents have been classified against their retained inputs. A two-file premise/goal fixture reproduces the include limitation. An isolated Lean bridge now connects the cited task to checked refutation rows and the final empty clause, with seven proofs and seven executable checks. Source-row rendering and runtime routing are still required before this becomes broader TSTP support.

The array checker source integration and the isolated exporter bridge have independent reviews. Focused kernel compatibility tests also check the existing helpers and concrete certificates against both checker versions. The bridge is not part of the installed exporter. No speedup is claimed from the array change until it is measured.

## Search

1. Discover a larger strategy schedule on training inputs disjoint from evaluation corpora. Select strategies using problem features and allow unequal slice lengths.
2. Add AVATAR splitting. First measure a producer-only expansion and its certificate cost; introduce a checked split rule only if needed, with an explicit definition for each fresh predicate.
3. Add deterministic learned clause selection. Record how the model was trained and keep evaluation inputs out of training.
4. Control the passive set with lazy orphan deletion, count-based resource limits and a more compact representation.
5. Improve unit-equality search through ground joinability, connectedness, critical-pair scoring and goal transformation.
6. Add literal-selection and ordering variants to the schedule, including KBO weight schemes and an LPO slice.
7. Profile before changing indexes. Candidates include discrimination trees, fingerprints, feature vectors and cached rewriting.
8. Add equality factoring to certificates with a checked inference rule.
9. Add ground instantiation with SAT for effectively propositional problems.
10. Add a parallel portfolio with an explicit shared resource budget and reproducible strategy records.
11. Revisit the remaining v3 search targets, including CSR114+13, CSR116+2, HWV116+1, COM146+1, COM123+1, CSR239+1 and the local block-21000 fixture. Historical time and memory observations are leads for profiling, not current measurements.

## Runtime and checking cost

12. Reduce time spent on unsuccessful schedule slices. Measure search, checking and output separately as well as end to end.
13. Reduce fixed per-problem costs, including goal listing and checker startup. Profile large-input preprocessing separately from short-certificate replay.
14. Replace repeated list-indexed clause lookup with an array store and improve substitution lookup where profiling justifies it. Preserve exact acceptance and rejection behavior; validate the actual runtime path.
15. Investigate position-only certificate nodes and chain nodes for demodulation, subsumption resolution and unit deletion. Each new representation needs checked semantics and malformed-certificate tests.
16. Improve the extracted clausifier's runtime while preserving its connection to the checked preprocessing definitions.

## Input coverage

17. Support larger theories currently rejected by byte limits. Evaluate decoding cost and premise selection before increasing limits.
18. Repeat the clausification-refusal census against the final v3 limits, then address the remaining cases.
19. Address formula height, term depth, literal-count bounds and memory use during signed-goal setup. Limits must remain explicit until the corresponding paths are validated.
20. Resolve the remaining small frontend gaps: non-ASCII comments, the `assumption` role and typed declarations found in otherwise FOF/CNF inputs. This does not move general typed reasoning into v4.

## Satisfiability

21. Certify satisfiability for problems with only infinite models. A saturated clause set needs a proved model construction or another checked satisfiability argument before it can yield a positive status.
22. Improve finite-model search: instance-size limits, incremental solving across domain sizes, maximum-size detection and domains guided by inferred sorts. A smaller sorted search must still produce a model checked against the original unsorted input.
23. Address model-evaluation costs and cases that exceed the existing budget. Consider per-path corollaries of the export determination theorem where they help document the result.

## Output and kernel replay

24. Export complete TSTP refutations for signed include bundles, including cited-premise certificates, and for signed single files with distinct objects. Cover goal and inputs-refutation paths, nested includes, selection lists and original statement identities. Unsupported paths must continue to refuse export explicitly.
25. Extend kernel replay beyond its current depth and runtime limits. Work includes the bundled independent kernels, structurally recursive preprocessing counterparts and passing certificates as Lean values.
26. Reassess the certificate-size cap after item 14 is integrated and measured. Do not raise it based only on an isolated data-structure result.

## Acceptance and evaluation

The entire Rust engine and runtime must remain safe Rust. External libraries are permitted when their algorithms help and they satisfy that constraint; testing and integration dependencies must remain distinguishable from runtime dependencies. New tooling does not require Python.

Checker changes must preserve or prove the intended acceptance semantics. Lean proofs must stay within the existing axiom policy: `propext`, `Classical.choice` and `Quot.sound`. Changes to an acceptance boundary receive an independent review, executable rejection tests and the relevant axiom audits. Source maps, import closures and installation checks must describe the source actually built.

Use focused replay and regression tests while implementing. Run a new end-to-end comparison only on a stable candidate, using fixed resource limits and preserved inputs. Report checked positive statuses separately from complete requested documents, and solved counts separately from timings on common solves. Strategy training and evaluation must use disjoint corpora. A local speedup or a recovered export path is not evidence that the whole version meets its competitive target.
