# Code map

This is a guide to the current source tree: where an input goes, where search happens, and where a result is checked. For the logical claims and trust assumptions, read [Design and verification](docs/DESIGN.md). For released support, commands and limits, read [Capabilities](docs/CAPABILITIES.md) and [Usage](docs/USAGE.md).

The installed `fang` command comes from `fang-launcher`. The root package is also named `fang`, but its executable is the older candidate-producing CNF engine. Running that executable directly does not run the installed checking pipeline.

The default profile is still called `v8`: this names the capability and certificate interfaces, not the release's search algorithm. It uses the v3 saturation search. `--profile cnf` and `--profile ground-fof` select separate older paths explicitly; the launcher does not retry a failed input through another profile. Likewise, `candidate`, `experimental`, `isolated` and version numbers in source names can describe a component's origin. Check the installed maps and call sites before deciding whether it is used.

## Folder tree

```text
Fang/
|-- Cargo.toml                 Root engine, workspace membership and local dependencies
|-- Cargo.lock                 Pinned Rust dependency graph
|-- rust-toolchain.toml        Rust toolchain selection
|-- runtime-staging.json       Source staging provenance
|-- src/                      Root CNF engine and shared term/literal types
|-- crates/                   43 crate directories, catalogued below
|   |-- fang-launcher/        Installed command, routes, checking and status delivery
|   |-- fang-saturation/      V3 refutation search and producer binaries
|   |-- fang-models/          Finite-model search and candidate certificates
|   |-- tptp-*/               Input, includes, roles and producer adapters
|   |-- *fof*/                Formula representations, parsers and preprocessing
|   |-- equality-*/           Equality terms, inference reconstruction and search
|   |-- fang-install/         Source builds, Lean builds and installation
|   |-- fang-source-checks/   Source maps and dependency validation
|   |-- v8-kernel*/           Exact-instance kernel replay and witnesses
|   `-- fang-*/               Shared hashing, serialization and process tools
|-- lean-v8/                  Current compiled checkers, exporters and proofs
|   |-- Fang/                Logic, core checker, source semantics and frontend proofs
|   |-- Product/             TSTP syntax, rendering and source-link proofs
|   `-- *.lean               Preprocessing, bundle/role/model entries and soundness
|-- lean/                    CNF and ground-FOF checkers for the older profiles
|   `-- Fang/                Their logic, checker and frontend modules
|-- proofs/
|   |-- tstp/                Older CNF export and composition proofs
|   `-- fof-tstp/            Older ground-FOF export and composition proofs
|-- tools/
|   |-- v8_szs/              Rust/Lean source maps and backend pins
|   |-- v8_kernel/           Kernel policy, recipe map and Lean support modules
|   `-- fof_szs/             Older ground-FOF source map
|-- tests/                    Root-engine integration tests
|-- examples/                 Small Rust/TPTP examples, including problems/
|-- docs/                     Usage, capabilities, design and roadmap
`-- LICENSES/                 Retained licenses and origin notices
```

Tests also live beside their code in `#[cfg(test)]` modules and in each crate's `tests/` directory. `lean-v8/*Controls.lean` contains executable checks and examples, while `*Audit.lean` modules collect axiom reports. Local build directories, experiments, benchmark runs and evidence archives are not part of the distributed source tree.

## Start here for a particular task

| Looking for | Entry point | Follow next |
| --- | --- | --- |
| Which command runs by default | [`dispatch::selected_profile`](crates/fang-launcher/src/dispatch.rs) | [`v8::run::pipeline`](crates/fang-launcher/src/v8/run.rs), then the installed capability |
| Input capture, includes and route selection | [`signed::discover` and `signed::route`](crates/fang-launcher/src/v8/signed.rs) | [`bundle::needs_bundle`](crates/fang-launcher/src/v8/bundle.rs) and [`run.rs`](crates/fang-launcher/src/v8/run.rs) |
| CNF syntax and the older CNF prover | [`src/parser.rs`](src/parser.rs), [`src/syntax.rs`](src/syntax.rs) | [`search::prove`](src/search.rs), [`Unifier::unify`](src/unify.rs) |
| Current CNF/FOF parsing | [`tptp-cnf-boolean/src/lib.rs`](crates/tptp-cnf-boolean/src/lib.rs) | [`prepare_named`](crates/fang-tptp-expanded/src/named_prepare.rs); bundles also use [`tptp-coverage`](crates/tptp-coverage/src/lib.rs) |
| FOF normalization and clausification | [`quantified-fof-core`](crates/quantified-fof-core/src/lib.rs), [`skolem-core`](crates/skolem-core/src/lib.rs) | [`binder-removal-core`](crates/binder-removal-core/src/lib.rs), [`fof-core`](crates/fof-core/src/lib.rs), [`naming.rs`](crates/fof-core/src/naming.rs) |
| V3 given-clause loop | [`Search`](crates/fang-saturation/src/search.rs) | [`Options`](crates/fang-saturation/src/options.rs), [`producer::refute_prepared_portfolio`](crates/fang-saturation/src/producer.rs) |
| Passive queues and pruning | [`Search::select`, `admit` and `take_passive`](crates/fang-saturation/src/search.rs) | [`Options::orphan_deletion` and `max_passive`](crates/fang-saturation/src/options.rs), [`stats.rs`](crates/fang-saturation/src/stats.rs), [`orphan_tests.rs`](crates/fang-saturation/src/orphan_tests.rs) |
| Stored-record and generated-conclusion limits | [`Search::try_push` and `derived_with_parents`](crates/fang-saturation/src/search.rs) | `max_stored` and `max_generated` in [`options.rs`](crates/fang-saturation/src/options.rs); boundary tests in [`count_limit_tests.rs`](crates/fang-saturation/src/count_limit_tests.rs). Both limits stop with a resource refusal. |
| Compact clause records | [`ClauseRec`](crates/fang-saturation/src/clause.rs) and [`Search::try_push`](crates/fang-saturation/src/search.rs) | Fixed-length literal arrays are allocated at admission. [`storage_profile.rs`](crates/fang-saturation/src/storage_profile.rs) contains the explicit allocation census. |
| Ground-congruence shortcut | [`ground_join.rs`](crates/fang-saturation/src/ground_join.rs) | Bounded congruence closure and explanation paths. [`ground_join_search.rs`](crates/fang-saturation/src/ground_join_search.rs) reconstructs existing paramodulation/equality-resolution rules; `Search::run` calls it once when enabled. |
| Ground-unit retrieval | [`Index::ground_units`, `ground_in_nonunits` and `ground_unit_key`](crates/fang-saturation/src/index.rs) | `Search::index_insert`, `subsumer_candidates`, `subsumed_candidates` and `subsumption_resolution` in [`search.rs`](crates/fang-saturation/src/search.rs); linear-reference comparisons in [`ground_unit_index_tests.rs`](crates/fang-saturation/src/ground_unit_index_tests.rs). |
| Term storage, ordering and substitutions | [`term.rs`](crates/fang-saturation/src/term.rs), [`kbo.rs`](crates/fang-saturation/src/kbo.rs), [`lpo.rs`](crates/fang-saturation/src/lpo.rs), [`subst.rs`](crates/fang-saturation/src/subst.rs) | `Order::compare` dispatches KBO or bounded LPO; literal ordering is shared. See also [`clause.rs`](crates/fang-saturation/src/clause.rs) and [`index.rs`](crates/fang-saturation/src/index.rs). |
| KBO symbol weights | [`weights.rs`](crates/fang-saturation/src/weights.rs) | `Scheme` selects uniform, constant-heavy or inverse-frequency weights. `Weights::pair` counts shared terms with multiplicity and refuses overflow or excess work. |
| KBO variable counts | [`variable_balance.rs`](crates/fang-saturation/src/variable_balance.rs) | `balance` retains expanded counting for small terms. `bounded` propagates multiplicity differences through shared nodes, with arithmetic and work limits. It affects search ordering, not certificate acceptance. |
| Literal selection | [`Search::eligibility`](crates/fang-saturation/src/search.rs) | [`Selection`](crates/fang-saturation/src/options.rs) includes weight, lookahead, ground-negative and negative-equality policies. [`selection_tests.rs`](crates/fang-saturation/src/selection_tests.rs) checks preferences and tie-breaking. |
| Premise selection and retained citations | [`sine.rs`](crates/fang-saturation/src/sine.rs), [`cited.rs`](crates/fang-saturation/src/cited.rs) | [`cited_inputs`](crates/tptp-signed-bundle/src/cited_inputs.rs), including distinct-object origins |
| Strategy training and evaluation memberships | [`benchmarks/v4-corpus`](benchmarks/v4-corpus/README.md) | Frozen training, validation and held-out lists, their hashes and the standalone Rust selector. This directory contains no benchmark outcomes. |
| Strategy training outcomes | [`benchmarks/v4-training`](benchmarks/v4-training/README.md) | The complete 2,048-cell task matrix, captured-input and binary hashes, and the safe Rust collection harness. Timings are development diagnostics; final evaluation remains separate. |
| Equality resolution, factoring and paramodulation | [`equality-inference-core`](crates/equality-inference-core/src/lib.rs), [`equality-paramodulation-core`](crates/equality-paramodulation-core/src/lib.rs) | V3 inference generation in [`search.rs`](crates/fang-saturation/src/search.rs) and certificate construction in [`proof.rs`](crates/fang-saturation/src/proof.rs) |
| Finite models | [`fang-models/src/lib.rs`](crates/fang-models/src/lib.rs) | [`search::search`](crates/fang-models/src/search.rs), [`sat.rs`](crates/fang-models/src/sat.rs), then [`ModelEntries.lean`](lean-v8/ModelEntries.lean) |
| Why a conjecture gives a particular SZS status | [`signed::listing`, `accepted` and `final_status`](crates/fang-launcher/src/v8/signed.rs) | [`run.rs`](crates/fang-launcher/src/v8/run.rs) and [`output.rs`](crates/fang-launcher/src/output.rs) |
| Compiled checker entry points | [`ExpandedNamedNativeMain.lean`](lean-v8/ExpandedNamedNativeMain.lean), [`SignedBundleNativeV6Main.lean`](lean-v8/SignedBundleNativeV6Main.lean) | The Lean route table below |
| TSTP output | [`run.rs`](crates/fang-launcher/src/v8/run.rs): `signed_documents`; [`stages.rs`](crates/fang-launcher/src/v8/stages.rs), [`protocol.rs`](crates/fang-launcher/src/v8/protocol.rs) | [`NamedDocumentDepth.lean`](lean-v8/NamedDocumentDepth.lean), [`CitedDocumentNativeCore.lean`](lean-v8/CitedDocumentNativeCore.lean), [`ModelExport.lean`](lean-v8/ModelExport.lean) |
| Kernel replay | [`v8/kernel.rs`](crates/fang-launcher/src/v8/kernel.rs) | [`v8-kernel/src/check.rs`](crates/v8-kernel/src/check.rs), [`generator/`](crates/v8-kernel/src/generator) |
| Deadlines, memory and child processes | [`fang-supervisor/src/lib.rs`](crates/fang-supervisor/src/lib.rs) | Launcher [`run.rs`](crates/fang-launcher/src/v8/run.rs) and [`models.rs`](crates/fang-launcher/src/v8/models.rs) |
| Source and executable identity | [`rust-sources.json`](tools/v8_szs/rust-sources.json), [`lean-sources.json`](tools/v8_szs/lean-sources.json) | [`Capability::load`](crates/fang-launcher/src/capability.rs), [`v8/verify.rs`](crates/fang-launcher/src/v8/verify.rs) |
| Installation and proof audits | [`v8_install.rs`](crates/fang-install/src/v8_install.rs), [`lean_build.rs`](crates/fang-install/src/lean_build.rs) | [`fang-source-checks`](crates/fang-source-checks/src/lib.rs), [`fang-axiom-audit`](crates/fang-axiom-audit/src/lib.rs) |

## One checked run, end to end

1. The installed launcher loads `v8-capability.json`, parses the command line and creates a supervised run. The capability binds the producer, checker and exporter paths to hashes. [`dispatch.rs`](crates/fang-launcher/src/dispatch.rs) chooses the profile; [`v8/run.rs`](crates/fang-launcher/src/v8/run.rs) owns the current pipeline and its run record.
2. The launcher captures the original bytes and included files. [`v8/signed.rs`](crates/fang-launcher/src/v8/signed.rs) identifies roles and selected goals; [`v8/bundle.rs`](crates/fang-launcher/src/v8/bundle.rs) handles bundle requirements and transport. A plain single file, an include/object bundle and a signed task need different checker inputs.
3. The selected Rust adapter prepares a numeric problem. The expanded and signed frontends perform normalization, Skolemization, binder removal and clausification. Naming introduces predicates to control formula expansion. The producer flags explicitly select `--search v3`; direct low-level producer calls have their own mode defaults, defined in [`producer::split`](crates/fang-saturation/src/producer.rs).
4. [`fang-saturation`](crates/fang-saturation/src/lib.rs) searches for an empty clause. It manages active/passive clauses, age/weight selection, term ordering, indexing, simplification and inference generation. [`proof.rs`](crates/fang-saturation/src/proof.rs) turns the selected derivation into the version-8 certificate. Signed bundle reduction records the original premises needed for replay, including declarations that introduce distinct objects.
5. The Lean checker reads the captured input and candidate independently. It reconstructs preprocessing and checks the inference trace. Rust search success alone is not acceptance. In the signed path, the checker's goal listing and one accepted certificate per required task determine the final status.
6. The compiled-mode schedule can also invoke [`fang-models`](crates/fang-models/src/lib.rs). It grounds finite domains and uses its SAT solver to construct an interpretation. [`ModelNativeMain.lean`](lean-v8/ModelNativeMain.lean) checks the candidate against the original problem. No model found means no model result.
7. With `--output tstp`, the matching Lean exporter renders the accepted refutation or interpretation. [`v8/protocol.rs`](crates/fang-launcher/src/v8/protocol.rs) validates stage output; [`output.rs`](crates/fang-launcher/src/output.rs) delivers SZS output. `Run::export_document` uses the remaining original command deadline, leaving a one-second output reserve. Search slices cannot shorten that export budget. Search, checking and export still share the command's resource limits, and export can fail after a logical candidate has been checked.

`--check kernel` uses the separate kernel producer and exact-instance replay path. `--check none` explicitly skips independent checking and labels results unchecked. See [Design and verification](docs/DESIGN.md) for the resulting trust differences.

## Installed names versus build targets

The installer deliberately keeps stable executable names. These mappings are recorded in [`rust-sources.json`](tools/v8_szs/rust-sources.json); the launcher itself is installed by [`fang-install`](crates/fang-install/src/v8_install.rs).

| Installed executable | Cargo target/source | Role |
| --- | --- | --- |
| `bin/fang` | [`fang-launcher/src/main.rs`](crates/fang-launcher/src/main.rs), target `fang-launcher` | Public checked command |
| `fang-v8-engine` | [`single_named.rs`](crates/fang-saturation/src/bin/single_named.rs), target `fang-v3-single-named` | Current single-file producer with naming |
| `fang-bundle-producer` | [`bundle.rs`](crates/fang-saturation/src/bin/bundle.rs), target `fang-v3-bundle` | Bundle producer |
| `fang-signed-producer` | [`cited_bundle_final.rs`](crates/fang-saturation/src/bin/cited_bundle_final.rs), target `fang-v3-cited-bundle-final` | Signed bundle producer with cited premises |
| `fang-signed-single-producer` | [`signed_named.rs`](crates/fang-saturation/src/bin/signed_named.rs), target `fang-v3-signed-named` | Signed single-file producer with naming |
| `fang-kernel-producer` | [`single.rs`](crates/fang-saturation/src/bin/single.rs), target `fang-v3-single` | Separate unnamed producer for kernel replay |
| `fang-model-find` | [`fang-models`](crates/fang-models/Cargo.toml), target `fang-model-find` | Finite-model candidates |
| `fang-v8-witness` | [`v8-kernel-witness/src/main.rs`](crates/v8-kernel-witness/src/main.rs), target `fang-v8-witness` | Kernel replay witness generation |

`cited_bundle_final.rs` directly includes [`experimental/cited_bundle_cli.rs`](crates/fang-saturation/src/experimental/cited_bundle_cli.rs) and [`experimental/final_limits.rs`](crates/fang-saturation/src/experimental/final_limits.rs). Those files are on the installed path despite their directory name. The other producer targets in [the saturation manifest](crates/fang-saturation/Cargo.toml) remain available for their respective transports and modes; the table above identifies which ones the installation selects.

## Rust crate catalogue

The root [Cargo manifest](Cargo.toml) declares 35 explicit members plus the root package, and excludes eight crate directories from workspace membership. An excluded crate can still be a path dependency or have a separately built executable. In particular, quantified frontend/core code is used by the preprocessing pipeline, and the ground-FOF driver builds separately. The tables cover the root package and all 43 shipped crate directories. Package names can differ from directory names; the two `fang-fof-core` manifests represent different source directories.

### Command, installation and shared runtime

| Directory / package | Responsibility and useful files |
| --- | --- |
| [`fang-launcher`](crates/fang-launcher/) / `fang-launcher` | Installed command. `dispatch.rs` selects a profile; `v8/` captures input and coordinates producers/checkers/exporters; `profile_cnf/` and `profile_ground_fof/` implement explicit older profiles. `capability.rs`, `manifest.rs` and `output.rs` define identity, records and delivery. |
| [`fang-install`](crates/fang-install/) / `fang-install` | Fetches the pinned backend, snapshots sources, builds Rust/Lean and installs the command. Start with `fetch.rs`, `lean_build.rs`, `v8_install.rs`; `local_build.rs` builds older profiles and `check_suite.rs` checks the older Lean proof suite. |
| [`fang-source-checks`](crates/fang-source-checks/) / `fang-source-checks` | Validates source maps, local dependency boundaries, file inventories and optional receipt provenance. `v8/` handles the current maps; `deps.rs`, `fof.rs` and `backend.rs` cover dependencies and backend inputs. |
| [`fang-supervisor`](crates/fang-supervisor/) / `fang-supervisor` | Runs bounded Linux child stages under a shared deadline, monitors owned processes and memory, and captures stage output and artifacts. |
| [`fang-hash`](crates/fang-hash/) / `fang-hash` | Safe Rust SHA-256, streaming/file hashing and tagged chunked hashes. `sha256.rs`, `stream.rs`, `file.rs` and `chunked.rs` implement the forms used by source and runtime identity checks. |
| [`fang-json`](crates/fang-json/) / `fang-json` | JSON values, bounded parsing and serialization for capabilities, manifests and reports. `python.rs` preserves formatting conventions from the former tools; it is Rust code. |
| [`fang-toml`](crates/fang-toml/) / `fang-toml` | Parses the TOML subset used by the Cargo manifests, lockfiles and toolchain files into `fang_json::Value`. |
| [`fang-axiom-audit`](crates/fang-axiom-audit/) / `fang-axiom-audit` | Parses Lean `#print axioms` output and enforces the allowed axiom set. Shared by build audits and replay checks. |
| [`fang-kernel-workspace`](crates/fang-kernel-workspace/) / `fang-kernel-workspace` | Creates and inventories fresh kernel workspaces, archives them and records partial retention. Shared by the launcher profiles and kernel entry. |
| [`v8-kernel`](crates/v8-kernel/) / `fang-v8-kernel` | Kernel entry, exact-instance Lean module generation and replay. `entry.rs`/`check.rs` run the check; `generator/` emits replay terms; `install.rs`, `helpers.rs` and `provision.rs` prepare its support files. |
| [`v8-kernel-witness`](crates/v8-kernel-witness/) / `fang-v8-kernel-witness` | Produces the preprocessing witness consumed by kernel replay. The command entry is `src/main.rs`. |

### Search, terms and inference

| Directory / package | Responsibility and useful files |
| --- | --- |
| [`src/`](src/) / root package `fang` | Shared `Term`, `Literal`, `Clause` and symbol types in `syntax.rs`; CNF parsing in `parser.rs`; unification in `unify.rs`; candidate refutation search in `search.rs`. The root `main.rs` exposes the older candidate-only CLI. Other crates reuse this library. |
| [`fang-saturation`](crates/fang-saturation/) / `fang-saturation` | V3 search. `search.rs` is the given-clause loop; `term.rs` stores terms, `subst.rs` substitutes, `kbo.rs` orders terms, `index.rs` indexes clauses, `sine.rs` selects premises and `proof.rs` builds certificates. `producer.rs` handles modes, limits, portfolios and statistics. |
| [`fang-models`](crates/fang-models/) / `fang-models` | Finite-domain search. `problem.rs` constructs tasks; `clausify.rs` and `flatten.rs` prepare them; `lib.rs` selects the search range; `search.rs` grounds domains; `sat.rs` solves the Boolean encoding; `evaluate.rs` checks candidates locally and `certificate.rs` serializes them for Lean. |
| [`fang-predicate-index`](crates/fang-predicate-index/) / `fang-predicate-index-core` | Predicate/sign indexing shared with the root search. Its library supplies the index contract; the V3 search also has its own indexing layer. |
| [`equality-inference-core`](crates/equality-inference-core/) / `fang-equality-inference-core` | Equality-aware atoms, literals and clauses, substitutions, and reconstruction of inference steps. `checked.rs` contains checked resource arithmetic used by reconstruction. |
| [`equality-occurrence-core`](crates/equality-occurrence-core/) / `fang-equality-occurrence-core` | Bounded operations on a selected term occurrence, used when rewriting one occurrence in an equality inference. |
| [`equality-paramodulation-core`](crates/equality-paramodulation-core/) / `fang-equality-paramodulation-core` | Reconstructs single-occurrence paramodulation using an equation direction and a position inside a clause. Builds on the inference and occurrence cores. |
| [`equality-search`](crates/equality-search/) / `fang-equality-search` | Equality-CNF candidate search, prepared-problem validation and certificate types/serialization. `ordered.rs` and `prepared.rs` implement the retained ordered-search path; V3 producers reuse its prepared-input and certificate interfaces. |

For finite-model domain limits, start at `function_free_bound` and `find` in [`fang-models/src/lib.rs`](crates/fang-models/src/lib.rs). The bound counts constants after Skolemization and is disabled by nonconstant functions. In [`search.rs`](crates/fang-models/src/search.rs), `Layout` assigns SAT variables, `ground` creates constraints, and `extract` reads only the model's function and predicate tables. `sequential_at_most_one` handles function cells for domains of size 16 or more; `planned` estimates storage before allocation. The launcher handles the distinct exhausted-bound outcome in [`v8/models.rs`](crates/fang-launcher/src/v8/models.rs). Exhaustion retires a model-search task without accepting a logical result.

### Input and preprocessing

| Directory / package | Responsibility and useful files |
| --- | --- |
| [`tptp-cnf-boolean`](crates/tptp-cnf-boolean/) / `fang-tptp-full-frontend-candidate` | Expanded TPTP CNF/FOF frontend, including Boolean syntax. Its parser is preparation code; the Lean checker separately interprets the original bytes. |
| [`tptp-coverage`](crates/tptp-coverage/) / `fang-tptp-coverage-candidate` | Bundle input and expansion: includes and selections, annotations, distinct objects and supported defined symbols. `src/lib.rs` exposes the parser and the bundle-related modules. |
| [`tptp-roles`](crates/tptp-roles/) / `fang-tptp-roles` | Role-aware declarations and obligations. `roles.rs` defines roles, input classes and signed declarations. |
| [`tptp-signed-roles`](crates/tptp-signed-roles/) / `fang-tptp-signed-roles` | Prepares a task for each selected conjecture, or the inputs task when there is no conjecture. Tracks clause origins and supports named preparation in `named_prepare.rs`. |
| [`tptp-signed-bundle`](crates/tptp-signed-bundle/) / `fang-tptp-signed-bundle` | Restores roles after include expansion and builds signed tasks. `cited_inputs.rs` chooses the original inputs needed for cited replay, including the declarations that introduce distinct objects. |
| [`tptp-bundle-v8`](crates/tptp-bundle-v8/) / `fang-tptp-bundle-v8` | Adapts a captured bundle to the expanded producer and its version-8 certificate transport. Bundle acceptance remains the Lean checker's job. |
| [`fang-tptp-expanded`](crates/fang-tptp-expanded/) / `fang-tptp-expanded-integration` | Connects expanded byte parsing to numeric preprocessing and prepared equality clauses. `named_prepare.rs` adds naming; `final_limits.rs` records the final preparation limits. |
| [`fang-v8`](crates/fang-v8/) / `fang-tptp-expanded-v8` | Version-8 candidate envelope and serialization around the expanded adapter. It does not itself establish a checked result. |
| [`equality-frontend`](crates/equality-frontend/) / `fang-equality-frontend` | Parses the equality-CNF frontend into the equality-aware representation. |
| [`quantified-equality-frontend`](crates/quantified-equality-frontend/) / `fang-quantified-equality-frontend` | Parses CNF and closed quantified FOF with built-in equality for the quantified equality pipeline. |
| [`fof-equality-bridge`](crates/fof-equality-bridge/) / `fang-fof-equality-bridge` | Converts between encoded numeric literals and explicit equality atoms, with reserved predicate identities. It is a representation bridge, not a byte parser. |
| [`quantified-equality-pipeline`](crates/quantified-equality-pipeline/) / `fang-quantified-equality-pipeline` | Combines quantified/equality preparation with candidate search and resource accounting. |
| [`quantified-pipeline`](crates/quantified-pipeline/) / `fang-quantified-pipeline` | Composes the equality-free quantified preprocessing stages and prepared clauses. |
| [`pipeline-observer`](crates/pipeline-observer/) / `fang-quantified-pipeline-observer` | Composes quantified preprocessing and exposes its intermediate results and statistics. `named.rs` supplies `prepare_parsed_named`, used by the current expanded producer. |
| [`skolem-core`](crates/skolem-core/) / `fang-skolem-core` | Introduces fresh Skolem symbols and transforms quantified formulas; tracks scopes, signatures and resource limits. |
| [`binder-removal-core`](crates/binder-removal-core/) / `fang-binder-removal-core` | Erases binders from suitably prepared NNF syntax. Its syntactic operation alone is not a semantic acceptance check. |
| [`fof-core`](crates/fof-core/) / `fang-fof-core` | Quantifier-free formula/NNF structures, normalization and distributive clausification. `nnf_entry.rs` and `naming.rs` provide entry and naming operations used by the expanded pipeline. |

### Separately scoped frontend and ground-FOF crates

These eight directories are in the root manifest's `exclude` list. Exclusion controls Cargo workspace membership; it does not determine whether other packages depend on their code.

| Directory / package | Responsibility |
| --- | --- |
| [`quantified-fof-core`](crates/quantified-fof-core/) / `fang-quantified-fof-core` | Quantified formula representation, binder identities, scope validation, rectification and NNF. Used by the quantified preprocessing crates. |
| [`quantified-fof-frontend`](crates/quantified-fof-frontend/) / `fang-quantified-fof-frontend` | CNF and closed FOF parser with nested quantifiers; a path dependency of quantified pipeline components. |
| [`ground-fof-core`](crates/ground-fof-core/) / `fang-ground-fof-core` | Ground, equality-free formulas and distributive preprocessing for the older ground-FOF path. |
| [`ground-fof-frontend`](crates/ground-fof-frontend/) / `fang-ground-fof-frontend` | Parser for the older mixed CNF/ground-FOF grammar. |
| [`ground-fof-search`](crates/ground-fof-search/) / `fang-ground-fof-search` | Connects that frontend and preprocessing to the root candidate search. |
| [`ground-fof-versioned`](crates/ground-fof-versioned/) / `fang-ground-fof-versioned` | Version-2 ground-FOF certificate envelope and the separately built `fang-ground-fof-driver` in `src/bin/driver.rs`. |
| [`fof-universal-core`](crates/fof-universal-core/) / `fang-fof-core` | Separately retained universal/scoped preprocessing source. It shares a package name with `crates/fof-core`, so use the directory path to distinguish them. |
| [`fof-universal-frontend`](crates/fof-universal-frontend/) / `fang-fof-frontend` | Separately retained frontend for mixed CNF, ground FOF and one explicit universal prefix. It is distinct from the expanded default frontend. |

## Lean checkers, logic and proof navigation

[`lean-v8/lakefile.toml`](lean-v8/lakefile.toml) declares the current Lean project. [`lean-sources.json`](tools/v8_szs/lean-sources.json) records source hashes, executable roots, dependency closures and audit declarations. Use that map when following what actually gets compiled into a particular checker or exporter.

| Installed entry | Main source | Acceptance or rendering modules to follow |
| --- | --- | --- |
| `fang-v8-check` | [`ExpandedNamedNativeMain.lean`](lean-v8/ExpandedNamedNativeMain.lean) | [`NamedDepthEntry.lean`](lean-v8/NamedDepthEntry.lean): `prepareNamedD` and the named acceptance path; [`NamedReplay.lean`](lean-v8/NamedReplay.lean), [`ExpandedLimitDecoderDepth.lean`](lean-v8/ExpandedLimitDecoderDepth.lean) |
| `fang-bundle-check` | [`BundleLimitNativeMain.lean`](lean-v8/BundleLimitNativeMain.lean) | [`BundleReplayLimit.lean`](lean-v8/BundleReplayLimit.lean), [`BundleFramerLimit.lean`](lean-v8/BundleFramerLimit.lean), [`CoverageDistinct.lean`](lean-v8/CoverageDistinct.lean) |
| `fang-signed-check` | [`SignedBundleNativeV6Main.lean`](lean-v8/SignedBundleNativeV6Main.lean) and [`SignedBundleNativeV6Core.lean`](lean-v8/SignedBundleNativeV6Core.lean) | [`NamedSignedDepth.lean`](lean-v8/NamedSignedDepth.lean), [`NamedRoleDepth.lean`](lean-v8/NamedRoleDepth.lean), [`NamedCitedDepth.lean`](lean-v8/NamedCitedDepth.lean), [`RoleCitedReadDepth.lean`](lean-v8/RoleCitedReadDepth.lean) |
| `fang-model-check` | [`ModelNativeMain.lean`](lean-v8/ModelNativeMain.lean) | [`ModelCertificate.lean`](lean-v8/ModelCertificate.lean), [`ModelSteps.lean`](lean-v8/ModelSteps.lean), [`ModelEntries.lean`](lean-v8/ModelEntries.lean), [`ModelMeanings.lean`](lean-v8/ModelMeanings.lean) |
| `fang-v8-tstp-named` | [`DocumentNamedNativeMain.lean`](lean-v8/DocumentNamedNativeMain.lean) | [`NamedDocumentDepth.lean`](lean-v8/NamedDocumentDepth.lean), [`NamedDocument.lean`](lean-v8/NamedDocument.lean) |
| `fang-goal-tstp-named` | [`GoalDocumentNamedNativeMain.lean`](lean-v8/GoalDocumentNamedNativeMain.lean) | Single-file paths: [`NamedGoalDocumentDepth.lean`](lean-v8/NamedGoalDocumentDepth.lean), [`NamedInputsDocument.lean`](lean-v8/NamedInputsDocument.lean). Cited bundles: [`CitedDocumentNativeCore.lean`](lean-v8/CitedDocumentNativeCore.lean) |
| `fang-bundle-tstp` | [`BundleTstpLimitNativeMain.lean`](lean-v8/BundleTstpLimitNativeMain.lean) | [`BundleDocumentLimit.lean`](lean-v8/BundleDocumentLimit.lean), [`BundleDocument.lean`](lean-v8/BundleDocument.lean) |
| `fang-v8-tstp`, `fang-goal-tstp` | [`DocumentNativeMain.lean`](lean-v8/DocumentNativeMain.lean), [`GoalDocumentV8NativeMain.lean`](lean-v8/GoalDocumentV8NativeMain.lean) | Unnamed expanded/goal export entries retained alongside the named exports |
| `fang-model-tstp` | [`ModelExportNativeMain.lean`](lean-v8/ModelExportNativeMain.lean) | [`ModelExport.lean`](lean-v8/ModelExport.lean), [`ModelExportComplete.lean`](lean-v8/ModelExportComplete.lean) |

For the mathematical definitions, begin with [`Fang/Logic.lean`](lean-v8/Fang/Logic.lean), [`Fang/Checker.lean`](lean-v8/Fang/Checker.lean) and [`Fang/SourceSemantics.lean`](lean-v8/Fang/SourceSemantics.lean). The rest of the proof chain is divided by transformation:

- Byte parsing and grammar: `Fof*`, `CnfBoolean*`, `ExpandedDecoder*` and the `Fang/Frontend*` modules connect accepted tokens to source formulas. [`CnfBooleanByteSemantics.lean`](lean-v8/CnfBooleanByteSemantics.lean) is a useful boundary between bytes and semantics.
- Quantifiers and preprocessing: [`QuantifiedFormula.lean`](lean-v8/QuantifiedFormula.lean), [`Skolem.lean`](lean-v8/Skolem.lean), [`BinderRemoval.lean`](lean-v8/BinderRemoval.lean), [`RemovalSemantics.lean`](lean-v8/RemovalSemantics.lean), [`ScopedCnfSemantics.lean`](lean-v8/ScopedCnfSemantics.lean) and [`NamedReplay.lean`](lean-v8/NamedReplay.lean) cover the representations and transformations used in replay.
- Equality and the certificate trace: [`EqualityOrderedCertificateInput.lean`](lean-v8/EqualityOrderedCertificateInput.lean), [`EqualityDerivation.lean`](lean-v8/EqualityDerivation.lean) and [`ExpandedReplay.lean`](lean-v8/ExpandedReplay.lean) connect inference reconstruction to refutation.
- Checked-clause storage: [`Trace.lean`](lean-v8/Trace.lean) defines `ArrayStore`; [`OrderedTrace.lean`](lean-v8/OrderedTrace.lean) adds ordered inference replay. Their `check` functions use arrays, while `checkList` retains the list reference and `check_eq_list` proves identical results and errors. The document builder's retained trace is separate, in [`EqualityTrace.lean`](lean-v8/EqualityTrace.lean).
- Includes, distinct objects and roles: `BundleFramer*`, `CoverageDistinct`, `Role*`, `Signed*` and `NamedCited*` connect the selected original records to replay. Cited replay proves the full input's result from the retained premises; distinct-object information must survive that reduction.
- TSTP syntax and meaning: [`Product/`](lean-v8/Product/) supplies term/clause rendering, annotated rows and source links. `ExpandedDocument`, `BundleDocument`, `NamedDocument`, `NamedGoalDocument` and `ModelExport` prove properties of the actual export functions.

The compiled entries use the limits in [`NativeLimits.lean`](lean-v8/NativeLimits.lean). Rust producer preparation has matching records in [`fang-tptp-expanded/src/final_limits.rs`](crates/fang-tptp-expanded/src/final_limits.rs) and [`fang-saturation/src/experimental/final_limits.rs`](crates/fang-saturation/src/experimental/final_limits.rs). These records are part of the executable contract, not just performance settings.

### Cited document export

The V4 cited exporter is under integration. `signed_documents` selects it by the producer's task kind and the optional pinned `tstp.cited_exporter` capability. This also covers a bundle task whose resolved closure contains only one file. [`CitedDocumentNativeCore.lean`](lean-v8/CitedDocumentNativeCore.lean) reads the bounded certificate envelope and sealed file triples, then selects the goal or input-refutation path.

| Component | Where to look |
| --- | --- |
| Retained goal task and checked derivation | [`NamedCitedDocumentTrace.lean`](lean-v8/NamedCitedDocumentTrace.lean): `build`, replay witnesses and final-clause properties |
| Retained input-refutation task | [`CitedInputsTrace.lean`](lean-v8/CitedInputsTrace.lean): `build` and its connection to the original cited inputs |
| Original file paths, statement names and roles | [`CitedSourceRows.lean`](lean-v8/CitedSourceRows.lean): `sourceItem`, `entryRow`, `sourceRows` and their byte-level parsing checks |
| Model preservation and distinct objects | [`CitedModels.lean`](lean-v8/CitedModels.lean): models of the original task justify the preprocessing group |
| Goal document assembly | [`CitedGoalDocument.lean`](lean-v8/CitedGoalDocument.lean): `goalDocument`, `exportGoalDocument`, labels and derivation rows |
| Selected goal and its negation | [`CitedGoalSemantics.lean`](lean-v8/CitedGoalSemantics.lean): `selected_goal_negated` and `goalDocument_negated` |
| Input-refutation document assembly | [`CitedInputsDocument.lean`](lean-v8/CitedInputsDocument.lean): `document` and `exportDocument` |
| Axiom reports and rejection controls | [`CitedDocumentAudit.lean`](lean-v8/CitedDocumentAudit.lean), [`CitedDocumentControls.lean`](lean-v8/CitedDocumentControls.lean) |

For comment bytes, [`TptpLexical.lean`](lean-v8/TptpLexical.lean) contains `validUtf8Tail`, `validUtf8Bytes` and `validCommentUtf8`. The lexer validates UTF-8 inside comments while retaining byte offsets. The formula and identifier grammar remains ASCII.

### Kernel replay and older profiles

For `--check kernel`, follow the Rust generator through [`tools/v8_kernel/policy.json`](tools/v8_kernel/policy.json), [`recipe/mixed/sources.json`](tools/v8_kernel/recipe/mixed/sources.json) and the support proofs in [`tools/v8_kernel/lean/`](tools/v8_kernel/lean/). This route constructs and checks an exact-instance Lean theorem. It is separate from the default compiled checker.

The older explicit profiles use [`lean/Main.lean`](lean/Main.lean) for CNF and [`lean/FofMain.lean`](lean/FofMain.lean) for ground FOF, with their TSTP mains and the proof trees in [`proofs/tstp/`](proofs/tstp/) and [`proofs/fof-tstp/`](proofs/fof-tstp/). Their build and trust details are in [`lean/README.md`](lean/README.md).

## Source maps and checks when changing code

[`tools/v8_szs/rust-sources.json`](tools/v8_szs/rust-sources.json) lists Rust files, data files, dependency manifests and installed producer mappings. [`tools/v8_szs/lean-sources.json`](tools/v8_szs/lean-sources.json) lists Lean sources, audits and executable closures. [`backend-pins.json`](tools/v8_szs/backend-pins.json) identifies the backend inputs. Changes to these mapped sources must be reconciled with their maps and checked by `fang-check-sources`; a successful local compile alone does not establish that the release source inventory is consistent.

For a Rust change, start with the relevant crate's tests, then the workspace checks. The ground-FOF driver is a separate Cargo build; a workspace-only check does not cover its executable. For a checker or exporter change, follow the affected executable's Lean closure and its axiom audits. Installed command tests must exercise the launcher, because calling a producer directly skips routing, capture, checking and output rules.

The product is Rust and Lean. Some Rust modules retain Python-oriented names or comments because they preserve the former tools' behavior; they do not require a Python interpreter. Testing and benchmark harnesses kept outside this source distribution have their own dependency and acceptance rules.
