# Design and verification

Fang separates searching for a proof from deciding whether the proof is valid. The Rust search writes a candidate certificate; an independent Lean checker decides. The logic is classical first-order logic with equality over one nonempty domain. Terms are finite trees and function and predicate symbols are uninterpreted.

## Execution

1. Capture the input file, and every file it includes, in a private run directory.
2. Choose the checking path from the captured input: single file, bundle (includes, distinct objects or annotations), or signed bundle (a conjecture or another non-axiom role).
3. Run the Rust producer. It parses the input, normalizes formulas, removes binders, Skolemizes and clausifies, then searches with binary resolution, factoring, paramodulation and equality resolution in a bounded given-clause loop. With conjectures there is one task per selected conjecture: the premises together with that conjecture negated.
4. Run the Lean checker on the captured bytes and the candidate. It parses the input again, redoes the preprocessing and checks every step of the certificate.
5. On request, run the TSTP exporter on the accepted input and certificate.

Resource limits can stop the search or the checker. An exhausted search is `GaveUp`, never a satisfiability claim.

## What is proved

Lean theorems connect acceptance by each checker to the original input bytes. Acceptance by the single-file checker proves that the input has no model. Acceptance by the bundle checker proves the same for the bundle, with includes and selections resolved and distinct objects pairwise unequal. For the signed checker, an accepted certificate for a conjecture proves that the premises entail it, and the `Theorem` endpoint needs at least one selected conjecture and an accepted certificate for each. The proofs cover parsing, name tables, normalization, binder removal, Skolemization, clausification, equality conversion and every inference rule of the certificate, and they hold for every value of the configurable checker limits.

The TSTP proofs cover the actual Lean export functions. An exported document starts with the original statements as leaves, follows them with justified preprocessing and inference rows, and ends with the empty clause. This covers the documents Fang prints, not arbitrary TSTP proofs.

The checkers' preprocessing is Lean code extracted from Fang's Rust with Charon and Aeneas. The proofs are about the extracted Lean definitions, and the checkers run those definitions, so the soundness of a result does not depend on the extraction.

The default mode runs the checker as compiled code. The kernel mode instead checks a theorem for the exact input and certificate in Lean's kernel. The TSTP exporters always run as compiled code.

The proofs use only Lean's standard axioms `propext`, `Classical.choice` and `Quot.sound`. The build reruns the axiom audits and fails on anything else, including `sorry`.

## Trust and limits

The TPTP grammar and semantics in the Lean sources must describe the intended problem. Lean's foundations and kernel, input capture and artifact identity are trusted. Compiled checking and rendering also trust the Lean compiler and runtime, I/O, the operating system and hardware. Hashes detect replaced files; they do not prove correct execution.

The checker does not verify the Rust search. Memory safety, completeness, fairness and performance of the search are separate claims, and none of them is made. Fang forbids unsafe code in its own Rust, but native allocation and stack limits still apply. No satisfiability or model result is claimed.

## Status rules for conjectures

The signed checker's own `--goals` listing decides the status. Theorem needs at least one selected conjecture and an accepted certificate for every listed index, and each acceptance prints its listed item. Unsatisfiable needs no selected conjecture and an accepted certificate for the task of the inputs. Otherwise the status is GaveUp, ResourceOut, Inappropriate or an input error, as the rejection and the budget decide. A checker rejection of a producer candidate is an Error and never a result. A partial set of proved conjectures is never reported, and one budget covers every task of an input.

The roles `axiom`, `hypothesis`, `definition`, `lemma`, `theorem` and `corollary` are premises, `conjecture` is a goal and `negated_conjecture` is an input that is already negated. The roles `assumption`, `plain`, `type`, `interpretation` and `logic` are Inappropriate, and so is input that selects both a conjecture and a negated conjecture. Fang never reports Satisfiable or CounterSatisfiable: a search that ends without a refutation is GaveUp or ResourceOut.

## Source layout

| Directory | Contents |
| --- | --- |
| `crates/` | Rust parsers, preprocessing, equality search, producers and the kernel witness |
| `src/` | The core Rust engine: terms, unification, resolution and factoring |
| `lean-v8/` | Lean checkers, TSTP exporters and their proofs |
| `lean/`, `proofs/` | The first release's CNF and ground-FOF checker and proofs, used by the older profiles |
| `tools/` | Fetch and build scripts, the `fang` command and the kernel mode |
| `tests/`, `examples/` | Rust regressions and small example problems |
| `LICENSES/` | Third-party notices |

Experiments, benchmark runs and evidence archives stay local and are not distributed with Fang.
