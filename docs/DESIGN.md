# Design and verification

Fang separates searching for a proof from deciding whether that proof is valid.
The current logic is classical first-order logic over one nonempty domain,
without built-in equality or interpreted theories. Terms are finite trees;
functions and predicates are uninterpreted.

## Execution

1. Capture the original input bytes in a private run directory.
2. Parse the restricted CNF language and remove identical duplicate literals.
3. Search in Rust using binary resolution, factoring and a bounded FIFO
   given-clause queue. A predicate/polarity index selects candidate pairs.
4. Check the resulting internal certificate with the independent Lean checker.
5. Optionally render a TSTP derivation with original leaves, preprocessing,
   variable renaming, substitutions and inference witnesses.

The engine uses owned terms, numeric identifiers, simultaneous substitutions
and first-order unification with an occurs check. Resource limits can stop
search or checking. Fang does not interpret an exhausted queue as SAT.

## What is proved

General Lean theorems connect acceptance by the independent checker to
unsatisfiability of the original input bytes under the declared grammar. They
cover source decoding, name interpretation, duplicate-literal preprocessing,
substitution, renaming, resolution, factoring and certificate trace soundness.

The TSTP proof covers the actual Lean export function. Successful export yields
the original source leaves, a justified derivation, exact inference metadata,
relevant ancestry, uniquely parsed ordered rows and a final empty clause.
This covers the emitted subset, not all TPTP syntax or arbitrary external proofs.

The default command profile checks a theorem for the exact captured problem
and internal certificate through Lean's kernel. The compiled profile executes
the independent checker instead. Both profiles execute the TSTP exporter as
compiled code; neither separately kernel-checks each printed byte stream.

The proofs use Lean's standard `propext`, `Classical.choice` and `Quot.sound`
axioms. They do not use application-specific axioms or admitted obligations.

## Trust and limits

The source grammar and semantics must describe the intended problem. Lean's
foundations, kernel implementation, input capture and artifact identity remain
trusted. Compiled checking and rendering also trust compilation, runtime, I/O,
the operating system and hardware. Hashes detect artifact changes; they do not
prove correct execution.

The independent checker does not verify the entire Rust engine. Memory safety,
functional correctness, logical soundness, calculus completeness, search
fairness and performance are separate claims. Fang forbids its own unsafe Rust,
but native allocation and stack limits still apply. No whole-search completeness
or SAT/model correctness is claimed. Performance remains an engineering target.

The development pipeline for direct Rust verification is
Rust -> Charon -> Aeneas -> Lean 4. Extraction and library-model correspondence
are additional trust boundaries. That work is separate from the reproducible
checker/exporter proofs shipped here; experimental extraction runs are local.

## Source layout

| Directory | Purpose |
| --- | --- |
| `src/`, `crates/` | Rust engine and predicate index |
| `lean/` | Independent checker, semantics and TSTP exporter |
| `proofs/tstp/` | Export correspondence proofs and replay command |
| `tools/` | Build, checked command, kernel replay and tests |
| `tests/`, `examples/` | Rust regressions and small authored problems |
| `LICENSES/` | Third-party notices and source references |

Experiment code, benchmark runs, evidence archives and development diaries are
kept locally and are not distributed with Fang.
