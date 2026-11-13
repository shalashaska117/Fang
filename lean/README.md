# Independent certificate checker

This project uses Lean 4.35.0 and its standard library. It does not depend on the
Aeneas backend or Mathlib. The theorems describe the independent certificate
checker, its logic and preprocessing, and the checked parts of the source frontend.
See [the trust boundary](../docs/DESIGN.md) for their scope.

Run the complete local proof suite from WSL or Linux:

```sh
cargo build --release --locked --offline -p fang-install
target/release/fang-check-suite . "$LEAN_ROOT/bin/lean"
```

Set `LEAN_ROOT` to the pinned Lean toolchain directory. The runner checks the exact version in
`lean-toolchain`. Optional `--timeout-seconds` and `--memory-mib` arguments change
the per-module limits, which default to 120 seconds and 2,048 MiB.

Each run copies every project Lean source into
`.local/checks/proof-suite-<UTC>/project`, records source hashes, and compiles
the import graph in dependency order. Compilation outputs go into a new native
directory under `/var/tmp`; existing workspace `.olean` files are not used.
The manifest records the tool version and executable hash, direct standard-library
import hashes, commands, timings, memory measurements and printed axiom audits.
The pinned Lean distribution supplies the standard library; the run does not copy
or rebuild that distribution.

The runner rejects proof holes, explicit custom axioms and native decision
shortcuts in the project sources. Every `#print axioms` result must use only
`propext`, `Classical.choice` and `Quot.sound`, or no axioms. This audit covers the
printed declarations; it does not certify the compiler or operating system.

Memory control uses Lean's heap limit and samples the process tree's RSS every
50 ms. The runner kills the process group above the RSS limit and checks GNU
time's maximum-RSS measurement afterward. A short peak can occur between samples.
Linux address-space limits are unsuitable here because Lean reserves virtual
address space before using resident memory.

All project modules are included, including examples, tests, and CLI entrypoints.
Compiling an IO entrypoint does not run its native IO regressions. A compiled
`#eval` check is separate from a kernel-checked theorem. The source-byte witness
corpus and native checker regressions have their own retained runs under
`evidence/prototype`.

`FrontendFuel` proves that increasing fuel preserves each successful parser
result and its complete final state. `FrontendConsumption` proves token-count
decrease for successful term, argument, literal, clause and statement parsing.
`FrontendFuelBound.statements_token_count_fuel` proves that the public
`tokens.length + 1` budget reproduces any result that succeeds at some fuel.
`FrontendComplete` constructs that successful execution from the independent
valid-input grammar. `Fang.decode_accepts_iff_valid` proves that the pure decoder
accepts exactly this language, including fixed arities and unique clause names.
The public theorem assumes no token classification, caller-built parser state,
fuel bound, or prior parser success. Native resource limits remain separate.

`SourceAsciiValidity` proves that the independent byte grammar admits only ASCII
and relates this property to the exact UTF-8 spelling of a Lean string.
`FrontendGrammarLexing` connects that grammar to the actual tokenizer without an
extra ASCII premise. Its correspondence includes token classification: the raw
lexer can return words that the grammar rejects. Full parser soundness and
completeness use this lexical result together with the separate syntax and table
proofs. `Fang.decoded_refutation_unsat` connects accepted certificates and proved
preprocessing to the original string's independent byte semantics.
