# Using Fang

Fang currently accepts strict, equality-free first-order CNF. TPTP is the input
language; TSTP is the annotated derivation format used for proof output.

## Build

The tested host is Linux/WSL with rustup-managed Rust 1.90.0, Lean 4.35.0 and
Python 3.14.4. Install those toolchains first and set `LEAN_BIN` to the directory
containing the pinned `lean` and `lake` executables.

```sh
python3 tools/build-local.py --out .local/fang --lean-tools "$LEAN_BIN"
```

The destination must be new. Setup captures the source, builds the Rust engine
and Lean checker/exporter, runs the Rust tests and independent Lean proof suite,
and retains the required legal notices. It uses installed toolchains offline.

## Run

```sh
.local/fang/bin/fang-szs examples/problems/mortality.p \
  --artifacts .local/runs/mortality --output tstp
```

The example says that every human is mortal, Socrates is human, and Socrates is
not mortal. The expected result is `Unsatisfiable` with a `CNFRefutation` block.

Each artifact directory must be new. It retains the captured `input.p`, internal
certificate, checker records and `solution.tstp`. Keep `input.p` beside
`solution.tstp`: the derivation's `file('input.p',...)` leaves refer to those exact
captured bytes. Run data stays local and is not part of the repository.

`--check kernel` is the default. It checks an input-specific theorem through
Lean's kernel. `--check compiled` explicitly selects the compiled checker;
there is no automatic fallback. Both profiles use the compiled TSTP exporter.
Omit `--output tstp` for status-only output.

Treat output as complete only after a successful exit and the closing
`SZS output end CNFRefutation` marker. Interrupted or failed writes can leave a
partial stream. [Design and verification](DESIGN.md) explains the guarantees.

## Accepted input

```tptp
cnf(all_humans,axiom,(~human(X) | mortal(X))).
cnf(socrates_human,axiom,(human(socrates))).
cnf(socrates_not_mortal,axiom,(~mortal(socrates))).
```

- ASCII `cnf(name,axiom,(clause)).` declarations with unique clause names.
- Names match `[a-z][a-z0-9_]*`; variables match `[A-Z][A-Za-z0-9_]*`.
- Variables are local to each clause and implicitly universally quantified.
- Constants, nested function terms and predicates have fixed arities.
- Positive and negated atoms form a disjunction; standalone `$false` is the
  empty clause. Nullary symbols have no empty `()` argument list.

Comments, quoted names, includes, input annotations, other roles, equality,
explicit quantifiers, `$true`, arithmetic and non-ASCII input are unsupported.
FOF, TFF, THF and SMT-LIB are not accepted. An ordinary predicate named `eq`
has no built-in equality meaning.

## Results and limits

`Unsatisfiable` means the selected checking path accepted a refutation.
`GaveUp` means search found no refutation within its strategy and bounds; it
does not mean SAT. Unsupported input, malformed input, resource exhaustion,
cancellation and execution failure have separate outcomes.

The defaults are 60 seconds for the whole invocation and 2 GiB of sampled
process-tree RSS. Use `--wall-seconds` and `--memory-mib` to adjust them. Sampling
can miss brief memory peaks. TSTP export accepts at most 1 MiB each of problem
and internal certificate, 1,000 certificate nodes and 16 MiB of output.

## Development and proof replay

```sh
cargo test
cargo build --release
python3 proofs/tstp/check.py \
  --installation .local/fang/installation.json \
  --out .local/tstp-proof-replay
```

The TSTP replay recompiles the distributed proof sources against the fresh
installation. It needs no historical runs or experimental data. Its output
directory must be new. The Rust executable on its own produces candidate
refutations; use `fang-szs` for checked logical results.
