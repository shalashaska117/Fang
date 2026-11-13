# Fang

Fang is an automated theorem prover for first-order logic, written in Rust. By default, an independent Lean 4 checker checks each refutation or finite model against the original input before Fang reports a result.

Fang reads TPTP CNF and FOF problems, with and without equality, including conjectures, include directives, annotations and distinct objects. Checked refutations give `Theorem` or `Unsatisfiable`; checked finite models give `Satisfiable` or `CounterSatisfiable`. It can print refutations and models in TSTP format, subject to the export limits in [Usage](docs/USAGE.md). Typed and higher-order input (TFF, THF) and arithmetic are rejected.

The explicit `--check none` option reports refutation candidates without checking them and labels each run as unchecked. It is never the default.

## Quick start

Use Linux or WSL with rustup-managed Rust 1.90.0 and Lean 4.35.0. Set `LEAN_ROOT` to the Lean 4.35.0 toolchain directory. Build the local Rust tools first. The fetch command needs network access for the pinned Lean packages and the prebuilt mathlib cache. The final build command builds Fang and the Lean checkers. Build time and memory use depend on the host and toolchain cache.

```sh
cargo build --release --locked --offline -p fang-install -p fang-source-checks
target/release/fang-fetch-v8-backend --work .local/backend --lean-toolchain "$LEAN_ROOT"
target/release/fang-build-v8-local --out .local/fang --lean-toolchain "$LEAN_ROOT" \
  --packages .local/backend/project/.lake/packages --lean-work /var/tmp/lean-build
export PATH="$PWD/.local/fang/bin:$PATH"
fang examples/problems/socrates.p
fang examples/problems/mortality.p --output tstp
fang help
```

The first example has a conjecture and prints `% SZS status Theorem`. Each run also prints the checking mode in a comment line. By default a compiled Lean checker decides, which means the Lean compiler and runtime are trusted; [Usage](docs/USAGE.md) describes the options.

- [Usage](docs/USAGE.md): build, commands, checking modes, statuses and limits.
- [Capabilities](docs/CAPABILITIES.md): formats, theories, inference rules, checking and measured results.
- [Design and verification](docs/DESIGN.md): architecture, what is proved and what is trusted.
- [Roadmap](docs/ROADMAP.md): what comes next.

## Attribution

Fang is inspired by [Vampire](https://github.com/vprover/vampire). It is an independent project and is not affiliated with or endorsed by the Vampire authors.

## License

Fang contributions use [BSD-3-Clause](LICENSE); retained third-party notices are in [LICENSES](LICENSES/). Fang is built locally from source for local use. If you redistribute built binaries, you must meet the LGPL-3.0 terms of GMP, which is statically linked into the Lean executables, and keep the other notices in `LICENSES/`.
