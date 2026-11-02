# Fang

Fang is an automated theorem prover for first-order logic, written in Rust. Every proof it finds is checked by an independent Lean 4 checker against the original input before Fang reports a result.

Fang reads TPTP CNF and FOF problems, with and without equality, including conjectures, include directives, annotations and distinct objects. It reports `Theorem` or `Unsatisfiable` only after the checker accepts, and it can print the proof as a TSTP refutation, except for problems that combine conjectures with include directives. It never reports that a problem is satisfiable. Typed and higher-order input (TFF, THF) and arithmetic are rejected.

The search is still weak. On 111 TPTP problems sampled from 37 domains, Fang proved 2 and Vampire proved 61 under the same limits of 60 seconds and 2 GiB. Improving the search is the goal of the next version.

## Quick start

Use Linux or WSL with rustup-managed Rust 1.90.0, Lean 4.35.0 and Python 3.14.4. Set `LEAN_ROOT` to the Lean 4.35.0 toolchain directory. The first command needs network access: it fetches the pinned Lean packages and the prebuilt mathlib cache. The second builds Fang; its Lean part takes about 20 minutes and close to 4 GiB of memory.

```sh
python3 tools/fetch-v8-backend.py --work .local/backend --lean-toolchain "$LEAN_ROOT"
python3 tools/build-v8-local.py --out .local/fang --lean-toolchain "$LEAN_ROOT" \
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
