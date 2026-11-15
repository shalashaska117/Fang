# V4 strategy training

The first complete matrix contains 256 training inputs and eight fixed strategies, for 2,048 task outcomes. The [JSON data](route-matrix-v1.json) contains every cell, captured-input hashes, producer routes, checker outcomes and diagnostic timings. The [problem lists](../v4-corpus/README.md) were frozen before training. Validation and held-out outcomes remain unused.

Each cell attempts one task: an inputs refutation if the checker lists no conjecture, otherwise the first listed conjecture. These counts are not whole-problem solve counts. Every positive result passed the unchanged compiled Lean checker and matched the selected task. Refusals, timeouts and capture failures stay in the data.

| Strategy override | Checked tasks | Additional to baseline |
| --- | ---: | ---: |
| kbo_weights=uniform | 72 | 0 |
| kbo_weights=constant-heavy | 68 | 0 |
| kbo_weights=invfreq | 67 | 0 |
| ordering=lpo | 64 | 1 |
| selection=ground-negative | 71 | 0 |
| selection=negative-equality | 69 | 0 |
| selection=lightest-negative | 67 | 1 |
| selection=lookahead | 73 | 1 |

At least one strategy checked 74 tasks. The default schedule is unchanged. Longer and unequal slices still need training measurements before schedule selection.

## Conditions

The measured installation was built from `c9fe618`, before the later stored-record limits and compact-storage work. Every strategy starts with `preset=step5`, `index=on`, `filter=on` and `simplify_new=on`, then applies the listed override. This baseline is one search configuration, not the full default launcher portfolio.

The harness follows the launcher's producer routing: plain single input, axiom bundle, signed single input or signed bundle. It allows two producer seconds and ten seconds for the complete cell, with 1,792 MiB for the producer and 2,048 MiB sampled across the process tree. Capture permits one MiB per file and four MiB per bundle. The cited producer reserves some of its slice for its replay search, leaving less than one second for discovery.

Low-priority development checks and installation work overlapped this run. The saved timings are diagnostic data, not controlled speed measurements. This matrix makes no performance claim against Vampire and does not replace the final three-mode benchmark.

## Reproduction

The [safe Rust harness](harness/src/main.rs) is byte-identical to the source used in this run. Its checks covered 40 positive task controls across all four routes and five corrupted-certificate rejections. Build the pinned source installation and verify its binaries against the JSON hashes. With the frozen TPTP archive extracted, run from the repository root:

```sh
cargo run --locked --release --manifest-path benchmarks/v4-training/harness/Cargo.toml -- \
  self-test /absolute/path/to/install /absolute/path/to/new-controls
cargo run --locked --release --manifest-path benchmarks/v4-training/harness/Cargo.toml -- \
  pilot /absolute/path/to/install /absolute/path/to/TPTP-v9.3.1 \
  /absolute/path/to/Fang/benchmarks/v4-corpus/train.tsv /absolute/path/to/new-results
```

The output directories must not exist. The harness refuses a membership file whose hash differs from the frozen training list. New runs can have different timed-search outcomes; retain their records separately.
