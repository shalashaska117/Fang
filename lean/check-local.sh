#!/usr/bin/env bash
# Copyright (c) 2026 Pietro Pellegrino. BSD 3-Clause license.
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
lean_tools=${FANG_LEAN_TOOLS:-${LEAN_BIN:-}}
if [[ -z "$lean_tools" ]]; then
  printf '%s\n' 'Set FANG_LEAN_TOOLS or LEAN_BIN to the pinned Lean toolchain bin directory.' >&2
  exit 2
fi
if [[ ! -x "$lean_tools/lean" ]]; then
  printf '%s\n' 'The selected Lean toolchain bin directory does not contain an executable lean.' >&2
  exit 2
fi
exec python3 "$root/tools/replay/check-suite.py" "$root" "$lean_tools/lean" "$@"
