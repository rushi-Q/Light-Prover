#!/bin/bash
# official-check.sh SOLUTION_EXPORT CHALLENGE_EXPORT COMPARATOR_JSON  -> exit = the OFFICIAL comparator's exit code
# Reference verdict for export-level tests: the unmodified Lean 4.36 `lake comparator` (statement/axiom comparison + Lean
# kernel replay + the kernels named in the config, e.g. nanoda), invoked directly (independently of the package's own
# check/official stage) in a fresh empty directory with a minimal environment. FV_T36 overrides the 4.36 toolchain root.
{ # whole script parsed before it runs (safe against edits while running)
set -u
TC=${FV_T36:-$HOME/.elan/toolchains/leanprover--lean4---v4.36.0}
SOL=$(readlink -f "$1"); CH=$(readlink -f "$2"); CFG=$(readlink -f "$3")
D=$(mktemp -d "${TMPDIR:-/tmp}/fvoff.XXXXXX"); trap 'rm -rf "$D"' EXIT
cp "$CFG" "$D/comparator.json"; cd "$D"
env -i HOME="$HOME" PATH="$TC/bin:/usr/bin:/bin" LANG=C.UTF-8 timeout "${FV_OFFICIAL_TIMEOUT:-3600}" \
  "$TC/bin/lake" comparator --config comparator.json --challenge-from-export "$CH" --solution-from-export "$SOL" 2>&1 | tail -n 3 | cut -c1-300
exit "${PIPESTATUS[0]}"
exit $?
}
