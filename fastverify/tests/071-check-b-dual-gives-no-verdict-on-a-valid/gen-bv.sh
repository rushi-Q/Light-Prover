#!/bin/bash
# gen-bv.sh OUT N: official Lean 4.33.1 build + official lean4export v4.33.0 of x/Main.lean with bvN := N
# (deepF := fun x0 .. x(N-1) => x0 used in riemannHypothesis's proof; innermost bvar index N-1)
set -e
H=$(cd "$(dirname "$0")" && pwd); T33=${FV_T33:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}
EXP=${FV_OFFICIAL_EXPORTER:-$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export}
W=$(mktemp -d "${TMPDIR:-/tmp}/fv071.XXXXXX"); trap 'rm -rf "$W"' EXIT
sed "s/^def bvN : Nat := 32768/def bvN : Nat := $2/" "$H/x/Main.lean" > "$W/Main.lean"
cd "$W" && PATH=$T33/bin:/usr/bin:/bin lean -o Main.olean Main.lean
LEAN_PATH=$W:$T33/lib/lean PATH=$T33/bin:/usr/bin:/bin "$EXP" Main -- $(cat "$H/x/export-targets.txt") > "$1"
