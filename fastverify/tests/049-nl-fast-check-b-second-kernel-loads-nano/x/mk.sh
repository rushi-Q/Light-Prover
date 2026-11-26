#!/bin/bash
# mk.sh: build proj/ with official Lean 4.33.1 and export with the official lean4export v4.33.0 -> challenge.export, solution.export
H=$(cd "$(dirname "$0")" && pwd); L=~/.elan/toolchains/leanprover--lean4---v4.33.1
OFF=$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export
TG=$(cat $LIGHT_LEAN/verify/challenge/export-targets.txt)
W=$(mktemp -d /tmp/x01-f049.XXXXXX); trap 'rm -rf "$W"' EXIT; cp "$H"/proj/*.lean "$W/"; cd "$W"; export PATH=$L/bin:$PATH LEAN_PATH=$W:$L/lib/lean
lean -o Challenge.olean Challenge.lean >/dev/null 2>&1; lean -o Main.olean Main.lean || exit 1
$OFF Challenge -- $TG > "$H/challenge.export" 2>/dev/null && $OFF Main -- $TG > "$H/solution.export" 2>/dev/null
echo "mk: challenge.export $(stat -c %s "$H/challenge.export") B, solution.export $(stat -c %s "$H/solution.export") B"
