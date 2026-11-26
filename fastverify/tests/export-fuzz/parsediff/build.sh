#!/bin/bash
# parsediff/build.sh OUTDIR : build `parsediff` from the TRUSTED reader sources of the sound check (check/sound/src:
# FastParse.lean, PChk/PersistentRead.lean, copied verbatim; their sha256 in OUTDIR/SOURCES.sha256) + ParseDiff.lean,
# with the official Lean 4.36.0 toolchain.
set -eu
OUT=$1; H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=${FV_UNDER_TEST:-$(cd "$H/../../.." && pwd)}
SRC=$FV/check/sound/src
TC=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["comparator"]["prefix"])' "$FV/config/components.json")
mkdir -p "$OUT/PChk"
cp "$SRC/FastParse.lean" "$OUT/"; cp "$SRC/PChk/PersistentRead.lean" "$OUT/PChk/"; cp "$H/ParseDiff.lean" "$OUT/"
echo "leanprover/lean4:v4.36.0" > "$OUT/lean-toolchain"
printf 'name = "parsediff"\ndefaultTargets = ["parsediff"]\n[[lean_lib]]\nname = "FastParse"\n[[lean_lib]]\nname = "PChk"\n[[lean_exe]]\nname = "parsediff"\nroot = "ParseDiff"\n' > "$OUT/lakefile.toml"
sha256sum "$SRC/FastParse.lean" "$SRC/PChk/PersistentRead.lean" > "$OUT/SOURCES.sha256"
cd "$OUT" && env -i PATH="$TC/bin:/usr/bin:/bin" HOME=/tmp lake build 2>&1 | tail -3
