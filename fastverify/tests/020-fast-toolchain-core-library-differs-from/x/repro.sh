#!/bin/bash
# repro for the core-library finding. Any host with docker (the ubuntu:24.04 image is loaded from a saved copy if missing, never pulled), else falls back
# to a native build of 7586a50cec. ~3 min (the constant dump imports Lean+Std+Lake twice).
set -u
H=$(cd "$(dirname "$0")" && pwd); W=$(mktemp -d /tmp/fcore.XXXXXX); trap 'rm -rf "$W"' EXIT
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1; export PATH=$T33/bin:$PATH
EXP=$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export
cp -r "$H/src" "$W/src"; cp "$H/Dump.lean" "$W/src/"; mkdir -p "$W/off" "$W/fast"; cd "$W/src"
if docker info >/dev/null 2>&1; then FAST="$H/fastlean"; FTC=/scratch/fastverify/tc/stage1/lib/lean; export FL_BIND="$W/fast:$W/src"; echo "FAST = /scratch/fastverify/tc/stage1 (real binary, ubuntu:24.04 container)"
else FAST=/scratch/fast-tc/7586/bin/lean; FTC=/scratch/fast-tc/7586/lib/lean; echo "FAST = FALLBACK /scratch/fast-tc/7586"; fi
echo "--- constants of Lean+Std+Lake core libraries (name, type hash, value hash):"
LEAN_PATH=$T33/lib/lean $T33/bin/lean --run Dump.lean > $W/off.txt; LEAN_PATH=$FTC $FAST --run Dump.lean > $W/fast.txt
cut -f1 $W/off.txt | sort > $W/on; cut -f1 $W/fast.txt | sort > $W/fn
echo "official: $(wc -l < $W/on) constants; fast: $(wc -l < $W/fn); only fast: $(comm -13 $W/on $W/fn | wc -l) (public: $(comm -13 $W/on $W/fn | grep -vc '^_private')); only official: $(comm -23 $W/on $W/fn | wc -l); same name but different type/value: $(join -t$'\t' <(sort $W/off.txt) <(sort $W/fast.txt) | awk -F'\t' '$2!=$4 || $3!=$5' | wc -l)"
echo "public fast-only: $(comm -13 $W/on $W/fn | grep -v '^_private' | paste -sd' ')"
for m in Probe UsesNewApi; do
  LEAN_PATH=$T33/lib/lean $T33/bin/lean -o $W/off/$m.olean $m.lean > $W/o 2>&1; ro=$?; echo "== $m.lean official rc=$ro: $(paste -sd' ' $W/o | cut -c1-160)"
  LEAN_PATH=$FTC $FAST -Ddebug.skipKernelTC=true -Dlinter.all=false -o $W/fast/$m.olean $m.lean > $W/o 2>&1; rf=$?; echo "== $m.lean fast     rc=$rf: $(paste -sd' ' $W/o | cut -c1-160)"
done
cd $W
LEAN_PATH=$W/off:$T33/lib/lean $EXP Probe -- flag > p.off 2>/dev/null; LEAN_PATH=$W/fast:$T33/lib/lean $EXP Probe -- flag > p.fast 2>/dev/null
echo "official lean4export of Probe.flag (export reads the official core, as pipeline/export.sh): official build vs fast build -> $(cmp -s p.off p.fast && echo IDENTICAL || echo DIFFERENT)"
diff <(grep -E 'Bool.(true|false)' p.off | head -3) <(grep -E 'Bool.(true|false)' p.fast | head -3)
LEAN_PATH=$W/fast:$T33/lib/lean $EXP UsesNewApi -- main_thm > u.fast 2>/dev/null; echo "fast build of UsesNewApi exported (rc=$?), official 4.36 leanchecker on it: $($HOME/.elan/toolchains/leanprover--lean4---v4.36.0/bin/leanchecker --from-export u.fast 2>&1 | tail -1)"
