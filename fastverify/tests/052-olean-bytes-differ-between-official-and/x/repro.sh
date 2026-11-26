#!/bin/bash
# repro: .olean byte equality official vs fast toolchain on 4 official Lean v4.33.1 test files (tests/elab, copied to src/).
# Any x86-64 host (docker for the real fast lean). Shows: oleans DIFFER, but the official lean4export of their constants is IDENTICAL.
set -u
H=$(cd "$(dirname "$0")" && pwd); W=$(mktemp -d /tmp/foln.XXXXXX); trap 'rm -rf "$W"' EXIT
T33=$HOME/.elan/toolchains/leanprover--lean4---v4.33.1; FTC=/scratch/fastverify/tc/stage1/lib/lean; export PATH=$T33/bin:$PATH
EXP=$LIGHT_LEAN/env/tools/lean4export/.lake/build/bin/lean4export
cp -r "$H/src" "$W/src"; mkdir -p $W/off $W/fast; cd $W/src; export FL_BIND="$W"
for m in ExprLens cbv_simproc byCasesMetaM allFieldForConstants; do
  LEAN_PATH=$T33/lib/lean $T33/bin/lean -o $W/off/$m.olean $m.lean > /dev/null 2>&1
  LEAN_PATH=$FTC "$H/fastlean" -o $W/fast/$m.olean $m.lean > /dev/null 2>&1
done
LEAN_PATH=$T33/lib/lean $T33/bin/lean --run "$H/Names.lean" $W/off > $W/names.tsv
for m in ExprLens cbv_simproc byCasesMetaM allFieldForConstants; do
  tg=$(awk -F'\t' -v m=$m '$1==m {print $2}' $W/names.tsv | tr ' ' '\n' | grep -v '^_private' | grep -v '\.0\.' | tr '\n' ' ')
  c=$(cmp -s $W/off/$m.olean $W/fast/$m.olean && echo IDENTICAL || echo "DIFFER (sizes $(stat -c %s $W/off/$m.olean) / $(stat -c %s $W/fast/$m.olean))")
  LEAN_PATH=$W/off:$T33/lib/lean $EXP $m -- $tg > $W/e.off 2>/dev/null; LEAN_PATH=$W/fast:$T33/lib/lean $EXP $m -- $tg > $W/e.fast 2>/dev/null
  e=$(cmp -s $W/e.off $W/e.fast && echo IDENTICAL || echo DIFFER)
  echo "$m: olean $c; official lean4export (all $(echo $tg | wc -w) public constants of the module, $(stat -c %s $W/e.off) bytes) $e"
done
