#!/bin/bash
# targeted_e2e.sh PKG OUT THREADS [TARGETS] [EXPORT] [DUR] : end-to-end test of the TARGETED overlap through the real
# wiring on rh-mid: build-fast's plan.jsonl/sched.out are emulated (test/fakebuild.py: the already built rh-mid tree's
# modules "finish" over DUR seconds in dependency order), PKG/overlap/snapdriver.py --targets sends targeted snapshots
# (PKG's pinned snapshot_exporter), PKG/overlap/incr-server.sh ... TARGETS runs PKG's pinned pleanchecker_incr, then
# PKG/check/sound/check-sound.sh judges EXPORT (default: the honest rh-mid export) with --incr-dir.
# TARGETS default: the 61 slowest kernel jobs of the rh-mid export (test/targets-mid.txt).
# Prints the verdict, the server's targeted-final lines and PASS/FAIL (expected: ACCEPT for the honest export with
# every target that is in the export verified and skipped; REJECT for a mutant).
# Inputs: FV_BENCH_INPUTS = benchmark inputs dir holding rh-mid/ (ref/proj = the built rh-mid project, ref/solution.export,
# challenge/challenge.export, challenge/comparator.json); TC33 = official Lean 4.33.1 toolchain (default ~/.elan).
set -u
PKG=$(readlink -f "$1"); OUT=$2; T=$3; HERE=$(dirname "$(readlink -f "$0")")
MID=${FV_BENCH_INPUTS:?benchmark inputs directory with rh-mid/ (required)}/rh-mid; PROJ=$MID/ref/proj
TG=${4:-$HERE/targets-mid.txt}; X=${5:-$MID/ref/solution.export}; DUR=${6:-120}
T33=${TC33:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}
mkdir -p "$OUT"; OUT=$(readlink -f "$OUT"); rm -rf "$OUT/incr" "$OUT/snaps" "$OUT/log" "$OUT/wd"; mkdir -p "$OUT/incr" "$OUT/snaps" "$OUT/log" "$OUT/wd"   # wd: the export copy must be visible to the server (its sandbox hides /tmp)
pin() { awk -v n="$1" '$1=="PIN" && $2==n {print $4}' "$PKG/check/sound/pins.env"; }
PLC=$(pin pleanchecker_incr); EXP=$(pin snapshot_exporter)
[ -x "$PLC" ] && [ -x "$EXP" ] || { echo "FAIL: pleanchecker_incr / snapshot_exporter not pinned"; exit 2; }
# module list + LEAN_PATH of the built rh-mid tree
(cd "$PROJ/src" && find . -name '*.lean' | sed 's|^\./||; s|\.lean$||; s|/|.|g' | sort) > "$OUT/mods.txt"
LP=$PROJ/.lake/build/lib/lean; for p in "$PROJ"/.lake/packages/*; do LP=$LP:$p/.lake/build/lib/lean; done
echo "$LP:$T33/lib/lean" > "$OUT/lp.txt"
"$PKG/overlap/incr-server.sh" "$OUT/incr" "$PLC" "$T" "$TG" &
SP=$!
python3 "$HERE/fakebuild.py" "$PROJ/src" "$OUT/mods.txt" "$OUT/lp.txt" "$OUT/log/build-fast" "$DUR" > "$OUT/fakebuild.log" 2>&1 &
FP=$!
python3 -I "$PKG/overlap/snapdriver.py" --log "$OUT/log/build-fast" --proj "$PROJ" --toolchain "$T33" --exporter "$EXP" \
  --incr-dir "$OUT/incr" --snap-dir "$OUT/snaps" --threads 8 --server-log "$OUT/incr/server.log" --targets "$TG" \
  --min-interval 10 2> "$OUT/snaps/driver.log"
wait $FP
sleep 10
"$PKG/check/sound/check-sound.sh" "$X" "$MID/challenge/challenge.export" "$MID/challenge/comparator.json" --threads "$T" \
  --incr-dir "$OUT/incr" --workdir "$OUT/wd" --json "$OUT/cs.json" --log "$OUT/cs.log" > /dev/null 2>&1
rc=$?
kill $SP 2>/dev/null; wait $SP 2>/dev/null
grep -E '^\[incr\] (targeted final|answered)' "$OUT/incr/server.log"
ans=$(grep -c '^\[incr\] answered' "$OUT/incr/server.log")
exp=0; [ "$X" = "$MID/ref/solution.export" ] || exp=1
if [ "$rc" = "$exp" ] && [ "$ans" -ge 1 ]; then echo "PASS rc=$rc (expected $exp, server answered)"; else echo "FAIL rc=$rc expected $exp answered=$ans"; exit 1; fi
