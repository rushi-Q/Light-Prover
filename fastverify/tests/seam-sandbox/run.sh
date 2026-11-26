#!/bin/bash
# tests/seam-sandbox/run.sh [WORKDIR]  (kind: e2e, sound mode; ~2.5 min on one host, no Mathlib)
# Seam probe of the BUILD SANDBOX under --preset sound: x/proj-escape's Solution.lean #evals IO at elaboration time
# (inside the build sandbox): writes to /dev/shm, /tmp, $HOME, /scratch, OUT/work, OUT/incr; counts the visible pids; starts
# a setsid+nohup detached process that sleeps 75 s and then writes into the project tree, OUT/work and the host /dev/shm.
# PASS rows: verdict ACCEPTED (the module proves the target honestly); the host /dev/shm, /tmp, $HOME files do not exist
# (private tmpfs); /scratch, OUT/work, OUT/incr writes failed with EROFS; <= 8 pids visible (own pid namespace); no
# survivor right after the run and after 90 s; none of the delayed writes happened.
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd); FV=${FASTVERIFY:-${FV_ROOT:-$(cd "$H/../.." && pwd)}}
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/seam-sandbox-work.XXXXXX")}; rm -rf "$W"; mkdir -p "$W"
OUT=$W/out; fails=0
row() { echo "$1 $2: $3"; [ "$1" = PASS ] || fails=$((fails+1)); }
rm -f /dev/shm/fv-seam-probe /dev/shm/fv-seam-late /tmp/fv-seam-probe "$HOME/fv-seam-probe"
"$FV/bin/fastverify" "$H/x/proj-escape" "$H/x/challenge" "$OUT" --preset sound --threads ${EVAL_THREADS:-8} --keep-work \
  > "$W/fastverify.log" 2>&1; rc=$?
v=$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["verdict"])' "$OUT/result.json" 2>/dev/null)
[ "$rc" = 0 ] && [ "$v" = ACCEPTED ] && row PASS verdict "exit $rc $v" || row FAIL verdict "exit $rc ${v:-none}"
P=$OUT/work/proj/.lake/fv-seam-probe.txt
[ -f "$P" ] && row PASS probe-ran "$(wc -l < "$P") lines" || row FAIL probe-ran "no $P"
for f in /dev/shm/fv-seam-probe /tmp/fv-seam-probe "$HOME/fv-seam-probe"; do
  [ -e "$f" ] && row FAIL "host-file $f" "exists (a sandbox write reached the host)" || row PASS "host-file $f" "absent"
done
for p in /scratch/fv-seam-probe "$OUT/work/proj/../fv-seam-probe" "$OUT/work/proj/../../incr/fv-seam-probe"; do
  # the write fails inside the sandbox: read-only (EROFS), or the directory is not visible there at all (ENOENT: OUT/incr
  # is not bound into the build sandbox); either way nothing may appear outside the sandbox
  if grep -qE "write $p: (read-only file system|no such file or directory)" "$P" 2>/dev/null && [ ! -e "$p" ]; then
    row PASS "erofs $p" "ok: $(grep -oE "read-only file system|no such file or directory" "$P" | head -1), nothing written"
  else row FAIL "erofs $p" "$(grep -F "write $p" "$P" 2>/dev/null) $([ -e "$p" ] && echo "(file exists outside the sandbox)")"; fi
done
n=$(sed -n 's/^visible pids: //p' "$P" 2>/dev/null)
[ -n "$n" ] && [ "$n" -le 8 ] && row PASS pid-namespace "$n pids visible" || row FAIL pid-namespace "${n:-?} pids visible"
s0=$(pgrep -f 'sleep 75' | wc -l)
[ "$s0" = 0 ] && row PASS survivors-now 0 || row FAIL survivors-now "$s0"
sleep 90
s1=$(pgrep -f 'sleep 75' | wc -l)
[ "$s1" = 0 ] && row PASS survivors-90s 0 || row FAIL survivors-90s "$s1"
for f in "$OUT/work/proj/.lake/fv-seam-late.txt" /dev/shm/fv-seam-late "$OUT/work/fv-seam-late"; do
  [ -e "$f" ] && row FAIL "late-write $f" exists || row PASS "late-write $f" absent
done
E=$(readlink -f "$OUT/solution.export"); case "$E" in /dev/shm/fastverify-export.*) rm -rf "$(dirname "$E")";; esac
[ "${KEEP_WORK:-0}" = 1 ] || rm -rf "$W"
echo "RESULT $([ $fails = 0 ] && echo PASS || echo FAIL) fails=$fails"
[ $fails = 0 ]
