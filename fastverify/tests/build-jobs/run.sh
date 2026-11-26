#!/bin/bash
# tests/build-jobs/run.sh [WORKDIR] - regression test: Lake sizes its build job pool by the
#   host's hardware concurrency, not by the CPU set the build runs under (cgroup cpuset / affinity); build/official-build.sh
#   (B0, the fallback of every preset) therefore ran 103 `lean` processes inside a 4-CPU scope (44 GB in 150 s, 15x slower).
#   Fix: `--threads N` becomes LEAN_NUM_THREADS=N inside the sandbox, which bounds Lake's pool and each lean's threads.
# Case: a synthetic 32-module project (no dependencies; every module burns ~5 s of elaboration CPU with `#eval`), built
#   with the official toolchain through build/official-build.sh --threads 4 under a 4-CPU `taskset`; the test samples the
#   number of concurrent `lean` processes of that build every 0.1 s. PASS: peak concurrency <= 4 + 1 (one short overlap at
#   job boundaries) AND the build succeeds. Without the fix the peak is min(32, host threads).
# Env: FASTVERIFY (package root), OFFICIAL_BUILD (script under test; default $FASTVERIFY/build/official-build.sh),
#   TC (toolchain prefix; default the 4.33.1 toolchain of ~/.elan), N (modules, default 32), TEST_THREADS (default 4).
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
FV=${FASTVERIFY:-$(cd "$H/../.." && pwd)}
OB=${OFFICIAL_BUILD:-$FV/build/official-build.sh}
TC=${TC:-$HOME/.elan/toolchains/leanprover--lean4---v4.33.1}
N=${N:-32}; T=${TEST_THREADS:-4}; unset THREADS LEAN_NUM_THREADS   # nothing may leak into the script under test
W=${1:-$(mktemp -d "${TMPDIR:-/tmp}/build-jobs.XXXXXX")}; rm -rf "$W"; mkdir -p "$W/proj/Jobs"
pass=0; fail=0
ok()  { pass=$((pass+1)); echo "PASS $1"; }
bad() { fail=$((fail+1)); echo "FAIL $1: $2"; }
[ -x "$TC/bin/lake" ] || { echo "SKIP: no toolchain at $TC"; exit 0; }
command -v taskset >/dev/null || { echo "SKIP: no taskset"; exit 0; }
# the project: N independent modules, each elaborating a ~1-2 s computation (deterministic, no I/O)
printf 'name = "buildjobs"\ndefaultTargets = ["Jobs"]\n\n[[lean_lib]]\nname = "Jobs"\n' > "$W/proj/lakefile.toml"
printf '{"version": "1.1.0", "packagesDir": ".lake/packages", "packages": [], "name": "buildjobs", "lakeDir": ".lake"}\n' > "$W/proj/lake-manifest.json"
"$TC/bin/lean" --version | sed -n 's/^Lean (version \([^,]*\),.*/leanprover\/lean4:v\1/p' > "$W/proj/lean-toolchain"
imports=""
for i in $(seq 1 "$N"); do
  printf 'def burn%d (n : Nat) : Nat := Id.run do\n  let mut acc := 0\n  for k in [0:n] do\n    acc := (acc * 1103515245 + k + %d) %% 2147483647\n  return acc\n\n#eval burn%d 120000000\n' "$i" "$i" "$i" > "$W/proj/Jobs/M$i.lean"
  imports="$imports"$'\n'"import Jobs.M$i"
done
printf '%s\n' "$imports" > "$W/proj/Jobs.lean"
# run the official build under a T-CPU affinity mask (the first T CPUs this shell may use) and sample the concurrent
# lean processes of THIS build
CPUS=$(python3 -I -c 'import os,sys; print(",".join(str(c) for c in sorted(os.sched_getaffinity(0))[:int(sys.argv[1])]))' "$T")
( taskset -c "$CPUS" "$OB" "$W/proj" "$W/proj" "$TC" --threads "$T" --log "$W/log" > "$W/build.out" 2>&1; echo "rc=$?" >> "$W/build.out" ) &
bp=$!
peak=0; samples=0
while kill -0 $bp 2>/dev/null; do
  c=$(pgrep -f -c "/bin/lea[n] .*$W/proj/" 2>/dev/null || true); c=${c:-0}   # [n]: no self-match of this loop
  [ "$c" -gt "$peak" ] && peak=$c
  samples=$((samples+1)); sleep 0.1
done
wait $bp
rc=$(sed -n 's/^rc=//p' "$W/build.out" | tail -1)
echo "  official build rc=$rc, modules=$N, --threads $T under taskset -c $CPUS: peak concurrent lean = $peak ($samples samples), host threads = $(nproc --all)"
[ "$rc" = 0 ] && ok "the synthetic $N-module project builds officially" || bad "build" "rc=$rc ($(tail -2 "$W/build.out" | tr '\n' ' ' | cut -c1-200))"
[ "$peak" -le $((T+1)) ] && ok "concurrent lean processes bounded by --threads ($peak <= $((T+1)))" || bad "job-pool regression: lake ran $peak lean processes at once with --threads $T" "the pool follows the host's $(nproc --all) threads, not the CPU set"
echo "RESULT: $pass PASS, $fail FAIL"
[ $fail = 0 ]
