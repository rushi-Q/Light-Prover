#!/bin/bash
# test-fvguard.sh [WORK] : unit test of tools/guard/fvguard.py. Every probe is BOUNDED (it ends by itself within
# seconds and uses at most ~1.5 GB / 60 processes / 600 MB of disk even if the guard did nothing), so the test is safe
# on a shared node. PASS iff each probe gives the expected outcome:
#   - honest commands: exit status passed through (0, 1, 3), no violation, exit 0 only for a command that exited 0
#   - memory (anonymous heap), memory hidden in a sandbox-private tmpfs (bwrap --tmpfs /tmp), processes, threads, wall,
#     RLIMIT_CPU, RLIMIT_FSIZE, RLIMIT_DATA, output volume, disk bytes, disk entries -> the right violation key, exit 125
#   - a daemonized orphan (setsid + background) is killed with the tree in CLI mode
#   - library API run(): same outcomes, stdout kept head+tail, the tree is gone afterwards
set -u
H=$(cd "$(dirname "$(readlink -f "$0")")/.." && pwd)
G=$H/fvguard.py
W=${1:-${TMPDIR:-/tmp}/fvguard-test.$$}; rm -rf "$W"; mkdir -p "$W"
bad=0
ok() { echo "PASS $*"; }
no() { echo "FAIL $*"; bad=1; }
viol() { python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["violation"])' "$1" 2>/dev/null; }
# expect LABEL WANT_RC WANT_VIOLATION -- guard args -- command
expect() {
  local label=$1 want_rc=$2 want_v=$3; shift 3
  local js=$W/$label.json
  timeout 120 python3 -I "$G" --json "$js" "$@" > "$W/$label.out" 2> "$W/$label.err"; local rc=$?
  local v; v=$(viol "$js")
  if [ "$rc" = "$want_rc" ] && [ "$v" = "$want_v" ]; then ok "$label: rc=$rc violation=$v $(python3 -I -c 'import json,sys; d=json.load(open(sys.argv[1])); print("wall", d["wall_s"], "peak", d["peak"], "detail", d["detail"])' "$js" 2>/dev/null | cut -c1-200)"
  else no "$label: rc=$rc (want $want_rc) violation=$v (want $want_v): $(tail -c 300 "$W/$label.err")"; fi
}
PY="python3 -I -c"
# --- honest commands
expect true   0 None --mem 1G --procs 50 --wall 30 -- /bin/true
expect false  1 None --mem 1G --procs 50 --wall 30 -- /bin/false
expect exit3  3 None --mem 1G --wall 30 -- /bin/sh -c 'exit 3'
expect sigterm 143 None --wall 30 -- /bin/sh -c 'kill -TERM $$'
# --- memory: 1.5 GB in 100 MB steps (bounded), limit 600 MB
expect mem-heap 125 mem --mem 600M --wall 60 -- $PY 'import time
b=[]
for i in range(15):
    b.append(bytearray(100<<20)); time.sleep(0.15)'
# same with the cheap metric
expect mem-heap-anon 125 mem --mem 600M --mem-metric anon --wall 60 -- $PY 'import time
b=[]
for i in range(15):
    b.append(bytearray(100<<20)); time.sleep(0.15)'
# --- memory hidden in a sandbox-private tmpfs: 1 GB written to /tmp inside bwrap, the writer's own RSS stays tiny
expect mem-tmpfs 125 mem --mem 400M --wall 60 -- /usr/bin/bwrap --ro-bind / / --tmpfs /tmp --dev /dev --proc /proc \
  --unshare-all --die-with-parent --new-session -- /bin/sh -c 'for i in 1 2 3 4 5 6 7 8 9 10; do dd if=/dev/zero of=/tmp/f$i bs=1M count=100 status=none; sleep 0.2; done'
# tmpfs under the limit: honest
expect tmpfs-ok 0 None --mem 400M --wall 60 -- /usr/bin/bwrap --ro-bind / / --tmpfs /tmp --dev /dev --proc /proc \
  --unshare-all --die-with-parent --new-session -- /bin/sh -c 'dd if=/dev/zero of=/tmp/f bs=1M count=50 status=none; sleep 0.5'
# --- processes: 60 sleepers (they end after 5 s anyway), limit 20; inside a pid namespace too
expect procs 125 procs --procs 20 --wall 60 -- /bin/sh -c 'for i in $(seq 1 60); do sleep 5 & done; wait'
expect procs-sandbox 125 procs --procs 20 --wall 60 -- /usr/bin/bwrap --ro-bind / / --tmpfs /tmp --dev /dev --proc /proc \
  --unshare-all --die-with-parent --new-session -- /bin/sh -c 'for i in $(seq 1 60); do sleep 5 & done; wait'
# --- threads: 64 threads sleeping 5 s, limit 32
expect threads 125 threads --threads 32 --wall 60 -- $PY 'import threading, time
ts=[threading.Thread(target=time.sleep, args=(5,)) for _ in range(64)]
[t.start() for t in ts]; [t.join() for t in ts]'
# --- wall
expect wall 125 wall --wall 1 -- /bin/sleep 10
# --- CPU (rlimit, per process): a 20 s busy loop, limit 2 CPU-s
expect cpu 125 cpu --cpu 2 --wall 60 -- $PY 'import time
t=time.time()
while time.time()-t<20: pass'
# tree CPU: two 20 s busy children, limit 3 CPU-s for the tree
expect tree-cpu 125 tree_cpu --tree-cpu 3 --wall 60 -- /bin/sh -c "$PY 'import time
t=time.time()
while time.time()-t<20: pass' & $PY 'import time
t=time.time()
while time.time()-t<20: pass' & wait"
# --- RLIMIT_FSIZE: a 100 MB file, limit 10 MB
expect fsize 125 fsize --fsize 10M --wall 60 -- /bin/dd if=/dev/zero of="$W/fsize.bin" bs=1M count=100 status=none
# --- RLIMIT_DATA: one 1 GB allocation at once (faster than any poll), limit 512 MB -> the allocation fails inside the
# command (MemoryError -> exit 1): no violation is visible to the guard, the command itself fails = what a caller sees
expect data 1 None --data 512M --wall 60 -- $PY 'b=bytearray(1<<30)'
# --- output: 50 MB on stdout, limit 10 MB
expect output 125 output --out 10M --wall 60 -- /bin/sh -c 'head -c 50000000 /dev/zero | tr "\0" x; sleep 2'
# --- disk: 30 x 10 MB files under a dir, limit 50 MB; and 5,000 empty files, limit 1,000 entries
mkdir -p "$W/d1" "$W/d2"
expect disk 125 disk --disk "$W/d1:50M" --wall 60 -- /bin/sh -c "for i in \$(seq 1 30); do dd if=/dev/zero of=$W/d1/f\$i bs=1M count=10 status=none; sleep 0.1; done"
expect disk-files 125 disk_files --disk "$W/d2:1G" --disk-files 1000 --wall 60 -- /bin/sh -c "cd $W/d2 && for i in \$(seq 1 5000); do : > f\$i; done; sleep 2"
# --- a daemonized orphan (new session, parent exits) dies with the tree in CLI mode
python3 -I "$G" --wall 30 -- /bin/sh -c "setsid sleep 37.5 > /dev/null 2>&1 < /dev/null & exit 0" > /dev/null 2>&1
sleep 0.5
if pgrep -u "$(id -u)" -f '^sleep 37.5$' > /dev/null; then no "orphan: a daemonized 'sleep 37.5' survived"; pkill -u "$(id -u)" -f '^sleep 37.5$'; else ok "orphan: daemonized descendant killed with the tree"; fi
# --- cgroup backend (kernel-enforced memory.max / TasksMax), only where a `cgrun` launcher works (see fvguard.py --cgroup; skipped otherwise)
CG=$(python3 -I -c "import sys; sys.path.insert(0, '$H'); import fvguard as g; print(g.Limits(cgroup='cgrun', mem=1<<30).cgroup_prefix()[0])")
if [ -x "$CG" ] && "$CG" --mem 64M -- /bin/true 2>/dev/null; then
  expect cg-honest 0 None --cgroup cgrun --mem 1G --nproc 64 --wall 30 -- /bin/sh -c 'sleep 0.3'
  expect cg-mem 125 mem --cgroup cgrun --mem 600M --wall 60 -- $PY 'import time
b=[]
for i in range(15):
    b.append(bytearray(100<<20)); time.sleep(0.15)'
  expect cg-tmpfs 125 mem --cgroup cgrun --mem 400M --wall 60 -- /usr/bin/bwrap --ro-bind / / --tmpfs /tmp --dev /dev --proc /proc \
    --unshare-all --die-with-parent --new-session -- /bin/sh -c 'for i in 1 2 3 4 5 6 7 8 9 10; do dd if=/dev/zero of=/tmp/f$i bs=1M count=100 status=none; sleep 0.2; done'
  # TasksMax: the kernel refuses the forks (the command fails by itself; no watchdog violation)
  timeout 60 python3 -I "$G" --cgroup cgrun --nproc 20 --wall 30 --json "$W/cg-tasks.json" -- $PY 'import subprocess
ok = fail = 0
ps = []
for i in range(60):
    try: ps.append(subprocess.Popen(["/bin/sleep", "2"])); ok += 1
    except OSError: fail += 1
print(ok, fail)
[p.wait() for p in ps]' > "$W/cg-tasks.out" 2>&1
  read -r okn failn < <(tail -1 "$W/cg-tasks.out")
  [ "${failn:-0}" -gt 0 ] && [ "${okn:-99}" -le 20 ] && ok "cg-tasks: TasksMax 20 -> $okn started, $failn refused by the kernel" || no "cg-tasks: $(tail -2 "$W/cg-tasks.out")"
else
  echo "SKIP cgroup backend: no working cgroup launcher on this host"
fi
# --- library API
python3 -I - "$H" <<'PY' && ok "library API: honest / mem / output / tree gone" || no "library API"
import os, sys, time
sys.path.insert(0, sys.argv[1])
import fvguard as g
r = g.run(["/bin/sh", "-c", "echo hello; echo err >&2; exit 4"], g.Limits.parse("mem=1G,wall=30"))
assert r.returncode == 4 and r.violation is None and r.stdout == "hello\n" and r.stderr == "err\n", r.as_dict()
r = g.run(["python3", "-I", "-c", "import time\nb=[]\nfor i in range(15):\n b.append(bytearray(100<<20)); time.sleep(0.15)"],
          g.Limits.parse("mem=600M,wall=60"))
assert r.returncode is None and r.violation == "mem", r.as_dict()
r = g.run(["/bin/sh", "-c", "head -c 3000000 /dev/zero | tr '\\0' y"], g.Limits.parse("keep=1000,wall=30"))
assert r.returncode == 0 and r.out_bytes == 3000000 and r.stdout.startswith("y" * 500) and "dropped" in r.stdout, r.as_dict()
r = g.run(["/bin/sh", "-c", "sleep 30.731 & sleep 30.731 & wait"], g.Limits.parse("wall=1"))
assert r.violation == "wall"
time.sleep(0.3)
assert os.system("pgrep -f '^sleep 30.731$' > /dev/null") != 0, "tree not gone"
print("lib ok")
PY
[ $bad = 0 ] && echo "RESULT PASS" || echo "RESULT FAIL"
rm -rf "$W"
exit $bad
