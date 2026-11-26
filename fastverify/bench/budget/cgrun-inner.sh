#!/bin/bash
# cgrun-inner.sh - the measuring half of cgrun.sh: runs INSIDE the limited cgroup (the scope launcher put us there), samples
# this process's own cgroup (found through /proc/self/cgroup) and records what the command used. Options as cgrun.sh
# minus the limits (--parent/--name/--mem/--high/--swap/--cpus/--quota are accepted and ignored: they were applied by
# the outer tool); the limits are reported from the cgroup files themselves.
#
#   cgrun.sh [--parent DIR] --name NAME [--mem SIZE] [--high SIZE] [--swap SIZE] [--cpus LIST] [--quota PCT]
#            [--sample SEC] [--json FILE] [--timeline FILE] [--timeout SEC] -- CMD...
#
#   --sample SEC  timeline sampling (default 1; 0 = off)   --ps SEC  per-process RSS sampling   --timeout SEC  SIGKILL after SEC
#   --json FILE / --timeline FILE  outputs (see cgrun.sh). Exit code = the command's exit code.
set -u
PARENT=/sys/fs/cgroup/d09; NAME=; MEM=max; HIGH=max; SWAP=0; CPUS=; QUOTA=; SAMPLE=1; JSONF=; TLF=; TMO=0; PS=0
while [ $# -gt 0 ]; do
  case "$1" in
    --parent) PARENT=$2; shift 2;; --name) NAME=$2; shift 2;; --mem) MEM=$2; shift 2;; --high) HIGH=$2; shift 2;;
    --swap) SWAP=$2; shift 2;; --cpus) CPUS=$2; shift 2;; --quota) QUOTA=$2; shift 2;; --sample) SAMPLE=$2; shift 2;;
    --json) JSONF=$2; shift 2;; --timeline) TLF=$2; shift 2;; --timeout) TMO=$2; shift 2;; --ps) PS=$2; shift 2;;
    --) shift; break;; *) echo "cgrun.sh: unknown argument $1" >&2; exit 2;;
  esac
done
[ -n "$NAME" ] && [ $# -gt 0 ] || { sed -n '2,20p' "$0" >&2; exit 2; }
CG=/sys/fs/cgroup$(cut -d: -f3 /proc/self/cgroup | head -1)
[ -r "$CG/memory.peak" ] || { echo "cgrun-inner.sh: cannot read $CG/memory.peak (not inside a cgroup-v2 leaf?)" >&2; exit 2; }
MEM=$(cat "$CG/memory.max" 2>/dev/null); HIGH=$(cat "$CG/memory.high" 2>/dev/null); SWAP=$(cat "$CG/memory.swap.max" 2>/dev/null)
CPUS=$(cat "$CG/cpuset.cpus.effective" 2>/dev/null); QUOTA=$(awk '$1!="max"{printf "%d", $1/$2*100}' "$CG/cpu.max" 2>/dev/null)
# sampler (runs in the leaf too; its own memory is negligible)
SPID=
if [ "$SAMPLE" != 0 ]; then
  : "${TLF:=/dev/null}"
  (
    T0=$(date +%s.%N)
    while :; do
      cur=$(cat "$CG/memory.current" 2>/dev/null) || break
      st=$(awk '/^anon |^file |^shmem |^kernel /{printf "%s=%s ", $1, $2}' "$CG/memory.stat" 2>/dev/null)
      printf '%.1f %s %s\n' "$(echo "$(date +%s.%N) - $T0" | bc)" "$cur" "$st"
      sleep "$SAMPLE"
    done
  ) >> "$TLF" 2>/dev/null &
  SPID=$!
fi
PSPID=; PSF=
if [ "$PS" != 0 ]; then
  PSF=${JSONF:-/tmp/cgrun.$$}.ps
  : > "$PSF"
  (
    T0=$(date +%s.%N)
    while :; do
      now=$(echo "$(date +%s.%N) - $T0" | bc)
      for pid in $(cat "$CG/cgroup.procs" 2>/dev/null); do
        [ "$pid" = "$$" ] && continue
        rss=$(awk '/^VmRSS:/{print $2*1024}' /proc/$pid/status 2>/dev/null) || continue
        [ -n "$rss" ] || continue
        comm=$(cat /proc/$pid/comm 2>/dev/null)
        printf '%.1f %s %s %s\n' "$now" "$pid" "$rss" "$comm"
      done
      sleep "$PS"
    done
  ) >> "$PSF" 2>/dev/null &
  PSPID=$!
fi
T0=$(date +%s.%N)
TERMINATED=0
on_term() { TERMINATED=1; }   # systemd stops the whole scope after an OOM kill (OOMPolicy=stop): still write the record
trap on_term TERM INT HUP
if [ "$TMO" != 0 ]; then timeout --signal=KILL "$TMO" "$@" & else "$@" & fi
CPID=$!
wait "$CPID"; RC=$?
[ "$TERMINATED" = 1 ] && { wait "$CPID" 2>/dev/null; RC=143; }
T1=$(date +%s.%N)
[ -n "$SPID" ] && { kill "$SPID" 2>/dev/null; wait "$SPID" 2>/dev/null; }
[ -n "$PSPID" ] && { kill "$PSPID" 2>/dev/null; wait "$PSPID" 2>/dev/null; }
TOPJ=null; COMMJ=null
if [ -n "$PSF" ] && [ -s "$PSF" ]; then
  IFS=$'\t' read -r TOPJ COMMJ < <(/usr/bin/python3 -I - "$PSF" <<'PY'
import json, sys
best = {}; comm_max = {}; conc = {}
for ln in open(sys.argv[1]):
    p = ln.split()
    if len(p) < 4: continue
    t, pid, rss, comm = float(p[0]), p[1], int(p[2]), p[3]
    if pid not in best or rss > best[pid][1]: best[pid] = (comm, rss, t if pid not in best else best[pid][2])
    comm_max[comm] = max(comm_max.get(comm, 0), rss)
    conc.setdefault((t, comm), 0); conc[(t, comm)] += 1
cmax = {}
for (t, comm), n in conc.items(): cmax[comm] = max(cmax.get(comm, 0), n)
top = sorted(((v[1], pid, v[0], v[2]) for pid, v in best.items()), reverse=True)[:12]
print(json.dumps([{"pid": pid, "comm": comm, "max_rss": rss, "first_s": t0} for rss, pid, comm, t0 in top]),
      json.dumps({c: {"max_rss": comm_max[c], "max_concurrent": cmax.get(c, 0)} for c in comm_max}), sep="\t")
PY
) || { TOPJ=null; COMMJ=null; }
fi
# collect
WALL=$(echo "$T1 - $T0" | bc | sed 's/^\./0./')
PEAK=$(cat "$CG/memory.peak" 2>/dev/null || echo null)
EV=$(awk '{printf "\"%s\":%s,", $1, $2}' "$CG/memory.events" 2>/dev/null | sed 's/,$//')
CPU=$(awk '{printf "\"%s\":%s,", $1, $2}' "$CG/cpu.stat" 2>/dev/null | sed 's/,$//')
PIDS=$(cat "$CG/pids.peak" 2>/dev/null || echo null)
MAXANON=null; MAXFILE=null; MAXSHMEM=null; MAXCUR=null
if [ -n "${TLF:-}" ] && [ "$TLF" != /dev/null ] && [ -s "$TLF" ]; then
  read -r MAXCUR MAXANON MAXFILE MAXSHMEM < <(awk '{c=$2; a=0; f=0; s=0; for(i=3;i<=NF;i++){split($i,kv,"="); if(kv[1]=="anon")a=kv[2]; if(kv[1]=="file")f=kv[2]; if(kv[1]=="shmem")s=kv[2]} if(c>mc)mc=c; if(a>ma)ma=a; if(f>mf)mf=f; if(s>ms)ms=s} END{print mc+0, ma+0, mf+0, ms+0}' "$TLF")
fi
CMDJ=$(printf '%s\n' "$@" | /usr/bin/python3 -I -c 'import json,sys; print(json.dumps(sys.stdin.read().split("\n")[:-1]))')
JS=$(printf '{"name":"%s","limits":{"memory_max":"%s","memory_high":"%s","swap_max":"%s","cpus":"%s","cpu_quota_pct":"%s"},"exit":%s,"wall_s":%s,"memory_peak":%s,"sampled_max":{"current":%s,"anon":%s,"file":%s,"shmem":%s},"memory_events":{%s},"cpu_stat":{%s},"pids_peak":%s,"top_procs":%s,"max_rss_by_comm":%s,"scope_terminated":%s,"host":"%s","cmd":%s}\n' \
  "$NAME" "$MEM" "$HIGH" "$SWAP" "$CPUS" "${QUOTA:-}" "$RC" "$WALL" "$PEAK" "$MAXCUR" "$MAXANON" "$MAXFILE" "$MAXSHMEM" "$EV" "$CPU" "$PIDS" "$TOPJ" "$COMMJ" "$([ "$TERMINATED" = 1 ] && echo true || echo false)" "$(hostname -s)" "$CMDJ")
printf '%s\n' "$JS"
[ -n "$JSONF" ] && printf '%s\n' "$JS" > "$JSONF"
exit "$RC"
