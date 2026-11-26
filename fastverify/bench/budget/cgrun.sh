#!/bin/bash
# cgrun.sh - run one command under cgroup-v2 limits and record what it used (peak memory, OOM kills, CPU, per-process RSS).
#
#   cgrun.sh --name NAME [--mem SIZE] [--cpus LIST] [--tasks N] [--sample SEC] [--ps SEC] [--json FILE] [--timeline FILE]
#            [--timeout SEC] -- CMD...
#
# The limits are applied by a site-provided scope launcher (CGRUN_TOOL; a transient systemd scope: memory.max = SIZE with
# swap 0 -> exceeding it = kernel OOM kill, AllowedCPUs = LIST, TasksMax = N; it needs sudo). Inside the scope,
# cgrun-inner.sh (same directory) samples the scope's own cgroup every --sample seconds (memory.current / anon / file /
# shmem -> --timeline), optionally every process's RSS (--ps SEC -> "top_procs", "max_rss_by_comm"), runs CMD (optionally
# under `timeout --signal=KILL SEC`) and writes ONE JSON object (--json FILE and stdout): limits as read from the cgroup,
# the command's exit code, wall seconds, memory.peak, sampled maxima, memory.events (oom, oom_kill, max, high), cpu.stat,
# pids.peak. Exit code = the command's (137 = killed; "oom_kill" > 0 tells an OOM kill from a timeout).
# Note: a forked child's RSS includes copy-on-write pages shared with its parent (a zygote tree shows the same ~N GB in
# every child); the cgroup's memory.peak charges shared pages once.
set -u
HERE=$(cd "$(dirname "$(readlink -f "$0")")" && pwd)
CGRUN=${CGRUN_TOOL:-cgrun}   # the cgroup scope launcher: an executable path, or a command name on PATH
NAME=; MEM=; CPUS=; TASKS=; INNER=()
while [ $# -gt 0 ]; do
  case "$1" in
    --name) NAME=$2; shift 2;; --mem) MEM=$2; shift 2;; --cpus) CPUS=$2; shift 2;; --tasks) TASKS=$2; shift 2;;
    --parent|--high|--swap|--quota) shift 2;;   # accepted for compatibility; not supported by the scope launcher
    --sample|--ps|--json|--timeline|--timeout) INNER+=("$1" "$2"); shift 2;;
    --) shift; break;; *) echo "cgrun.sh: unknown argument $1" >&2; exit 2;;
  esac
done
[ -n "$NAME" ] && [ $# -gt 0 ] || { sed -n '2,16p' "$0" >&2; exit 2; }
LIM=(--name "$NAME")
[ -n "$MEM" ] && [ "$MEM" != max ] && LIM+=(--mem "$MEM")
[ -n "$CPUS" ] && LIM+=(--cpus "$CPUS")
[ -n "$TASKS" ] && LIM+=(--tasks "$TASKS")
exec "$CGRUN" "${LIM[@]}" -- "$HERE/cgrun-inner.sh" --name "$NAME" "${INNER[@]}" -- "$@"
