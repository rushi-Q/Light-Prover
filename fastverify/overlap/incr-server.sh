#!/bin/bash
# incr-server.sh DIR PLEANCHECKER THREADS [TARGETS] : run the incremental Lean-kernel leg (pleanchecker --incremental=DIR)
# in a sandbox like the comparator's kernels (no network, read-only /, home dirs and /tmp hidden, clean environment).
# Full mode (no TARGETS): lowest CPU priority (nice 19: it only uses CPU the build leaves idle).
# Targeted mode (TARGETS = file of declaration names, e.g. check/sound/hints/default.txt): the file is copied to
# DIR/targets.txt and passed as --targeted=DIR/targets.txt; nice 0 (only the target checks run during the build: ~24k
# CPU-s for the 279 RH hints; at nice 19 they would starve behind a saturated build, and the final replay must not lose to the
# other check legs); PCHK_PRIO_FILE = the same list for the final replay. INCR_NICE overrides the nice level.
# DIR must exist and be private to this run; it gets the FIFO DIR/cmd, the lock DIR/lock and the answers DIR/res-*.
# stderr -> DIR/server.log. Exit = the server's.
# /dev/shm stays visible read-only: the final export may live there (fastverify --export-dir /dev/shm).
set -u
DIR=$(readlink -f -- "$1"); PLC=$(readlink -f -- "$2"); T=$3; TG=${4:-}
[ -d "$DIR" ] || { echo "incr-server: no directory $DIR" >&2; exit 2; }
[ -p "$DIR/cmd" ] || mkfifo -m 600 "$DIR/cmd" || exit 2
[ -f "$DIR/lock" ] || : > "$DIR/lock" || exit 2
NICE=19; EXTRA=(); SENV=()
if [ -n "$TG" ]; then
  cp -- "$TG" "$DIR/targets.txt" || { echo "incr-server: cannot copy $TG" >&2; exit 2; }
  NICE=0; EXTRA=("--targeted=$DIR/targets.txt")
  # the final replay runs in this process: priority hints (order only, absent names ignored) = the targets + the CS
  # hint list (check/sound/hints/default.txt: with fewer targets the other long jobs must stay in front) +
  # overlap/hints-next.txt (the next tier of slow jobs, which forms the tail once the targets are skipped)
  HERE="$(dirname -- "$(readlink -f -- "$0")")"
  cat "$DIR/targets.txt" > "$DIR/prio.txt" || exit 2
  for f in "$HERE/../check/sound/hints/default.txt" "$HERE/hints-next.txt"; do [ -f "$f" ] && cat -- "$f" >> "$DIR/prio.txt"; done
  SENV=(--setenv PCHK_PRIO_FILE "$DIR/prio.txt" --setenv PCHK_SLOW_MS 10000)
  # transparent huge pages from mimalloc (allocator option, verdict-neutral): kept on a host without direct-compaction
  # stalls so far (/proc/vmstat compact_stall 0, e.g. the 384-thread server: THP is ~10 % faster), off elsewhere (a compaction
  # storm stalled a fragmented host with ~280 concurrent target checks). INCR_THP=1/0 forces on/off.
  THP=${INCR_THP:-}
  if [ -z "$THP" ]; then
    CS=$(awk '$1=="compact_stall"{print $2}' /proc/vmstat 2>/dev/null)
    if [ "${CS:-1}" = 0 ]; then THP=1; else THP=0; fi
  fi
  [ "$THP" = 1 ] || SENV+=(--setenv MIMALLOC_ALLOW_THP 0)
fi
NICE=${INCR_NICE:-$NICE}
exec env -i /usr/bin/bwrap --unshare-all --die-with-parent --new-session \
  --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run --tmpfs /tmp --dev /dev --proc /proc \
  --ro-bind-try /dev/shm /dev/shm \
  --bind "$DIR" "$DIR" --chdir "$DIR" \
  --setenv HOME "$DIR" --setenv LANG C.UTF-8 --setenv LEAN_ABORT_ON_PANIC 1 --setenv LEAN_STACK_SIZE_KB 917376 \
  --setenv PATH /usr/bin:/bin "${SENV[@]}" \
  -- /usr/bin/nice -n "$NICE" "$PLC" "--incremental=$DIR" "${EXTRA[@]}" "-j$T" -v 2>> "$DIR/server.log"
