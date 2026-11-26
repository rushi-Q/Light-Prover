#!/bin/bash
# incr-server-args.sh DIR PLEANCHECKER THREADS [EXTRA ARGS...] : fastverify/overlap/incr-server.sh's exact sandbox and
# arguments, plus EXTRA arguments for pleanchecker (e.g. --targeted=FILE for the targeted mode). Test harness only.
# GATE_SERVER_NO_THP=1: MIMALLOC_ALLOW_THP=0 for the server (allocator option, verdict-neutral; for hosts with fragmented
# memory where THP direct compaction stalls an RH-size server).
set -u
DIR=$(readlink -f -- "$1"); PLC=$(readlink -f -- "$2"); T=$3; shift 3
[ -d "$DIR" ] || { echo "incr-server-args: no directory $DIR" >&2; exit 2; }
[ -p "$DIR/cmd" ] || mkfifo -m 600 "$DIR/cmd" || exit 2
[ -f "$DIR/lock" ] || : > "$DIR/lock" || exit 2
RO=(); for a in "$@"; do case "$a" in --targeted=*) RO+=(--ro-bind "${a#--targeted=}" "${a#--targeted=}");; esac; done
exec env -i /usr/bin/bwrap --unshare-all --die-with-parent --new-session \
  --ro-bind / / --tmpfs /home --tmpfs /root --tmpfs /run --tmpfs /tmp --dev /dev --proc /proc \
  --ro-bind-try /dev/shm /dev/shm "${RO[@]}" \
  --bind "$DIR" "$DIR" --chdir "$DIR" \
  --setenv HOME "$DIR" --setenv LANG C.UTF-8 --setenv LEAN_ABORT_ON_PANIC 1 --setenv LEAN_STACK_SIZE_KB 917376 \
  --setenv PATH /usr/bin:/bin ${GATE_SERVER_NO_THP:+--setenv MIMALLOC_ALLOW_THP 0} \
  -- /usr/bin/nice -n 19 "$PLC" "--incremental=$DIR" "-j$T" -v "$@" 2>> "$DIR/server.log"
