#!/bin/bash
# lib/macos/stage.sh - sourced by the build and export stage scripts on macOS (Apple silicon), never run.
# It supplies what those scripts take from Linux and macOS does not have:
#   bwrap        -> macos_guarded: lib/macos/sandbox-run.py (denies by default) under tools/guard/fvguard.py
#   timeout      -> the wall-time limit of that guard (STAGE_WALL, which a script sets for its timed build)
#   bind mounts  -> macos_deps: each dependency destination is a link to its checkout, made once
#   nproc, sha256sum, realpath -e|-m, mv -T and mapfile -t (bash 4) -> the functions below, for the forms the scripts
#                   use, so that the lines using them are the same on both systems; another form fails
# A script sets D (the fastverify directory), PY, STAGE_OS, STAGE_PID (its own process id) and STAGE_WALL=0. The build
# scripts export them: their timed build runs sandbox() in a child bash, which sources this file again.

macos_budget() { # macos_budget KEY: one figure of lib/budget.py's host limits
  "$PY" -I -c 'import runpy, sys; print(runpy.run_path(sys.argv[1])["host_limits"]()[sys.argv[2]])' \
    "$D/lib/budget.py" "$1"
}
nproc() { # nproc: the default number of workers, what CPUs and available memory carry
  [ $# = 0 ] || { echo "nproc $*: this form is not available on macOS" >&2; return 2; }
  macos_budget build_jobs
}
sha256sum() { /usr/bin/shasum -a 256 "$@"; }
realpath() { # realpath -e|-m -- PATH: the canonical path; -e fails unless PATH exists
  "$PY" -I -c 'import os, sys
if len(sys.argv) != 4 or sys.argv[1] not in ("-e", "-m") or sys.argv[2] != "--":
    sys.exit("realpath " + " ".join(sys.argv[1:]) + ": this form is not available on macOS")
flag, _, path = sys.argv[1:]
sys.exit(1) if flag == "-e" and not os.path.exists(path) else print(os.path.realpath(path))' "$@"
}
mv() { # mv -T SRC DST is rename(2); BSD mv would move SRC into an existing directory DST
  [ "$1" = -T ] || { /bin/mv "$@"; return; }
  "$PY" -I -c 'import os, sys; os.rename(sys.argv[1], sys.argv[2])' "$2" "$3"
}
mapfile() { # mapfile -t NAME: one element per line of standard input
  [ $# = 2 ] && [ "$1" = -t ] || { echo "mapfile $*: this form is not available on macOS" >&2; return 2; }
  local line; eval "$2=()"
  while IFS= read -r line || [ -n "$line" ]; do eval "$2+=(\"\$line\")"; done
}

macos_guarded() ( # macos_guarded OUT WORK TC [--read PATH | --write PATH | --setenv NAME VALUE]... -- CMD...
  # Readable: TC, the developer tools and every --read PATH. Writable: every --write PATH and a private directory made
  # in WORK, which CMD gets as HOME and TMPDIR. No network, none of the user's other files, and an environment of PATH,
  # LANG and every --setenv. OUT, if not empty, is opened here as CMD's standard output (the sandbox does not grant
  # it). The guard ends CMD with the stage (as bwrap's --die-with-parent does), after STAGE_WALL (what GNU timeout
  # takes: seconds, or a number with s, m, h or d), and when the physical footprint of CMD's processes exceeds the
  # machine's memory; it exits 125 then. An error of this function is exit 126, and so is a guard that ends without
  # its report: a status of the guard itself is never taken for CMD's. None of these is ever the project's verdict.
  out=$1 work=$2 tc=$3; shift 3
  developer=$(/usr/bin/xcode-select -p) || exit 126
  state=$(mktemp -d "$work/.fv-sandbox.XXXXXXXX") && state=$(cd "$state" && pwd -P) && mkdir "$state/home" || exit 126
  # The directory is removed when this function ends, also when it is killed together with the stage: a process in
  # a session of its own waits until nobody holds descriptor 9 (this function, the guard), frees what CMD may have
  # made unremovable (modes, the user's immutable flag) and removes it
  /usr/bin/mkfifo "$state/end" && exec 9<> "$state/end" || { /bin/rm -rf -- "$state"; exit 126; }
  "$PY" -I -c 'import os, subprocess, sys
try:
    os.setsid()
except OSError:
    pass
sys.stdin.read()
for step in ("/bin/chmod -R u+rwX", "/usr/bin/chflags -R nouchg", "/bin/rm -rf --"):
    subprocess.call(step.split() + [sys.argv[1]])' "$state" < "$state/end" 9>&- > /dev/null 2>&1 &
  trap 'exec 9>&-; wait; /bin/rm -rf -- "$state"' EXIT
  trap 'exit 126' INT TERM HUP
  private=$state/home   # the guard's report is written next to it, where CMD cannot write
  run=("$D/lib/macos/sandbox-run.py" --read "$tc" --read "$developer" --read "$private" --write "$private"
       --setenv PATH "$tc/bin:$developer/usr/bin:/usr/bin:/bin" --setenv HOME "$private" --setenv TMPDIR "$private"
       --setenv LANG C.UTF-8)
  until [ "${1-}" = -- ]; do
    case "${1-}" in
      --read|--write) run+=("$1" "$2"); shift 2 ;; --setenv) run+=("$1" "$2" "$3"); shift 3 ;; *) exit 126 ;;
    esac
  done
  shift
  # /usr/bin/python3 is a launcher that asks the developer tools for the interpreter. With Xcode as the developer
  # directory it needs frameworks of Xcode outside that directory, which the sandbox does not grant
  [ "$1" != /usr/bin/python3 ] || { shift; set -- "$developer/usr/bin/python3" "$@"; }
  run+=(-- "$@")   # the launcher starts CMD itself: a CMD that cannot start is its exit 126 or 127, never CMD's status
  [ -z "$out" ] || run=(/bin/sh -c 'exec "$@" > "$0"' "$out" "${run[@]}")
  guard=(--owner-pid "$STAGE_PID" --mem "$(macos_budget mem_total)" --json "$state/guard")
  [ "${STAGE_WALL:-0}" = 0 ] || guard+=(--wall "$("$PY" -I -c 'import sys
d = sys.argv[1]; unit = {"s": 1, "m": 60, "h": 3600, "d": 86400}.get(d[-1:])
seconds = float(d[:-1]) * unit if unit else float(d)
print(seconds) if seconds >= 0 else sys.exit("not a duration: " + d)' "$STAGE_WALL")")
  env -i PATH=/usr/bin:/bin "$PY" -I "$D/tools/guard/fvguard.py" "${guard[@]}" -- "${run[@]}"
  rc=$?; [ -s "$state/guard" ] || rc=126
  exit $rc
)

macos_deps() { # macos_deps BINDFILE PROJ: mkbinds on macOS. The same rule: each destination is made ONCE, before any
  # untrusted code runs, never through a symlink (realpath = the path itself, before and after), never outside PROJ.
  local src dst
  while IFS=$'\t' read -r src dst; do
    [ -n "$src" ] || continue
    bindok "$src" "$dst" "$2" || return 2
    [ "$src" = "$dst" ] && continue
    [ -d "$src" ] && [ ! -e "$dst" ] && [ ! -L "$dst" ] && [ "$(realpath -m -- "$dst")" = "$dst" ] || return 2
    mkdir -p -- "${dst%/*}" && ln -s -- "$src" "$dst" || return 2
    [ "$(realpath -e -- "${dst%/*}")" = "${dst%/*}" ] || return 2
  done < "$1"
}

macos_sandbox() ( # macos_sandbox PROJ TC BINDFILE LOGDIR THREADS CMD...: sandbox() of the build scripts on macOS,
  # with the same grants: TC and every source of BINDFILE readable, PROJ and LOGDIR writable, CMD started in PROJ.
  proj=$1 tc=$2 binds=$3 logd=$4 threads=$5; shift 5
  work=${TMPDIR:-/tmp} args=(--read "$D/lib/budget.py")
  [ -z "$proj" ] || args+=(--read "$proj" --write "$proj")
  [ -z "$proj" ] || [ ! -w "${proj%/*}" ] || work=${proj%/*}
  if [ -n "$binds" ]; then
    while IFS=$'\t' read -r src dst; do
      [ -n "$src" ] || continue
      # nothing is created here (macos_deps made the links before any untrusted code ran); a helper path that is
      # missing, or a link that no longer leads to its checkout -> no sandbox (fail closed)
      bindok "$src" "$dst" "$proj" || exit 126
      if [ "$src" = "$dst" ]; then [ -e "$src" ] || exit 126
      else [ -L "$dst" ] && [ "$(/usr/bin/readlink -- "$dst")" = "$src" ] || exit 126; fi
      args+=(--read "$src")
    done < "$binds"
  fi
  [ -z "$logd" ] || args+=(--read "$logd" --write "$logd")
  [ -z "$threads" ] || args+=(--setenv LEAN_NUM_THREADS "$threads")
  cd "${proj:-/}" || exit 126
  macos_guarded "" "$work" "$tc" "${args[@]}" -- "$@"
)

macos_lpconfined() { # macos_lpconfined FILE PROJ TC BINDFILE: the LEAN_PATH rule where a dependency is a link, not a
  # mount. On Linux every entry is inside PROJ, because the checkouts are mounted there. Lake on macOS resolves the link
  # and lists the checkout itself. So an entry is TC/lib/lean, or a plain path inside PROJ that resolves to itself, or
  # a plain path that resolves into the checkout of a BINDFILE line whose link still leads there, named by the checkout
  # or through the link. Any other directory, also another directory of the packages workspace, is refused.
  "$PY" -I - "$1" "$2" "$3" "$4" <<'PY'
import os, sys
lp, proj, tc = open(sys.argv[1]).read().strip(), sys.argv[2], sys.argv[3]
links = [row.split("\t") for row in open(sys.argv[4]).read().split("\n") if row]
def below(path, root):
    return path == root or path.startswith(root + os.sep)
for e in lp.split(":"):
    if not e or e == os.path.join(tc, "lib", "lean"):
        continue
    if any(ord(c) < 32 or 127 <= ord(c) <= 159 for c in e) or not os.path.isabs(e) or ".." in e.split("/"):
        sys.exit("LEAN_PATH entry is not a plain absolute path: %r" % e)
    n = os.path.normpath(e)
    real = os.path.realpath(n)
    if n.startswith(proj + os.sep) and real == n:
        continue
    for src, dst in links:
        parent = os.path.dirname(dst)
        if (src != dst and (below(n, src) or below(n, dst)) and below(real, src) and os.path.islink(dst)
                and os.path.realpath(parent) == parent and os.path.realpath(dst) == src):
            break
    else:
        sys.exit("LEAN_PATH entry outside the project %s and its dependencies (or through a symlink): %r" % (proj, e))
PY
}
